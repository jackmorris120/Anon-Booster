package Generater.MUTMutation.Inlining;

import spoon.reflect.code.*;
import spoon.reflect.declaration.CtElement;
import spoon.reflect.declaration.CtVariable;
import spoon.reflect.declaration.CtMethod;
import spoon.reflect.declaration.CtParameter;
import spoon.reflect.declaration.CtType;
import spoon.reflect.factory.Factory;
import spoon.reflect.path.CtRole;
import spoon.reflect.reference.*;
import spoon.reflect.visitor.filter.TypeFilter;


import java.util.*;

public class MethodInliner {
    private final Factory factory;
    private Map<CtMethod<?>, CtBlock<?>> methodBodyCache = new HashMap<>();

    public MethodInliner(Factory factory) {
        this.factory = factory;
    }

    public Factory getFactory() {
        return this.factory;
    }

    private boolean isDirectlyRecursive(CtMethod<?> method) {
        if (method.getBody() == null)
            return false;
        for (CtInvocation<?> invocation : method.getBody().getElements(new TypeFilter<>(CtInvocation.class))) {
            if (method.equals(invocation.getExecutable().getDeclaration())) {
                return true;
            }
        }
        return false;
    }

    private void renameVariable(CtBlock<?> body, String oldName, String newName) {
        if (oldName.equals(newName))
            return;
        body.getElements(new TypeFilter<>(CtLocalVariable.class)).stream()
                .filter(v -> v.getSimpleName().equals(oldName))
                .forEach(v -> v.setSimpleName(newName));
        body.getElements(new TypeFilter<>(CtVariableAccess.class)).stream()
                .filter(va -> va.getVariable() != null && va.getVariable().getSimpleName().equals(oldName))
                .forEach(va -> va.getVariable().setSimpleName(newName));
    }

    /**
     * Try to find a concrete implementation of an abstract method
     * by looking at the receiver's actual type
     */
    private CtMethod<?> findConcreteImplementation(CtInvocation<?> invocation, CtMethod<?> abstractMethod) {
        try {
            CtType<?> receiverTypeDecl = null;
            
            // Get the receiver's actual type
            CtExpression<?> target = invocation.getTarget();
            
            if (target == null) {
                // No explicit receiver (implicit 'this') - use the declaring class of the invocation
                // This happens when calling methods from parent classes
                CtElement parent = invocation.getParent();
                while (parent != null && !(parent instanceof CtMethod)) {
                    parent = parent.getParent();
                }
                if (parent instanceof CtMethod) {
                    CtMethod<?> containingMethod = (CtMethod<?>) parent;
                    receiverTypeDecl = containingMethod.getDeclaringType();
                }
            } else if (target.getType() != null) {
                receiverTypeDecl = target.getType().getTypeDeclaration();
            }
            
            if (receiverTypeDecl == null) {
                return null;
            }
            
            CtTypeReference<?> receiverType = receiverTypeDecl.getReference();
            
            // If receiver type is the same as abstract method's declaring type, can't help
            if (receiverType.getQualifiedName().equals(abstractMethod.getDeclaringType().getQualifiedName())) {
                return null;
            }
            
            // Look for a method with the same signature in the concrete type
            String methodName = abstractMethod.getSimpleName();
            for (CtMethod<?> method : receiverTypeDecl.getMethods()) {
                if (method.getSimpleName().equals(methodName) &&
                    parametersMatch(method, abstractMethod)) {
                    return method;
                }
            }
            
            // Not found in the immediate type, check superclasses
            CtTypeReference<?> superClass = receiverTypeDecl.getSuperclass();
            while (superClass != null) {
                CtType<?> superTypeDecl = superClass.getTypeDeclaration();
                if (superTypeDecl == null) break;
                
                for (CtMethod<?> method : superTypeDecl.getMethods()) {
                    if (method.getSimpleName().equals(methodName) &&
                        parametersMatch(method, abstractMethod) &&
                        !method.isAbstract()) {
                        return method;
                    }
                }
                superClass = superTypeDecl.getSuperclass();
            }
        } catch (Exception e) {
            // Silently fail and return null
        }
        return null;
    }
    
    /**
     * Check if two methods have the same parameter types
     */
    private boolean parametersMatch(CtMethod<?> method1, CtMethod<?> method2) {
        List<CtParameter<?>> params1 = method1.getParameters();
        List<CtParameter<?>> params2 = method2.getParameters();
        
        if (params1.size() != params2.size()) {
            return false;
        }
        
        for (int i = 0; i < params1.size(); i++) {
            String type1 = params1.get(i).getType().getQualifiedName();
            String type2 = params2.get(i).getType().getQualifiedName();
            if (!type1.equals(type2)) {
                return false;
            }
        }
        
        return true;
    }

    private Map<String, CtExpression<?>> mapParametersToArguments(CtMethod<?> method, CtInvocation<?> invocation) {
        Map<String, CtExpression<?>> map = new HashMap<>();
        List<CtParameter<?>> parameters = method.getParameters();
        List<CtExpression<?>> arguments = invocation.getArguments();
        if (parameters.size() != arguments.size()) {
            return map;
        }
        for (int i = 0; i < parameters.size(); i++) {
            map.put(parameters.get(i).getSimpleName(), arguments.get(i));
        }
        return map;
    }

    private void replaceParametersWithArguments(CtBlock<?> body, Map<String, CtExpression<?>> paramToArgMap) {
        body.getElements(new TypeFilter<>(CtVariableRead.class)).forEach(varRead -> {
            String varName = varRead.getVariable().getSimpleName();
            if (paramToArgMap.containsKey(varName)) {
                varRead.replace(paramToArgMap.get(varName).clone());
            }
        });
    }

    public boolean inline(CtInvocation<?> invocation, String newVarName, int inlineOpId) {
        // Get the parent test method name for debugging
        CtMethod<?> parentTestMethod = invocation.getParent(CtMethod.class);
        String testMethodName = parentTestMethod != null ? parentTestMethod.getSimpleName() : "unknown";
        
        CtExecutableReference<?> executableRef = invocation.getExecutable();
        if (executableRef.getDeclaration() == null || !(executableRef.getDeclaration() instanceof CtMethod)) {
            return false;
        }

        CtMethod<?> calledMethod = (CtMethod<?>) executableRef.getDeclaration();

        if (isDirectlyRecursive(calledMethod)) {
            if (invocation.getRoleInParent() == CtRole.STATEMENT) {
                invocation.delete();
            } else {
                invocation.replace(factory.createLiteral(null));
            }
            return true;
        }

        if (calledMethod.isAbstract() || calledMethod.getBody() == null
                || calledMethod.getBody().getStatements().isEmpty()) {
            
            // Try to find concrete implementation
            CtMethod<?> concreteMethod = findConcreteImplementation(invocation, calledMethod);
            if (concreteMethod != null && !concreteMethod.isAbstract() && concreteMethod.getBody() != null) {
                // Use concrete implementation instead
                calledMethod = concreteMethod;
            } else {
                // No concrete implementation found - use default value
                CtTypeReference<?> returnType = calledMethod.getType();
                if (returnType != null && !returnType.getSimpleName().equals("void")) {
                    // Replace with null for non-void methods
                    invocation.replace(factory.createLiteral(null));
                    return true;
                } else {
                    // Skip void abstract methods
                    return false;
                }
            }
        }

        CtBlock<?> cachedTemplate = methodBodyCache.get(calledMethod);
        if (cachedTemplate == null) {
            cachedTemplate = calledMethod.getBody().clone();
            methodBodyCache.put(calledMethod, cachedTemplate);
        }

        CtBlock<?> clonedBody = cachedTemplate.clone();
        renameLocalVariables(clonedBody, inlineOpId);

        Map<String, CtExpression<?>> paramToArgMap = mapParametersToArguments(calledMethod, invocation);
        replaceParametersWithArguments(clonedBody, paramToArgMap);

        CtStatement statementToModify = (invocation.getRoleInParent() == CtRole.STATEMENT) ? invocation
                : invocation.getParent(CtStatement.class);
        if (statementToModify == null) {
            // System.out.println("[DEBUG] -> FAILURE: Could not find a parent statement to
            // modify.");
            return false;
        }

        if ("void".equals(calledMethod.getType().getSimpleName())) {
            statementToModify.replace(clonedBody.getStatements());
        } else {
            boolean isUsedAsExpression = (invocation.getRoleInParent() != CtRole.STATEMENT);

            // MethodInliner.java의 inline() 메서드 내부

            if (isUsedAsExpression) {
                List<CtReturn<?>> allReturns = clonedBody.getElements(new TypeFilter<>(CtReturn.class));
                if (allReturns.isEmpty() || allReturns.get(allReturns.size() - 1).getReturnedExpression() == null) {
                    // System.out.println("[DEBUG] -> FAILURE: Non-void method is missing a valid
                    // return statement.");
                    return false;
                }
                CtReturn<?> mainReturn = allReturns.remove(allReturns.size() - 1);
                CtExpression<?> returnedExpression = mainReturn.getReturnedExpression();
                allReturns.forEach(CtElement::delete);
                mainReturn.delete();

                List<CtStatement> setupStatements = clonedBody.getStatements();
                CtTypeReference<?> type = calledMethod.getType();
                CtExpression<?> initialValue;
                if (type.isPrimitive()) {
                    // 타입이 원시 타입일 경우, 이름에 따라 적절한 기본값을 할당합니다.
                    switch (type.getSimpleName()) {
                        case "boolean":
                            initialValue = factory.createLiteral(false);
                            break;
                        case "byte":
                            initialValue = factory.createLiteral((byte) 0);
                            break;
                        case "short":
                            initialValue = factory.createLiteral((short) 0);
                            break;
                        case "int":
                            initialValue = factory.createLiteral(0);
                            break;
                        case "long":
                            initialValue = factory.createLiteral(0L);
                            break;
                        case "float":
                            initialValue = factory.createLiteral(0.0f);
                            break;
                        case "double":
                            initialValue = factory.createLiteral(0.0d);
                            break;
                        case "char":
                            initialValue = factory.createLiteral('\u0000');
                            break;
                        default:
                            // 이론적으로 발생하지 않지만, 안전장치로 null을 할당합니다.
                            initialValue = factory.createLiteral(null);
                            break;
                    }
                } else {
                    // 원시 타입이 아닌 모든 참조(객체) 타입은 null로 초기화합니다.
                    initialValue = factory.createLiteral(null);
                }
                String sanitizedNewVarName = sanitizeForIdentifier(newVarName);

                CtLocalVariable<?> tempVar = factory.createLocalVariable();
                // Preserve fully qualified type name
                CtTypeReference<?> qualifiedTypeRef = factory.Type().createReference(type.getQualifiedName());
                tempVar.setType((CtTypeReference) qualifiedTypeRef);
                tempVar.setSimpleName(sanitizedNewVarName);
                tempVar.setDefaultExpression((CtExpression) initialValue);
                CtAssignment<?, ?> assignment = factory.createAssignment();
                assignment.setAssigned((CtExpression) factory.createVariableWrite(tempVar.getReference(), false));
                assignment.setAssignment((CtExpression) returnedExpression.clone());

                CtBlock<?> parentBlock = invocation.getParent(CtBlock.class);
                if (parentBlock == null) {
                    // System.err.println("FATAL: Cannot find parent block from invocation. Inlining
                    // failed.");
                    return false;
                }

                // 2. 부모 블록의 문장 리스트를 순회하여, 우리가 받은 invocation 객체를 포함하는 문장을 찾습니다.
                // 이것이 객체 참조 대신 '내용'으로 찾는 가장 확실한 방법입니다.
                CtStatement targetStatement = null;
                int insertionIndex = -1;
                List<CtStatement> blockStatements = parentBlock.getStatements();

                for (int i = 0; i < blockStatements.size(); i++) {
                    CtStatement currentStmt = blockStatements.get(i);
                    // 이 문장(currentStmt)이 우리가 찾는 invocation을 자식으로 가지고 있는지 확인
                    if (!currentStmt.getElements(new TypeFilter<CtInvocation<?>>(CtInvocation.class) {
                        @Override
                        public boolean matches(CtInvocation<?> element) {
                            // 내용이나 구조가 아닌, 정확히 그 '객체'인지 참조로 비교
                            return element == invocation;
                        }
                    }).isEmpty()) {
                        targetStatement = currentStmt;
                        insertionIndex = i;
                        break;
                    }
                }

                if (targetStatement == null) {
                    // System.err.println(
                    // "FATAL: Could not re-locate the target statement by content search. Inlining
                    // failed.");
                    return false;
                }

                // 3. 이제 확실한 타겟을 찾았으므로, 변경 및 삽입을 수행합니다.
                invocation.replace(factory.createVariableRead(tempVar.getReference(), false));

                List<CtStatement> statementsToInsert = new ArrayList<>();
                statementsToInsert.add(tempVar.clone());
                for (CtStatement setupStmt : setupStatements) {
                    statementsToInsert.add(setupStmt.clone());
                }
                statementsToInsert.add(assignment.clone());

                blockStatements.addAll(insertionIndex, statementsToInsert);

            } else {
                // void 메서드 처리 로직 (기존과 동일)
                // System.out.println(
                // "[DEBUG] -> INFO: Inlining a non-void method as a statement. All return
                // statements will be removed.");
                List<CtReturn<?>> allReturns = clonedBody.getElements(new TypeFilter<>(CtReturn.class));
                for (CtReturn<?> ret : allReturns) {
                    ret.delete();
                }
                statementToModify.replace(clonedBody.getStatements());
            }
        }
        return true;
    }

    private void renameLocalVariables(CtBlock<?> body, int inlineOpId) {
        int localVarIndex = 0;
        // 이미 이름이 변경된 변수 선언을 추적하여 중복 변경을 방지합니다.
        Set<CtLocalVariable<?>> alreadyRenamed = new HashSet<>();
    
        // 스코프가 명확하고 충돌이 잦은 for-each 루프를 먼저 찾아 처리합니다.
        for (CtForEach forEachLoop : body.getElements(new TypeFilter<>(CtForEach.class))) {
            CtLocalVariable<?> loopVar = forEachLoop.getVariable();
            if (loopVar == null || alreadyRenamed.contains(loopVar)) continue;
    
            String oldName = loopVar.getSimpleName();
            String typeName = sanitizeTypeName(loopVar.getType().getSimpleName());
            String newName = typeName + "_iL_" + inlineOpId + "_" + localVarIndex++;
    
            // 해당 루프의 몸통(body) 안에서만 사용처를 찾아 이름을 변경합니다.
            CtStatement loopBody = forEachLoop.getBody();
            if (loopBody != null) {
                for (CtVariableAccess<?> access : loopBody.getElements(new TypeFilter<>(CtVariableAccess.class))) {
                    if (access.getVariable() != null && oldName.equals(access.getVariable().getSimpleName())) {
                        access.getVariable().setSimpleName(newName);
                    }
                }
            }
            loopVar.setSimpleName(newName);
            alreadyRenamed.add(loopVar);
        }
    
        // 루프 변수가 아닌, 나머지 모든 일반 지역 변수들을 처리합니다.
        for (CtLocalVariable<?> varDecl : body.getElements(new TypeFilter<>(CtLocalVariable.class))) {
            if (alreadyRenamed.contains(varDecl)) continue;
    
            String oldName = varDecl.getSimpleName();
            String typeName = sanitizeTypeName(varDecl.getType().getSimpleName());
            String newName = oldName + "_iL_" + inlineOpId + "_" + localVarIndex++;
            
            // 변수가 선언된 가장 가까운 블록(스코프)을 찾습니다.
            CtBlock<?> ownerBlock = varDecl.getParent(CtBlock.class);
            if (ownerBlock != null) {
                // 해당 블록 내에서만 사용처를 찾아 이름을 변경하여 이름 충돌을 방지합니다.
                for (CtVariableAccess<?> access : ownerBlock.getElements(new TypeFilter<>(CtVariableAccess.class))) {
                    CtVariableReference<?> varRef = access.getVariable();
                    if (varRef != null && oldName.equals(varRef.getSimpleName())) {
                        CtVariable<?> accessDecl = varRef.getDeclaration();
                        if (accessDecl == null || accessDecl.equals(varDecl)) {
                            varRef.setSimpleName(newName);
                        }
                    }
                }
            }
            varDecl.setSimpleName(newName);
            alreadyRenamed.add(varDecl);
        }
    }

    private String sanitizeTypeName(String typeSimpleName) {
        if (typeSimpleName == null || typeSimpleName.isEmpty()) return "object";
        if ("?".equals(typeSimpleName)) {
            return "wildcard";
        }
        // 제네릭과 배열 기호를 제거하거나 안전한 문자로 변경
        String sanitized = typeSimpleName.replaceAll("\\[\\]", "_array").replaceAll("<.*>", "");
        if (sanitized.isEmpty()) return "object";
        
        // 첫 글자를 소문자로 변경
        return Character.toLowerCase(sanitized.charAt(0)) + sanitized.substring(1);
    }
    
    private String sanitizeForIdentifier(String name) {
        if (name == null || name.isEmpty()) {
            return "renamedVar";
        }
        if (!Character.isJavaIdentifierStart(name.charAt(0))) {
            return "sanitized_" + name.replaceAll("[^a-zA-Z0-9_$]", "_");
        }
        return name;
    }
}