package RegressionOracles;

import RegressionOracles.RegressionUtil.Logger;
import RegressionOracles.RegressionUtil.Util;
import spoon.Launcher;
import spoon.reflect.code.*;
import spoon.reflect.declaration.CtClass;
import spoon.reflect.declaration.CtMethod;
import spoon.reflect.factory.Factory;
import spoon.reflect.reference.CtExecutableReference;
import utils.Pair;
import spoon.reflect.reference.CtTypeReference;
import spoon.reflect.declaration.CtElement;


import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

/**
 * Created by Mijung
 */
public class ObserverInstrumenter {

    private Factory factory;

    public ObserverInstrumenter(Factory factory) {
        this.factory = factory;
    }


    // Overload for backward compatibility - uses testClass.getSimpleName() as testName
    public Pair<CtClass,List<String>> instrumentObserver(CtMethod testMethod, Map<CtMethod, List<CtLocalVariable>> localVariablesPerTestMethod, Map<CtMethod, List<CtLocalVariable>> localVariablesPrimitive) {
        final CtClass testClass = testMethod.getParent(CtClass.class);
        return instrumentObserver(testMethod, localVariablesPerTestMethod, localVariablesPrimitive, testClass.getSimpleName());
    }

    // New version with explicit testName parameter (for primitive tests where testName != testClass.getSimpleName())
    public Pair<CtClass,List<String>> instrumentObserver(CtMethod testMethod, Map<CtMethod, List<CtLocalVariable>> localVariablesPerTestMethod, Map<CtMethod, List<CtLocalVariable>> localVariablesPrimitive, String testName) {
        final CtClass testClass = testMethod.getParent(CtClass.class);
        testClass.removeMethod(testMethod);
        final CtMethod<?> clone = testMethod.clone();

        List<String> instrumentedStatements = new ArrayList<>();

        // Collect variables from the CLONED method instead of using the original method's variables
        // This ensures variable.getParent() matches the clone, not the original
        if (localVariablesPerTestMethod.containsKey(testMethod)) {
            // Get variable types from original, but find them in clone
            List<CtLocalVariable> originalVars = localVariablesPerTestMethod.get(testMethod);
            List<CtLocalVariable> clonedVars = findVariablesInClone(clone, originalVars);
            instrumentedStatements.addAll(instrument(testName, clone, clonedVars));
        }
        if (localVariablesPrimitive.containsKey(testMethod)) {
            List<CtLocalVariable> originalVars = localVariablesPrimitive.get(testMethod);
            List<CtLocalVariable> clonedVars = findVariablesInClone(clone, originalVars);
            instrumentedStatements.addAll(instrumentPrimitive(testName, clone, clonedVars));
        }

        testClass.addMethod(clone);
        return new Pair<CtClass,List<String>>(testClass,instrumentedStatements);
    }

    /**
     * Find corresponding variables in cloned method based on variable names from original
     * 스코프 검증 추가: conditional statement 내부의 변수는 제외
     */
    private List<CtLocalVariable> findVariablesInClone(CtMethod<?> clonedMethod, List<CtLocalVariable> originalVars) {
        List<CtLocalVariable> clonedVars = new ArrayList<>();

        // Get all local variables from the cloned method
        List<CtLocalVariable> allClonedVars = clonedMethod.getElements(new spoon.reflect.visitor.filter.TypeFilter<>(CtLocalVariable.class));

        // For each original variable, find the corresponding one in clone by name and type
        for (CtLocalVariable originalVar : originalVars) {
            String varName = originalVar.getSimpleName();
            String varType = originalVar.getType().getQualifiedName();

            // Find matching variable in clone
            for (CtLocalVariable clonedVar : allClonedVars) {
                if (clonedVar.getSimpleName().equals(varName) &&
                    clonedVar.getType().getQualifiedName().equals(varType)) {
                    
                    // ★ 핵심 추가: 메서드 스코프에만 속한 변수만 수집
                    // conditional statement (for, if, while 등) 내부의 변수는 제외
                    if (isVariableInMethodScope(clonedVar, clonedMethod)) {
                        clonedVars.add(clonedVar);
                    }
                    break;  // Found match, move to next original variable
                }
            }
        }

        return clonedVars;
    }

    public CtClass instrumentObserver(CtMethod<?> testMethod, List<CtLocalVariable> localVariables) {
        final CtClass testClass = testMethod.getParent(CtClass.class);
        testClass.removeMethod(testMethod);
        final CtMethod<?> clone = testMethod.clone();
        instrument(testClass.getSimpleName(), clone, localVariables);
        testClass.addMethod(clone);
//        System.out.println(clone);
        return testClass;
    }


    public List<String> instrumentPrimitive(String testName, CtMethod<?> testMethod, List<CtLocalVariable> ctLocalVariables) {
        List<String> instrumentedStatements = new ArrayList<>();
        for(CtLocalVariable ctLocalVariable:ctLocalVariables) {
            // Check if the variable is in the method-level scope (not inside blocks like loops/conditions)
            if (isVariableInMethodScope(ctLocalVariable, testMethod)) {
                // 로컬 변수를 직접 읽는 코드 생성
                CtVariableAccess<?> varRead = factory.Code().createVariableRead(
                    ctLocalVariable.getReference(), false);
                CtInvocation invocationToObserve = createObservePrimitive(testName, Util.getKey(ctLocalVariable), varRead);
                // 메서드 끝에 observer 삽입
                testMethod.getBody().insertEnd(invocationToObserve);
                instrumentedStatements.add(invocationToObserve.toString()+";");
            }
        }
        return instrumentedStatements;
    }

    void instrumentPrimitive(String testName, CtMethod testMethod, CtLocalVariable localVariable) {
        // 로컬 변수를 직접 읽는 코드 생성
        CtVariableAccess<?> varRead = factory.Code().createVariableRead(
            localVariable.getReference(), false);
        CtInvocation invocationToObserve = createObservePrimitive(testName, Util.getKey(localVariable), varRead);
        // 메서드 끝에 observer 삽입
        testMethod.getBody().insertEnd(invocationToObserve);
    }

    // CtInvocation createObservePrimitive(String testName, String assignmentVarName, CtExpression assigned) {
    //     CtTypeAccess accessToLogger =
    //             factory.createTypeAccess(factory.createCtTypeReference(Logger.class));
    //     CtExecutableReference refObserve = factory.Type().get(Logger.class)
    //             .getMethodsByName("observe").get(0).getReference();
    //     return factory.createInvocation(
    //             accessToLogger,
    //             refObserve,
    //             factory.createLiteral(testName),
    //             factory.createLiteral(assignmentVarName),
    //             assigned
    //     );
    // }

    public List<String> instrument(String testName, CtMethod<?> testMethod, List<CtLocalVariable> ctLocalVariables) {
         List<String> allInstrumentedStatements = new ArrayList<>();
         
         // 필드 참조(CtFieldRead)도 observe하여 로컬 변수와 필드를 분리
         observeFieldReferences(testName, testMethod, allInstrumentedStatements);

         for (CtLocalVariable ctLocalVariable : ctLocalVariables) {
             // Check if the variable is in the method-level scope (not inside blocks like loops/conditions)
             if (!isVariableInMethodScope(ctLocalVariable, testMethod)) {
                 continue;
             }

             CtTypeReference<?> varType = ctLocalVariable.getType();
             
             // 1. String 타입 또는 Primitive 타입이면 변수 자체의 값을 observe
             boolean shouldObserveVariable = false;
             if (varType != null) {
                 if ("java.lang.String".equals(varType.getQualifiedName())) {
                     shouldObserveVariable = true;
                 } else if (varType.isPrimitive()) {
                     shouldObserveVariable = true;
                 }
             }
             
               if (shouldObserveVariable) {
                   // 로컬 변수를 직접 읽는 코드 생성 (필드 참조와 혼동되지 않도록)
                   CtVariableAccess<?> varRead = factory.Code().createVariableRead(
                       ctLocalVariable.getReference(), false);
                   CtInvocation observeVariable =
                       createObservePrimitive(testName, Util.getKey(ctLocalVariable), varRead);
                   
                   // Debug logging for String variables
                //    if ("java.lang.String".equals(varType.getQualifiedName())) {
                //        System.out.println("[ObserverInstrumenter] Adding observer for String variable: " + ctLocalVariable.getSimpleName() + " = " + ctLocalVariable.getDefaultExpression());
                //    }
                   
                   // 메서드 끝에 observer 삽입 (MUT 실행 후 최종 상태 캡처)
                   testMethod.getBody().insertEnd(observeVariable);
                   allInstrumentedStatements.add(observeVariable.toString() + ";");
               }

               // [핵심 수정] null 초기화 또는 빈 문자열 초기화 변수는 getter 처리 제외
               // Check if variable is initialized to null or empty string
               boolean isNullInitialized = false;
               boolean isEmptyStringInitialized = false;
               CtExpression defaultExpr = ctLocalVariable.getDefaultExpression();
               if (defaultExpr instanceof CtLiteral) {
                   Object value = ((CtLiteral) defaultExpr).getValue();
                   if (value == null) {
                       isNullInitialized = true;
                   } else if (value instanceof String && ((String) value).isEmpty()) {
                       isEmptyStringInitialized = true;
                   }
               }
               
               // 2. getter가 있으면 getter의 결과를 observe (null 초기화 또는 빈 문자열 초기화 제외)
               List<CtMethod> getters = Util.getGetters(ctLocalVariable);
               if (getters.size() > 0 && !isNullInitialized && !isEmptyStringInitialized) {
                  CtIf ifStatement = factory.Core().createIf();
                  CtExpression<Boolean> cond =
                      factory.Code().createCodeSnippetExpression(ctLocalVariable.getSimpleName() + "!=null");
                  ifStatement.setCondition(cond);

                  CtBlock thenBlock = factory.Core().createBlock();
                  CtTypeReference<?> t = ctLocalVariable.getType();
                  if (t != null && "java.lang.String".equals(t.getQualifiedName())) {
                      CtVariableAccess<?> varRead =
                          factory.Code().createVariableRead(ctLocalVariable.getReference(), false);
                      CtInvocation observeStringSelf =
                          createObservePrimitive(testName, Util.getKey(ctLocalVariable) + ".[String]", varRead);
                      thenBlock.addStatement(observeStringSelf);
                  }

                  for (CtMethod getter : getters) {
                      CtInvocation invocationToGetter = Util.invok(getter, ctLocalVariable);
                      CtInvocation invocationToObserve =
                          createObserve(testName, Util.getKey(getter, ctLocalVariable), invocationToGetter);
                      thenBlock.addStatement(invocationToObserve.clone());
                  }

                  CtBlock elseBlock = factory.Core().createBlock();
                  // In else block, observe that it was null
                  // (This is already done by the initial observeVariable call above if shouldObserveVariable is true)

                  ifStatement.setThenStatement(thenBlock);
                  if (thenBlock.getStatements().size() > 0) {
                      testMethod.getBody().insertEnd(ifStatement);
                      allInstrumentedStatements.addAll(Arrays.asList(ifStatement.toString().split("\n")));
                  }
               } else if (!shouldObserveVariable && !isNullInitialized && !isEmptyStringInitialized) {
                  // Object에 getter가 없으면 null 체크 후 관찰 (하지만 값 자체는 logging용)
                  CtIf ifStatement = factory.Core().createIf();
                  CtExpression<Boolean> cond =
                      factory.Code().createCodeSnippetExpression(ctLocalVariable.getSimpleName() + "!=null");
                  ifStatement.setCondition(cond);

                  CtBlock thenBlock = factory.Core().createBlock();
                  // 로컬 변수를 직접 읽는 코드 생성
                  CtVariableAccess<?> varRead = factory.Code().createVariableRead(
                      ctLocalVariable.getReference(), false);
                  CtInvocation observeVariable =
                      createObservePrimitive(testName, Util.getKey(ctLocalVariable), varRead);
                  thenBlock.addStatement(observeVariable);

                  CtBlock elseBlock = factory.Core().createBlock();
                  CtExpression nullAssigned = factory.Code().createCodeSnippetExpression("null");
                  CtInvocation observeNull =
                      createObservePrimitive(testName, Util.getKey(ctLocalVariable), nullAssigned);
                  elseBlock.addStatement(observeNull);

                  ifStatement.setThenStatement(thenBlock);
                  ifStatement.setElseStatement(elseBlock);
                  testMethod.getBody().insertEnd(ifStatement);
                  allInstrumentedStatements.addAll(Arrays.asList(ifStatement.toString().split("\n")));
               } else if (isNullInitialized) {
                   // [핵심 수정] null로 초기화된 변수는 단순히 null만 observe
                   CtExpression nullAssigned = factory.Code().createCodeSnippetExpression("null");
                   CtInvocation observeNull =
                       createObservePrimitive(testName, Util.getKey(ctLocalVariable), nullAssigned);
                   testMethod.getBody().insertEnd(observeNull);
                   allInstrumentedStatements.add(observeNull.toString() + ";");
               } else if (isEmptyStringInitialized) {
                   // [NEW] 빈 문자열로 초기화된 String 변수는 getter 관찰 제외
                   // 빈 문자열의 getter 결과(isEmpty()=true, length()=0)는 신뢰할 수 없음
                   // 아무것도 observe하지 않음
               }
         }

         return allInstrumentedStatements;
     }


    void instrument(String testName, CtMethod testMethod, CtLocalVariable localVariable) {
        
        CtTypeReference<?> t = localVariable.getType();
        if (t != null && "java.lang.String".equals(t.getQualifiedName())) {
            CtVariableAccess<?> varRead =
                factory.Code().createVariableRead(localVariable.getReference(), false);
            CtInvocation observeStringSelf =
                createObservePrimitive(testName, Util.getKey(localVariable), varRead);
            testMethod.getBody().insertEnd(observeStringSelf);
        }

   
        List<CtMethod> getters = Util.getGetters(localVariable);
        getters.forEach(getter -> {
            CtInvocation invocationToGetter = Util.invok(getter, localVariable);
            CtInvocation invocationToObserve =
                createObserve(testName, Util.getKey(getter, localVariable), invocationToGetter);
            testMethod.getBody().insertEnd(invocationToObserve);
        });
    }

    // CtInvocation createObserve(String testName, String getterKey, CtInvocation invocationToGetter) {
    //     CtTypeAccess accessToLogger =
    //             factory.createTypeAccess(factory.createCtTypeReference(Logger.class));
    //     CtExecutableReference refObserve = factory.Type().get(Logger.class)
    //             .getMethodsByName("observe").get(0).getReference();
    //     return factory.createInvocation(
    //             accessToLogger,
    //             refObserve,
    //             factory.createLiteral(testName),
    //             factory.createLiteral(getterKey),
    //             invocationToGetter
    //     );
    // }


    // In Booster/RegressionOracles/ObserverInstrumenter.java

    // 1. createObserve 메서드를 아래 코드로 교체합니다.
    CtInvocation createObserve(String testName, String getterKey, CtInvocation invocationToGetter) {
        // ★★★ 핵심 수정 ★★★
        // 1. Logger 클래스에 대한 참조를 생성합니다.
        CtTypeReference<?> loggerRef = factory.Type().createReference("RegressionOracles.RegressionUtil.Logger");
        
        // 2. Logger 클래스를 가리키는 CtTypeAccess 객체를 만듭니다. (예: "Logger.")
        CtTypeAccess<?> accessToLogger = factory.createTypeAccess(loggerRef);

        // 3. 'observe' 메서드에 대한 참조를 수동으로 생성합니다.
        CtExecutableReference<Void> refObserve = factory.createExecutableReference();
        refObserve.setSimpleName("observe");
        refObserve.setDeclaringType(loggerRef); // 이 메서드가 Logger 클래스 소속임을 명시

        // 4. 최종 호출문을 조합합니다.
        return factory.createInvocation(
                accessToLogger,
                refObserve,
                factory.createLiteral(testName),
                factory.createLiteral(getterKey),
                invocationToGetter
        );
    }

    // 2. createObservePrimitive 메서드도 동일한 방식으로 교체합니다.
    CtInvocation createObservePrimitive(String testName, String assignmentVarName, CtExpression assigned) {
        // ★★★ 동일하게 수정 ★★★
        CtTypeReference<?> loggerRef = factory.Type().createReference("RegressionOracles.RegressionUtil.Logger");
        CtTypeAccess accessToLogger = factory.createTypeAccess(loggerRef);
        
        CtExecutableReference<Void> refObserve = factory.createExecutableReference();
        refObserve.setSimpleName("observe");
        refObserve.setDeclaringType(loggerRef);

        return factory.createInvocation(
                accessToLogger,
                refObserve,
                factory.createLiteral(testName),
                factory.createLiteral(assignmentVarName),
                assigned
        );
    }
    
    /**
     * 테스트 메서드에서 사용된 모든 필드 참조(CtFieldRead)를 observe합니다.
     * 로컬 변수와 필드 참조를 구분하여 올바른 assertion을 생성합니다.
     */
    private void observeFieldReferences(String testName, CtMethod<?> testMethod, List<String> allInstrumentedStatements) {
        // 메서드 내의 모든 CtFieldRead를 찾기
        List<CtFieldRead<?>> fieldReads = testMethod.getBody().getElements(
            new spoon.reflect.visitor.filter.TypeFilter<>(CtFieldRead.class));
        
        // 이미 observe한 필드를 추적하여 중복 제거
        java.util.Set<String> observedFields = new java.util.HashSet<>();
        
        for (CtFieldRead<?> fieldRead : fieldReads) {
            String fieldQualifiedName = fieldRead.getVariable().getQualifiedName();
            
            // 중복 제거: 같은 필드를 여러 번 observe하지 않도록
            if (observedFields.contains(fieldQualifiedName)) {
                continue;
            }
            observedFields.add(fieldQualifiedName);
            
            // 필드 참조는 "field$FQN" 형식의 키로 observe
            String fieldKey = "field$" + fieldQualifiedName;
            CtInvocation observeField = createObservePrimitive(testName, fieldKey, fieldRead);
            testMethod.getBody().insertEnd(observeField);
            allInstrumentedStatements.add(observeField.toString() + ";");
        }
    }

    /**
     * Check if a local variable is declared at method level scope (not inside blocks like loops/conditions)
     * 
     * 주의: 변수가 for/while/if 등의 제어문에서 직접 선언된 경우도 제외
     * 예: for (int i = 0; ...) → i는 루프 제어 변수이므로 관찰 불가
     *     if (condition) { int x = 1; } → x는 if 블록 내 변수이므로 관찰 불가
     */
    private boolean isVariableInMethodScope(CtLocalVariable variable, CtMethod method) {
        if (variable == null || method == null) {
            return false;
        }

        // ★ 먼저 변수의 부모를 확인: 루프나 조건문에서 직접 선언된 변수인지 체크
        CtElement directParent = variable.getParent();
        
        // for/while 루프의 제어 변수 확인
        if (directParent instanceof CtLoop) {
            // 변수가 루프의 직접적인 부모인 경우 → 루프 제어 변수
            // 예: for (int i = 0; ...) 에서 i
            return false;
        }
        
        // if/switch 제어문 내의 변수 확인
        if (directParent instanceof CtIf || directParent instanceof CtSwitch) {
            return false;
        }
        
        // Get the parent element of the variable
        CtElement parent = variable.getParent();

        // Keep going up the parent chain until we find a CtBlock or CtMethod
        while (parent != null) {
            if (parent instanceof CtMethod) {
                // If we reached the method directly, it's method-level scope
                return parent.equals(method);
            } else if (parent instanceof CtBlock) {
                // Check if this block is the method's body
                CtBlock block = (CtBlock) parent;
                CtElement blockParent = block.getParent();

                if (blockParent instanceof CtMethod && blockParent.equals(method)) {
                    // This is the method's main body block - method level scope
                    return true;
                } else if (blockParent instanceof CtLoop ||
                          blockParent instanceof CtIf ||
                          blockParent instanceof CtTry ||
                          blockParent instanceof CtSwitch) {
                    // This is a block inside a control structure - not method level scope
                    return false;
                }
            }
            parent = parent.getParent();
        }

        return false;
    }
}
