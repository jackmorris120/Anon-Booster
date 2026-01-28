package Generater.MUTMutation;

import Compiler.Compiler;
import java.util.concurrent.TimeoutException;
import org.evosuite.shaded.org.hibernate.dialect.Sybase11Dialect;
import spoon.Launcher;
import spoon.reflect.CtModel;
import spoon.reflect.code.*;
import spoon.reflect.declaration.*;
import spoon.reflect.factory.Factory;
import spoon.reflect.visitor.filter.TypeFilter;
import spoon.support.reflect.code.*;
import spoon.reflect.reference.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import utils.Config;
import utils.Pair;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.io.IOException;
import java.util.*;
import javax.tools.*;

public class ASTParser {
    // Stores the Method Invocation(key) and Stmts(value) above it
    private static Map<CtAbstractInvocation, List<CtElement>> methodToSequence = new HashMap<>();
    private static Set<String> visitedMUTs = new HashSet<>();
    private static String packageName;
    private static Set<String> packageNameList = new HashSet<>();
    private static Set<String> importStmts = new HashSet<>();
    private static Set<String> CUT_PublicMethods = new HashSet<>();
    private static HashMap<String, CtMethod<?>> CUT_PublicMethods_Map = new HashMap<>();
    public static Map<String, Set<CtConstructor<?>>> CUT_Constructors_Map = new HashMap<>();
    public static Map<String, Set<CtConstructor<?>>> All_Constructors_Map = new HashMap<>();
    public static Map<String, List<CtTypeReference<?>>> abstractToImplsMap = new HashMap<>();
    private static HashMap<String, Set<CtMethod<?>>> allMethods = new HashMap<>();
    private static boolean recursiveMethodCalls = Config.recursiveMethodCalls;
    private static Set<CtTypeReference> MUTParamTypes = new HashSet<>();

    public static HashMap<String, Set<CtMethod<?>>> getAllMethods() {
        return allMethods;
    }

    public static void insertAllMethods(String type, CtMethod method) {
        allMethods.computeIfAbsent(type, k -> new HashSet<>()).add(method);
    }

    public static String getPackageName() {
        return packageName;
    }

    public static Set<String> getVisitedMUTs() {
        return visitedMUTs;
    }

    public static void insertVisitedMuts(String element) {
        visitedMUTs.add(element);
    }

    public static Set<String> getCUT_PublicMethods() {
        return CUT_PublicMethods;
    }

    public static Map<String, List<CtTypeReference<?>>> getAbstractToImplsMap() {
        return abstractToImplsMap;
    }

    public static Map<String, Set<CtConstructor<?>>> getCUT_Constructors_Map() {
        return CUT_Constructors_Map;
    }

    public static HashMap<String, CtMethod<?>> getCUT_PublicMethods_Map() {
        return CUT_PublicMethods_Map;
    }

    public static int getCUT_PublicMethodSize() {
        return CUT_PublicMethods.size();
    }

    public static Map<String, Set<CtConstructor<?>>> getAll_Constructors_Map() {
        return All_Constructors_Map;
    }

    public static void insertMethodSequence(CtAbstractInvocation<?> invocation, List<CtElement> sequence) {
        if (invocation == null) {
            throw new IllegalArgumentException("Invocation cannot be null");
        }
        if (sequence == null) {
            throw new IllegalArgumentException("Sequence cannot be null");
        }
        methodToSequence.put(invocation, new ArrayList<>(sequence)); // 깊은 복사로 저장
    }

    public static List<CtElement> getMethodSequence(CtAbstractInvocation<?> invocation) {
        if (invocation == null) {
            throw new IllegalArgumentException("Invocation cannot be null");
        }
        return methodToSequence.get(invocation); // 키가 없으면 null 반환
    }

    /**
     * handle method invocations and constructors
     *
     * @param method
     */
    public static void processMethodInvokeAndConstructor(CtMethod method) throws Exception {
        List<CtStatement> statements = method.getBody().getStatements();
        if (statements.size() == 0) {
            return;
        }

        int stmtIndex = statements.size() - 1;
        CtStatement lastStatement = null;
        CtAbstractInvocation mut = null;

        Pair<CtAbstractInvocation, CtStatement> mutPair = identifyMUT(method);
        if (mutPair == null) {
            return;
        }
        mut = mutPair.getKey();
        lastStatement = mutPair.getValue();
        if (mut != null) {
            if (isAssertion((CtStatement) mut) || mut.toString().toLowerCase().contains("junit.framework")) {
                return;
            }

            List<CtElement> results = retrieveBackSlice(lastStatement, method);
            methodToSequence.put(mut, results);
            processMUT(mut, method, false);
        }
    }

    public static boolean isInvocation(CtStatement stmt) {
        return stmt.getElements(new TypeFilter<>(CtInvocationImpl.class)).size() > 0;
    }

    public static boolean isLocalVariable(CtStatement stmt) {
        return stmt.getElements(new TypeFilter<>(CtLocalVariable.class)).size() == 1;
    }

    public static boolean isConstructor(CtStatement stmt) {
        return stmt.getElements(new TypeFilter<>(CtConstructorCallImpl.class)).size() > 0;
    }

    private static boolean isTryBlock(CtStatement stmt) {
        return stmt instanceof CtTry;
    }

    private static void gatherMUTParamTypes(CtMethod method) {
        Pair<CtAbstractInvocation, CtStatement> mutPair = identifyMUT(method);
        if (mutPair == null) {
            return;
        }
        CtAbstractInvocation mut = null;
        CtStatement lastStatement = null;
        try {
            mut = mutPair.getKey();
            lastStatement = mutPair.getValue();
        } catch (Exception e) {
            System.out.println("===========================================");
            System.out.println("Error Occured");
            // // e.printStackTrace();
            System.out.println(mutPair.getKey());
            System.out.println(mutPair.getValue());
        }

        CtTypeReference varType = null; // Receiver Object Type
        List<CtElement> args = mut.getArguments();

        CtElement varName = null;
        if (mut instanceof CtInvocationImpl) { // Method Invoke
            CtInvocationImpl invoke = (CtInvocationImpl) mut;
            if (invoke.getTarget() instanceof CtVariableReadImpl) { // Receiver Object reads variable
                varType = ((CtVariableReadImpl) invoke.getTarget()).getVariable().getType();
            } else if (invoke.getTarget() instanceof CtTypeAccessImpl) { // static invocation
                varType = null;
            } else {
                return;
            }
        } else if (mut instanceof CtConstructorCallImpl) {
            CtConstructorCallImpl invoke = (CtConstructorCallImpl) mut;
            varType = null;
        }
        MUTParamTypes.add(varType);
        /*
         * Process parameter args for the Last STMT
         * This does not include Receiver Objects
         */
        List<CtTypeReference<?>> formalParamTypes = mut.getExecutable().getParameters();
        boolean hasVarargs = false;
        if (!formalParamTypes.isEmpty()) {
            CtTypeReference<?> lastParamType = formalParamTypes.get(formalParamTypes.size() - 1);
            hasVarargs = lastParamType.isArray();
        }

        // Check if varargs is actually used (more args than formal params)
        boolean isVarargsUsed = hasVarargs && args.size() > formalParamTypes.size();

        int pos = 0;
        for (CtElement arg : args) {
            CtTypeReference type = null;
            CtTypeReference castType = null;
            List<CtTypeReference> casts = ((CtExpression) arg).getTypeCasts();
            type = ((CtExpression) arg).getType();
            // 형변환 타입이 있으면 변환 타입 사용 아니면 인자의 타입 가져옴
            if (casts.size() != 0)
                castType = casts.get(0);
            if (type == null && castType == null)
                continue;
            assert type != null || castType != null;

            CtTypeReference finalType = castType != null ? castType : type;

            // Only apply component type extraction when varargs is actually used
            if (isVarargsUsed && pos >= formalParamTypes.size() - 1) {
                if (finalType.isArray()) {
                    finalType = ((spoon.reflect.reference.CtArrayTypeReference<?>) finalType).getComponentType();
                }
            }

            MUTParamTypes.add(finalType);
            pos++;
        }
    }

    /**
     * get statement list by line number
     *
     * @param arg        기준이 되는 AST 요소
     * @param statements 비교할 Statement 리스트
     * @return 유효한 위치 정보를 기준으로 한 Statement 목록
     */
    private static List<CtElement> getStatements(CtElement arg, List<CtStatement> statements) {
        List<CtElement> backSlicing = new LinkedList<>();

        // 기준 요소의 위치 정보가 유효한지 확인
        if (arg == null) {
            return backSlicing;
        }
        if (arg.getPosition() == null || !arg.getPosition().isValidPosition()) {
            return backSlicing;
        }

        int argLine;
        try {
            argLine = arg.getPosition().getLine();
        } catch (UnsupportedOperationException e) {
            // // e.printStackTrace();
            return backSlicing;
        }

        for (CtStatement statement : statements) {
            if (statement.getPosition() == null || !statement.getPosition().isValidPosition()
                    || isAssertion(statement)) {
                continue;
            }
            int stmtLine;
            try {
                stmtLine = statement.getPosition().getLine();
            } catch (UnsupportedOperationException e) {
                continue;
            }

            if (argLine == stmtLine || argLine > stmtLine) {
                // [핵심 수정] 변수-to-변수 할당 형태는 제외 (br_121 = br_140; 같은 형태)
                if (!isVariableToVariableAssignment(statement)) {
                    backSlicing.add(statement);
                }
            }
        }
        return backSlicing;
    }

    /**
     * link the method name and arguments type
     * also vartype varname arguments
     * e.g.) int length = text.length(); // 여기서 text가 수신자 객체
     * 
     * @param mut
     * @throws Exception
     */
    public static void processMUT(CtAbstractInvocation mut, CtMethod method, boolean isDummy) throws Exception {

        List<CtTypeReference> types = new ArrayList<>();
        String methodName = mut.getExecutable().getSimpleName();
        CtElement varName = null;
        CtTypeReference<?> varType = null; // Receiver Object Type
        List<CtElement> args = mut.getArguments();

        if (mut instanceof CtInvocationImpl) {
            CtInvocationImpl invoke = (CtInvocationImpl) mut;
            CtExpression<?> target = invoke.getTarget();

            if (target instanceof CtVariableReadImpl) {
                varName = ((CtVariableReadImpl) target).getVariable();
                varType = ((CtVariableReadImpl) target).getVariable().getType();
            } else if (target instanceof CtFieldRead) {
                varName = target;
                varType = ((CtFieldRead<?>) target).getType();
            } else if (target instanceof CtTypeAccessImpl) {
                varName = null;
                varType = null;
            } else {
                return;
            }
        } else if (mut instanceof CtConstructorCallImpl) {
            varName = null;
            varType = null;
        }

        List<CtElement> stats = methodToSequence.get(mut);

        assert stats != null;
        assert args != null;
        assert methodName != null;

        List<CtTypeReference<?>> formalParamTypes = mut.getExecutable().getParameters();
        List<CtElement> subStats = (stats != null) ? new ArrayList<>(stats) : new ArrayList<>();

        boolean hasVarargs = false;
        if (!formalParamTypes.isEmpty()) {
            CtTypeReference<?> lastParamType = formalParamTypes.get(formalParamTypes.size() - 1);
            hasVarargs = lastParamType.isArray();
        }

        // Check if varargs is actually used (more args than formal params)
        boolean isVarargsUsed = hasVarargs && args.size() > formalParamTypes.size();

        for (int i = 0; i < args.size(); i++) {
            CtElement arg = args.get(i);
            CtTypeReference<?> effectiveType = null;

            boolean isNullLiteral = arg instanceof CtLiteral && ((CtLiteral<?>) arg).getValue() == null;

            if (isNullLiteral && i < formalParamTypes.size()) {
                effectiveType = formalParamTypes.get(i);
            } else {
                CtTypeReference<?> type = ((CtExpression<?>) arg).getType();
                List<CtTypeReference<?>> casts = ((CtExpression<?>) arg).getTypeCasts();
                effectiveType = casts.isEmpty() ? type : casts.get(0);

                if ((effectiveType == null || effectiveType.isImplicit()) && arg instanceof CtInvocation) {
                    CtInvocation<?> invocation = (CtInvocation<?>) arg;
                    CtExecutable<?> declaration = invocation.getExecutable().getDeclaration();
                    if (declaration instanceof CtMethod && ((CtMethod<?>) declaration).isAbstract()) {
                        effectiveType = invocation.getExecutable().getType();
                    }
                }
            }

            if (effectiveType == null || effectiveType.isImplicit()) {
                System.err.println("Could not determine type for arg: " + arg.toString());
                continue;
            }

            // Only apply component type extraction for actual varargs arguments
            // i.e., when varargs is actually used (more args than formal params)
            if (isVarargsUsed && i >= formalParamTypes.size() - 1 && effectiveType.isArray()) {
                // This is a varargs argument - extract the component type
                effectiveType = ((spoon.reflect.reference.CtArrayTypeReference<?>) effectiveType).getComponentType();
            }

            if (arg instanceof CtVariableRead || arg instanceof CtFieldRead
                    || !arg.getElements(new TypeFilter<>(CtVariableRead.class)).isEmpty()) {
                CandidatePool.insertVarTypeToInputPool(new Pair<>(effectiveType, arg), subStats);
            } else {
                CandidatePool.insertDirectToValues(effectiveType, arg);
            }
            types.add(effectiveType);
        }

        types.add(0, varType);

        // --- 호출 객체(Receiver Object) 처리 ---
        if (!(varName == null && varType == null)) {
            CandidatePool.insertVarTypeToInputPool(new Pair<>(varType, varName), stats);
        }

        String mutSig = varType + "." + mut.getExecutable().getSignature();
        if (!visitedMUTs.contains(mutSig)) {
            CandidatePool.insertMUTnameToArgtypes(mut, types);
            visitedMUTs.add(mutSig);
            for (CtTypeReference requiredType : types) {
                MUTParamTypes.add(requiredType);
            }
        }
    }

    private static List<CtElement> retrieveDummyBackSlice(CtElement target, List<CtStatement> statements) {
        List<CtElement> ret = new ArrayList<>();
        for (CtStatement stmt : statements) {
            // [핵심 수정] 변수-to-변수 할당 형태는 제외 (br_121 = br_140; 같은 형태)
            if (!isVariableToVariableAssignment(stmt)) {
                ret.add(stmt);
            }

            if (stmt.toString().equals(target.toString())) {
                break;
            }
        }
        return ret;
    }

    /**
     * add type to variable map
     *
     * @param testcase
     * @throws Exception
     */
    public static void processVartypeTovarnames(CtMethod testcase) throws Exception {
        List<CtLocalVariable> vars = testcase.getBody().getElements(new TypeFilter<>(CtLocalVariable.class));
        Map<String, CtLocalVariable> seenStates = new HashMap<>();

        for (CtLocalVariable var : vars) {

            if (var.getParent(CtIf.class) != null || var.getParent(CtLoop.class) != null) {
                continue;
            }
            CtTypeReference type = var.getType();
            assert type != null;
            String normalizedSignature = normalizeDeclaration(var);

            // Enhanced duplicate detection: check both processed declarations and state
            // similarity
            if (CandidatePool.isDeclarationProcessed(type, normalizedSignature)) {
                continue;
            }

            // Additional state-based deduplication
            String stateKey = generateStateKey(var, testcase);
            if (seenStates.containsKey(stateKey)) {
                // Skip this variable as we've seen an equivalent state
                continue;
            }

            // Process array types explicitly
            if (type.isArray()) {
                List<CtElement> varStmts = retrieveDummyBackSlice(var, testcase.getBody().getStatements());
                CandidatePool.insertVarTypeToInputPool(new Pair<>(type, var), varStmts);
            }
            seenStates.put(stateKey, var);

            CtElement varName = var.getReference();

            List<CtElement> stats = getStatements(var, testcase.getBody().getStatements());
            assert stats != null;

            CandidatePool.insertVarTypeToInputPool(new Pair(type, varName), stats);

            CandidatePool.addProcessedDeclaration(type, normalizedSignature);
        }
    }

    public static void processDummyVartypeTovarnames(CtMethod testcase) throws Exception {
        List<CtLocalVariable> vars = testcase.getBody().getElements(new TypeFilter<>(CtLocalVariable.class));

        for (CtLocalVariable var : vars) {
            CtTypeReference type = var.getType();
            assert type != null;

            CandidatePool.insertVartypeTovarnames(type, var);
            CtElement varName = var.getReference();
            List<CtElement> stats = retrieveDummyBackSlice(var, testcase.getBody().getStatements());
            assert stats != null;
            Pair typeAndName = new Pair(type, varName);

            if (type.isArray()) {
                CandidatePool.insertVarTypeToInputPool(new Pair<>(type, var), stats);
            }

            boolean result = CandidatePool.insertVarTypeToInputPool(typeAndName, stats);

        }
    }

    /**
     * main process to Parse and initialize Sequence pool
     *
     * @param testcases
     */
    private static void process(Set<CtMethod> testcases) throws Exception {

        for (CtMethod ctMethod : testcases) {

            removeTryCatchAndAssertion(ctMethod);
            // processMethodInvokeAndConstructor(ctMethod);
            processVartypeTovarnames(ctMethod);
            processPrimitiveVal(ctMethod);
        }

    }

    public static String normalizeDeclaration(CtLocalVariable<?> var) {
        String typeName = var.getType().getQualifiedName();
        StringBuilder normalized = new StringBuilder(typeName).append(" <VAR>");

        if (var.getDefaultExpression() != null) {
            CtExpression<?> expr = var.getDefaultExpression();
            String expressionString = normalizeExpression(expr);
            normalized.append(" = ").append(expressionString);
        } else {
            normalized.append(";");
        }

        return normalized.toString();
    }

    private static String normalizeExpression(CtExpression<?> expr) {
        if (expr == null)
            return "null";

        // Normalize constructor calls to their canonical form
        if (expr instanceof CtConstructorCall) {
            CtConstructorCall<?> ctorCall = (CtConstructorCall<?>) expr;
            StringBuilder sb = new StringBuilder();
            sb.append("new ").append(ctorCall.getType().getQualifiedName()).append("(");

            List<CtExpression<?>> args = ctorCall.getArguments();
            for (int i = 0; i < args.size(); i++) {
                if (i > 0)
                    sb.append(", ");
                sb.append(normalizeExpression(args.get(i)));
            }
            sb.append(")");
            return sb.toString();
        }

        // Normalize method invocations
        if (expr instanceof CtInvocation) {
            CtInvocation<?> invocation = (CtInvocation<?>) expr;
            StringBuilder sb = new StringBuilder();

            CtExpression<?> target = invocation.getTarget();
            if (target != null) {
                String targetStr = normalizeExpression(target);
                sb.append(targetStr).append(".");
            }

            sb.append(invocation.getExecutable().getSimpleName()).append("(");
            List<CtExpression<?>> args = invocation.getArguments();
            for (int i = 0; i < args.size(); i++) {
                if (i > 0)
                    sb.append(", ");
                sb.append(normalizeExpression(args.get(i)));
            }
            sb.append(")");
            return sb.toString();
        }

        // Normalize literals to their canonical string representation
        if (expr instanceof CtLiteral) {
            CtLiteral<?> literal = (CtLiteral<?>) expr;
            Object value = literal.getValue();
            if (value == null)
                return "null";
            if (value instanceof String)
                return "\"" + value + "\"";
            return value.toString();
        }

        // Normalize variable references to just the variable name
        if (expr instanceof CtVariableRead) {
            CtVariableRead<?> varRead = (CtVariableRead<?>) expr;
            return varRead.getVariable().getSimpleName();
        }

        // Normalize field access
        if (expr instanceof CtFieldRead) {
            CtFieldRead<?> fieldRead = (CtFieldRead<?>) expr;
            StringBuilder sb = new StringBuilder();
            if (fieldRead.getTarget() != null) {
                sb.append(normalizeExpression(fieldRead.getTarget())).append(".");
            }
            sb.append(fieldRead.getVariable().getSimpleName());
            return sb.toString();
        }

        // For other expressions, use a simplified string representation
        return expr.toString().replaceAll("\\s+", " ").trim();
    }

    private static String generateStateKey(CtLocalVariable var, CtMethod testcase) {
        StringBuilder stateKey = new StringBuilder();

        // Include type information
        stateKey.append(var.getType().getQualifiedName()).append("|");

        // Include the normalized declaration
        stateKey.append(normalizeDeclaration(var)).append("|");

        // Include context: statements that come before this variable declaration
        List<CtElement> precedingStmts = getStatements(var, testcase.getBody().getStatements());
        StringBuilder contextHash = new StringBuilder();
        for (CtElement stmt : precedingStmts) {
            if (stmt != var) { // Exclude the variable itself
                contextHash.append(stmt.toString().replaceAll("\\s+", " ").trim()).append(";");
            }
        }
        stateKey.append(contextHash.toString().hashCode()).append("|");

        // Include variable dependencies: what variables this one depends on
        Set<String> dependencies = extractVariableDependencies(var);
        String depString = dependencies.stream().sorted().reduce("", (a, b) -> a + "," + b);
        stateKey.append(depString);

        return stateKey.toString();
    }

    private static Set<String> extractVariableDependencies(CtLocalVariable var) {
        Set<String> dependencies = new HashSet<>();

        if (var.getDefaultExpression() != null) {
            // Find all variable reads in the default expression
            List<CtVariableRead> varReads = var.getDefaultExpression()
                    .getElements(new TypeFilter<>(CtVariableRead.class));
            for (CtVariableRead varRead : varReads) {
                dependencies.add(varRead.getVariable().getSimpleName());
            }

            // Find all field reads in the default expression
            List<CtFieldRead> fieldReads = var.getDefaultExpression().getElements(new TypeFilter<>(CtFieldRead.class));
            for (CtFieldRead fieldRead : fieldReads) {
                dependencies.add(fieldRead.getVariable().getSimpleName());
            }
        }

        return dependencies;
    }

    private static Pair<CtAbstractInvocation, CtStatement> identifyMUT(CtMethod method) {
        if (method.getBody() == null || method.getBody().getStatements().isEmpty()) {
            return null;
        }

        List<CtStatement> statements = method.getBody().getStatements();

        for (int i = statements.size() - 1; i >= 0; i--) {
            CtStatement currentStatement = statements.get(i);

            if (currentStatement instanceof CtTry) {
                CtTry tryBlock = (CtTry) currentStatement;
                if (tryBlock.getBody() != null && !tryBlock.getBody().getStatements().isEmpty()) {
                    Factory factory = method.getFactory();
                    CtMethod<?> tempMethod = factory.createMethod();
                    tempMethod.setBody(tryBlock.getBody());
                    Pair<CtAbstractInvocation, CtStatement> resultFromTry = identifyMUT(tempMethod);
                    if (resultFromTry != null) {
                        return resultFromTry;
                    }
                }
            }

            if (currentStatement instanceof CtInvocation) {
                return new Pair<>((CtInvocation) currentStatement, currentStatement);
            }

            if (currentStatement instanceof CtLocalVariable) {
                CtExpression<?> defaultExpr = ((CtLocalVariable<?>) currentStatement).getDefaultExpression();
                if (defaultExpr instanceof CtAbstractInvocation) {
                    return new Pair<>((CtAbstractInvocation) defaultExpr, currentStatement);
                }
            }
        }
        return null;
    }

    private static void removeTryCatchAndAssertion(CtMethod<?> testcase) {
        if (testcase == null || testcase.getBody() == null) {
            return;
        }

        // 1. 메서드 내의 모든 @Override 어노테이션을 먼저 제거합니다.
        List<CtAnnotation<?>> annotations = testcase.getElements(new TypeFilter<>(CtAnnotation.class));
        for (int i = annotations.size() - 1; i >= 0; i--) {
            CtAnnotation<?> annotation = annotations.get(i);
            if (annotation.isParentInitialized()
                    && Override.class.getName().equals(annotation.getAnnotationType().getQualifiedName())) {
                annotation.delete();
            }
        }

        // 2. 메서드 본문을 재귀적으로 처리하여 재구성합니다.
        List<CtStatement> newStatements = processStatementList(testcase.getBody().getStatements());

        // 3. 재구성된 최종 코드로 메서드 본문을 교체합니다.
        testcase.getBody().setStatements(newStatements);
    }

    private static List<CtStatement> processStatementList(List<CtStatement> statements) {
        if (statements == null)
            return new ArrayList<>();
        List<CtStatement> result = new ArrayList<>();
        for (CtStatement stmt : statements) {
            result.addAll(processSingleStatement(stmt));
        }
        return result;
    }

    private static List<CtStatement> processSingleStatement(CtStatement statement) {
        if (statement instanceof CtInvocation && isAssertionInvocation((CtInvocation<?>) statement)) {
            CtInvocation<?> assertion = (CtInvocation<?>) statement;
            List<CtStatement> extractedInvocations = new ArrayList<>();

            for (CtExpression<?> arg : assertion.getArguments()) {
                for (CtInvocation<?> call : arg.getElements(new TypeFilter<>(CtInvocation.class))) {
                    if (!isAssertionInvocation(call) && !"getMessage".equals(call.getExecutable().getSimpleName())) {

                        // 1. 원본 호출문을 정보 유실 없이 복제합니다.
                        CtInvocation<?> preservedCall = call.clone();
                        if (!preservedCall.getTypeCasts().isEmpty()) {
                            preservedCall.setTypeCasts(Collections.emptyList());
                        }

                        extractedInvocations.add(preservedCall);
                    }
                }
            }
            return extractedInvocations;
        }

        if (statement instanceof CtTry) {
            CtTry ctTry = (CtTry) statement;
            if (ctTry.getBody() != null) {
                return processStatementList(ctTry.getBody().getStatements());
            }
            return Collections.emptyList();
        }

        if (statement instanceof CtBlock) {
            return processStatementList(((CtBlock<?>) statement).getStatements());
        }

        CtStatement clonedStatement = statement.clone();
        if (clonedStatement instanceof CtLoop) {
            CtLoop loop = (CtLoop) clonedStatement;
            if (loop.getBody() instanceof CtBlock) {
                CtBlock<?> bodyBlock = (CtBlock<?>) loop.getBody();
                bodyBlock.setStatements(processStatementList(bodyBlock.getStatements()));
            } else if (loop.getBody() != null) {
                List<CtStatement> newBodyStmts = processStatementList(Collections.singletonList(loop.getBody()));
                if (!newBodyStmts.isEmpty()) {
                    loop.setBody(statement.getFactory().createBlock().setStatements(newBodyStmts));
                } else {
                    loop.setBody(null);
                }
            }
        } else if (clonedStatement instanceof CtIf) {
            CtIf ctIf = (CtIf) clonedStatement;
            if (ctIf.getThenStatement() != null) {
                List<CtStatement> newThenStmts = processStatementList(
                        Collections.singletonList(ctIf.getThenStatement()));
                if (!newThenStmts.isEmpty()) {
                    ctIf.setThenStatement(statement.getFactory().createBlock().setStatements(newThenStmts));
                } else {
                    ctIf.setThenStatement(null);
                }
            }
            if (ctIf.getElseStatement() != null) {
                List<CtStatement> newElseStmts = processStatementList(
                        Collections.singletonList(ctIf.getElseStatement()));
                if (!newElseStmts.isEmpty()) {
                    ctIf.setElseStatement(statement.getFactory().createBlock().setStatements(newElseStmts));
                } else {
                    ctIf.setElseStatement(null);
                }
            }
            if (ctIf.getThenStatement() == null && ctIf.getElseStatement() == null) {
                return Collections.emptyList();
            }
        }

        for (CtMethod<?> nestedMethod : clonedStatement.getElements(new TypeFilter<>(CtMethod.class))) {
            removeTryCatchAndAssertion(nestedMethod);
        }

        return Collections.singletonList(clonedStatement);
    }

    private static boolean isAssertionInvocation(CtInvocation<?> invocation) {

        CtExecutableReference<?> executable = invocation.getExecutable();
        if (executable == null) {
            return false;
        }
        String methodName = executable.getSimpleName().toLowerCase();

        if (!methodName.startsWith("assert") && !methodName.equals("fail")) {
            return false;
        }

        CtExpression<?> target = invocation.getTarget();
        if (target != null) {
            String targetString = target.toString().toLowerCase();
            if (targetString.contains("junit") || targetString.contains("assert")) {
                return true;
            }
        }

        CtTypeReference<?> declaringType = executable.getDeclaringType();
        if (declaringType != null) {
            String qualifiedName = declaringType.getQualifiedName();
            if (qualifiedName != null) {
                String qnLower = qualifiedName.toLowerCase();
                if (qnLower.contains("junit") || qnLower.contains("assert")) {
                    return true;
                }
            }
        }
        return false;
    }

    private static List<CtStatement> processTryBlock(CtStatement state) {
        List<CtStatement> results = new ArrayList<>();
        List<CtStatement> tryStmts = ((CtTryImpl) state).getBody().getStatements();
        // Add Stmts inside the Try block
        for (CtStatement tryStmt : tryStmts) {
            if (!isAssertion(tryStmt)) {
                results.add(tryStmt);
            }
        }
        return results;
    }

    private static List<CtElement> retrieveBackSlice(CtElement targetStmt, CtMethod<?> method) {
        List<CtStatement> statements = method.getBody().getStatements();
        List<CtElement> results = new ArrayList<>();

        int targetIndex = statements.indexOf(targetStmt);
        if (targetIndex < 0) {
            return results;
        }

        for (int i = 0; i < targetIndex; i++) {
            CtStatement state = statements.get(i);
            if (isAssertion(state)) {
                continue;
            }
            if (isTryBlock(state)) {
                results.addAll(processTryBlock(state));
            } else {
                results.add(state);
            }
        }
        return results;
    }

    public static boolean isAssertion(CtStatement stmt) {
        if (stmt instanceof CtAssert<?>) {
            return true;
        }

        if (stmt instanceof CtInvocation<?>) {
            CtInvocation<?> invocation = (CtInvocation<?>) stmt;

            if (invocation.getExecutable() == null || invocation.getExecutable().getDeclaringType() == null) {
                return false;
            }

            String qualifiedName = invocation.getExecutable().getDeclaringType().getQualifiedName();
            String methodName = invocation.getExecutable().getSimpleName();

            boolean isJUnit3 = "junit.framework.TestCase".equals(qualifiedName)
                    && methodName.startsWith("assert");
            boolean isJUnit4or5 = "org.junit.Assert".equals(qualifiedName)
                    && (methodName.startsWith("assert") || methodName.equals("fail"));
            boolean isTestNG = "org.testng.Assert".equals(qualifiedName)
                    && (methodName.startsWith("assert") || methodName.equals("fail"));
            boolean isGenericAssert = qualifiedName.toLowerCase().contains("assert")
                    && (methodName.toLowerCase().startsWith("assert") || methodName.equalsIgnoreCase("fail"));
            boolean isCustomAssert = stmt.toString().toLowerCase().contains("assert");

            return isJUnit3 || isJUnit4or5 || isTestNG || isGenericAssert || isCustomAssert;
        }

        return false;
    }

    private static boolean isConditionalStmt(CtStatement stmt) {
        if (stmt instanceof CtIf || stmt instanceof CtFor || stmt instanceof CtForEach || stmt instanceof CtWhile
                || stmt instanceof CtDo) {

            return true;
        }
        return false;
    }

    private static boolean isAnonymousClass(CtStatement statement) {
        if (statement instanceof CtLocalVariable) {
            CtLocalVariable<?> var = (CtLocalVariable<?>) statement;
            if (var.getDefaultExpression() instanceof CtNewClass) {
                return true; // 익명 클래스가 포함된 로컬 변수
            }
        } else if (statement instanceof CtNewClass) {
            return true;
        }
        return false;
    }

    private static Set<CtMethod> getTestCases(CtModel ctModel) {
        Set<CtMethod> testcases = new HashSet<CtMethod>();
        List<CtType<?>> types = ctModel.getElements(new TypeFilter<>(CtType.class));
        for (CtType<?> type : types) {
            if (!(type instanceof CtClass) || type.getDeclaringType() != null)
                continue;

            for (CtMethod<?> method : type.getMethods()) {
                if (isTestMethod(method)) {
                    testcases.add((CtMethod) method);
                }
            }
        }
        return testcases;
    }

    private static void processPrimitiveVal(CtMethod<?> testcase) {
        if (testcase == null) {
            return;
        }
        List<CtElement> allElements = testcase.getElements(new TypeFilter<>(CtElement.class));
        for (CtElement element : allElements) {
            if (element instanceof CtLiteral<?>) {
                CtLiteral<?> literal = (CtLiteral<?>) element;
                CtTypeReference<?> typeRef = literal.getType();
                if (typeRef != null && (isLiteral(typeRef))) {
                    CandidatePool.insertDirectToValues(typeRef, literal);
                }
            }
        }
    }

    private static boolean isLiteral(CtTypeReference<?> type) {
        if (type.isPrimitive() || type.getQualifiedName().equals("java.lang.String"))
            return true;
        return false;
    }

    /**
     * init the spoon
     *
     * @param path
     * @return
     */
    private static CtModel init(String path) {
        Launcher launcher = new Launcher();
        spoon.compiler.Environment env = launcher.getEnvironment();
        // Configure environment to preserve FQNs during parsing
        env.setAutoImports(false); // Disable auto imports to preserve FQNs
        env.setNoClasspath(true); // Don't try to resolve classpath to avoid unwanted simplification
        launcher.addInputResource(path);
        launcher.buildModel();

        String[] classpath = Arrays.stream(Config.CLASS_PATH.split(java.io.File.pathSeparator))
                .filter(p -> p != null && !p.trim().isEmpty())
                .distinct()
                .toArray(String[]::new);
        env.setSourceClasspath(classpath);
        CtModel model = launcher.getModel();
        return model;
    }

    private static void renameVariable(CtModel testClass) {
        List<CtMethod> methods = testClass.getElements(new TypeFilter<>(CtMethod.class));
        int index = 0;
        Set<CtVariable> usedDefs = new HashSet<>();
        for (CtMethod method : methods) {
            List<CtVariableReference> vars = method.getElements(new TypeFilter<>(CtVariableReference.class));
            Map<CtVariable, List<CtVariableReference>> defUsePair = new HashMap<>();
            for (CtVariableReference var : vars) {
                // System.out.println(var.toString());
                CtVariable def = var.getDeclaration();
                if (def == null) {
                    continue;
                }
                // System.out.println(def.toString());
                usedDefs.add(def);
                if (!defUsePair.containsKey(def))
                    defUsePair.put(def, new LinkedList<>());
                defUsePair.get(def).add(var);
            }
            for (CtVariable def : defUsePair.keySet()) {
                List<CtVariableReference> refs = defUsePair.get(def);
                String varName = def.getSimpleName() + "_" + index;
                index++;
                for (CtVariableReference ref : refs) {
                    if (!ref.getModifiers().contains(ModifierKind.STATIC))
                        ref.setSimpleName(varName);
                }
                def.setSimpleName(varName);
            }
        }
        for (CtVariable var : testClass.getElements(new TypeFilter<>(CtVariable.class))) {
            if (var.getReference().getSimpleName().contains("_"))
                continue;
            var.setSimpleName(var.getSimpleName() + "_" + index);
            index++;
        }
    }

    /**
     * main entry of the ast parser
     *
     * @param path
     */
    public static void parser(String path)
            throws Exception, TimeoutException {
        CtModel ctModel = init(path);

        // Renames all the variables that are used in basetest to avoid naming conflicts
        System.out.println("Renaming variables in the basetest...");
        renameVariable(ctModel);
        System.out.println("Renaming variables in the basetest completed.");
        // Gets package name of the basetest e.g.) package Generater.MUTMutation;
        getPackage(ctModel);
        Set<CtMethod> testcases = getTestCases(ctModel);
        try {
            process(testcases);
        } catch (Exception e) {
            System.out.println("Process terminated due to : " + e.getMessage());
            // // e.printStackTrace();
            throw e;
        }
    }

    private static boolean isTestMethod(CtMethod<?> method) {
        boolean j3 = method.getSimpleName().startsWith("test");
        // JUnit4 이상 스타일: @Test 애노테이션
        boolean j4 = method.getAnnotations().stream()
                .anyMatch(a -> a.getAnnotationType().getSimpleName().equals("Test"));
        // public인지 확인
        boolean isPublic = method.hasModifier(ModifierKind.PUBLIC);
        // public 이면서, JUnit3 또는 JUnit4 이상 스타일이고, 바디가 비어있지 않아야 함
        return isPublic
                && (j3 || j4)
                && method.getBody() != null
                && !method.getBody().getStatements().isEmpty();
    }

    public static void scanAllProductFiles(String rootDir, boolean simple) {
        int methodSigNum = 0;
        if (!simple) {
            List<String> result = new ArrayList<>();
            File root = new File(rootDir);

            if (!root.exists() || !root.isDirectory()) {
                System.out.println("Invalid Root Dir " + rootDir);
                return;
            }

            Stack<File> stack = new Stack<>();
            stack.push(root);

            while (!stack.isEmpty()) {
                File current = stack.pop();
                if (current.isDirectory()) {
                    File[] subFiles = current.listFiles();
                    if (subFiles != null) {
                        for (File f : subFiles) {
                            stack.push(f);
                        }
                    }
                } else {
                    String fileName = current.getName();
                    if (fileName.endsWith(".java") && !fileName.contains("Test") && !fileName.contains("test")) {
                        String absPath = current.getAbsolutePath();
                        result.add(absPath);
                        Set<String> methodSignatures = scanMethodSignatures(absPath);
                        methodSigNum += methodSignatures.size();
                        // productCodeMap.put(absPath,methodSignatures);
                    }
                }
            }

            System.out.println("Total Number of Product Code Files : " + result.size());
            System.out.println("Total Number of Public Methods : " + methodSigNum);
            return;
        } else {
            String fileName = rootDir;
            Set<String> methodSignatures = scanMethodSignatures(fileName);
            methodSigNum += methodSignatures.size();
            // productCodeMap.put(fileName,methodSignatures);
            System.out.println("Total Number of Public Methods : " + methodSigNum);
            return;
        }

    }

    private static Set<String> scanMethodSignatures(String path) {
        // System.out.println("Class : " + path);
        CtModel ctModel = init(path);
        List<CtMethod> methods = ctModel.getElements(new TypeFilter<>(CtMethod.class));
        Set<String> signatures = new HashSet<>();

        for (CtMethod method : methods) {
            CtType<?> declaringType = method.getDeclaringType();
            if (declaringType != null && declaringType.hasModifier(ModifierKind.PUBLIC)) {

                if (declaringType.getDeclaringType() == null) {
                    String fqcn = declaringType.getQualifiedName();
                    String methodSig = method.getSignature();
                    String fullSignature = fqcn + "." + methodSig;
                    // System.out.println(" - " + fullSignature);
                    signatures.add(fullSignature);
                }
            }
        }
        return signatures;
    }

    /**
     * get package name
     *
     * @param clazz
     */
    private static void getPackage(CtModel clazz) {

        List<String> className = Arrays.asList(Config.FULL_CLASS_NAME.split("\\."));
        packageName = String.join(".", className.subList(0, className.size() - 1));
        packageNameList.add(packageName);

    }

    /**
     * Parse package from Config.BUGTRIGGERINGTESTS
     * 
     * @return package name extracted from bug triggering tests
     */
    public static Set<String> extractPackageNamesFromBugTriggeringTests(String BTTests) {
        Set<String> packageNames = new HashSet<>();

        if (BTTests == null || BTTests.trim().isEmpty()) {
            return packageNames;
        }

        String[] testEntries = BTTests.split(";");

        for (String entry : testEntries) {
            String className = entry;
            if (entry.contains("::")) {
                className = entry.substring(0, entry.indexOf("::"));
            }

            // Extract package name from fully qualified class name
            int lastDotIndex = className.lastIndexOf('.');
            if (lastDotIndex > 0) {
                String packageName = className.substring(0, lastDotIndex);
                packageNames.add(packageName);
            }
        }

        return packageNames;
    }

    public static List<String> convertClassToPath(String BTTests) {
        // 중복된 파일 경로를 방지하기 위해 Set을 사용합니다.
        Set<String> filePaths = new HashSet<>();

        if (BTTests == null || BTTests.trim().isEmpty()) {
            return new ArrayList<>();
        }

        String[] testEntries = BTTests.split(";");

        for (String entry : testEntries) {
            String className = entry;
            if (entry.contains("::")) {
                className = entry.substring(0, entry.indexOf("::"));
            }
            String pathSuffix = className.replace('.', File.separatorChar) + ".java";
            String finalPath = Config.BUILD_PATH + File.separator + pathSuffix;
            filePaths.add(finalPath);

        }
        return new ArrayList<>(filePaths);
    }

    public static void gatherConstructorsAndMethods(String srcRootDir, List<String> cutFiles) {
        if (srcRootDir == null || srcRootDir.isEmpty()) {
            System.err.println("Source root directory is not provided. Skipping pre-processing.");
            return;
        }
        System.err.println("[DEBUG-ASTParser] srcRootDir: " + srcRootDir);
        System.err.println("[DEBUG-ASTParser] cutFiles size: " + (cutFiles != null ? cutFiles.size() : 0));

        String targetPackage = extractPackageFromCUTFiles(cutFiles);
        System.err.println("[DEBUG-ASTParser] Extracted targetPackage: " + targetPackage);

        // Update Config.PACKAGE with the correct CUT package for consistency
        Config.PACKAGE = targetPackage;

        CtModel model = init(srcRootDir);
        if (model == null) {
            System.err.println("[DEBUG-ASTParser] model is null - returning");
            return;
        }

        Set<String> cutFileSet = new HashSet<>(cutFiles);
        System.err.println("[DEBUG-ASTParser] cutFileSet size: " + cutFileSet.size());
        Set<CtConstructor<?>> allConstructorsInModel = new HashSet<>(
                model.getElements(new TypeFilter<>(CtConstructor.class)));
        Set<CtMethod<?>> allMethods = new HashSet<>(model.getElements(new TypeFilter<>(CtMethod.class)));

        for (CtConstructor<?> constructor : allConstructorsInModel) {
            CtType<?> declaringType = constructor.getDeclaringType();
            if (declaringType == null) {
                continue;
            }

            // --- [핵심 수정: public 생성자와 같은 패키지의 protected 생성자 수집] ---
            boolean shouldInclude = false;

            if (constructor.isPublic()) {
                shouldInclude = true;
            } else if (constructor.isProtected()) {
                String constructorPackage = (declaringType.getPackage() != null)
                        ? declaringType.getPackage().getQualifiedName()
                        : "";
                if (constructorPackage.equals(targetPackage)) {
                    shouldInclude = true;
                }
            }

            if (shouldInclude) {
                All_Constructors_Map.computeIfAbsent(declaringType.getQualifiedName(), k -> new HashSet<>())
                        .add(constructor);
            }
            // --- [수정 끝] ---

            // 2. CUT 파일에 속하는 생성자를 CUT_Constructors_Map에 추가
            // Nested class의 경우 public constructor만, 일반 class는 public/protected만 포함
            if (constructor.getPosition().isValidPosition()) {
                String sourcePath = constructor.getPosition().getFile().getAbsolutePath();
                if (cutFileSet.contains(sourcePath)) {
                    String fqcn = declaringType.getQualifiedName();
                    boolean isNestedClass = fqcn.contains("$");

                    String constructorPackage = (declaringType.getPackage() != null)
                            ? declaringType.getPackage().getQualifiedName()
                            : "";

                    // Skip nested classes - only include constructors from top-level classes
                    if (isNestedClass) {
                        continue;
                    }

                    boolean shouldIncludeInCUT = false;

                    if (constructor.isPublic()) {
                        // Public constructors always included
                        shouldIncludeInCUT = true;
                    } else if (constructor.isProtected()) {
                        // Protected constructors included if in same package
                        shouldIncludeInCUT = constructorPackage.equals(targetPackage);
                    } else if (!constructor.isPrivate()) {
                        // Package-private constructors included if in same package
                        shouldIncludeInCUT = constructorPackage.equals(targetPackage);
                    }

                    if (shouldIncludeInCUT) {
                        CUT_Constructors_Map.computeIfAbsent(fqcn, k -> new HashSet<>())
                                .add(constructor);
                    }
                }
            }
        }

        if (recursiveMethodCalls) {
            for (CtMethod<?> method : allMethods) {
                CtTypeReference<?> returnTypeRef = method.getType();
                String returnTypeName = (returnTypeRef != null) ? returnTypeRef.getQualifiedName() : "UNKNOWN";
                insertAllMethods(returnTypeName, method);
            }
        }

        buildAbstractToImplsMap(model);

        // Add constructors for all implementations in abstractToImplsMap
        for (List<CtTypeReference<?>> implementations : abstractToImplsMap.values()) {
            for (CtTypeReference<?> implType : implementations) {
                CtType<?> implClass = implType.getTypeDeclaration();
                if (implClass != null) {
                    List<CtConstructor<?>> implConstructors = implClass
                            .getElements(new TypeFilter<>(CtConstructor.class));
                    for (CtConstructor<?> constructor : implConstructors) {
                        if (constructor.isPublic() ||
                                (constructor.isProtected() &&
                                        constructor.getDeclaringType().getPackage() != null &&
                                        constructor.getDeclaringType().getPackage().getQualifiedName()
                                                .equals(targetPackage))) {
                            All_Constructors_Map.computeIfAbsent(implType.getQualifiedName(), k -> new HashSet<>())
                                    .add(constructor);
                        }
                    }
                }
            }
        }

        int methodsInCutFiles = 0;
        int publicMethods = 0;
        int protectedMethods = 0;
        int privateMethods = 0;
        int packagePrivateMethods = 0;
        int methodsChecked = 0;
        int methodsInCUTButNotMatching = 0;

        for (CtMethod<?> method : allMethods) {
            if (method.getPosition().isValidPosition()) {
                String sourcePath = method.getPosition().getFile().getAbsolutePath();
                methodsChecked++;

                // 디버깅: 처음 5개 메서드의 경로 출력

                if (cutFileSet.contains(sourcePath)) {
                    methodsInCutFiles++;
                    CtType<?> declaringType = method.getDeclaringType();
                    String fqcn = (declaringType != null) ? declaringType.getQualifiedName() : "UNKNOWN";

                    // Skip all nested classes (public, private, protected) - only test top-level
                    // classes
                    boolean isNestedClass = fqcn.contains("$");
                    if (isNestedClass) {
                        continue; // Skip all nested classes
                    }

                    // Count by visibility
                    if (method.isPublic()) {
                        publicMethods++;
                    } else if (method.isProtected()) {
                        protectedMethods++;
                    } else if (method.isPrivate()) {
                        privateMethods++;
                    } else {
                        packagePrivateMethods++;
                    }

                    // Determine if method should be included as MUT
                    // MegaTestClass will be generated in the CUT package (targetPackage)
                    // So we can test both Public and Protected APIs from the same package
                    boolean shouldInclude = false;

                    if (method.isPublic()) {
                        // Always include public methods
                        shouldInclude = true;

                    } else if (method.isProtected()) {
                        // Include protected methods only if they're in the same package as
                        // MegaTestClass (targetPackage)
                        // This is because MegaTestClass is generated in the CUT package,
                        // so it has access to protected members of classes in the same package
                        String methodPackage = (declaringType.getPackage() != null)
                                ? declaringType.getPackage().getQualifiedName()
                                : "";

                        shouldInclude = methodPackage.equals(targetPackage);
                    }

                    if (shouldInclude) {
                        String fullSignature = fqcn + "." + method.getSignature();
                        CUT_PublicMethods.add(fullSignature);
                        CUT_PublicMethods_Map.put(fullSignature, method);
                    }
                }
            }
        }

    }

    private static void buildAbstractToImplsMap(CtModel model) {
        List<CtType<?>> types = model.getElements(new TypeFilter<>(CtType.class));
        for (CtType<?> type : types) {
            // 구체적인 클래스만 처리
            if (!type.isInterface() && !type.isAbstract()) {
                Set<CtTypeReference<?>> allSuperTypes = new HashSet<>();
                collectAllSuperTypes(type, allSuperTypes);

                for (CtTypeReference<?> superType : allSuperTypes) {
                    // --- [핵심 수정] ---
                    // CtTypeReference 객체 대신, 클래스의 전체 이름(String)을 키로 사용합니다.
                    abstractToImplsMap.computeIfAbsent(superType.getQualifiedName(), k -> new ArrayList<>())
                            .add(type.getReference());
                }
            }
        }
    }

    private static void collectAllSuperTypes(CtType<?> type, Set<CtTypeReference<?>> collectedTypes) {
        if (type == null) {
            return;
        }

        // 1. 슈퍼클래스를 추가하고, 재귀적으로 탐색
        CtTypeReference<?> superClassRef = type.getSuperclass();
        // 참조가 유효하고, 이름이 있으며, 성공적으로 Set에 추가되었는지 확인
        if (superClassRef != null && superClassRef.getQualifiedName() != null && collectedTypes.add(superClassRef)) {
            collectAllSuperTypes(superClassRef.getTypeDeclaration(), collectedTypes);
        }

        // 2. 인터페이스들을 추가하고, 각각 재귀적으로 탐색
        for (CtTypeReference<?> ifaceRef : type.getSuperInterfaces()) {
            // 참조가 유효하고, 이름이 있으며, 성공적으로 Set에 추가되었는지 확인
            if (ifaceRef != null && ifaceRef.getQualifiedName() != null && collectedTypes.add(ifaceRef)) {
                collectAllSuperTypes(ifaceRef.getTypeDeclaration(), collectedTypes);
            }
        }
    }

    public static void printAbstractToImplsMap() {
        System.out.println("\n=======================================================");
        System.out.println("      Contents of abstractToImplsMap");
        System.out.println("=======================================================");

        if (abstractToImplsMap == null || abstractToImplsMap.isEmpty()) {
            System.out.println("Map is empty or null.");
            System.out.println("=======================================================\n");
            return;
        }

        System.out.println("Total mapped super types: " + abstractToImplsMap.size());
        System.out.println("-------------------------------------------------------");
        // 맵의 각 엔트리(Key-Value 쌍)를 순회합니다.
        for (Map.Entry<String, List<CtTypeReference<?>>> entry : abstractToImplsMap.entrySet()) {
            String superType = entry.getKey();
            List<CtTypeReference<?>> implementations = entry.getValue();

            // 상위 타입(Key)의 이름을 출력합니다.
            System.out.println("Super-type (Key): " + superType);

            if (implementations == null || implementations.isEmpty()) {
                System.out.println("  -> No implementations found.");
            } else {
                // 해당 상위 타입에 매핑된 모든 구체적인 구현체(Value)들을 출력합니다.
                for (CtTypeReference<?> impl : implementations) {
                    System.out.println("  -> Implemented by (Value): " + impl.getQualifiedName());
                }
            }
            System.out.println(); // 각 항목 사이에 공백 라인을 추가하여 가독성을 높입니다.
        }

        System.out.println("=======================================================\n");
    }

    public static void printAllConstructorsMap() {
        System.out.println("\n=======================================================");
        System.out.println("      Contents of All_Constructors_Map");
        System.out.println("=======================================================");

        if (All_Constructors_Map == null || All_Constructors_Map.isEmpty()) {
            System.out.println("Map is empty or null.");
            System.out.println("=======================================================\n");
            return;
        }

        System.out.println("Total classes with collected constructors: " + All_Constructors_Map.size());
        System.out.println("-------------------------------------------------------");

        // 맵의 각 엔트리(Key-Value 쌍)를 순회합니다.
        for (Map.Entry<String, Set<CtConstructor<?>>> entry : All_Constructors_Map.entrySet()) {
            String className = entry.getKey();
            Set<CtConstructor<?>> constructors = entry.getValue();

            // 클래스 이름(Key)을 출력합니다.
            System.out.println("Class (Key): " + className);

            if (constructors == null || constructors.isEmpty()) {
                System.out.println("  -> No constructors found for this class.");
            } else {
                // 해당 클래스에 대해 수집된 모든 생성자(Value)들의 시그니처를 출력합니다.
                for (CtConstructor<?> constructor : constructors) {
                    System.out.println("  -> Constructor Signature (Value): " + constructor.getSignature());
                }
            }
            System.out.println(); // 각 항목 사이에 공백 라인을 추가하여 가독성을 높입니다.
        }

        System.out.println("=======================================================\n");
    }

    /**
     * Extract package name from CUT files when Config.PACKAGE is not set
     * 
     * @param cutFiles List of CUT file paths
     * @return extracted package name or empty string if not found
     */
    private static String extractPackageFromCUTFiles(List<String> cutFiles) {
        if (cutFiles == null || cutFiles.isEmpty()) {
            return "";
        }

        // Try each CUT file to extract package from "package" declaration
        for (String cutFile : cutFiles) {
            try {
                BufferedReader reader = new BufferedReader(new FileReader(cutFile));
                String line;
                while ((line = reader.readLine()) != null) {
                    line = line.trim();
                    // Look for "package xxx;" declaration
                    if (line.startsWith("package ") && line.endsWith(";")) {
                        String packageName = line.substring(8, line.length() - 1); // Remove "package " and ";"
                        reader.close();
                        return packageName;
                    }
                }
                reader.close();
            } catch (Exception e) {
                System.err.println("[ERROR] Failed to read package from CUT file: " + cutFile);
            }
        }

        return "";
    }

    /**
     * Check if a statement is a variable-to-variable assignment or this assignment
     * (e.g., br_121 = br_140; or obj = this;)
     * This identifies statements that should be EXCLUDED from collection:
     * - obj1 = obj2; (simple variable assignment)
     * - var_123 = var_456; (variable to variable)
     * - obj = this; (this assignment)
     * 
     * We want to exclude these because they don't actually initialize the object,
     * they just copy references from other variables or use this.
     * Other assignments (field reads, method calls, etc.) should still be
     * collected.
     * 
     * @param statement The statement to check
     * @return true if this is a variable-to-variable or this assignment (should be
     *         excluded), false otherwise
     */
    private static boolean isVariableToVariableAssignment(CtStatement statement) {
        if (statement == null) {
            return false;
        }

        // Check if this is an assignment statement (not a declaration)
        if (statement instanceof CtAssignment) {
            CtAssignment<?, ?> assignment = (CtAssignment<?, ?>) statement;
            CtExpression<?> rightHandSide = assignment.getAssignment();

            // Only exclude: variable read or this access
            // Keep: field reads, method calls, etc.
            if (rightHandSide instanceof CtVariableRead ||
                    rightHandSide instanceof CtThisAccess) {
                return true;
            }
        }

        // Check if this is a local variable declaration with a variable initializer or
        // this
        // Examples: Type var = other_var; Type obj = this;
        if (statement instanceof CtLocalVariable) {
            CtLocalVariable<?> localVar = (CtLocalVariable<?>) statement;
            CtExpression<?> defaultExpr = localVar.getDefaultExpression();

            if (defaultExpr != null) {
                // Only exclude: variable read or this access
                // Keep: field reads, method calls, etc.
                if (defaultExpr instanceof CtVariableRead ||
                        defaultExpr instanceof CtThisAccess) {
                    return true;
                }
            }
        }

        return false;
    }

}