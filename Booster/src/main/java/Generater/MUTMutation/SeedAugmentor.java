package Generater.MUTMutation;

import spoon.Launcher;
import spoon.reflect.reference.CtVariableReference;
import spoon.reflect.visitor.filter.TypeFilter;
import spoon.reflect.code.*;
import spoon.reflect.declaration.*;
import spoon.reflect.factory.Factory;
import spoon.reflect.reference.CtTypeReference;
import spoon.reflect.reference.CtExecutableReference;
import spoon.reflect.reference.CtArrayTypeReference;
import java.util.concurrent.TimeoutException;

import spoon.support.reflect.code.*;
import utils.Config;
import utils.Pair;

import javax.tools.*;
import java.io.*;
import java.lang.reflect.Field;
import java.util.Comparator;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.net.URI;
import java.net.URLClassLoader;
import java.util.*;
import java.lang.reflect.Constructor;
import java.util.stream.Collectors;
import Generater.MUTMutation.InputCombinations;

public class SeedAugmentor {

    private static List<String> neglectedMUTs;
    private static HashMap<CtTypeReference, Set<CtConstructor<?>>> generatedConstructors = new HashMap<>();
    private static HashMap<Pair<CtTypeReference, CtElement>, Set<List<CtElement>>> baseVartypeToInputPool;
    private static HashMap<CtTypeReference, List<Pair<CtTypeReference, CtElement>>> baseVarTypeNamePoolAsList;
    private static HashMap<CtTypeReference<?>, List<CtElement>> baseDirectToValuesAsList;
    private static Map<String, CtConstructor<?>> abstractConstructorCache = new HashMap<>();
    private static boolean recursiveMethodCalls = Config.recursiveMethodCalls;
    private static int dummyVarCounter = 0;
    private static boolean usedInputPool = false;
    private static final Random rand = new Random();
    private static Factory factory;
    private static Map<CtTypeReference<?>, List<CtStatement>> creationSequenceCache = new HashMap<>();

    // Debug switches for various logging
    private static final boolean DEBUG_STRING_MUTATION = false;
    private static final boolean DEBUG_POOL_AUGMENTATION = false;
    private static final boolean DEBUG_MUT_ANALYSIS = false;
    private static final boolean DEBUG_OBJECT_GENERATION = false;
    private static final boolean DEBUG_POOL_MONITORING = false;

    // Performance optimization caches
    private static Map<String, List<CtMethod<?>>> factoryMethodCache = new HashMap<>();
    private static Map<String, List<CtMethod<?>>> allMethodCache = new HashMap<>();
    private static Set<String> factoryMethodNames = new HashSet<>(Arrays.asList(
            "getInstance", "newInstance", "create", "createInstance",
            "valueOf", "of", "from", "parse", "build", "get"));
    private static Map<String, Boolean> typeCompatibilityCache = new HashMap<>();

    // Track which types have already had variants generated
    private static Set<String> variantsGeneratedTypes = new HashSet<>();

    // Track which types have already had null objects registered
    private static Set<String> nullObjectsRegisteredTypes = new HashSet<>();

    // Track types that should always be regenerated (like NullPropertyPointer)
    private static Set<String> alwaysRegenerateTypes = new HashSet<>(
            java.util.Arrays.asList(
                    "org.apache.commons.jxpath.ri.model.beans.NullPropertyPointer"));

    // Track which types have been regenerated in current session
    private static Set<String> regeneratedInSession = new HashSet<>();

    // MUT-based pool analysis cache
    private static Map<CtTypeReference<?>, Integer> typePoolSizeCache = new HashMap<>();
    private static Set<CtTypeReference<?>> typesNeedingAugmentation = new HashSet<>();
    private static final int MIN_POOL_SIZE_THRESHOLD = 5; // Pool size should be > this value
    private static final int SAFE_POOL_SIZE = MIN_POOL_SIZE_THRESHOLD + 1; // Target for generation

    // Debugging statistics
    private static Map<String, Integer> generationAttemptStats = new HashMap<>();
    private static Map<String, Integer> generationSuccessStats = new HashMap<>();
    private static long totalGenerationTime = 0;
    private static int totalPoolAugmentationCalls = 0;

    private static ThreadLocal<Set<String>> currentlyGeneratingTypes = ThreadLocal.withInitial(HashSet::new);

    /**
     * ENTRY POINT
     */

    public static void augmentInitalSeed() {
        long newStartTime = System.currentTimeMillis();

        // Clear caches for fresh start
        clearCaches();

        baseVarTypeNamePoolAsList = new HashMap<>();
        HashMap<CtTypeReference, Set<Pair<CtTypeReference, CtElement>>> baseVarTypeNamePool = new HashMap<>(
                CandidatePool.getVarTypeNamePool());
        baseVarTypeNamePool.forEach((key, value) -> {
            baseVarTypeNamePoolAsList.put(key, new ArrayList<>(value));
        });
        baseVartypeToInputPool = new HashMap<>(CandidatePool.getVartypeToInputPool());
        baseDirectToValuesAsList = new HashMap<>();
        HashMap<CtTypeReference, Set<CtElement>> directToValues = CandidatePool.getDirectToValues();
        directToValues.forEach((key, value) -> {
            baseDirectToValuesAsList.put(key, new ArrayList<>(value));
        });
        // Analyze MUT requirements and identify types needing augmentation
        analyzeRequiredTypesFromMUTs();

        neglectedMUTs = findOutNeglectedMUTS();
        if (neglectedMUTs == null) {
            return;
        }
        if (factory == null) {
            factory = new Launcher().getFactory();
        }
        System.out.println("NeglectedMUTs Size : " + neglectedMUTs.size() + " | # Public API of CUT : "
                + ASTParser.getCUT_PublicMethodSize());
        System.out.println("Generating Dummy MUTs for Neglected Public APIs");
        generateDummyMUTS(neglectedMUTs);

        // Generate additional objects for types with insufficient pool size
        generateAdditionalObjectsForInsufficientTypes();

        // Generate NULL objects for all MUT parameter types
        generateNullObjectsForAllMUTTypes();

        long augmentationEndTime = System.currentTimeMillis() - newStartTime;

    }

    /**
     * Clear all caches to free memory
     */
    public static void clearCaches() {
        factoryMethodCache.clear();
        allMethodCache.clear();
        typeCompatibilityCache.clear();
        creationSequenceCache.clear();
        abstractConstructorCache.clear();
        typePoolSizeCache.clear();
        typesNeedingAugmentation.clear();
        variantsGeneratedTypes.clear();
        nullObjectsRegisteredTypes.clear();
        regeneratedInSession.clear();
        currentlyGeneratingTypes.get().clear();
    }

    /**
     * MAIN FUNCTIONS
     */

    private static void generateDummyMUTS(List<String> neglectedMUTs) {
        // Factory factory = new Launcher().getFactory();
        long testCaseGenTime = 0;
        long testParsingTime = 0;
        long time_budget_ms = 50000;
        long startTime = System.currentTimeMillis();
        // 1. 모든 '가짜' 테스트 메소드를 생성하여 리스트에만 저장합니다.
        List<CtMethod<?>> generatedDummyMethods = new ArrayList<>();

        long generationStartTime = System.currentTimeMillis();
        for (String neglectedMUT : neglectedMUTs) {
            // [타이머] 생성 루프 시작 시점에서 시간 초과 여부를 확인합니다.
            long elapsedTime = System.currentTimeMillis() - startTime;
            if (elapsedTime >= time_budget_ms) {
                System.out.println("\n[INFO] SeedAugmentor timed out during generation. Budget: " + time_budget_ms
                        + "ms, Elapsed: " + elapsedTime + "ms");
                break; // 생성을 중단합니다.
            }

            CtMethod<?> neglectedPublicAPI = ASTParser.getCUT_PublicMethods_Map().get(neglectedMUT);
            if (neglectedPublicAPI == null) {
                continue;
            }
            // System.out.println("Generating Dummy Method for : " +
            // neglectedPublicAPI.getSignature());
            CtMethod<?> dummyMethod = generateDummyTestMethod(factory, neglectedPublicAPI);
            if (dummyMethod != null) {
                // System.out.println("Dummy Method : ");
                // System.out.println(dummyMethod);
                generatedDummyMethods.add(dummyMethod);
            }
        }
        testCaseGenTime = System.currentTimeMillis() - generationStartTime;

        // 2. 생성된 모든 '가짜' 메소드들을 한 번에 파싱합니다.
        long parsingStartTime = System.currentTimeMillis();
        for (CtMethod<?> dummyMethod : generatedDummyMethods) {
            try {
                // ★ MUT 호출 정보 수집 (MUT pool에 추가)
                // ASTParser.processMethodInvokeAndConstructor(dummyMethod);
                // ★ 변수 정보 수집 (Variable pool에 추가)
                ASTParser.processDummyVartypeTovarnames(dummyMethod);
            } catch (Exception e) {
                System.err
                        .println("Exception raised while parsing a dummy test method: " + dummyMethod.getSimpleName());
                // e.printStackTrace();
            }
        }
        testParsingTime = System.currentTimeMillis() - parsingStartTime;

    }

    /**
     * Generates dummy test method for neglected public API
     * 
     * 
     * @param factory
     * @param neglectedPublicAPI
     * @param isStatic
     * @return
     */
    // seqc/SeedAugmentor.java

    private static CtMethod<?> generateDummyTestMethod(
            Factory factory,
            CtMethod<?> neglectedPublicAPI) {
        dummyVarCounter = 0;
        // 1) 새로 만들 dummy test method 생성 (기존과 동일)
        CtMethod<Void> dummyTestMethod = factory.createMethod();
        dummyTestMethod.setSimpleName("dummyTest" + System.currentTimeMillis());
        dummyTestMethod.setType(factory.Type().createReference(void.class));
        CtBlock<?> body = factory.createBlock();
        dummyTestMethod.setBody(body);

        // 2) receiver 및 인자 타입 수집 (개선된 로직 적용)
        List<CtTypeReference<?>> argTypes = new ArrayList<>();
        boolean isStatic = isStatic(neglectedPublicAPI);

        if (isStatic) {
            // Static 메소드는 receiver가 없으므로 null 추가
            argTypes.add(null);
        } else {
            // 인스턴스 메소드는 리시버 타입을 신중하게 결정
            CtTypeReference<?> originalReceiverType = neglectedPublicAPI.getDeclaringType().getReference();
            CtType<?> typeDecl = originalReceiverType.getTypeDeclaration();

            // 리시버 타입이 public 구상 클래스가 아니면, 대체 가능한 구현체를 찾습니다.
            if (typeDecl != null && (typeDecl.isAbstract() || !typeDecl.isPublic())) {
                // InputCombinations의 개선된 헬퍼 메소드를 호출합니다.
                CtTypeReference<?> concreteType = InputCombinations.findSuitableImplementation(originalReceiverType);
                if (concreteType != null) {
                    argTypes.add(concreteType);
                } else {
                    argTypes.add(originalReceiverType); // 대체재를 못 찾으면 원래 타입으로 진행
                }
            } else {
                argTypes.add(originalReceiverType); // public 구상 클래스이면 그대로 추가
            }
        }
        // 파라미터 타입 추가
        for (CtParameter<?> param : neglectedPublicAPI.getParameters()) {
            argTypes.add(param.getType());
        }

        // 3) 각 타입별로 값/변수 준비
        List<Object> argValues = new ArrayList<>();
        for (int i = 0; i < argTypes.size(); i++) {
            CtTypeReference<?> typeRef = argTypes.get(i);
            if (typeRef == null) { // static 메소드의 receiver 위치
                argValues.add(null);
                continue;
            }
            CtElement replacableCand = pickRandomPrim(typeRef);
            if (replacableCand != null) {
                argValues.add(replacableCand);
            } else {
                // 객체 생성이 필요한 경우 createDefaultVarRef 호출
                argValues.add(createDefaultVarRef(typeRef, factory, body));
            }
        }

        // 4) 최종 호출문 생성
        CtInvocation<?> finalInvocation = factory.createInvocation();
        finalInvocation.setExecutable((CtExecutableReference) neglectedPublicAPI.getReference());

        if (isStatic) {
            // Static 호출의 경우, Target을 클래스로 설정
            CtTypeAccess<?> typeAccess = factory.createTypeAccess(neglectedPublicAPI.getDeclaringType().getReference());
            finalInvocation.setTarget(typeAccess);
        } else {
            // 인스턴스 호출의 경우, receiver 객체를 Target으로 설정
            Object receiverValue = argValues.get(0);
            if (receiverValue instanceof CtVariableReference<?>) {
                CtVariableReference<?> receiverRef = (CtVariableReference<?>) receiverValue;
                CtVariableRead<?> receiverRead = factory.createVariableRead();
                receiverRead.setVariable((CtVariableReference) receiverRef);
                finalInvocation.setTarget(receiverRead);
            } else {
                // receiver를 생성하지 못하면 더미 테스트 생성을 중단
                return null;
            }
        }

        // 5) 인자 설정
        List<CtExpression<?>> arguments = new ArrayList<>();
        for (int i = 1; i < argValues.size(); i++) { // 인자는 1번 인덱스부터 시작
            Object argValue = argValues.get(i);
            if (argValue instanceof CtVariableReference<?>) {
                CtVariableReference<?> paramRef = (CtVariableReference<?>) argValue;
                CtVariableRead<?> paramRead = factory.createVariableRead();
                paramRead.setVariable((CtVariableReference) paramRef);
                arguments.add(paramRead);
            } else if (argValue instanceof CtLiteral<?>) {
                arguments.add((CtLiteral<?>) argValue);
            } else if (argValue instanceof CtExpression) { // handleDummyParameterVals 등이 CtExpression을 반환하는 경우
                arguments.add((CtExpression<?>) argValue);
            } else {
                arguments.add(factory.createLiteral(null));
            }
        }
        finalInvocation.setArguments(arguments);

        // 6) 메서드 본문에 호출문 추가
        body.addStatement(finalInvocation);
        // System.out.println("dummyTestMethod: \n" + dummyTestMethod);
        return dummyTestMethod;

    }

    private static CtVariableReference<?> createDefaultVarRef(CtTypeReference<?> typeRef, Factory factory,
            CtBlock<?> body) {

        // 1. handleDummyParameterVals를 호출하여 객체 생성 표현식(initExpr)을 얻어옵니다.
        // 이 호출은 이제 Object 타입에 대해 Pool에서 실제 객체를 가져와 더 구체적인 표현식을 반환할 수 있습니다.
        CtExpression<?> initExpr = handleDummyParameterVals(typeRef, body, factory, 0);

        if (initExpr != null) {
            String varName = "mockUp_" + System.currentTimeMillis() + "_" + dummyVarCounter++;

            // Pool에서 가져온 것이 이미 변수인 경우, 그 변수를 그대로 사용합니다.
            if (initExpr instanceof CtVariableRead) {
                return ((CtVariableRead<?>) initExpr).getVariable();
            }

            // --- [핵심 수정: 모든 변수 선언에 타입 추론 적용] ---
            // 요청된 타입(typeRef, 예: Object) 대신,
            // 실제로 생성된 초기화 표현식(initExpr, 예: new ArrayList())의 '실제 타입'을 가져옵니다.
            CtTypeReference<?> actualType = initExpr.getType();

            // 표현식의 타입을 알 수 없거나(예: null 리터럴) 너무 일반적일 경우, 원래 요청된 타입으로 대체합니다.
            if (actualType == null || actualType.isImplicit() || actualType.getQualifiedName().equals("?")) {
                actualType = typeRef;
            }

            CtLocalVariable localVar = factory.createLocalVariable();
            localVar.setSimpleName(varName);
            // setType과 setDefaultExpression 호출 시, 필요한 타입으로 명시적으로 캐스팅합니다.
            localVar.setType(actualType.clone());
            localVar.setDefaultExpression((CtExpression) initExpr);

            body.addStatement(localVar);
            return localVar.getReference();
        }

        // System.out.println("[ERROR] createDefaultVarRef could not get an
        // initialization expression for: " + typeRef.getQualifiedName());
        return null;
    }

    /**
     * Creates a default value for a given type.
     * For primitive types, returns appropriate default values (0, false, etc.)
     * For reference types, returns null.
     */
    private static CtExpression<?> createDefaultValueForType(CtTypeReference<?> typeRef, Factory factory) {
        if (typeRef == null) {
            return factory.createLiteral(null);
        }

        if (typeRef.isPrimitive()) {
            switch (typeRef.getSimpleName()) {
                case "boolean":
                    return factory.createLiteral(false);
                case "byte":
                    return factory.createLiteral((byte) 0);
                case "short":
                    return factory.createLiteral((short) 0);
                case "int":
                    return factory.createLiteral(0);
                case "long":
                    return factory.createLiteral(0L);
                case "float":
                    return factory.createLiteral(0.0f);
                case "double":
                    return factory.createLiteral(0.0d);
                case "char":
                    return factory.createLiteral('\u0000');
                default:
                    return factory.createLiteral(null);
            }
        } else {
            // Reference types: return null
            return factory.createLiteral(null);
        }
    }

    /**
     * Generates MockUp Variables based on thier Instance or Type
     */

    private static CtLocalVariable<?> createMockUpVarForType(
            CtTypeReference<?> typeRef,
            String varName,
            Factory factory,
            CtBlock<?> body) {
        if (typeRef == null || varName == null)
            return null;
        CtLocalVariable<?> localVar = factory.Core().createLocalVariable();
        localVar.setSimpleName(varName);
        localVar.setType((CtTypeReference) typeRef);

        CtExpression<?> initExpr = null;

        if (isLiteral(typeRef)) {
            initExpr = generateMockUpPrims(typeRef, factory);
        } else {
            if (typeRef.isArray()) {
                initExpr = generateMockUpArrays(typeRef, factory, body, 0);
            } else if (typeRef.isInterface() || isAbstractClass(typeRef)) {
                initExpr = generateAbstractExpr(typeRef, factory, body, 0);
            } else {
                initExpr = generateConcreteExpr(typeRef, factory, body, 0);
            }
        }

        if (initExpr != null) {
            localVar.setDefaultExpression((CtExpression) initExpr);
        } else {
            // initExpr이 null인 경우, 타입에 맞는 기본값으로 초기화
            CtExpression<?> defaultValue = createDefaultValueForType(typeRef, factory);
            localVar.setDefaultExpression((CtExpression) defaultValue);
        }
        return localVar;
    }

    /*
     * Generates Expression Stmt for MockUp Vars to be initialized
     * 
     */

    public static CtExpression<?> createDefaultExpressionForType(CtTypeReference<?> type, Factory factory,
            CtBlock<?> body, int currentDepth) {

        if (type == null) {
            return factory.createLiteral(null);
        }

        String typeQualifiedName = type.getQualifiedName();

        if (typeQualifiedName.equals("java.lang.Object")) {
            return pickRandomElementFromAnyPool(factory, body);
        }

        Set<String> generatingTypes = currentlyGeneratingTypes.get();
        if (generatingTypes.contains(typeQualifiedName)) {
            return makeTypedNull(factory, type);
        }

        try {
            generatingTypes.add(typeQualifiedName);

            CtExpression<?> cachedResult = tryGetFromCreationCache(type, factory, body);
            if (cachedResult != null) {
                return cachedResult;
            }

            if (isLiteral(type)) {
                return createLiteralExpression(type, factory);
            }

            if (currentDepth > Config.MAX_DEPTH) {
                return generateDefaultConstructorCall(type, factory, body);
            }

            return createAndCacheExpression(type, factory, body, currentDepth);
        } finally {
            generatingTypes.remove(typeQualifiedName);
        }
    }

    /**
     * Try to get expression from creation cache
     */
    private static CtExpression<?> tryGetFromCreationCache(CtTypeReference<?> type, Factory factory, CtBlock<?> body) {
        if (!creationSequenceCache.containsKey(type)) {
            return null;
        }

        List<CtStatement> cachedStmts = creationSequenceCache.get(type);
        cachedStmts.forEach(stmt -> body.addStatement(stmt.clone()));

        CtStatement lastStmt = cachedStmts.get(cachedStmts.size() - 1);

        // Handle different types of last statements
        if (lastStmt instanceof CtLocalVariable) {
            CtLocalVariable<?> lastVar = (CtLocalVariable<?>) lastStmt;
            CtVariableRead varRead = factory.createVariableRead();
            varRead.setVariable(lastVar.getReference());
            return varRead;
        } else if (lastStmt instanceof CtInvocation || lastStmt instanceof CtConstructorCall) {
            return (CtExpression<?>) lastStmt;
        } else {
            return makeTypedNull(factory, type);
        }
    }

    /**
     * Create literal expression
     */
    private static CtExpression<?> createLiteralExpression(CtTypeReference<?> type, Factory factory) {
        CtElement replacableCand = pickRandomPrim(type);
        if (replacableCand != null) {
            return (CtExpression<?>) replacableCand;
        } else {
            return generateMockUpPrims(type, factory);
        }
    }

    /**
     * Create expression and cache the creation sequence
     */
    private static CtExpression<?> createAndCacheExpression(CtTypeReference<?> type, Factory factory,
            CtBlock<?> body, int currentDepth) {

        // Record statements before creation
        int statementsBefore = body.getStatements().size();

        // Create expression based on type
        CtExpression<?> initExpr = createExpressionByType(type, factory, body, currentDepth);

        // Cache the creation sequence if successful
        cacheCreationSequenceIfNeeded(type, body, statementsBefore, initExpr);

        return initExpr;
    }

    /**
     * Create expression based on type
     */
    private static CtExpression<?> createExpressionByType(CtTypeReference<?> type, Factory factory,
            CtBlock<?> body, int currentDepth) {

        if (type.isArray()) {
            return generateMockUpArrays(type, factory, body, currentDepth + 1);
        } else if (type.isInterface() || isAbstractClass(type)) {
            return generateAbstractExpr(type, factory, body, currentDepth + 1);
        } else {
            return generateConcreteExpr(type, factory, body, currentDepth + 1);
        }
    }

    /**
     * Cache creation sequence if needed
     */
    private static void cacheCreationSequenceIfNeeded(CtTypeReference<?> type, CtBlock<?> body,
            int statementsBefore, CtExpression<?> initExpr) {

        int statementsAfter = body.getStatements().size();
        if (initExpr != null && !(initExpr instanceof CtLiteral)) {
            if (statementsAfter > statementsBefore) {
                List<CtStatement> creationSequence = body.getStatements().subList(statementsBefore, statementsAfter);
                creationSequenceCache.put(type, new ArrayList<>(creationSequence));
            }
        }
    }

    private static CtExpression<?> handleDummyParameterVals(CtTypeReference<?> paramType, CtBlock<?> body,
            Factory factory, int currentDepth) {

        // 1. Check for basic cases first (primitives, simple types)
        CtExpression<?> basicResult = tryBasicParameterGeneration(paramType, factory, body, currentDepth);
        // IMPORTANT: Only return if the result is valid AND not a null literal
        if (isValidNonNullExpression(basicResult)) {
            return basicResult;
        }

        // 2. Try finding replacement from candidate pool FIRST
        // This allows us to reuse existing objects (like TextNode for JsonNode) before
        // creating new ones
        CtExpression<?> poolResult = tryGetFromCandidatePool(paramType, body, factory, currentDepth);
        if (poolResult != null) {
            return poolResult;
        }

        // 3. Try creating new object from scratch (as fallback when pool is empty)
        CtExpression<?> newObjectResult = tryCreateNewObject(paramType, factory, body, currentDepth);
        // IMPORTANT: Only return if the result is valid AND not a null literal
        if (isValidNonNullExpression(newObjectResult)) {
            return newObjectResult;
        }

        // 4. Final fallback to simple argument
        return tryFinalFallback(paramType, factory);
    }

    /**
     * Try basic parameter generation (primitives, depth limits, etc.)
     */
    private static CtExpression<?> tryBasicParameterGeneration(CtTypeReference<?> paramType, Factory factory,
            CtBlock<?> body, int currentDepth) {

        // Check for reusable primitive values first
        CtElement replacableCand = pickRandomPrim(paramType);
        if (replacableCand != null) {
            return (CtExpression) replacableCand;
        }

        // Check depth limits
        int maxDepthForRecursive = Math.min(Config.MAX_DEPTH, 3);
        if (currentDepth > maxDepthForRecursive) {
            return generateDefaultConstructorCall(paramType, factory, body);
        }

        // Early exit for complex types at depth > 2
        if (currentDepth > 2 && !isSimpleType(paramType)) {
            CtExpression<?> simpleArg = createSimpleArgument(paramType, factory);
            if (isValidNonNullExpression(simpleArg)) {
                return simpleArg;
            }
            return factory.createLiteral(null);
        }

        return null;
    }

    /**
     * Try creating a new object from scratch
     */
    private static CtExpression<?> tryCreateNewObject(CtTypeReference<?> paramType, Factory factory,
            CtBlock<?> body, int currentDepth) {

        CtBlock<?> tempBodyForCreation = factory.createBlock();
        CtExpression<?> newlyCreatedExpr = createDefaultExpressionForType(paramType, factory, tempBodyForCreation,
                currentDepth + 1);

        if (isValidNonNullExpression(newlyCreatedExpr)) {
            List<CtStatement> tempStatements = tempBodyForCreation.getStatements();
            tempStatements.forEach(stmt -> body.addStatement(stmt.clone()));

            // ★ 핵심 수정 1: 마지막 statement가 변수 선언이면, 그 변수를 참조하도록 변경
            if (!tempStatements.isEmpty()) {
                CtStatement lastStmt = tempStatements.get(tempStatements.size() - 1);
                if (lastStmt instanceof CtLocalVariable) {
                    CtLocalVariable<?> lastVar = (CtLocalVariable<?>) lastStmt;
                    CtVariableRead<Object> varRef = factory.createVariableRead();
                    varRef.setVariable((CtVariableReference<Object>) (CtVariableReference<?>) lastVar.getReference());
                    return varRef;
                }
            }

            // ★ 핵심 수정 2: 변수가 없으면, 복잡한 expression은 변수로 저장
            if (!isSimpleExpression(newlyCreatedExpr)) {
                // Handle array types: remove [] from the name
                String typeName = paramType.getSimpleName();
                if (paramType.isArray()) {
                    typeName = paramType.getQualifiedName().replaceAll("\\[\\]", "");
                    typeName = typeName.substring(typeName.lastIndexOf('.') + 1);
                }
                String varName = "extracted_" + typeName + "_" +
                        System.currentTimeMillis() + "_" + dummyVarCounter++;
                CtLocalVariable<?> extractedVar = factory.createLocalVariable();
                extractedVar.setSimpleName(varName);
                extractedVar.setType((CtTypeReference) paramType.clone());
                // Clone the expression to avoid modifying the original
                extractedVar.setDefaultExpression((CtExpression) newlyCreatedExpr.clone());
                body.addStatement(extractedVar);

                CtVariableRead<Object> varRef = factory.createVariableRead();
                varRef.setVariable((CtVariableReference<Object>) (CtVariableReference<?>) extractedVar.getReference());
                return varRef;
            }

            return newlyCreatedExpr;
        }

        return null;
    }

    /**
     * Try getting replacement from candidate pool
     * NOTE: This function ONLY looks up from the pool, does NOT create new objects
     */
    private static CtExpression<?> tryGetFromCandidatePool(CtTypeReference<?> paramType, CtBlock<?> body,
            Factory factory, int currentDepth) {

        totalPoolAugmentationCalls++;

        // Pure pool lookup - no object creation here
        CtExpression<?> exprFromPool = lookupCollectedInputs(paramType, body, factory, currentDepth);
        if (exprFromPool != null) {
            usedInputPool = true;
            return exprFromPool;
        }

        // Pool lookup failed - return null
        // Object creation will be handled by tryCreateNewObject in
        // handleDummyParameterVals
        return null;
    }

    /**
     * Final fallback attempt
     */
    private static CtExpression<?> tryFinalFallback(CtTypeReference<?> paramType, Factory factory) {
        CtExpression<?> simpleArg = createSimpleArgument(paramType, factory);
        if (isValidNonNullExpression(simpleArg)) {
            return simpleArg;
        }

        return null;
    }

    /**
     * Check if a type is simple enough to allow deeper recursion
     */
    private static boolean isSimpleType(CtTypeReference<?> type) {
        if (type == null)
            return false;

        String typeName = type.getQualifiedName();

        // Primitive types and their wrappers
        if (type.isPrimitive() ||
                typeName.startsWith("java.lang.") ||
                typeName.startsWith("java.util.") ||
                typeName.equals("java.lang.String")) {
            return true;
        }

        // Arrays of simple types
        if (type.isArray()) {
            CtTypeReference<?> componentType = ((CtArrayTypeReference<?>) type).getComponentType();
            return isSimpleType(componentType);
        }

        return false;
    }

    private static CtExpression<?> lookupCollectedInputs(CtTypeReference<?> paramType, CtBlock<?> body, Factory factory,
            int currentDepth) {

        // 1. 호환되는 모든 타입 후보를 수집합니다. (자기 자신 포함)
        Set<CtTypeReference<?>> compatibleTypes = new HashSet<>();

        // Track if we're searching for an array type
        boolean isSearchingForArray = paramType.isArray();
        CtTypeReference<?> searchType = paramType;

        // If paramType is an array, search for element type instead
        if (isSearchingForArray) {
            CtArrayTypeReference<?> arrayType = (CtArrayTypeReference<?>) paramType;
            CtTypeReference<?> elementType = arrayType.getComponentType();
            searchType = elementType;
        }

        compatibleTypes.add(searchType);

        // Get implementations for the search type (element type if array)
        String lookupKey = searchType.getQualifiedName();
        List<CtTypeReference<?>> implementations = ASTParser.abstractToImplsMap.get(lookupKey);

        if (implementations != null) {
            compatibleTypes.addAll(implementations);
        }

        // 2. 호환되는 모든 타입의 변수들을 CandidatePool에서 수집합니다.
        List<Pair<CtTypeReference, CtElement>> compatibleCandidates = new ArrayList<>();

        // --- [핵심 로직: abstractToImplsMap의 구현체들을 활용하여 pool 검색] ---
        for (CtTypeReference<?> typeToFind : compatibleTypes) {
            String typeNameToFind = typeToFind.getQualifiedName();

            // baseVarTypeNamePoolAsList의 모든 키를 순회합니다.
            for (Map.Entry<CtTypeReference, List<Pair<CtTypeReference, CtElement>>> entry : baseVarTypeNamePoolAsList
                    .entrySet()) {
                CtTypeReference<?> keyType = entry.getKey();

                // BUG FIX: Compare with typeToFind (which includes implementations from
                // abstractToImplsMap)
                // instead of paramType to properly utilize inheritance information
                if (isCompatibleType(keyType, typeToFind)) {
                    compatibleCandidates.addAll(entry.getValue());
                    // Don't break here - there might be multiple compatible entries
                }
            }
        }
        // --- [수정 끝] ---

        if (!compatibleCandidates.isEmpty()) {
            boolean isDebugType = paramType.getQualifiedName().contains("PropertyPointer");

            // Check pool quality and potentially create new objects for diversity
            int nonNullCount = countNonNullCandidates(compatibleCandidates, paramType);
            int totalCount = compatibleCandidates.size();

            // If pool is small or mostly null, try to create diverse objects
            // Increased threshold from 3 to 15 for more aggressive object generation
            boolean shouldCreateNew = (totalCount < 15) || (nonNullCount == 0) ||
                    (rand.nextDouble() < 0.3 && nonNullCount < 10);

            if (shouldCreateNew) {
                // Keep creating new diverse objects until we reach 15 or can't create more
                int targetPoolSize = 15;
                int createdCount = 0;
                int maxAttemptsPerType = 10; // Limit attempts per type to avoid infinite loops
                int failedAttempts = 0;
                int maxFailedAttempts = 3; // Stop if we fail 3 times in a row

                while (totalCount < targetPoolSize && createdCount < maxAttemptsPerType
                        && failedAttempts < maxFailedAttempts) {
                    // Try to create a new diverse object via constructor
                    CtExpression<?> newObject = tryCreateViaConstructorFromPool(paramType, factory, body, currentDepth);

                    if (newObject != null && !isNullLiteral(newObject)) {
                        createdCount++;
                        totalCount++; // Simulate adding to pool
                        failedAttempts = 0; // Reset failed attempts counter

                        // Return the first created object, others will be added to pool on subsequent
                        // calls
                        if (createdCount == 1) {
                            return newObject;
                        }
                    } else {
                        failedAttempts++;

                        if (failedAttempts >= maxFailedAttempts) {
                            break;
                        }
                    }
                }

            }

            // Pool에서 찾은 후보가 너무 적으면 새로 생성하는 것이 나을 수 있습니다. (기존 로직)
            // if (compatibleCandidates.size() < 4 && !paramType.isPrimitive()) {
            // return null;
            // }

            // 3. 찾은 후보 중 하나를 랜덤으로 선택하여 그 생성 시퀀스를 사용합니다.
            Pair<CtTypeReference, CtElement> randCand = compatibleCandidates
                    .get(rand.nextInt(compatibleCandidates.size()));
            Set<List<CtElement>> inputPool = baseVartypeToInputPool.get(randCand);

            if (inputPool != null && !inputPool.isEmpty()) {
                List<List<CtElement>> inputPoolList = new ArrayList<>(inputPool);
                List<CtElement> randomInputSequence = inputPoolList.get(rand.nextInt(inputPoolList.size()));

                if (!randomInputSequence.isEmpty()) {
                    // 시퀀스의 마지막 구문에서 변수 참조를 추출합니다.
                    CtElement lastElement = randomInputSequence.get(randomInputSequence.size() - 1);
                    CtExpression<?> resultExpression = null;

                    if (lastElement instanceof CtAssignment<?, ?>) {
                        CtAssignment<?, ?> assign = (CtAssignment<?, ?>) lastElement;
                        if (assign.getAssigned() instanceof CtVariableWrite<?>) {
                            CtVariableWrite<?> write = (CtVariableWrite<?>) assign.getAssigned();
                            resultExpression = factory.createVariableRead(write.getVariable(), false);
                        }
                    } else if (lastElement instanceof CtLocalVariable<?>) {
                        resultExpression = factory.createVariableRead(((CtLocalVariable<?>) lastElement).getReference(),
                                false);
                    } else if (lastElement instanceof CtInvocationImpl<?>) {
                        resultExpression = (CtExpression<?>) lastElement;
                    }

                    // 최종적으로 찾은 객체의 타입이 우리가 필요로 하는 타입과 호환되는지 확인합니다.
                    if (resultExpression != null && resultExpression.getType() != null) {
                        // If we were searching for array type, wrap the result
                        if (isSearchingForArray) {
                            // Check if result is compatible with element type
                            if (isCompatibleType(resultExpression.getType(), searchType)) {
                                // 해당 객체를 만드는 데 필요했던 모든 구문(시퀀스)을 현재 메소드 본문에 추가합니다.
                                addInputStatementsToBody(randomInputSequence, body);

                                // Wrap in array
                                CtNewArray arrayExpr = factory.createNewArray();
                                arrayExpr.setType((CtTypeReference) paramType);
                                List elements = new ArrayList<>();
                                elements.add(resultExpression);
                                arrayExpr.setElements(elements);
                                return arrayExpr;
                            }
                        } else if (isCompatibleType(resultExpression.getType(), paramType)) {
                            // 해당 객체를 만드는 데 필요했던 모든 구문(시퀀스)을 현재 메소드 본문에 추가합니다.
                            addInputStatementsToBody(randomInputSequence, body);
                            // 생성된 객체를 읽는 표현식을 반환합니다.
                            return resultExpression;
                        }
                    }
                }
            }
        }
        return null; // Pool에서 적절한 객체를 찾지 못한 경우
    }

    /**
     * Count the number of non-null candidates in the pool
     * Each candidate (pair) counts as 1, regardless of how many sequences it has
     */
    private static int countNonNullCandidates(List<Pair<CtTypeReference, CtElement>> candidates,
            CtTypeReference<?> paramType) {
        int nonNullCount = 0;
        for (Pair<CtTypeReference, CtElement> candidate : candidates) {
            Set<List<CtElement>> inputPool = baseVartypeToInputPool.get(candidate);
            if (inputPool != null && !inputPool.isEmpty()) {
                // Check if at least one sequence is non-null
                boolean hasNonNull = false;
                for (List<CtElement> sequence : inputPool) {
                    if (!sequence.isEmpty()) {
                        CtElement lastElement = sequence.get(sequence.size() - 1);

                        if (lastElement instanceof CtLocalVariable<?>) {
                            CtLocalVariable<?> var = (CtLocalVariable<?>) lastElement;
                            CtExpression<?> defaultExpr = var.getDefaultExpression();
                            if (isValidNonNullExpression(defaultExpr)) {
                                hasNonNull = true;
                                break;
                            }
                        } else if (lastElement instanceof CtAssignment<?, ?>) {
                            CtAssignment<?, ?> assign = (CtAssignment<?, ?>) lastElement;
                            CtExpression<?> assigned = assign.getAssignment();
                            if (isValidNonNullExpression(assigned)) {
                                hasNonNull = true;
                                break;
                            }
                        }
                    }
                }
                if (hasNonNull) {
                    nonNullCount++;
                }
            }
        }
        return nonNullCount;
    }

    /**
     * Check if all candidates in the pool are null objects
     */
    private static boolean checkIfAllCandidatesAreNull(List<Pair<CtTypeReference, CtElement>> candidates,
            CtTypeReference<?> paramType) {
        for (Pair<CtTypeReference, CtElement> candidate : candidates) {
            // Get the input sequences for this candidate
            Set<List<CtElement>> inputPool = baseVartypeToInputPool.get(candidate);
            if (inputPool != null && !inputPool.isEmpty()) {
                for (List<CtElement> sequence : inputPool) {
                    if (!sequence.isEmpty()) {
                        CtElement lastElement = sequence.get(sequence.size() - 1);

                        // Check if this sequence creates a non-null object
                        if (lastElement instanceof CtLocalVariable<?>) {
                            CtLocalVariable<?> var = (CtLocalVariable<?>) lastElement;
                            CtExpression<?> defaultExpr = var.getDefaultExpression();

                            // Use isValidNonNullExpression for consistency
                            // This catches null literals, casted nulls, and constructors with all null args
                            if (isValidNonNullExpression(defaultExpr)) {
                                return false; // Found at least one non-null candidate
                            }
                        } else if (lastElement instanceof CtAssignment<?, ?>) {
                            CtAssignment<?, ?> assign = (CtAssignment<?, ?>) lastElement;
                            CtExpression<?> assigned = assign.getAssignment();

                            // Use isValidNonNullExpression for consistency
                            if (isValidNonNullExpression(assigned)) {
                                return false; // Found at least one non-null candidate
                            }
                        }
                    }
                }
            }
        }
        return true; // All candidates are null objects
    }

    /**
     * Try to create a new object via constructor when pool only has null objects
     * This creates the object and adds all necessary statements to the body
     * 
     * Enhanced version that tries multiple strategies:
     * 1. Tries abstractToImplsMap for alternative implementations
     * 2. Tries different constructors prioritizing diversity
     * 3. Falls back to Pool objects if creation fails
     */
    private static CtExpression<?> tryCreateViaConstructorFromPool(CtTypeReference<?> paramType, Factory factory,
            CtBlock<?> body, int currentDepth) {
        // Prevent infinite recursion
        if (currentDepth > Config.MAX_DEPTH) {
            return tryGetObjectFromPool(paramType, factory, body);
        }

        // Collect all possible types to try (original type + implementations)
        List<CtTypeReference<?>> typesToTry = new ArrayList<>();
        typesToTry.add(paramType);

        // Add implementations from abstractToImplsMap
        List<CtTypeReference<?>> implementations = ASTParser.abstractToImplsMap.get(paramType.getQualifiedName());
        if (implementations != null && !implementations.isEmpty()) {
            typesToTry.addAll(implementations);
            Collections.shuffle(typesToTry, rand); // Shuffle for diversity
        }

        // Filter out types that already exist in the pool
        // Exception: Types in alwaysRegenerateTypes can be regenerated once per session
        // NEW: If pool has < 3 objects, allow regeneration for diversity
        List<CtTypeReference<?>> newTypesToTry = new ArrayList<>();
        for (CtTypeReference<?> typeToCheck : typesToTry) {
            String typeQName = typeToCheck.getQualifiedName();
            boolean shouldAlwaysRegenerate = alwaysRegenerateTypes.contains(typeQName);
            boolean hasBeenRegenerated = regeneratedInSession.contains(typeQName);
            boolean alreadyInPool = isTypeAlreadyInPool(typeToCheck);
            int poolCount = getPoolCountForType(typeToCheck);

            if (!alreadyInPool) {
                // Type not in pool - always include
                newTypesToTry.add(typeToCheck);
            } else if (poolCount < 3) {
                // Type in pool but count < 3 - include for diversity
                newTypesToTry.add(typeToCheck);
            } else if (shouldAlwaysRegenerate && !hasBeenRegenerated) {
                // Type in pool but should always be regenerated (only once per session)
                newTypesToTry.add(typeToCheck);
            }
        }
        typesToTry = newTypesToTry;

        // Try each type with multiple constructors
        for (int typeIndex = 0; typeIndex < typesToTry.size(); typeIndex++) {
            CtTypeReference<?> typeToTry = typesToTry.get(typeIndex);

            if (!isTypeAccessible(typeToTry)) {
                continue;
            }

            if (!isInstantiable(typeToTry)) {
                continue;
            }

            // Get all constructors for this type
            Map<String, Set<CtConstructor<?>>> constructorsMap = ASTParser.getAll_Constructors_Map();
            Set<CtConstructor<?>> allConstructors = constructorsMap.get(typeToTry.getQualifiedName());

            // If no direct constructors found, try to find constructors for compatible
            // implementations
            if (allConstructors == null || allConstructors.isEmpty()) {
                String typeQName = typeToTry.getQualifiedName();
                Map<String, List<CtTypeReference<?>>> abstractToImplsMap = ASTParser.getAbstractToImplsMap();
                List<CtTypeReference<?>> compatibleImpls = abstractToImplsMap.get(typeQName);

                if (compatibleImpls != null && !compatibleImpls.isEmpty()) {
                    allConstructors = new HashSet<>();
                    for (CtTypeReference<?> implType : compatibleImpls) {
                        Set<CtConstructor<?>> implConstructors = constructorsMap.get(implType.getQualifiedName());
                        if (implConstructors != null && !implConstructors.isEmpty()) {
                            allConstructors.addAll(implConstructors);
                        }
                    }
                }
            }

            if (allConstructors == null || allConstructors.isEmpty()) {
                continue;
            }

            // Filter accessible constructors and prioritize by parameter complexity
            List<CtConstructor<?>> accessibleConstructors = new ArrayList<>();
            String targetPackage = Config.PACKAGE != null ? Config.PACKAGE : "";

            for (CtConstructor<?> constructor : allConstructors) {
                String constructorPackage = (constructor.getDeclaringType().getPackage() != null)
                        ? constructor.getDeclaringType().getPackage().getQualifiedName()
                        : "";
                boolean isAccessible = false;

                if (constructor.isPublic()) {
                    isAccessible = true;
                } else if (constructor.isProtected()) {
                    isAccessible = constructorPackage.equals(targetPackage);
                } else if (!constructor.isPrivate()) {
                    isAccessible = constructorPackage.equals(targetPackage);
                }

                if (isAccessible) {
                    accessibleConstructors.add(constructor);
                }
            }

            if (accessibleConstructors.isEmpty()) {
                continue;
            }

            // Sort constructors by priority: public > protected, primitive count (desc),
            // param count (desc)
            accessibleConstructors.sort((c1, c2) -> {
                // 1. Prefer public constructors over protected
                if (c1.isPublic() != c2.isPublic()) {
                    return c1.isPublic() ? -1 : 1;
                }

                // 2. Prefer constructors with more primitive parameters (easier to generate)
                int primitiveCount1 = countPrimitiveParameters(c1);
                int primitiveCount2 = countPrimitiveParameters(c2);
                if (primitiveCount1 != primitiveCount2) {
                    return Integer.compare(primitiveCount2, primitiveCount1);
                }

                // 3. Prefer constructors with more parameters (more specific/complete
                // initialization)
                return Integer.compare(c2.getParameters().size(), c1.getParameters().size());
            });

            // Try each constructor in priority order
            for (int ctorIndex = 0; ctorIndex < accessibleConstructors.size(); ctorIndex++) {
                CtConstructor<?> constructor = accessibleConstructors.get(ctorIndex);

                try {
                    CtBlock<?> tempBody = factory.createBlock();
                    CtExpression<?> newObject = createConstructorCallFromConstructorWithPoolFallback(
                            constructor, factory, tempBody, currentDepth + 1, typeToTry);

                    // Check if the created object is not null
                    if (newObject != null && !isNullLiteral(newObject)) {
                        // Add all statements from tempBody to the actual body (includes dependencies)
                        for (CtStatement stmt : tempBody.getStatements()) {
                            body.addStatement(stmt.clone());
                        }

                        // Track if this type is marked for one-time regeneration
                        String typeQName = typeToTry.getQualifiedName();
                        if (alwaysRegenerateTypes.contains(typeQName)) {
                            regeneratedInSession.add(typeQName);
                        }

                        return newObject;
                    }
                } catch (Exception e) {
                    // Constructor creation failed, try next one
                }
            }
        }

        // All construction attempts failed, fallback to Pool
        return tryGetObjectFromPool(paramType, factory, body);
    }

    /**
     * Fallback: Try to get an existing object from Pool instead of creating new one
     */
    private static CtExpression<?> tryGetObjectFromPool(CtTypeReference<?> paramType, Factory factory,
            CtBlock<?> body) {
        if (baseVarTypeNamePoolAsList == null || baseVarTypeNamePoolAsList.isEmpty()) {
            return null;
        }

        // Find compatible types in pool
        for (Map.Entry<CtTypeReference, List<Pair<CtTypeReference, CtElement>>> entry : baseVarTypeNamePoolAsList
                .entrySet()) {
            if (isCompatibleType(entry.getKey(), paramType)) {
                List<Pair<CtTypeReference, CtElement>> candidates = entry.getValue();
                if (candidates != null && !candidates.isEmpty()) {
                    Pair<CtTypeReference, CtElement> candidate = candidates.get(rand.nextInt(candidates.size()));
                    Set<List<CtElement>> inputPool = baseVartypeToInputPool.get(candidate);

                    if (inputPool != null && !inputPool.isEmpty()) {
                        List<CtElement> sequence = new ArrayList<>(inputPool).get(0);
                        if (!sequence.isEmpty()) {
                            addInputStatementsToBody(sequence, body);
                            CtElement lastElement = sequence.get(sequence.size() - 1);

                            if (lastElement instanceof CtLocalVariable) {
                                CtLocalVariable<?> var = (CtLocalVariable<?>) lastElement;
                                return factory.createVariableRead(var.getReference(), false);
                            } else if (lastElement instanceof CtAssignment) {
                                CtAssignment<?, ?> assign = (CtAssignment<?, ?>) lastElement;
                                if (assign.getAssigned() instanceof CtVariableWrite) {
                                    CtVariableWrite<?> write = (CtVariableWrite<?>) assign.getAssigned();
                                    return factory.createVariableRead(write.getVariable(), false);
                                }
                            }
                        }
                    }
                }
            }
        }

        return null;
    }

    /**
     * Create constructor call with Pool fallback for parameters
     * If parameter creation fails, tries to use objects from Pool instead of null
     */
    private static CtExpression<?> createConstructorCallFromConstructorWithPoolFallback(
            CtConstructor<?> constructor, Factory factory, CtBlock<?> body, int currentDepth,
            CtTypeReference<?> targetType) {

        boolean isDebugType = targetType.getQualifiedName().contains("PropertyPointer");

        CtConstructorCall<?> constructorCall = factory.createConstructorCall();
        constructorCall.setType((CtTypeReference) targetType.clone());

        List<CtExpression<?>> args = new ArrayList<>();

        for (int i = 0; i < constructor.getParameters().size(); i++) {
            CtParameter<?> param = constructor.getParameters().get(i);
            CtTypeReference<?> paramType = param.getType();

            // Register null object for this parameter type
            registerNullObjectForType(paramType, factory);

            // Check for hardcoded type preferences for specific constructor combinations
            CtExpression<?> paramExpr = tryGetPreferredTypeForConstructor(targetType, paramType, factory, body,
                    currentDepth);

            if (paramExpr != null && !isNullLiteral(paramExpr)) {
                args.add(paramExpr);
                continue;
            }

            // Try to create parameter value
            paramExpr = handleDummyParameterVals(paramType, body, factory, currentDepth);

            // If creation failed or returned null, try to get from Pool
            if (paramExpr == null || isNullLiteral(paramExpr)) {
                paramExpr = tryGetObjectFromPool(paramType, factory, body);
            }

            // If still null, use simple default
            if (paramExpr == null || isNullLiteral(paramExpr)) {
                paramExpr = createSimpleArgument(paramType, factory);
            }

            args.add(paramExpr);
        }

        constructorCall.setArguments(args);
        return constructorCall;
    }

    private static CtExpression<?> generateMockUpPrims(CtTypeReference<?> typeRef, Factory factory) {
        if (typeRef == null) {
            throw new IllegalArgumentException("typeRef cannot be null");
        }

        CtExpression<?> initExpr = null;
        if (isLiteral(typeRef)) {
            switch (typeRef.getSimpleName()) {
                case "int":
                case "short":
                case "byte":
                case "long":
                    initExpr = factory.createLiteral(0);
                    break;
                case "float":
                case "double":
                    initExpr = factory.createLiteral(0.0);
                    break;
                case "boolean":
                    initExpr = factory.createLiteral(false);
                    break;
                case "char":
                    initExpr = factory.createLiteral('a');
                    break;
                case "String":
                    initExpr = factory.createLiteral("dummy");
                    break;
                default:
                    initExpr = null; // void 등 특수 케이스
                    break;
            }
        }
        return initExpr;
    }

    // seqc/SeedAugmentor.java

    private static CtExpression<?> generateMockUpArrays(CtTypeReference<?> typeRef, Factory factory, CtBlock<?> body,
            int currentDepth) {
        if (typeRef == null) {
            throw new IllegalArgumentException("typeRef cannot be null");
        }

        if (currentDepth > Config.MAX_DEPTH) {
            return factory.createLiteral(null);
        }

        if (typeRef instanceof CtArrayTypeReference<?>) {
            CtArrayTypeReference<?> arrayTypeRef = (CtArrayTypeReference<?>) typeRef;
            CtTypeReference<?> componentType = arrayTypeRef.getComponentType();

            // --- [핵심 수정: Raw Type 및 올바른 API 사용] ---
            // CtNewArray<?> 대신 Raw Type 'CtNewArray'를 사용합니다.
            CtNewArray newArray = factory.createNewArray();

            if (componentType.getQualifiedName().equals("java.lang.Object")) {
                CtExpression<?> randomElement = pickRandomElementFromAnyPool(factory, body);

                if (randomElement != null) {
                    CtTypeReference<?> actualComponentType = randomElement.getType();
                    if (actualComponentType != null && !actualComponentType.isImplicit()) {
                        // createArrayTypeReference는 인자 없이 호출 후, setComponentType을 사용해야 합니다.
                        CtArrayTypeReference actualArrayType = factory.createArrayTypeReference();
                        actualArrayType.setComponentType(actualComponentType);

                        newArray.setType(actualArrayType);
                        newArray.setElements(Collections.singletonList(randomElement));
                        return newArray;
                    }
                }
                newArray.setType(arrayTypeRef.clone());
                newArray.setElements(Collections
                        .singletonList((CtExpression) makeTypedNull(factory, arrayTypeRef.getComponentType())));
                return newArray;
            } else {
                newArray.setType(typeRef.clone());
                CtExpression<?> initExpr = createDefaultExpressionForType(componentType, factory, body,
                        currentDepth + 1);

                // Verify that initExpr is compatible with componentType
                if (initExpr != null && initExpr.getType() != null) {
                    // Check if types are compatible
                    if (!isCompatibleType(initExpr.getType(), componentType)) {
                        // Incompatible - use null instead
                        System.out.println(
                                "[WARN] Array element type mismatch: expected " + componentType.getQualifiedName() +
                                        ", got " + initExpr.getType().getQualifiedName() + " - using null");
                        initExpr = makeTypedNull(factory, componentType);
                    }
                }

                newArray.setElements(Collections.singletonList(initExpr));
                return newArray;
            }
        }

        return factory.createLiteral(null);
    }

    private static CtExpression<?> pickRandomElementFromAnyPool(Factory factory, CtBlock<?> body) {
        List<CtExpression<?>> candidates = new ArrayList<>();

        if (baseDirectToValuesAsList != null && !baseDirectToValuesAsList.isEmpty()) {
            List<CtTypeReference<?>> types = new ArrayList<>(baseDirectToValuesAsList.keySet());
            CtTypeReference<?> randomType = types.get(rand.nextInt(types.size()));
            List<CtElement> values = baseDirectToValuesAsList.get(randomType);
            if (values != null && !values.isEmpty()) {
                candidates.add((CtExpression<?>) values.get(rand.nextInt(values.size())));
            }
        }

        if (baseVartypeToInputPool != null && !baseVartypeToInputPool.isEmpty()) {
            List<Pair<CtTypeReference, CtElement>> keys = new ArrayList<>(baseVartypeToInputPool.keySet());
            Pair<CtTypeReference, CtElement> randomKey = keys.get(rand.nextInt(keys.size()));

            Set<List<CtElement>> sequences = baseVartypeToInputPool.get(randomKey);
            if (sequences != null && !sequences.isEmpty()) {
                List<CtElement> randomSequence = new ArrayList<>(sequences).get(0);
                if (!randomSequence.isEmpty()) {
                    addInputStatementsToBody(randomSequence, body);

                    CtElement lastElement = randomSequence.get(randomSequence.size() - 1);
                    if (lastElement instanceof CtLocalVariable) {
                        return factory.createVariableRead(((CtLocalVariable<?>) lastElement).getReference(), false);
                    }
                }
            }
        }

        if (!candidates.isEmpty()) {
            return candidates.get(rand.nextInt(candidates.size()));
        }

        return null;
    }

    private static CtExpression<?> generateAbstractExpr(
            CtTypeReference<?> typeRef,
            Factory factory,
            CtBlock<?> body,
            int currentDepth) {

        // Register null object for this abstract type before attempting to create it
        registerNullObjectForType(typeRef, factory);

        // Check if the abstract type is accessible
        if (!isTypeAccessible(typeRef)) {
            // Abstract type is not accessible, return null
            return makeTypedNull(factory, typeRef);
        }

        // --- [NEW: 우선순위 1 - Factory 메소드 탐색] ---
        CtInvocation<?> factoryMethodCall = tryCreateFromFactoryMethod(typeRef, factory, body, currentDepth);
        if (factoryMethodCall != null) {
            return factoryMethodCall;
        }

        // 1. 하드코딩된 규칙 맵을 사용하여 흔한 추상 타입을 처리합니다.
        Map<String, Class<?>> abstractTypeToImpl = new HashMap<>();
        abstractTypeToImpl.put("java.util.List", ArrayList.class);
        abstractTypeToImpl.put("java.util.Map", HashMap.class);
        abstractTypeToImpl.put("java.util.Set", HashSet.class);
        abstractTypeToImpl.put("java.io.Writer", java.io.StringWriter.class);
        abstractTypeToImpl.put("java.lang.Number", Long.class); // Number의 기본 구현체로 Long을 사용

        String qualifiedName = typeRef.getQualifiedName();
        Class<?> implClass = abstractTypeToImpl.get(qualifiedName);

        if (implClass != null) {
            CtConstructorCall<?> constructorCall = factory.createConstructorCall();
            CtTypeReference<?> implTypeRef = factory.Type().createReference(implClass);
            constructorCall.setType((CtTypeReference) implTypeRef);

            // [핵심 수정] 각 클래스에 맞는 유효한 생성자 인자를 제공합니다.
            if (implClass == String.class) {
                constructorCall.setArguments(Collections.singletonList(factory.createLiteral("dummy")));
            } else if (implClass == Long.class) {
                // Long 클래스는 인자가 없는 기본 생성자가 없으므로, 유효한 인자(0L)를 넣어줍니다.
                constructorCall.setArguments(Collections.singletonList(factory.createLiteral(0L)));
            }
            // ArrayList, HashMap 등은 인자 없는 기본 생성자 호출이 유효하므로 별도 처리가 필요 없습니다.

            // Add to CandidatePool for reuse
            addToCandidatePool(implTypeRef, constructorCall, factory, "variant_" + implClass.getSimpleName());

            return constructorCall;
        }

        // 2. 맵에 규칙이 없으면, 프로젝트 코드 내에서 구현체를 탐색합니다.
        CtExpression<?> foundExpr = tryFindConcreteImplementation(typeRef, factory, body, currentDepth + 1);
        if (foundExpr != null) {
            return foundExpr;
        }

        // 3. 모든 방법이 실패하면 null을 반환합니다.
        // System.err.println("No concrete implementation or rule found for abstract
        // type: " + typeRef);
        return makeTypedNull(factory, typeRef);
    }

    private static CtExpression<?> tryFindConcreteImplementation(CtTypeReference<?> typeRef, Factory factory,
            CtBlock<?> body, int currentDepth) {
        String abstractKey = typeRef.getQualifiedName();

        // Try both with and without generic parameters
        List<CtTypeReference<?>> impls = ASTParser.getAbstractToImplsMap().get(typeRef.getQualifiedName());

        // If not found, try removing generic parameters
        if (impls == null || impls.isEmpty()) {
            String baseType = typeRef.getQualifiedName().replaceAll("<.*>", "");
            if (!baseType.equals(typeRef.getQualifiedName())) {
                impls = ASTParser.getAbstractToImplsMap().get(baseType);
            }
        }

        if (impls != null && !impls.isEmpty()) {
            // Check if the abstract type itself is accessible
            if (!isTypeAccessible(typeRef)) {
                // Abstract type is not accessible, skip variant generation
                return null;
            }

            // Check if we've already generated variants for this type
            if (variantsGeneratedTypes.contains(abstractKey)) {
                // Select implementation with simplest constructor (prioritize primitive
                // parameters)
                CtTypeReference<?> selectedImpl = selectImplementationWithSimplestConstructor(impls);
                if (selectedImpl != null) {
                    CtConstructor<?> constructor = findMatchingConstructor(selectedImpl, factory);
                    if (constructor != null) {
                        return createConstructorCallFromConstructor(constructor, factory, body, currentDepth,
                                selectedImpl);
                    }
                }
                return null;
            }

            // Mark this type as having variants generated
            variantsGeneratedTypes.add(abstractKey);

            // [DIVERSITY] Generate up to 3 diverse implementations (not including null)
            int variantsToGenerate = Math.min(3, impls.size()); // Generate up to 3 variants
            List<CtTypeReference<?>> shuffledImpls = new ArrayList<>(impls);
            Collections.shuffle(shuffledImpls, rand);

            CtExpression<?> firstSuccessful = null;
            int successCount = 0;

            for (int i = 0; i < shuffledImpls.size() && successCount < variantsToGenerate; i++) {
                CtTypeReference<?> impl = shuffledImpls.get(i);

                // Skip implementations that are not accessible
                if (!isTypeAccessible(impl)) {
                    continue;
                }

                CtConstructor<?> constructor = findMatchingConstructor(impl, factory);

                if (constructor != null) {
                    CtBlock<?> tempBody = factory.createBlock();
                    CtExpression<?> expr = createConstructorCallFromConstructor(constructor, factory, tempBody,
                            currentDepth, impl);

                    if (expr != null) {
                        // Create a variable for this variant and add sequence to pool
                        String varName = "variant_" + impl.getSimpleName() + "_" + System.currentTimeMillis() + "_"
                                + dummyVarCounter++;
                        CtLocalVariable<?> varDecl = factory.createLocalVariable();
                        varDecl.setSimpleName(varName);
                        // Use actual implementation type instead of abstract type for better type
                        // information
                        varDecl.setType((CtTypeReference) impl.clone());
                        varDecl.setDefaultExpression((CtExpression) expr.clone());

                        // Build the complete sequence: all statements + variable declaration
                        List<CtElement> sequence = new ArrayList<>();
                        tempBody.getStatements().forEach(stmt -> sequence.add(stmt.clone()));
                        sequence.add(varDecl.clone());

                        // Add to vartypeToInputPool with the sequence - use actual implementation type!
                        Pair<CtTypeReference, CtElement> pair = new Pair<>(impl, varDecl.getReference());
                        CandidatePool.insertVarTypeToInputPool(pair, sequence);

                        // Keep first successful one to return
                        if (firstSuccessful == null) {
                            firstSuccessful = expr;
                            tempBody.getStatements().forEach(stmt -> body.addStatement(stmt.clone()));
                            abstractConstructorCache.put(abstractKey, constructor);
                        }

                        successCount++;
                    }
                }
            }

            // After generating variants, also add a null object (separate from the 3
            // variants)
            if (firstSuccessful != null && !hasNullObjectInPool(typeRef)) {
                createAndRegisterNullObject(typeRef, factory);
            }

            return firstSuccessful;
        }

        return null; // 구현체를 찾지 못한 경우
    }

    /**
     * Optimized factory method creation with caching to reduce overhead
     */
    public static CtInvocation<?> tryCreateFromFactoryMethod(CtTypeReference<?> typeRef, Factory factory,
            CtBlock<?> body, int currentDepth) {
        if (currentDepth > Config.MAX_DEPTH) {
            return null;
        }

        String typeName = typeRef.getQualifiedName();

        // Check cache first
        List<CtMethod<?>> cachedFactoryMethods = factoryMethodCache.get(typeName);
        if (cachedFactoryMethods == null) {
            // Build cache entry
            cachedFactoryMethods = buildFactoryMethodCache(typeRef);
            factoryMethodCache.put(typeName, cachedFactoryMethods);
        }

        if (cachedFactoryMethods.isEmpty()) {
            return null;
        }

        // Try cached factory methods in priority order
        for (CtMethod<?> factoryMethod : cachedFactoryMethods) {
            CtBlock<?> tempBody = factory.createBlock();
            CtInvocation<?> methodCall = createFactoryMethodCall(factoryMethod, factory, tempBody, currentDepth);

            if (methodCall != null) {
                tempBody.getStatements().forEach(stmt -> body.addStatement(stmt.clone()));
                // System.out.println("[FACTORY] Created object using factory method: " +
                // factoryMethod.getDeclaringType().getSimpleName() + "." +
                // factoryMethod.getSimpleName());
                return methodCall;
            }
        }

        return null;
    }

    /**
     * Build and cache factory methods for a type (called once per type)
     */
    private static List<CtMethod<?>> buildFactoryMethodCache(CtTypeReference<?> typeRef) {
        HashMap<String, Set<CtMethod<?>>> allMethodsMap = ASTParser.getAllMethods();
        Set<CtMethod<?>> methods = allMethodsMap.get(typeRef.getQualifiedName());

        if (methods == null || methods.isEmpty()) {
            return Collections.emptyList();
        }

        List<CtMethod<?>> factoryMethodCandidates = new ArrayList<>();
        String targetPackage = Config.PACKAGE;

        for (CtMethod<?> method : methods) {
            // Quick checks first (most likely to fail)
            if (!method.hasModifier(ModifierKind.STATIC)) {
                continue;
            }

            // Method name pattern check (fast string operation)
            String methodName = method.getSimpleName();
            if (!isFactoryMethodName(methodName)) {
                continue;
            }

            // Accessibility check
            if (!isMethodAccessible(method, targetPackage)) {
                continue;
            }

            // Return type compatibility (expensive check last)
            CtTypeReference<?> returnType = method.getType();
            if (returnType != null && isCompatibleTypeCached(returnType, typeRef)) {
                factoryMethodCandidates.add(method);
            }
        }

        // Sort once and cache the result
        factoryMethodCandidates.sort((m1, m2) -> {
            int paramDiff = m1.getParameters().size() - m2.getParameters().size();
            if (paramDiff != 0) {
                return paramDiff;
            }

            String name1 = m1.getSimpleName();
            String name2 = m2.getSimpleName();
            int priority1 = getFactoryMethodPriority(name1);
            int priority2 = getFactoryMethodPriority(name2);
            return priority1 - priority2;
        });

        return factoryMethodCandidates;
    }

    /**
     * Fast factory method name check using pre-built set
     */
    private static boolean isFactoryMethodName(String methodName) {
        if (factoryMethodNames.contains(methodName)) {
            return true;
        }

        // Check prefixes for common patterns (createXxx, buildXxx, etc.)
        for (String factoryName : factoryMethodNames) {
            if (methodName.startsWith(factoryName)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Optimized method accessibility check
     */
    private static boolean isMethodAccessible(CtMethod<?> method, String targetPackage) {
        // private 메소드는 같은 패키지여도 접근 불가
        if (method.isPrivate()) {
            return false;
        }

        if (method.isPublic()) {
            return true;
        }

        // Protected 메소드는 같은 패키지에만 접근 가능
        if (method.isProtected()) {
            String methodPackage = (method.getDeclaringType().getPackage() != null)
                    ? method.getDeclaringType().getPackage().getQualifiedName()
                    : "";
            return methodPackage.equals(targetPackage);
        }

        // Package-private 메소드는 같은 패키지만 접근 가능
        String methodPackage = (method.getDeclaringType().getPackage() != null)
                ? method.getDeclaringType().getPackage().getQualifiedName()
                : "";

        return methodPackage.equals(targetPackage);
    }

    /**
     * Returns priority value for factory method names (lower = higher priority)
     */
    private static int getFactoryMethodPriority(String methodName) {
        if (methodName.equals("getInstance"))
            return 0;
        if (methodName.equals("newInstance"))
            return 1;
        if (methodName.equals("create"))
            return 2;
        if (methodName.equals("createInstance"))
            return 3;
        if (methodName.equals("valueOf"))
            return 4;
        if (methodName.equals("of"))
            return 5;
        if (methodName.equals("from"))
            return 6;
        if (methodName.equals("parse"))
            return 7;
        if (methodName.equals("build"))
            return 8;
        if (methodName.equals("get"))
            return 9;
        return 10; // Other factory methods
    }

    /**
     * Cached version of type compatibility check to reduce overhead
     */
    public static boolean isCompatibleTypeCached(CtTypeReference<?> returnType, CtTypeReference<?> targetType) {
        String cacheKey = returnType.getQualifiedName() + ":" + targetType.getQualifiedName();
        Boolean cached = typeCompatibilityCache.get(cacheKey);

        if (cached != null) {
            return cached;
        }

        boolean compatible = isCompatibleType(returnType, targetType);
        typeCompatibilityCache.put(cacheKey, compatible);
        return compatible;
    }

    /**
     * Checks if return type is compatible with target type
     */
    private static boolean isCompatibleType(CtTypeReference<?> returnType, CtTypeReference<?> targetType) {
        if (returnType == null || targetType == null) {
            return false;
        }

        // Fast equality check first
        if (returnType.equals(targetType)) {
            return true;
        }

        // CRITICAL: Array types and base types should NOT be compatible
        // DateTimeFieldType[] should NOT be compatible with DateTimeFieldType
        if (returnType.isArray() != targetType.isArray()) {
            return false;
        }

        // If both are arrays, check their component types
        if (returnType.isArray() && targetType.isArray()) {
            // For arrays, compare the qualified names without the [] suffix
            String returnTypeName = returnType.getQualifiedName().replace("[]", "");
            String targetTypeName = targetType.getQualifiedName().replace("[]", "");
            return returnTypeName.equals(targetTypeName);
        }

        // For generic types, we need to check both the raw type and type arguments
        if (returnType.getActualTypeArguments() != null && !returnType.getActualTypeArguments().isEmpty() ||
                targetType.getActualTypeArguments() != null && !targetType.getActualTypeArguments().isEmpty()) {

            // Both must have the same raw type first
            if (!returnType.getQualifiedName().equals(targetType.getQualifiedName())) {
                return false;
            }

            // Check if both have type arguments
            List<CtTypeReference<?>> returnArgs = returnType.getActualTypeArguments();
            List<CtTypeReference<?>> targetArgs = targetType.getActualTypeArguments();

            // If one has type arguments and the other doesn't, they're not compatible
            if ((returnArgs == null || returnArgs.isEmpty()) != (targetArgs == null || targetArgs.isEmpty())) {
                return false;
            }

            // If both have type arguments, they must match
            if (returnArgs != null && targetArgs != null &&
                    returnArgs.size() == targetArgs.size()) {
                for (int i = 0; i < returnArgs.size(); i++) {
                    if (!isCompatibleType(returnArgs.get(i), targetArgs.get(i))) {
                        return false;
                    }
                }
                return true;
            }

            // If type arguments don't match in size, not compatible
            return false;
        }

        // Fast qualified name check for non-generic types
        String returnTypeName = returnType.getQualifiedName();
        String targetTypeName = targetType.getQualifiedName();
        if (returnTypeName.equals(targetTypeName)) {
            return true;
        }

        // Expensive subtype check last
        try {
            return returnType.isSubtypeOf(targetType);
        } catch (Exception e) {
            // If subtype checking fails, assume incompatible
            return false;
        }
    }

    /**
     * Creates a factory method call with appropriate parameters
     */
    private static CtInvocation<?> createFactoryMethodCall(CtMethod<?> factoryMethod, Factory factory, CtBlock<?> body,
            int currentDepth) {
        CtInvocation<?> methodCall = factory.createInvocation();
        methodCall.setExecutable((CtExecutableReference) factoryMethod.getReference());

        // Set target to the class (since it's a static method)
        CtTypeAccess<?> typeAccess = factory.createTypeAccess();
        typeAccess.setAccessedType((CtTypeReference) factoryMethod.getDeclaringType().getReference());
        methodCall.setTarget(typeAccess);

        // Generate arguments for the factory method
        List<CtExpression<?>> args = new ArrayList<>();

        for (CtParameter<?> param : factoryMethod.getParameters()) {
            CtTypeReference<?> paramType = param.getType();

            // Register null object for each parameter type
            registerNullObjectForType(paramType, factory);

            CtExpression<?> paramInitExpr = handleDummyParameterVals(paramType, body, factory, currentDepth + 1);

            // Safety check
            if (paramInitExpr != null && paramInitExpr.getType() != null
                    && !paramInitExpr.getType().isSubtypeOf(paramType)) {
                paramInitExpr = null;
            }

            if (paramInitExpr == null ||
                    (isNullLiteral(paramInitExpr) && !paramType.getQualifiedName().equals("java.lang.Object"))) {
                // Try to create a simple default value for the parameter
                CtExpression<?> simpleDefault = createSimpleArgument(paramType, factory);
                args.add(simpleDefault);
                continue;
            }

            if (isLiteral(paramType) || usedInputPool) {
                args.add(paramInitExpr);
                usedInputPool = false;
            } else {
                // Create local variable for complex parameters
                String argVarName = "factoryParam_" + System.currentTimeMillis() + "_" + dummyVarCounter++;
                CtLocalVariable<?> localVar = factory.createLocalVariable();
                localVar.setSimpleName(argVarName);
                localVar.setType((CtTypeReference) paramType.clone());
                localVar.setDefaultExpression((CtExpression) paramInitExpr);
                body.addStatement(localVar);

                CtVariableRead<?> varRead = factory.createVariableRead();
                varRead.setVariable((CtVariableReference) localVar.getReference());
                args.add(varRead);
            }
        }

        methodCall.setArguments(args);
        return methodCall;
    }

    private static CtExpression<?> generateConcreteExpr(CtTypeReference<?> typeRef, Factory factory, CtBlock<?> body,
            int currentDepth) {
        // Register null object for this type before attempting to create it
        registerNullObjectForType(typeRef, factory);

        // Check if the type is accessible
        if (!isTypeAccessible(typeRef)) {
            // Type is not accessible, return null
            return makeTypedNull(factory, typeRef);
        }

        // Check if the type can be instantiated (not abstract, not interface)
        if (!isInstantiable(typeRef)) {
            // Type is abstract or interface, try to find implementation
            return generateAbstractExpr(typeRef, factory, body, currentDepth);
        }

        if (currentDepth > Config.MAX_DEPTH) {
            return generateDefaultConstructorCall(typeRef, factory, body);
        }

        // --- [NEW: 우선순위 1 - Factory 메소드 탐색] ---
        CtInvocation<?> factoryMethodCall = tryCreateFromFactoryMethod(typeRef, factory, body, currentDepth);
        if (factoryMethodCall != null) {
            return factoryMethodCall;
        }

        Map<String, Set<CtConstructor<?>>> constructorsMap = ASTParser.getAll_Constructors_Map();
        Set<CtConstructor<?>> allConstructors = constructorsMap.get(typeRef.getQualifiedName());

        if (allConstructors != null && !allConstructors.isEmpty()) {
            boolean isDebugType = typeRef.getQualifiedName().contains("PropertyPointer");

            // --- [핵심 수정: 접근 가능한 생성자 필터링 및 우선순위 부여] ---
            String targetTestPackage = Config.PACKAGE;

            // If Config.PACKAGE is empty, try to get the package from the type itself
            if (targetTestPackage == null || targetTestPackage.isEmpty()) {
                if (typeRef.getPackage() != null) {
                    targetTestPackage = typeRef.getPackage().getQualifiedName();
                }
            }

            List<CtConstructor<?>> accessibleCandidates = new ArrayList<>();

            for (CtConstructor<?> constructor : allConstructors) {
                String constructorPackage = (constructor.getDeclaringType().getPackage() != null)
                        ? constructor.getDeclaringType().getPackage().getQualifiedName()
                        : "";

                // 조건: private이 아니고, 1) public 이거나, 2) 생성될 테스트와 같은 패키지에 속해 있는가?
                boolean isAccessible = !constructor.isPrivate()
                        && (constructor.isPublic() || constructorPackage.equals(targetTestPackage));

                if (isAccessible) {
                    accessibleCandidates.add(constructor);
                }
            }
            // --- [수정 끝] ---

            // 접근 가능한 후보가 있을 경우에만 생성자 호출을 시도합니다.
            if (!accessibleCandidates.isEmpty()) {
                // Primitive 파라미터가 많은 순, 파라미터 개수가 적은 순으로 정렬
                accessibleCandidates.sort((c1, c2) -> {
                    int primitiveCount1 = countPrimitiveParameters(c1);
                    int primitiveCount2 = countPrimitiveParameters(c2);

                    if (primitiveCount1 != primitiveCount2) {
                        return Integer.compare(primitiveCount2, primitiveCount1);
                    }

                    return Integer.compare(c1.getParameters().size(), c2.getParameters().size());
                });

                // ★ 랜덤하게 Constructor 선택 (다양성 증대)
                int randomIndex = rand.nextInt(accessibleCandidates.size());
                CtConstructor<?> selectedConstructor = accessibleCandidates.get(randomIndex);

                CtBlock<?> tempBody = factory.createBlock();
                CtConstructorCall<?> call = createConstructorCallFromConstructor(selectedConstructor, factory, tempBody,
                        currentDepth, typeRef);

                if (call != null) {
                    tempBody.getStatements().forEach(stmt -> body.addStatement(stmt.clone()));
                    return call;
                }

                // 선택된 Constructor가 실패하면 정렬된 순서대로 다른 Constructor들 시도
                for (CtConstructor<?> constructor : accessibleCandidates) {
                    if (constructor == selectedConstructor) {
                        continue; // 이미 시도한 것은 건너뛰기
                    }

                    tempBody = factory.createBlock();
                    call = createConstructorCallFromConstructor(constructor, factory, tempBody,
                            currentDepth, typeRef);

                    if (call != null) {
                        tempBody.getStatements().forEach(stmt -> body.addStatement(stmt.clone()));
                        return call;
                    }
                }
            }
        }

        // (이하 recursiveMethodCalls 등의 Fallback 로직은 기존과 동일)
        if (recursiveMethodCalls) {
            CtMethod<?> selectedMethod = findMatchingMethod(typeRef, factory);
            if (selectedMethod != null) {
                return createMethodInvo(selectedMethod, factory, body, currentDepth);
            }
        }

        return generateDefaultConstructorCall(typeRef, factory, body);
    }

    private static CtExpression<?> generateDefaultConstructorCall(CtTypeReference<?> type, Factory factory,
            CtBlock<?> body) {
        if (type == null) {
            return factory.createLiteral(null);
        }

        // Handle arrays specially - create empty array or array with null element
        if (type.isArray()) {
            return generateMockUpArrays(type, factory, body, 0);
        }

        // Handle String specially
        if ("java.lang.String".equals(type.getQualifiedName())) {
            return factory.createLiteral("");
        }

        // Check if the type can be instantiated
        if (!isInstantiable(type)) {
            // Type is abstract or interface, cannot create constructor call
            // Factory method lookup is already done in generateAbstractExpr and
            // generateConcreteExpr
            // Doing it here would cause infinite recursion
            return makeTypedNull(factory, type);
        }

        // Try to find any available constructor for the type
        Map<String, Set<CtConstructor<?>>> constructorsMap = ASTParser.getAll_Constructors_Map();
        Set<CtConstructor<?>> allConstructors = constructorsMap.get(type.getQualifiedName());

        if (allConstructors != null && !allConstructors.isEmpty()) {
            // Find the constructor with the fewest parameters that we can satisfy
            // Prioritize constructors with primitive/basic types
            List<CtConstructor<?>> sortedConstructors = new ArrayList<>(allConstructors);
            sortedConstructors.sort((c1, c2) -> {
                int primitiveCount1 = countPrimitiveParameters(c1);
                int primitiveCount2 = countPrimitiveParameters(c2);

                if (primitiveCount1 != primitiveCount2) {
                    return Integer.compare(primitiveCount2, primitiveCount1);
                }

                return Integer.compare(c1.getParameters().size(), c2.getParameters().size());
            });

            for (CtConstructor<?> constructor : sortedConstructors) {
                // Check if constructor is accessible
                String constructorPackage = (constructor.getDeclaringType().getPackage() != null)
                        ? constructor.getDeclaringType().getPackage().getQualifiedName()
                        : "";
                boolean isAccessible = !constructor.isPrivate()
                        && (constructor.isPublic() || constructorPackage.equals(Config.PACKAGE));

                if (isAccessible) {
                    try {
                        // Try to create constructor call with simplified parameters
                        CtConstructorCall<?> constructorCall = createSimpleConstructorCall(constructor, factory, body);
                        if (constructorCall != null) {
                            return constructorCall;
                        }
                    } catch (Exception e) {
                        // Continue to next constructor if this one fails
                        continue;
                    }
                }
            }
        }

        // If no constructor can be created, return null
        return makeTypedNull(factory, type);
    }

    /**
     * Select implementation with the simplest constructor (most primitive
     * parameters, fewest total parameters)
     */
    private static CtTypeReference<?> selectImplementationWithSimplestConstructor(
            List<CtTypeReference<?>> implementations) {
        if (implementations == null || implementations.isEmpty()) {
            return null;
        }

        Map<String, Set<CtConstructor<?>>> constructorsMap = ASTParser.getAll_Constructors_Map();
        CtTypeReference<?> bestImpl = null;
        int maxPrimitiveCount = -1;
        int minParamCount = Integer.MAX_VALUE;

        for (CtTypeReference<?> impl : implementations) {
            Set<CtConstructor<?>> constructors = constructorsMap.get(impl.getQualifiedName());
            if (constructors == null || constructors.isEmpty()) {
                continue;
            }

            for (CtConstructor<?> constructor : constructors) {
                if (!constructor.isPublic()) {
                    continue;
                }

                int primitiveCount = countPrimitiveParameters(constructor);
                int paramCount = constructor.getParameters().size();

                if (primitiveCount > maxPrimitiveCount ||
                        (primitiveCount == maxPrimitiveCount && paramCount < minParamCount)) {
                    bestImpl = impl;
                    maxPrimitiveCount = primitiveCount;
                    minParamCount = paramCount;
                }
            }
        }

        return bestImpl != null ? bestImpl : implementations.get(0);
    }

    /**
     * Count the number of primitive/basic type parameters in a constructor
     */
    private static int countPrimitiveParameters(CtConstructor<?> constructor) {
        int count = 0;
        for (Object param : constructor.getParameters()) {
            if (param instanceof spoon.reflect.declaration.CtParameter) {
                spoon.reflect.declaration.CtParameter<?> ctParam = (spoon.reflect.declaration.CtParameter<?>) param;
                CtTypeReference<?> type = ctParam.getType();
                if (type != null && isPrimitiveOrBasicType(type)) {
                    count++;
                }
            }
        }
        return count;
    }

    /**
     * Check if a type is primitive or basic (String, wrapper types, etc.)
     */
    private static boolean isPrimitiveOrBasicType(CtTypeReference<?> type) {
        String typeName = type.getQualifiedName();
        return type.isPrimitive() ||
                typeName.equals("java.lang.String") ||
                typeName.equals("java.lang.Integer") ||
                typeName.equals("java.lang.Long") ||
                typeName.equals("java.lang.Double") ||
                typeName.equals("java.lang.Float") ||
                typeName.equals("java.lang.Boolean") ||
                typeName.equals("java.lang.Character") ||
                typeName.equals("java.lang.Byte") ||
                typeName.equals("java.lang.Short");
    }

    /**
     * Create a constructor call with minimal complexity for fallback cases
     */
    private static CtConstructorCall<?> createSimpleConstructorCall(CtConstructor<?> constructor, Factory factory,
            CtBlock<?> body) {

        CtTypeReference<?> declaringType = constructor.getDeclaringType().getReference();
        CtConstructorCall<?> constructorCall = createBasicConstructorCall(factory, declaringType);

        List<CtExpression<?>> args = generateArgumentsWithFallback(
                constructor.getParameters(), factory, body, 0, true);

        constructorCall.setArguments(args);
        return constructorCall;
    }

    /**
     * Create simple arguments for constructors with intelligent object creation
     */
    public static CtExpression<?> createSimpleArgument(CtTypeReference<?> paramType, Factory factory) {
        return createSimpleArgumentWithDepth(paramType, factory, 0);
    }

    /**
     * Create arguments with controlled depth to avoid infinite recursion
     */
    public static CtExpression<?> createSimpleArgumentWithDepth(CtTypeReference<?> paramType, Factory factory,
            int depth) {
        if (paramType == null) {
            return factory.createLiteral(null);
        }

        // Prevent deep recursion
        if (depth > 2) {
            return SeedAugmentor.makeTypedNull(factory, paramType);
        }

        // Try primitive default first
        CtExpression<?> primitiveDefault = createPrimitiveDefault(paramType, factory, "dummy", true);
        if (primitiveDefault != null) {
            return primitiveDefault;
        }

        // For complex types, delegate to complex argument creation
        return createComplexArgument(paramType, factory, depth);
    }

    /**
     * Handle complex argument creation with multiple strategies
     */
    private static CtExpression<?> createComplexArgument(CtTypeReference<?> paramType, Factory factory, int depth) {
        String typeName = paramType.getQualifiedName();

        // 0. Handle array types
        if (paramType.isArray()) {
            CtBlock<?> tempBody = factory.createBlock();
            return generateMockUpArrays(paramType, factory, tempBody, depth);
        }

        // 1. Try to get from existing pool first (highest priority)
        CtElement existing = pickRandomPrim(paramType);
        if (existing != null) {
            return (CtExpression<?>) existing;
        }

        // 2. Try to find from collected inputs
        if (baseVarTypeNamePoolAsList != null) {
            // CRITICAL FIX: First try to find exact array type match
            // This prevents wrapping a null_JavaType[] variable in another array
            if (paramType.isArray()) {
                for (Map.Entry<CtTypeReference, List<Pair<CtTypeReference, CtElement>>> entry : baseVarTypeNamePoolAsList
                        .entrySet()) {
                    CtTypeReference<?> poolType = entry.getKey();
                    // Check for exact array type match (including array dimensions)
                    if (isCompatibleType(poolType, paramType)) {
                        List<Pair<CtTypeReference, CtElement>> candidates = entry.getValue();
                        if (!candidates.isEmpty()) {
                            Pair<CtTypeReference, CtElement> candidate = candidates
                                    .get(rand.nextInt(candidates.size()));
                            if (candidate.getValue() instanceof CtVariable) {
                                CtVariable<?> var = (CtVariable<?>) candidate.getValue();
                                CtVariableRead<?> varRead = factory.createVariableRead();
                                varRead.setVariable((CtVariableReference) var.getReference());
                                return varRead; // Return directly - no wrapping needed
                            }
                        }
                    }
                }
            }

            // If exact array match not found, search for element type and wrap
            CtTypeReference<?> searchType = paramType;
            boolean needsArrayWrapping = false;
            if (paramType.isArray()) {
                CtArrayTypeReference<?> arrayType = (CtArrayTypeReference<?>) paramType;
                searchType = arrayType.getComponentType();
                needsArrayWrapping = true;
            }

            for (Map.Entry<CtTypeReference, List<Pair<CtTypeReference, CtElement>>> entry : baseVarTypeNamePoolAsList
                    .entrySet()) {
                CtTypeReference<?> poolType = entry.getKey();
                if (isCompatibleType(poolType, searchType)) {
                    List<Pair<CtTypeReference, CtElement>> candidates = entry.getValue();
                    if (!candidates.isEmpty()) {
                        // Create a variable reference to the pooled object
                        Pair<CtTypeReference, CtElement> candidate = candidates.get(rand.nextInt(candidates.size()));
                        if (candidate.getValue() instanceof CtVariable) {
                            CtVariable<?> var = (CtVariable<?>) candidate.getValue();
                            CtVariableRead<?> varRead = factory.createVariableRead();
                            varRead.setVariable((CtVariableReference) var.getReference());

                            // Wrap in array if needed
                            if (needsArrayWrapping) {
                                // CRITICAL: Check if varRead is already an array type
                                // If so, return it directly without wrapping
                                if (varRead.getType() != null && varRead.getType().isArray()) {
                                    return varRead; // Already an array, no wrapping needed
                                }
                                CtNewArray arrayExpr = factory.createNewArray();
                                arrayExpr.setType((CtTypeReference) paramType);
                                List elements = new ArrayList<>();
                                elements.add(varRead);
                                arrayExpr.setElements(elements);
                                return arrayExpr;
                            }

                            return varRead;
                        }
                    }
                }
            }
        }

        // 3. Try common patterns for known interface types
        CtExpression<?> commonImpl = createCommonImplementation(paramType, factory, depth);
        if (commonImpl != null) {
            return commonImpl;
        }

        // Check if the type can be instantiated (after trying common implementations)
        if (!isInstantiable(paramType)) {
            // Type is abstract or interface, return null
            return makeTypedNull(factory, paramType);
        }

        // 4. Try to create via constructor
        CtExpression<?> constructorCall = tryCreateViaConstructor(paramType, factory, depth);
        if (constructorCall != null) {
            return constructorCall;
        }

        // 5. Try factory methods as last resort
        CtExpression<?> factoryCall = tryCreateViaFactoryMethod(paramType, factory, depth);
        if (factoryCall != null) {
            return factoryCall;
        }

        try {
            Map<String, Set<CtConstructor<?>>> constructorsMap = ASTParser.getAll_Constructors_Map();
            Set<CtConstructor<?>> constructors = constructorsMap.get(typeName);

            if (constructors != null) {
                // Find the simplest constructor - prioritize primitive parameters
                CtConstructor<?> simplestConstructor = null;
                int maxPrimitiveCount = -1;
                int minParams = Integer.MAX_VALUE;

                for (CtConstructor<?> constructor : constructors) {
                    if (constructor.isPublic()) {
                        int primitiveCount = countPrimitiveParameters(constructor);
                        int paramCount = constructor.getParameters().size();

                        if (primitiveCount > maxPrimitiveCount ||
                                (primitiveCount == maxPrimitiveCount && paramCount < minParams)) {
                            simplestConstructor = constructor;
                            maxPrimitiveCount = primitiveCount;
                            minParams = paramCount;
                        }
                    }
                }

                if (simplestConstructor != null && minParams <= 6) { // Allow up to 6 parameters
                    CtConstructorCall<?> call = factory.createConstructorCall();
                    call.setType((CtTypeReference) paramType.clone());

                    List<CtExpression<?>> args = new ArrayList<>();
                    for (CtParameter<?> param : simplestConstructor.getParameters()) {
                        CtTypeReference<?> paramTypeInner = param.getType();

                        // Use a very simple strategy here - just use basic defaults
                        CtExpression<?> arg = createBasicDefault(paramTypeInner, factory);
                        args.add(arg);
                    }

                    call.setArguments(args);
                    return call;
                }
            }
        } catch (Exception e) {
            // Ignore and fall through
        }

        // 8. Final fallback to null
        return SeedAugmentor.makeTypedNull(factory, paramType);
    }

    /**
     * Create primitive default values with configurable string value and complex
     * type handling
     */
    private static CtExpression<?> createPrimitiveDefault(CtTypeReference<?> paramType, Factory factory,
            String stringDefault, boolean handleComplexTypes) {
        if (paramType == null) {
            return factory.createLiteral(null);
        }

        String typeName = paramType.getQualifiedName();

        // Handle primitive types and wrappers
        switch (typeName) {
            case "java.lang.String":
                return factory.createLiteral(stringDefault);
            case "int":
            case "java.lang.Integer":
                return factory.createLiteral(0);
            case "long":
            case "java.lang.Long":
                return factory.createLiteral(0L);
            case "double":
            case "java.lang.Double":
                return factory.createLiteral(0.0);
            case "float":
            case "java.lang.Float":
                return factory.createLiteral(0.0f);
            case "boolean":
            case "java.lang.Boolean":
                return factory.createLiteral(false);
            case "char":
            case "java.lang.Character":
                return factory.createLiteral('a');
            case "short":
            case "java.lang.Short":
                return factory.createLiteral((short) 0);
            case "byte":
            case "java.lang.Byte":
                return factory.createLiteral((byte) 0);
            case "java.lang.Comparable":
                return factory.createLiteral("comparable");
            default:
                return handleComplexTypes ? null : factory.createLiteral(null);
        }
    }

    /**
     * Create very basic default values for force creation
     */
    private static CtExpression<?> createBasicDefault(CtTypeReference<?> paramType, Factory factory) {
        return createPrimitiveDefault(paramType, factory, "default", false);
    }

    public static CtExpression<?> makeTypedNull(Factory factory, CtTypeReference<?> targetType) {
        if (targetType == null || targetType.isPrimitive()) {
            return factory.createLiteral(null);
        }
        CtLiteral<?> nl = factory.createLiteral(null);
        nl.addTypeCast((CtTypeReference) targetType.clone());
        return nl;
    }

    /**
     * Create common implementations for well-known interface types
     */
    // Cache to track already added common implementations to avoid duplicates
    private static Set<String> addedCommonImplementations = new HashSet<>();

    /**
     * Helper method to add generated objects to CandidatePool (with deduplication)
     */
    private static void addToCandidatePool(CtTypeReference<?> actualType, CtExpression<?> expr, Factory factory,
            String varPrefix) {
        try {
            // Create a normalized signature for this expression to check for duplicates
            String normalizedSignature = actualType.getQualifiedName() + "::"
                    + expr.toString().replaceAll("\\s+", " ").trim();

            // Check if this exact object has already been added to the pool
            if (addedCommonImplementations.contains(normalizedSignature)) {
                // System.out.println("[DEBUG POOL SKIP] Skipping duplicate: " +
                // actualType.getSimpleName());
                return;
            }

            String varName = varPrefix + "_" + System.currentTimeMillis() + "_" + dummyVarCounter++;
            CtLocalVariable<?> localVar = factory.createLocalVariable();
            localVar.setSimpleName(varName);
            localVar.setType((CtTypeReference) actualType.clone());
            localVar.setDefaultExpression((CtExpression) expr.clone());

            List<CtElement> sequence = new ArrayList<>();
            sequence.add(localVar);

            Pair<CtTypeReference, CtElement> pair = new Pair<>(actualType, localVar.getReference());
            CandidatePool.insertVarTypeToInputPool(pair, sequence);

            // Mark this signature as processed to avoid duplicates
            addedCommonImplementations.add(normalizedSignature);

            // System.out.println("[DEBUG POOL ADD] Added " + actualType.getSimpleName() + "
            // to CandidatePool with variable: " + varName);
        } catch (Exception e) {
            // Silently fail if adding to pool fails
        }
    }

    private static CtExpression<?> createCommonImplementation(CtTypeReference<?> paramType, Factory factory,
            int depth) {
        String typeName = paramType.getQualifiedName();

        switch (typeName) {
            case "org.apache.commons.jxpath.ri.compiler.NodeTest":
                CtConstructorCall<?> nodeTypeTest = factory.createConstructorCall();
                nodeTypeTest.setType(factory.createReference("org.apache.commons.jxpath.ri.compiler.NodeTypeTest"));
                nodeTypeTest.setArguments(Arrays.asList(factory.createLiteral(1)));
                // System.out.println("[DEBUG NODE TEST] Generated object using NodeTypeTest");

                // Add to CandidatePool for reuse
                CtTypeReference<?> nodeTypeTestRef = factory
                        .createReference("org.apache.commons.jxpath.ri.compiler.NodeTypeTest");
                addToCandidatePool(nodeTypeTestRef, nodeTypeTest, factory, "variant_NodeTypeTest");

                return nodeTypeTest;
            case "java.lang.Comparable":
                return factory.createLiteral("comparable");
            case "java.awt.Paint":
                // Create Color.BLACK as a Paint implementation
                CtConstructorCall<?> colorCall = factory.createConstructorCall();
                colorCall.setType(factory.createTypeReference().setSimpleName("Color"));
                // Color(int r, int g, int b)
                colorCall.setArguments(Arrays.asList(
                        factory.createLiteral(0),
                        factory.createLiteral(0),
                        factory.createLiteral(0)));
                return colorCall;
            case "java.awt.Stroke":
                // Create new BasicStroke()
                CtConstructorCall<?> basicStroke = factory.createConstructorCall();
                basicStroke.setType(factory.createTypeReference().setSimpleName("BasicStroke"));
                return basicStroke;
            case "org.jfree.chart.labels.CategoryItemLabelGenerator":
                CtConstructorCall<?> labelGen = factory.createConstructorCall();
                labelGen.setType(factory.createTypeReference().setSimpleName("StandardCategoryItemLabelGenerator"));
                return labelGen;
            case "org.jfree.chart.labels.CategoryToolTipGenerator":
                CtConstructorCall<?> tooltipGen = factory.createConstructorCall();
                tooltipGen.setType(factory.createTypeReference().setSimpleName("StandardCategoryToolTipGenerator"));
                return tooltipGen;
            case "org.jfree.chart.urls.CategoryURLGenerator":
                CtConstructorCall<?> urlGen = factory.createConstructorCall();
                urlGen.setType(factory.createTypeReference().setSimpleName("StandardCategoryURLGenerator"));
                return urlGen;
            case "org.jfree.chart.axis.ValueAxis":
                CtConstructorCall<?> valueAxis = factory.createConstructorCall();
                valueAxis.setType(factory.createTypeReference().setSimpleName("NumberAxis"));
                valueAxis.setArguments(Arrays.asList(factory.createLiteral("axis")));
                return valueAxis;
            case "org.jfree.chart.plot.Marker":
                CtConstructorCall<?> marker = factory.createConstructorCall();
                marker.setType(factory.createTypeReference().setSimpleName("ValueMarker"));
                marker.setArguments(Arrays.asList(factory.createLiteral(0.0)));
                return marker;
            case "java.util.List":
                CtConstructorCall<?> arrayList = factory.createConstructorCall();
                arrayList.setType(factory.createTypeReference().setSimpleName("ArrayList"));

                // Add to CandidatePool for reuse
                CtTypeReference<?> arrayListRef = factory.createReference("java.util.ArrayList");
                addToCandidatePool(arrayListRef, arrayList, factory, "variant_ArrayList");

                return arrayList;
            case "java.util.Map":
                CtConstructorCall<?> hashMap = factory.createConstructorCall();
                hashMap.setType(factory.createTypeReference().setSimpleName("HashMap"));

                // Add to CandidatePool for reuse
                CtTypeReference<?> hashMapRef = factory.createReference("java.util.HashMap");
                addToCandidatePool(hashMapRef, hashMap, factory, "variant_HashMap");

                return hashMap;
            case "java.util.Set":
                CtConstructorCall<?> hashSet = factory.createConstructorCall();
                hashSet.setType(factory.createTypeReference().setSimpleName("HashSet"));

                // Add to CandidatePool for reuse
                CtTypeReference<?> hashSetRef = factory.createReference("java.util.HashSet");
                addToCandidatePool(hashSetRef, hashSet, factory, "variant_HashSet");

                return hashSet;
            case "java.io.Reader":
                CtConstructorCall<?> stringReaderCall = factory.createConstructorCall();
                stringReaderCall.setType(factory.createTypeReference().setSimpleName("StringReader"));
                stringReaderCall.setArguments(Arrays.asList(factory.createLiteral("")));
                return stringReaderCall;
            case "java.io.InputStream":
                CtConstructorCall<?> byteArrayInputStreamCall = factory.createConstructorCall();
                byteArrayInputStreamCall.setType(factory.createTypeReference().setSimpleName("ByteArrayInputStream"));
                byteArrayInputStreamCall.setArguments(Arrays.asList(factory.createLiteral(new byte[0])));
                return byteArrayInputStreamCall;
            default:
                return null;
        }
    }

    /**
     * Try to create object via constructor
     */
    private static CtExpression<?> tryCreateViaConstructor(CtTypeReference<?> paramType, Factory factory, int depth) {
        // Check if the type can be instantiated
        if (!isInstantiable(paramType)) {
            return null;
        }

        try {
            Map<String, Set<CtConstructor<?>>> constructorsMap = ASTParser.getAll_Constructors_Map();
            Set<CtConstructor<?>> constructors = constructorsMap.get(paramType.getQualifiedName());

            if (constructors != null) {
                // Sort by parameter count (prefer simpler constructors)
                List<CtConstructor<?>> sortedConstructors = new ArrayList<>(constructors);
                sortedConstructors.sort(Comparator.comparingInt(c -> c.getParameters().size()));

                for (CtConstructor<?> constructor : sortedConstructors) {
                    if (constructor.isPublic() && constructor.getParameters().size() <= 3) { // Limit complexity
                        CtConstructorCall<?> call = createBasicConstructorCall(factory, paramType);

                        List<CtExpression<?>> args = generateSimpleArgumentsForParameters(
                                constructor.getParameters(), factory, depth + 1);

                        if (areAllArgumentsValid(args)) {
                            call.setArguments(args);
                            return call;
                        }
                    }
                }
            }
        } catch (Exception e) {
            // Continue to next strategy
        }
        return null;
    }

    /**
     * Try to create object via factory method
     */
    private static CtExpression<?> tryCreateViaFactoryMethod(CtTypeReference<?> paramType, Factory factory, int depth) {
        try {
            HashMap<String, Set<CtMethod<?>>> allMethodsMap = ASTParser.getAllMethods();
            Set<CtMethod<?>> methods = allMethodsMap.get(paramType.getQualifiedName());

            if (methods != null) {
                for (CtMethod<?> method : methods) {
                    if (method.hasModifier(ModifierKind.STATIC) &&
                            method.isPublic() &&
                            isFactoryMethodName(method.getSimpleName()) &&
                            method.getParameters().size() <= 2) { // Limit complexity

                        CtInvocation<?> invocation = factory.createInvocation();
                        invocation.setExecutable((CtExecutableReference) method.getReference());

                        // Set target to the class
                        CtTypeAccess<?> typeAccess = factory.createTypeAccess();
                        typeAccess.setAccessedType((CtTypeReference) method.getDeclaringType().getReference());
                        invocation.setTarget(typeAccess);

                        List<CtExpression<?>> args = new ArrayList<>();
                        boolean canCreate = true;

                        for (CtParameter<?> param : method.getParameters()) {
                            CtExpression<?> arg = createSimpleArgumentWithDepth(param.getType(), factory, depth + 1);
                            if (arg == null) {
                                canCreate = false;
                                break;
                            }
                            args.add(arg);
                        }

                        if (canCreate) {
                            invocation.setArguments(args);
                            return invocation;
                        }
                    }
                }
            }
        } catch (Exception e) {
            // Continue to fallback
        }
        return null;
    }

    // SeedAugmentor.java
    // seqc/SeedAugmentor.java

    private static CtConstructorCall<?> createConstructorCallFromConstructor(CtConstructor<?> constructor,
            Factory factory, CtBlock<?> body, int currentDepth, CtTypeReference<?> typeRef) {
        List<CtExpression<?>> args = new ArrayList<>();
        CtConstructorCall<?> constructorCall = createBasicConstructorCall(factory, typeRef);

        // Register null object for the type being constructed
        registerNullObjectForType(typeRef, factory);

        for (CtParameter<?> param : constructor.getParameters()) {
            CtTypeReference<?> paramType = param.getType();
            // Register null object for each parameter type
            registerNullObjectForType(paramType, factory);

            // Check for hardcoded type preferences FIRST
            CtExpression<?> paramInitExpr = tryGetPreferredTypeForConstructor(typeRef, paramType, factory, body,
                    currentDepth + 1);

            if (paramInitExpr != null && !isNullLiteral(paramInitExpr)) {
                args.add(paramInitExpr);
                continue;
            }

            // CRITICAL FIX: Use a temporary body to collect all prerequisite statements
            // Then add them to the actual body BEFORE using the expression
            CtBlock<?> tempBodyForParam = factory.createBlock();

            paramInitExpr = handleDummyParameterVals(paramType, tempBodyForParam, factory, currentDepth + 1);

            // Add all statements from tempBody to actual body
            // This ensures all variable definitions are included
            List<CtStatement> tempStatements = tempBodyForParam.getStatements();
            tempStatements.forEach(stmt -> body.addStatement(stmt.clone()));

            // ★ 핵심 수정 1: 마지막 statement가 변수 선언이면, 그 변수를 참조하도록 변경
            // 이렇게 하면 inline constructor call을 방지하고 변수를 먼저 선언할 수 있음
            if (!tempStatements.isEmpty()) {
                CtStatement lastStmt = tempStatements.get(tempStatements.size() - 1);
                if (lastStmt instanceof CtLocalVariable) {
                    CtLocalVariable<?> lastVar = (CtLocalVariable<?>) lastStmt;
                    CtVariableRead<Object> varRef = factory.createVariableRead();
                    varRef.setVariable((CtVariableReference<Object>) (CtVariableReference<?>) lastVar.getReference());
                    paramInitExpr = varRef;
                }
            }

            // ★ 핵심 수정 2: 복잡한 expression(Constructor call, Method invocation 등)을 변수로 저장
            // 단계적으로 필요한 타입을 선언하고 참조하도록 함
            if (paramInitExpr != null && !isSimpleExpression(paramInitExpr)) {
                // Handle array types: remove [] from the name
                String typeName = paramType.getSimpleName();
                if (paramType.isArray()) {
                    typeName = paramType.getQualifiedName().replaceAll("\\[\\]", "");
                    typeName = typeName.substring(typeName.lastIndexOf('.') + 1);
                }
                String paramVarName = "param_" + typeName + "_" +
                        System.currentTimeMillis() + "_" + dummyVarCounter++;
                CtLocalVariable<?> paramVar = factory.createLocalVariable();
                paramVar.setSimpleName(paramVarName);
                paramVar.setType((CtTypeReference) paramType.clone());
                // Clone the expression to avoid modifying the original
                paramVar.setDefaultExpression((CtExpression) paramInitExpr.clone());
                body.addStatement(paramVar);

                CtVariableRead<Object> varRef = factory.createVariableRead();
                varRef.setVariable((CtVariableReference<Object>) (CtVariableReference<?>) paramVar.getReference());
                paramInitExpr = varRef;
            }

            // --- START: 안정성 검사 (기존과 동일) ---
            if (paramInitExpr != null && paramInitExpr.getType() != null
                    && !paramInitExpr.getType().isSubtypeOf(paramType)) {
                paramInitExpr = null;
            }
            // --- END: 안정성 검사 ---

            // --- [핵심 수정: 실패 조건 완화 및 간단한 기본값 제공] ---
            if (paramInitExpr == null ||
                    (isNullLiteral(paramInitExpr) && !paramType.getQualifiedName().equals("java.lang.Object"))) {
                // Try to create a simple default value for the parameter
                paramInitExpr = createSimpleArgument(paramType, factory);
                // Don't add yet - need to check if array wrapping is needed
            }
            // --- [수정 끝] ---

            // Check if we need to wrap paramInitExpr in an array
            if (paramType.isArray() && paramInitExpr != null && paramInitExpr.getType() != null) {
                if (paramInitExpr.getType().isArray()) {
                    // Both are arrays - check if they're compatible
                    String paramElementType = paramType.getQualifiedName().replace("[]", "");
                    String exprElementType = paramInitExpr.getType().getQualifiedName().replace("[]", "");

                    if (!paramElementType.equals(exprElementType)) {
                        // Incompatible array types - use null or create correct type
                        paramInitExpr = makeTypedNull(factory, paramType);
                    }
                } else {
                    // paramType is array but expression is not - wrap it if compatible
                    try {
                        CtArrayTypeReference<?> arrayType = (CtArrayTypeReference<?>) paramType;
                        CtTypeReference<?> elementType = arrayType.getComponentType();

                        // Only wrap if types are actually compatible
                        if (isCompatibleType(paramInitExpr.getType(), elementType)) {
                            // Compatible - wrap it
                            CtNewArray arrayExpr = factory.createNewArray();
                            arrayExpr.setType((CtTypeReference) paramType);
                            List elements = new ArrayList<>();
                            elements.add(paramInitExpr);
                            arrayExpr.setElements(elements);
                            paramInitExpr = arrayExpr;
                        } else {
                            // Incompatible - use null instead
                            paramInitExpr = makeTypedNull(factory, paramType);
                        }
                    } catch (Exception e) {
                        paramInitExpr = makeTypedNull(factory, paramType);
                    }
                }
            }

            if (isLiteral(paramType) || usedInputPool) {
                args.add(paramInitExpr);
                usedInputPool = false;
            } else {
                // CRITICAL: Check for generic type variables (T, E, K, V, etc.)
                // Replace with Object to avoid compilation errors
                CtTypeReference<?> actualParamType = paramType;
                if (isTypeVariable(paramType.getQualifiedName())) {
                    actualParamType = factory.Type().objectType();
                }

                String argVarName = "mockUp_" + System.currentTimeMillis() + "_" + dummyVarCounter++;
                CtLocalVariable<?> localVar = factory.createLocalVariable();
                localVar.setSimpleName(argVarName);
                localVar.setType((CtTypeReference) actualParamType.clone());
                localVar.setDefaultExpression((CtExpression) paramInitExpr);
                body.addStatement(localVar);

                CtVariableRead<?> varRead = factory.createVariableRead();
                varRead.setVariable((CtVariableReference) localVar.getReference());
                args.add(varRead);
            }
        }
        constructorCall.setArguments(args);

        return constructorCall;
    }

    private static CtMethod<?> findMatchingMethod(CtTypeReference<?> typeRef, Factory factory) {
        String typeName = typeRef.getQualifiedName();

        // Use cached methods list if available
        List<CtMethod<?>> cachedMethods = allMethodCache.get(typeName);
        if (cachedMethods == null) {
            cachedMethods = buildAllMethodCache(typeRef);
            allMethodCache.put(typeName, cachedMethods);
        }

        if (cachedMethods.isEmpty()) {
            return null;
        }

        // Try factory methods first (they're sorted at the front)
        Random rand = new Random();
        int factoryMethodCount = 0;

        // Count factory methods at the front of the list
        for (CtMethod<?> method : cachedMethods) {
            if (method.hasModifier(ModifierKind.STATIC) &&
                    method.getType() != null &&
                    isFactoryMethodName(method.getSimpleName()) &&
                    isCompatibleTypeCached(method.getType(), typeRef)) {
                factoryMethodCount++;
            } else {
                break; // Factory methods are at the front, so we can break
            }
        }

        // Prefer factory methods (70% chance if available)
        if (factoryMethodCount > 0 && rand.nextDouble() < 0.7) {
            return cachedMethods.get(0); // Return highest priority factory method
        }

        // Fall back to any cached method
        return cachedMethods.get(rand.nextInt(cachedMethods.size()));
    }

    /**
     * Build and cache sorted method list for a type
     */
    private static List<CtMethod<?>> buildAllMethodCache(CtTypeReference<?> typeRef) {
        HashMap<String, Set<CtMethod<?>>> allMethodsMap = ASTParser.getAllMethods();
        Set<CtMethod<?>> methods = allMethodsMap.get(typeRef.getQualifiedName());

        if (methods == null || methods.isEmpty()) {
            return Collections.emptyList();
        }

        List<CtMethod<?>> factoryMethods = new ArrayList<>();
        List<CtMethod<?>> otherMethods = new ArrayList<>();

        String targetPackage = Config.PACKAGE != null ? Config.PACKAGE : "";

        for (CtMethod<?> method : methods) {
            // Must be static and return compatible type for factory methods
            if (method.hasModifier(ModifierKind.STATIC) &&
                    method.getType() != null &&
                    isCompatibleTypeCached(method.getType(), typeRef) &&
                    isFactoryMethodName(method.getSimpleName()) &&
                    isMethodAccessible(method, targetPackage)) {
                factoryMethods.add(method);
            } else if (isMethodAccessible(method, targetPackage)) {
                otherMethods.add(method);
            }
        }

        // Sort factory methods by priority
        factoryMethods.sort((m1, m2) -> {
            int paramDiff = m1.getParameters().size() - m2.getParameters().size();
            if (paramDiff != 0) {
                return paramDiff;
            }

            String name1 = m1.getSimpleName();
            String name2 = m2.getSimpleName();
            int priority1 = getFactoryMethodPriority(name1);
            int priority2 = getFactoryMethodPriority(name2);
            return priority1 - priority2;
        });

        // Combine lists with factory methods first
        List<CtMethod<?>> result = new ArrayList<>(factoryMethods.size() + otherMethods.size());
        result.addAll(factoryMethods);
        result.addAll(otherMethods);

        return result;
    }

    private static CtInvocation<?> createMethodInvo(CtMethod<?> selectedMethod, Factory factory, CtBlock<?> body,
            int currentDepth) {
        CtInvocation<?> methodCall = factory.createInvocation();
        methodCall.setExecutable((CtExecutableReference) selectedMethod.getReference());
        // ... (메소드 상단 Target 설정 로직은 동일) ...
        if (selectedMethod.hasModifier(ModifierKind.STATIC)) {
            CtTypeAccess<?> typeAccess = factory.createTypeAccess();
            typeAccess.setAccessedType((CtTypeReference) selectedMethod.getDeclaringType().getReference());
            methodCall.setTarget(typeAccess);
        } else {
            // non-static 메소드는 receiver 객체가 필요함
            // receiver type이 접근 가능한 생성자를 가지고 있는지 확인
            CtTypeReference<?> receiverType = selectedMethod.getDeclaringType().getReference();
            if (!hasAccessibleConstructor(receiverType)) {
                // receiver를 만들 수 없으면 이 메소드를 포기
                return null;
            }

            CtExpression<?> instance = createDefaultExpressionForType(receiverType,
                    factory, body, currentDepth);

            // instance 생성 실패 시 메소드 포기
            if (instance == null || isNullLiteral(instance)) {
                return null;
            }

            methodCall.setTarget(instance);
        }

        List<CtExpression<?>> args = new ArrayList<>();

        for (CtParameter<?> param : selectedMethod.getParameters()) {
            CtTypeReference<?> paramType = param.getType();
            CtExpression<?> paramInitExpr = handleDummyParameterVals(paramType, body, factory, currentDepth + 1);

            // --- START: 최종 안정성 검사 ---
            if (paramInitExpr != null && paramInitExpr.getType() != null
                    && !paramInitExpr.getType().isSubtypeOf(paramType)) {
                paramInitExpr = null;
            }
            // --- END: 최종 안정성 검사 ---

            if (isLiteral(paramType)) {
                args.add(paramInitExpr);
            } else if (usedInputPool) {
                args.add(paramInitExpr);
                usedInputPool = false;
            } else {
                // paramInitExpr가 null일 경우를 대비한 방어 코드
                if (paramInitExpr == null) {
                    // Try to create a simple default value for the parameter
                    CtExpression<?> simpleDefault = createSimpleArgument(paramType, factory);
                    args.add(simpleDefault);
                    continue;
                }
                String argVarName = "mockUp_" + System.currentTimeMillis() + "_" + dummyVarCounter++;

                CtLocalVariable<?> localVar = factory.createLocalVariable();
                localVar.setSimpleName(argVarName);
                localVar.setType((CtTypeReference) paramType);
                localVar.setDefaultExpression((CtExpression) paramInitExpr);
                body.addStatement(localVar);

                CtVariableRead<?> varRead = factory.createVariableRead();
                varRead.setVariable((CtVariableReference) localVar.getReference());
                args.add(varRead);
            }
        }
        methodCall.setArguments(args);
        return methodCall;
    }

    /**
     * UTILITY FUNCTIONS
     */

    /**
     * Check if a type is accessible from the test package (must be public or same
     * package)
     */
    /**
     * Hardcoded type preferences for specific constructor combinations
     * 
     * Example: When constructing NullPropertyPointer with NodePointer parameter,
     * prefer NullPointer over other NodePointer implementations
     */
    private static CtExpression<?> tryGetPreferredTypeForConstructor(
            CtTypeReference<?> targetType, CtTypeReference<?> paramType, Factory factory, CtBlock<?> body,
            int currentDepth) {

        String targetTypeName = targetType.getQualifiedName();
        String paramTypeName = paramType.getQualifiedName();

        boolean isDebugType = targetTypeName.contains("PropertyPointer") || paramTypeName.contains("PropertyPointer");

        // Hardcoded preference: NullPropertyPointer + NodePointer -> prefer NullPointer
        if (targetTypeName.contains("NullPropertyPointer") &&
                paramTypeName.contains("NodePointer") && !paramTypeName.contains("Property")) {

            String preferredType = "org.apache.commons.jxpath.ri.model.beans.NullPointer";
            CtTypeReference<?> nullPointerRef = factory.Type().createReference(preferredType);

            if (isDebugType || DEBUG_OBJECT_GENERATION) {
            }

            // Try to get NullPointer from pool first
            CtExpression<?> nullPointerExpr = tryGetObjectFromPoolByType(nullPointerRef, factory, body);
            if (nullPointerExpr != null && !isNullLiteral(nullPointerExpr)) {
                return nullPointerExpr;
            }

            // If not in pool, try to create NullPointer
            CtBlock<?> tempBody = factory.createBlock();
            nullPointerExpr = generateConcreteExpr(nullPointerRef, factory, tempBody, currentDepth + 1);
            if (nullPointerExpr != null && !isNullLiteral(nullPointerExpr)) {
                tempBody.getStatements().forEach(stmt -> body.addStatement(stmt.clone()));
                return nullPointerExpr;
            }
        }

        return null;
    }

    /**
     * Try to get object from pool by specific type
     */
    private static CtExpression<?> tryGetObjectFromPoolByType(CtTypeReference<?> targetType, Factory factory,
            CtBlock<?> body) {
        if (baseVarTypeNamePoolAsList == null || baseVarTypeNamePoolAsList.isEmpty()) {
            return null;
        }

        String targetTypeName = targetType.getQualifiedName();

        // Look for exact type match in pool
        for (Map.Entry<CtTypeReference, List<Pair<CtTypeReference, CtElement>>> entry : baseVarTypeNamePoolAsList
                .entrySet()) {
            if (entry.getKey().getQualifiedName().equals(targetTypeName)) {
                List<Pair<CtTypeReference, CtElement>> candidates = entry.getValue();
                if (candidates != null && !candidates.isEmpty()) {
                    Pair<CtTypeReference, CtElement> candidate = candidates.get(0);
                    Set<List<CtElement>> inputPool = baseVartypeToInputPool.get(candidate);

                    if (inputPool != null && !inputPool.isEmpty()) {
                        List<CtElement> sequence = new ArrayList<>(inputPool).get(0);
                        if (!sequence.isEmpty()) {
                            addInputStatementsToBody(sequence, body);
                            CtElement lastElement = sequence.get(sequence.size() - 1);

                            if (lastElement instanceof CtLocalVariable) {
                                return factory.createVariableRead(((CtLocalVariable<?>) lastElement).getReference(),
                                        false);
                            } else if (lastElement instanceof CtAssignment) {
                                CtAssignment<?, ?> assign = (CtAssignment<?, ?>) lastElement;
                                if (assign.getAssigned() instanceof CtVariableWrite) {
                                    CtVariableWrite<?> write = (CtVariableWrite<?>) assign.getAssigned();
                                    return factory.createVariableRead(write.getVariable(), false);
                                }
                            }
                        }
                    }
                }
            }
        }

        return null;
    }

    /**
     * Check if a type is already in the CandidatePool
     */
    private static boolean isTypeAlreadyInPool(CtTypeReference<?> typeRef) {
        if (typeRef == null || baseVarTypeNamePoolAsList == null) {
            return false;
        }

        String typeToCheckName = typeRef.getQualifiedName();

        // Check if this type exists in the pool
        for (Map.Entry<CtTypeReference, List<Pair<CtTypeReference, CtElement>>> entry : baseVarTypeNamePoolAsList
                .entrySet()) {
            if (entry.getKey().getQualifiedName().equals(typeToCheckName)) {
                List<Pair<CtTypeReference, CtElement>> candidates = entry.getValue();
                if (candidates != null && !candidates.isEmpty()) {
                    return true;
                }
            }
        }

        return false;
    }

    /**
     * Get the number of candidates in the pool for a given type
     */
    private static int getPoolCountForType(CtTypeReference<?> typeRef) {
        if (typeRef == null || baseVarTypeNamePoolAsList == null) {
            return 0;
        }

        String typeToCheckName = typeRef.getQualifiedName();

        // Count candidates for this type in the pool
        for (Map.Entry<CtTypeReference, List<Pair<CtTypeReference, CtElement>>> entry : baseVarTypeNamePoolAsList
                .entrySet()) {
            if (entry.getKey().getQualifiedName().equals(typeToCheckName)) {
                List<Pair<CtTypeReference, CtElement>> candidates = entry.getValue();
                if (candidates != null) {
                    return candidates.size();
                }
            }
        }

        return 0;
    }

    private static boolean isTypeAccessible(CtTypeReference<?> typeRef) {
        if (typeRef == null) {
            return false;
        }

        // Get the actual type declaration
        CtType<?> typeDecl = typeRef.getTypeDeclaration();
        if (typeDecl == null) {
            // Can't determine, assume it's accessible (might be from external library)
            return true;
        }

        // Check if the type is public
        if (typeDecl.isPublic()) {
            return true;
        }

        // If not public, check if it's in the same package
        String typePackage = (typeDecl.getPackage() != null)
                ? typeDecl.getPackage().getQualifiedName()
                : "";
        String targetPackage = Config.PACKAGE;

        return typePackage.equals(targetPackage);
    }

    /**
     * Check if a type can be instantiated (not abstract, not interface)
     */
    private static boolean isInstantiable(CtTypeReference<?> typeRef) {
        if (typeRef == null) {
            return false;
        }

        // Interfaces cannot be instantiated
        if (typeRef.isInterface()) {
            return false;
        }

        // Get the actual type declaration
        CtType<?> typeDecl = typeRef.getTypeDeclaration();
        if (typeDecl == null) {
            // Can't determine, assume it's instantiable (might be from external library)
            return true;
        }

        // Abstract classes cannot be instantiated
        if (typeDecl.isAbstract()) {
            return false;
        }

        return true;
    }

    /**
     * Check if a type has at least one accessible constructor
     */
    private static boolean hasAccessibleConstructor(CtTypeReference<?> typeRef) {
        Map<String, Set<CtConstructor<?>>> constructorsMap = ASTParser.getAll_Constructors_Map();
        Set<CtConstructor<?>> constructors = constructorsMap.get(typeRef.getQualifiedName());

        if (constructors == null || constructors.isEmpty()) {
            return false;
        }

        String targetPackage = Config.PACKAGE;
        for (CtConstructor<?> constructor : constructors) {
            String constructorPackage = (constructor.getDeclaringType().getPackage() != null)
                    ? constructor.getDeclaringType().getPackage().getQualifiedName()
                    : "";

            // private이 아니고, public이거나 같은 패키지면 접근 가능
            boolean isAccessible = !constructor.isPrivate()
                    && (constructor.isPublic() || constructorPackage.equals(targetPackage));
            if (isAccessible) {
                return true;
            }
        }

        return false;
    }

    private static CtConstructor<?> findMatchingConstructor(CtTypeReference<?> typeRef, Factory factory) {
        // Retrieve the map of constructors from ASTParser
        Map<String, Set<CtConstructor<?>>> constructorsMap = ASTParser.getAll_Constructors_Map();

        // Get the set of constructors for the exact type using its qualified name
        Set<CtConstructor<?>> constructors = constructorsMap.get(typeRef.getQualifiedName());
        if (constructors == null || constructors.isEmpty()) {
            return null; // No constructors available for this type
        }

        // Filter out private constructors
        String targetPackage = Config.PACKAGE;
        Set<CtConstructor<?>> accessibleConstructors = new HashSet<>();
        for (CtConstructor<?> constructor : constructors) {
            String constructorPackage = (constructor.getDeclaringType().getPackage() != null)
                    ? constructor.getDeclaringType().getPackage().getQualifiedName()
                    : "";

            // private이 아니고, public이거나 같은 패키지면 허용
            boolean isAccessible = !constructor.isPrivate()
                    && (constructor.isPublic() || constructorPackage.equals(targetPackage));
            if (isAccessible) {
                accessibleConstructors.add(constructor);
            }
        }

        // No accessible constructors
        if (accessibleConstructors.isEmpty()) {
            return null;
        }

        // Get or initialize the set of generated constructors for this type
        Set<CtConstructor<?>> generated = generatedConstructors.computeIfAbsent(typeRef, k -> new HashSet<>());

        // Find constructors that haven't been generated yet
        Set<CtConstructor<?>> available = new HashSet<>(accessibleConstructors);
        available.removeAll(generated);

        // Select a constructor - randomly choose from available candidates
        CtConstructor<?> selected;
        List<CtConstructor<?>> candidateList;

        if (!available.isEmpty()) {
            candidateList = new ArrayList<>(available);
        } else {
            candidateList = new ArrayList<>(accessibleConstructors);
        }

        // ★ 랜덤하게 constructor 선택
        // 이전: 정렬된 순서대로 선택 (항상 같은 constructor)
        // 현재: 모든 후보 중에서 무작위로 선택 (다양성 증대)
        int randomIndex = rand.nextInt(candidateList.size());
        selected = candidateList.get(randomIndex);

        // Mark the selected constructor as generated
        generated.add(selected);

        return selected;
    }

    private static CtElement pickRandomPrim(CtTypeReference<?> typeRef) {
        if (isLiteral(typeRef) || typeRef.isArray()) {
            List<CtElement> reusablePrimList = baseDirectToValuesAsList.get(typeRef);

            if (reusablePrimList != null && !reusablePrimList.isEmpty()) {

                List<CtElement> validCandidates = new ArrayList<>();
                for (CtElement prim : reusablePrimList) {
                    boolean allMatch = prim.getReferencedTypes().stream()
                            .allMatch(tmp -> tmp.equals(typeRef));
                    if (allMatch) {
                        validCandidates.add(prim);
                    }
                }

                if (!validCandidates.isEmpty()) {
                    return validCandidates.get(rand.nextInt(validCandidates.size()));
                }
            }
        }
        return null;
    }

    private static boolean isAssignableFrom(CtTypeReference<?> superType, CtTypeReference<?> subType, Factory factory) {
        if (superType.equals(subType)) {
            return true;
        }

        CtType<?> subTypeDecl = subType.getTypeDeclaration();
        if (subTypeDecl == null) {
            return false; // 선언이 없으면 확인 불가
        }

        // 상위 클래스 확인
        CtTypeReference<?> superClass = subTypeDecl.getSuperclass();
        while (superClass != null) {
            if (superClass.equals(superType)) {
                return true;
            }
            superClass = superClass.getTypeDeclaration() != null ? superClass.getTypeDeclaration().getSuperclass()
                    : null;
        }

        // 인터페이스 확인
        Set<CtTypeReference<?>> interfaces = subTypeDecl.getSuperInterfaces();
        for (CtTypeReference<?> iface : interfaces) {
            if (iface.equals(superType) || isAssignableFrom(superType, iface, factory)) {
                return true;
            }
        }

        return false;
    }

    private static void addInputStatementsToBody(List<CtElement> input, CtBlock<?> body) {
        if (input == null || input.isEmpty()) {
            return;
        }

        // CRITICAL FIX: Clone ALL statements as a group to maintain variable
        // relationships
        // Problem: If we clone individually, variable references become orphaned from
        // their definitions
        // Solution: Create all statements first, establishing their variable scope
        // context,
        // then clone them together so references are properly preserved

        List<CtStatement> statementsToAdd = new ArrayList<>();

        // First: Collect all statements
        for (CtElement element : input) {
            if (element instanceof CtStatement) {
                statementsToAdd.add((CtStatement) element);
            }
        }

        // Second: Add ALL statements to target body
        // By adding them all at once, the clone() preserves internal variable
        // references
        for (CtStatement stmt : statementsToAdd) {
            // IMPORTANT: Use clone() to create independent copy
            // This preserves variable references WITHIN the cloned statement tree
            CtStatement clonedStmt = stmt.clone();
            body.addStatement(clonedStmt);
        }
    }

    private static boolean isAbstractClass(CtTypeReference<?> typeRef) {
        return typeRef.getTypeDeclaration() != null && typeRef.getTypeDeclaration().isAbstract();
    }

    private static boolean isLiteral(CtTypeReference<?> type) {
        if (type.isPrimitive() || type.getQualifiedName().equals("java.lang.String"))
            return true;
        return false;
    }

    private static boolean isStatic(CtMethod<?> method) {
        return method.getModifiers().contains(ModifierKind.STATIC);
    }

    private static boolean isTypeVariable(String typeName) {
        if (typeName == null || typeName.isEmpty()) {
            return false;
        }

        // Single uppercase letter (T, E, K, V, etc.)
        if (typeName.length() == 1 && Character.isUpperCase(typeName.charAt(0))) {
            return true;
        }

        // Type variable patterns
        if (typeName.contains("TypeVariable") || typeName.startsWith("? ")) {
            return true;
        }

        return false;
    }

    /**
     * Helper method to check if an expression is a null literal
     */
    private static boolean isNullLiteral(CtExpression<?> expr) {
        return expr instanceof CtLiteral && ((CtLiteral<?>) expr).getValue() == null;
    }

    /**
     * Helper method to check if an expression is valid (not null and not a null
     * literal)
     */
    private static boolean isValidNonNullExpression(CtExpression<?> expr) {
        return expr != null && !isNullLiteral(expr) && !isConstructorWithAllNullArgs(expr);
    }

    /**
     * Check if expression is simple enough to be used inline (without creating a
     * variable)
     * Simple expressions: literals, variable reads, typed null casts
     * Complex expressions: constructor calls, method invocations, array creations
     * (need variables)
     */
    private static boolean isSimpleExpression(CtExpression<?> expr) {
        if (expr == null) {
            return true; // null is simple
        }

        // Simple expressions that can be used inline
        if (expr instanceof CtLiteral) {
            return true; // Literals: 0, "string", null, etc.
        }
        if (expr instanceof CtVariableRead) {
            return true; // Already a variable reference
        }
        if (expr instanceof CtFieldRead) {
            return true; // Field access is simple
        }

        // Typed null cast like ((Type) null) is considered simple
        if (isNullLiteral(expr)) {
            return true;
        }

        // Complex expressions that should be stored in variables
        if (expr instanceof CtConstructorCall) {
            return false; // Constructor calls should be in variables
        }
        if (expr instanceof CtInvocation) {
            return false; // Method invocations should be in variables
        }
        if (expr instanceof CtNewArray) {
            return false; // Array creations should be in variables
        }

        // Default: consider it complex to be safe
        return false;
    }

    /**
     * Check if expression is a constructor call with all arguments being null
     * literals
     */
    private static boolean isConstructorWithAllNullArgs(CtExpression<?> expr) {
        if (!(expr instanceof CtConstructorCall)) {
            return false;
        }

        CtConstructorCall<?> constructorCall = (CtConstructorCall<?>) expr;
        List<CtExpression<?>> args = constructorCall.getArguments();

        // If no arguments, it's not "all null"
        if (args == null || args.isEmpty()) {
            return false;
        }

        // Check if ALL arguments are null literals (cast or not)
        for (CtExpression<?> arg : args) {
            if (!isNullOrCastedNull(arg)) {
                return false;
            }
        }

        return true;
    }

    /**
     * Check if expression is null or a casted null like ((Type) (null))
     */
    private static boolean isNullOrCastedNull(CtExpression<?> expr) {
        if (expr == null) {
            return true;
        }

        // Direct null literal
        if (isNullLiteral(expr)) {
            return true;
        }

        // Check for type cast with null value
        // Pattern: ((Type) (null)) or ((Type) null)
        String exprStr = expr.toString().trim();

        // More precise pattern: starts with (( and contains null
        // This checks if the entire expression is a casted null, not just contains null
        // somewhere
        if (exprStr.startsWith("((") && exprStr.endsWith("))")) {
            // Extract the content between outer parentheses
            String content = exprStr.substring(2, exprStr.length() - 2).trim();

            // Check if it's a type cast: (Type) (null) or (Type) null
            if (content.matches(".*\\)\\s*\\(?\\s*null\\s*\\)?$")) {
                return true;
            }
        }

        // Also check simpler pattern: (Type) null without extra parentheses
        if (exprStr.matches("\\(.*\\)\\s*null")) {
            return true;
        }

        return false;
    }

    /**
     * Helper method to normalize type name for variable naming
     */
    private static String normalizeTypeNameForVariable(CtTypeReference<?> type) {
        return type.getSimpleName().toLowerCase().replace("[", "").replace("]", "");
    }

    /**
     * Create a basic constructor call with type set
     */
    private static CtConstructorCall<?> createBasicConstructorCall(Factory factory, CtTypeReference<?> type) {
        CtConstructorCall<?> constructorCall = factory.createConstructorCall();
        constructorCall.setType((CtTypeReference) type.clone());
        return constructorCall;
    }

    /**
     * Generate arguments for constructor/method parameters with fallback handling
     */
    private static List<CtExpression<?>> generateArgumentsWithFallback(List<CtParameter<?>> parameters,
            Factory factory, CtBlock<?> body, int currentDepth, boolean useSimpleFallback) {

        List<CtExpression<?>> args = new ArrayList<>();

        for (CtParameter<?> param : parameters) {
            CtTypeReference<?> paramType = param.getType();
            CtExpression<?> argExpr = null;

            if (useSimpleFallback) {
                argExpr = createSimpleArgument(paramType, factory);
            } else {
                argExpr = handleDummyParameterVals(paramType, body, factory, currentDepth + 1);

                // Type safety check
                if (argExpr != null && argExpr.getType() != null
                        && !argExpr.getType().isSubtypeOf(paramType)) {
                    argExpr = null;
                }

                // Fallback for failed arguments
                if (argExpr == null ||
                        (isNullLiteral(argExpr) && !paramType.getQualifiedName().equals("java.lang.Object"))) {
                    argExpr = createSimpleArgument(paramType, factory);
                }
            }

            args.add(argExpr);
        }

        return args;
    }

    /**
     * Check if all arguments in list are valid (non-null, non-null-literal)
     */
    private static boolean areAllArgumentsValid(List<CtExpression<?>> args) {
        return args.stream().allMatch(arg -> isValidNonNullExpression(arg));
    }

    /**
     * Generate simple arguments for parameters with depth control
     */
    private static List<CtExpression<?>> generateSimpleArgumentsForParameters(List<CtParameter<?>> parameters,
            Factory factory, int depth) {
        List<CtExpression<?>> args = new ArrayList<>();

        for (CtParameter<?> param : parameters) {
            CtExpression<?> arg = createSimpleArgumentWithDepth(param.getType(), factory, depth);
            args.add(arg);
        }

        return args;
    }

    /**
     * SETUP FUNCTIONS
     */

    private static List<String> findOutNeglectedMUTS() {
        List<String> ret = new ArrayList<>();
        Set<String> CUT_PublicMethods = ASTParser.getCUT_PublicMethods();
        List<String> baseMUTSignatures = getBaseMUTSignature();

        if (CUT_PublicMethods.isEmpty()) {
            return ret;
        }
        Set<String> baseMUTSet = new HashSet<>(baseMUTSignatures);
        // System.out.println("Size of Base MUT SET : " + baseMUTSet.size());
        for (String CUT_PublicMethod : CUT_PublicMethods) {
            // System.out.println("AUG SIG :" + CUT_PublicMethod);
            if (!baseMUTSet.contains(CUT_PublicMethod)) {
                ret.add(CUT_PublicMethod);
            }
        }
        return ret;
    }

    private static List<String> getBaseMUTSignature() {
        Set<MUTInput> temp = InputCombinations.getMuts();
        if (temp == null) {
            return new ArrayList<>();
        }
        List<String> baseMUTSignatures = new ArrayList<>();
        for (MUTInput mut : temp) {
            // System.out.println("MUT SIG : " + mut.getMethodSignature());
            baseMUTSignatures.add(mut.getMethodSignature());
        }
        return baseMUTSignatures;
    }

    // =================================================================
    // RETRY FAILED MUTs AND NULL OBJECT GENERATION METHODS
    // =================================================================

    /**
     * Retry failed MUTs with seed augmentation by generating dummy test methods for
     * specific types
     */
    public static void retryFailedMUTsWithSeedAugmentation(InputCombinations inputCombinations) throws Exception {
        Set<InputCombinations.FailedMUT> failedMUTs = inputCombinations.getFailedMUTs();

        if (failedMUTs.isEmpty()) {
            return;
        }

        int maxRetryAttempts = 2;

        for (int attempt = 1; attempt <= maxRetryAttempts; attempt++) {
            Set<InputCombinations.FailedMUT> currentBatchFailures = new HashSet<>(failedMUTs);
            failedMUTs.clear(); // Clear for this attempt

            if (currentBatchFailures.isEmpty()) {
                break; // No more failed MUTs to retry
            }

            // Generate dummy test methods for the specific failed types
            generateDummyTestsForFailedTypes(currentBatchFailures);

            // Reprocess the failed MUTs
            Set<MUTInput> newMUTs = inputCombinations.retryFailedMUTs(currentBatchFailures);

            if (newMUTs != null && !newMUTs.isEmpty()) {
                inputCombinations.addMUTs(newMUTs);
            }

            // If no more failures in this attempt, break
            if (failedMUTs.isEmpty()) {
                break;
            }
        }

        if (!failedMUTs.isEmpty()) {
            System.out.println("[WARN] " + failedMUTs.size() + " MUTs could not be recovered after " + maxRetryAttempts
                    + " attempts.");
        }
    }

    /**
     * Generate dummy test methods specifically for the failed types - one
     * constructor per test
     */
    private static void generateDummyTestsForFailedTypes(Set<InputCombinations.FailedMUT> currentFailures)
            throws Exception {
        if (factory == null) {
            factory = new Launcher().getFactory();
        }

        List<CtMethod<?>> generatedDummyMethods = new ArrayList<>();

        // Track processed constructor signatures to avoid duplicates
        Set<String> processedConstructorSignatures = new HashSet<>();

        // Group failed MUTs by their failed types
        Map<String, List<InputCombinations.FailedMUT>> failuresByType = new HashMap<>();
        for (InputCombinations.FailedMUT failure : currentFailures) {
            String typeName = failure.getFailedType().getQualifiedName();
            failuresByType.computeIfAbsent(typeName, k -> new ArrayList<>()).add(failure);
        }

        for (Map.Entry<String, List<InputCombinations.FailedMUT>> entry : failuresByType.entrySet()) {
            String typeName = entry.getKey();
            List<InputCombinations.FailedMUT> failuresForType = entry.getValue();
            CtTypeReference<?> targetType = failuresForType.get(0).getFailedType();

            // Skip if variants were already generated for this type
            if (variantsGeneratedTypes.contains(typeName)) {
                System.out.println("[INFO] Skipping retry for " + typeName + " - variants already generated");
                continue;
            }

            // Generate separate tests for each constructor of this type
            List<CtMethod<?>> constructorTests = generateOneTestPerConstructor(factory, targetType,
                    processedConstructorSignatures);
            generatedDummyMethods.addAll(constructorTests);

            // Also generate tests for concrete implementations if this is an abstract type
            List<CtTypeReference<?>> implementations = ASTParser.abstractToImplsMap.get(typeName);
            if (implementations != null && !implementations.isEmpty()) {
                // Don't generate implementation tests if we already have variants for this
                // abstract type
                System.out.println("[INFO] Skipping implementation tests for " + typeName
                        + " - trying direct constructor tests only");
            }
        }

        // Parse the generated dummy methods to populate the input pools
        for (CtMethod<?> dummyMethod : generatedDummyMethods) {
            try {
                ASTParser.processDummyVartypeTovarnames(dummyMethod);
            } catch (Exception e) {
                System.err.println("[ERROR] Failed to parse dummy test method: " + dummyMethod.getSimpleName());
                // e.printStackTrace();
            }
        }

        // System.out.println("[INFO] Generated " + generatedDummyMethods.size() + "
        // dummy tests (one constructor per test)");
    }

    /**
     * Generate separate dummy test methods - one per constructor for the specified
     * type
     */
    private static List<CtMethod<?>> generateOneTestPerConstructor(Factory factory, CtTypeReference<?> targetType,
            Set<String> processedSignatures) {
        List<CtMethod<?>> constructorTests = new ArrayList<>();

        try {
            // Try default constructor first
            String defaultConstructorSig = targetType.getQualifiedName() + "()";
            if (!processedSignatures.contains(defaultConstructorSig)) {
                CtMethod<?> defaultConstructorTest = createSingleConstructorTest(factory, targetType, null, "default");
                if (defaultConstructorTest != null) {
                    constructorTests.add(defaultConstructorTest);
                    processedSignatures.add(defaultConstructorSig);
                }
            }

            // Get all available constructors for this type
            Map<String, Set<CtConstructor<?>>> constructorsMap = ASTParser.getAll_Constructors_Map();
            Set<CtConstructor<?>> constructors = constructorsMap.get(targetType.getQualifiedName());

            if (constructors != null && !constructors.isEmpty()) {
                // Sort constructors by parameter count to try simpler ones first
                List<CtConstructor<?>> sortedConstructors = new ArrayList<>(constructors);
                sortedConstructors.sort(Comparator.comparingInt(c -> c.getParameters().size()));

                int constructorIndex = 0;
                for (CtConstructor<?> constructor : sortedConstructors) {
                    // Create constructor signature
                    StringBuilder sigBuilder = new StringBuilder(targetType.getQualifiedName() + "(");
                    for (int i = 0; i < constructor.getParameters().size(); i++) {
                        if (i > 0)
                            sigBuilder.append(",");
                        sigBuilder.append(constructor.getParameters().get(i).getType().getQualifiedName());
                    }
                    sigBuilder.append(")");
                    String constructorSig = sigBuilder.toString();

                    // Skip if we've already processed this constructor signature
                    if (!processedSignatures.contains(constructorSig)) {
                        CtMethod<?> constructorTest = createSingleConstructorTest(factory, targetType, constructor,
                                "constructor" + constructorIndex);
                        if (constructorTest != null) {
                            constructorTests.add(constructorTest);
                            processedSignatures.add(constructorSig);
                            constructorIndex++;
                        }
                    }
                }
            }

        } catch (Exception e) {
            System.err
                    .println("[ERROR] Failed to generate constructor tests for type: " + targetType.getQualifiedName());
            // e.printStackTrace();
        }

        return constructorTests;
    }

    /**
     * Create a single dummy test method using one specific constructor
     */
    private static CtMethod<?> createSingleConstructorTest(Factory factory, CtTypeReference<?> targetType,
            CtConstructor<?> constructor, String constructorType) {
        try {
            CtMethod<Void> dummyTestMethod = factory.createMethod();
            dummyTestMethod.setSimpleName("dummyTest" + targetType.getSimpleName() + "_" + constructorType + "_"
                    + System.currentTimeMillis());
            dummyTestMethod.setType(factory.Type().createReference(void.class));
            CtBlock<?> body = factory.createBlock();
            dummyTestMethod.setBody(body);

            // Create one instance using the specific constructor
            createSingleInstanceWithConstructor(factory, body, targetType, constructor);
            return dummyTestMethod;
        } catch (Exception e) {
            System.err
                    .println("[ERROR] Failed to create single constructor test for: " + targetType.getQualifiedName());
            return null;
        }
    }

    /**
     * Create a single instance using a specific constructor
     */
    private static void createSingleInstanceWithConstructor(Factory factory, CtBlock<?> body,
            CtTypeReference<?> targetType, CtConstructor<?> constructor) {
        // Check if the type can be instantiated
        if (!isInstantiable(targetType)) {
            System.err.println("[ERROR] Cannot instantiate abstract type: " + targetType.getQualifiedName());
            return;
        }

        try {
            // Try factory method first
            CtInvocation<?> factoryCall = tryCreateFromFactoryMethod(targetType, factory, body, 0);
            if (factoryCall != null) {
                // Create var for the factory result
                String typeSimpleName = normalizeTypeNameForVariable(targetType);
                String varName = typeSimpleName + "_" + System.nanoTime() + "_" + (int) (Math.random() * 1000);
                CtLocalVariable<?> var = factory.createLocalVariable();
                var.setSimpleName(varName);
                var.setType((CtTypeReference) targetType.clone());
                var.setDefaultExpression((CtExpression) factoryCall);
                body.addStatement(var);
                return;
            }

            // Fallback to constructor
            CtConstructorCall<?> constructorCall = factory.createConstructorCall();
            constructorCall.setType((CtTypeReference) targetType.clone());

            // If no specific constructor, try default
            if (constructor == null) {
                constructorCall.setArguments(new ArrayList<>());
            } else {
                // Generate args using enhanced method
                List<CtExpression<?>> args = new ArrayList<>();
                for (CtParameter<?> param : constructor.getParameters()) {
                    CtExpression<?> argExpr = createDefaultExpressionForType(param.getType(), factory, body, 0);
                    // Type compatibility check
                    if (argExpr != null && argExpr.getType() != null &&
                            isCompatibleTypeCached(argExpr.getType(), param.getType())) {
                        args.add(argExpr);
                    } else {
                        // If incompatible, fallback to null or simple arg
                        args.add(createSimpleArgument(param.getType(), factory));
                    }
                }
                constructorCall.setArguments(args);
            }

            // Create var for the constructor result
            String typeSimpleName = normalizeTypeNameForVariable(targetType);
            String varName = typeSimpleName + "_" + System.nanoTime() + "_" + (int) (Math.random() * 1000);
            CtLocalVariable<?> var = factory.createLocalVariable();
            var.setSimpleName(varName);
            var.setType((CtTypeReference) targetType.clone());
            var.setDefaultExpression((CtExpression) constructorCall);
            body.addStatement(var);

        } catch (Exception e) {
            System.err.println(
                    "[ERROR] Failed to create instance with constructor for: " + targetType.getQualifiedName());
        }
    }

    /**
     * Add null objects to the input pool for all types required by Public+Protected
     * APIs
     */
    public static void addNullObjectsForPublicAPITypes() {
        try {
            HashMap<String, CtMethod<?>> publicAPIs = ASTParser.getCUT_PublicMethods_Map();
            Set<CtTypeReference<?>> requiredTypes = new HashSet<>();

            // Collect all types required by Public+Protected APIs
            for (CtMethod<?> method : publicAPIs.values()) {
                boolean isStatic = method.getModifiers().contains(spoon.reflect.declaration.ModifierKind.STATIC);

                // Add receiver type for non-static methods
                if (!isStatic) {
                    requiredTypes.add(method.getDeclaringType().getReference());
                }

                // Add parameter types
                for (CtParameter<?> param : method.getParameters()) {
                    CtTypeReference<?> paramType = param.getType();
                    if (paramType != null && !paramType.isPrimitive()) {
                        requiredTypes.add(paramType);
                    }
                }
            }

            // System.out.println("[INFO] Adding null objects for " + requiredTypes.size() +
            // " types required by Public APIs");

            if (factory == null) {
                factory = new Launcher().getFactory();
            }
            int nullObjectsAdded = 0;

            for (CtTypeReference<?> type : requiredTypes) {
                // Skip java.lang.Class - it's handled via DirectToValues with class literals
                if ("java.lang.Class".equals(type.getQualifiedName())) {
                    continue;
                }

                // Check if we already have a null object for this type using normalized
                // declaration approach
                String nullObjectSignature = createNullObjectSignature(type);
                if (CandidatePool.isDeclarationProcessed(type, nullObjectSignature)) {
                    continue;
                }

                // Try to create actual object via constructor instead of null
                List<CtElement> objectSequence = tryCreateActualObjectSequence(type, factory);

                if (objectSequence != null && !objectSequence.isEmpty()) {
                    // Successfully created actual object with complete sequence
                    CtLocalVariable<?> objectVar = (CtLocalVariable<?>) objectSequence.get(objectSequence.size() - 1);
                    CtElement varNameElement = objectVar.getReference();

                    Pair<CtTypeReference, CtElement> typeAndName = new Pair<>(type, varNameElement);
                    boolean inserted = CandidatePool.insertVarTypeToInputPool(typeAndName, objectSequence);

                    if (inserted) {
                        CandidatePool.addProcessedDeclaration(type, nullObjectSignature);
                        nullObjectsAdded++;
                    }

                    // After successful constructor creation, also add a null object (separate from
                    // the 3 variants)
                    if (!hasNullObjectInPool(type)) {
                        String nullVarName = generateNullVarName(type);
                        CtLocalVariable<?> nullVar = factory.createLocalVariable();
                        nullVar.setSimpleName(nullVarName);
                        nullVar.setType((CtTypeReference) type.clone());
                        nullVar.setDefaultExpression(factory.createLiteral(null));

                        // Insert null object into CandidatePool
                        CtElement nullVarNameElement = nullVar.getReference();
                        List<CtElement> nullStmts = new ArrayList<>();
                        nullStmts.add(nullVar);

                        Pair<CtTypeReference, CtElement> nullTypeAndName = new Pair<>(type, nullVarNameElement);
                        boolean nullInserted = CandidatePool.insertVarTypeToInputPool(nullTypeAndName, nullStmts);

                        if (nullInserted) {
                            nullObjectsAdded++;
                        }
                    }
                } else {
                    // Fallback to null object if constructor creation fails
                    String varName = generateNullVarName(type);
                    CtLocalVariable<?> nullVar = factory.createLocalVariable();
                    nullVar.setSimpleName(varName);
                    nullVar.setType((CtTypeReference) type.clone());
                    nullVar.setDefaultExpression(factory.createLiteral(null));

                    // Insert into CandidatePool
                    CtElement varNameElement = nullVar.getReference();
                    List<CtElement> stmts = new ArrayList<>();
                    stmts.add(nullVar);

                    Pair<CtTypeReference, CtElement> typeAndName = new Pair<>(type, varNameElement);
                    boolean inserted = CandidatePool.insertVarTypeToInputPool(typeAndName, stmts);

                    if (inserted) {
                        CandidatePool.addProcessedDeclaration(type, nullObjectSignature);
                        nullObjectsAdded++;
                    }
                }
            }

            // System.out.println("[INFO] Successfully added " + nullObjectsAdded + " null
            // objects to the input pool");

        } catch (Exception e) {
            System.err.println("[ERROR] Failed to add null objects for Public API types: " + e.getMessage());
            // e.printStackTrace();
        }
    }

    /**
     * Generate a unique variable name for null object
     */
    private static String generateNullVarName(CtTypeReference<?> type) {
        String typeSimpleName = normalizeTypeNameForVariable(type);
        long timestamp = System.nanoTime();
        int random = (int) (Math.random() * 1000);
        return "null_" + typeSimpleName + "_" + timestamp + "_" + random;
    }

    /**
     * Create a normalized signature for null objects to prevent duplicates
     * Similar to ASTParser.normalizeDeclaration but specifically for null objects
     */
    private static String createNullObjectSignature(CtTypeReference<?> type) {
        return type.getQualifiedName() + " <VAR> = null";
    }

    /**
     * Try to create an actual object via constructor with complete sequence
     * Returns a list containing all necessary statements including parameter
     * declarations
     */
    private static List<CtElement> tryCreateActualObjectSequence(CtTypeReference<?> type, Factory factory) {
        try {

            // Create a temporary body for constructor creation
            CtBlock<?> tempBody = factory.createBlock();

            // Try to create object via constructor - this will populate tempBody with
            // necessary statements
            CtExpression<?> constructorExpr = generateConcreteExpr(type, factory, tempBody, 0);

            if (constructorExpr != null && !isNullLiteral(constructorExpr)) {
                // Successfully created a non-null object
                String varName = generateActualVarName(type);
                CtLocalVariable<?> objectVar = factory.createLocalVariable();
                objectVar.setSimpleName(varName);
                objectVar.setType((CtTypeReference) type.clone());
                objectVar.setDefaultExpression((CtExpression) constructorExpr);

                // Create the complete sequence: all prerequisite statements + final variable
                // declaration
                List<CtElement> sequence = new ArrayList<>();

                // Add all statements from tempBody (these are the prerequisite variable
                // declarations)
                // Must clone to avoid reference issues when inserting into different contexts
                for (CtStatement stmt : tempBody.getStatements()) {
                    sequence.add(stmt.clone());
                }

                // Add the final object variable declaration
                // CRITICAL: Must clone to preserve variable references when used in different
                // contexts
                sequence.add(objectVar.clone());

                return sequence;
            }
        } catch (Exception e) {
            // Constructor creation failed, will fallback to null
        }

        return null; // Failed to create actual object
    }

    /**
     * Generate variable name for actual object (not null)
     */
    private static String generateActualVarName(CtTypeReference<?> type) {
        String typeSimpleName = normalizeTypeNameForVariable(type);
        return typeSimpleName.toLowerCase() + "_" + System.nanoTime() + "_" + (int) (Math.random() * 1000);
    }

    /**
     * Check if the pool already has a null object for the given type
     * Uses cache for fast lookup
     */
    private static boolean hasNullObjectInPool(CtTypeReference<?> type) {
        if (type == null) {
            return false;
        }

        // Fast cache check first
        String typeName = type.getQualifiedName();
        if (nullObjectsRegisteredTypes.contains(typeName)) {
            return true;
        }

        // Check in baseVarTypeNamePoolAsList (initialization snapshot) for pre-existing
        // null objects
        if (baseVarTypeNamePoolAsList != null) {
            for (Map.Entry<CtTypeReference, List<Pair<CtTypeReference, CtElement>>> entry : baseVarTypeNamePoolAsList
                    .entrySet()) {
                CtTypeReference<?> poolType = entry.getKey();
                if (isCompatibleType(poolType, type)) {
                    List<Pair<CtTypeReference, CtElement>> candidates = entry.getValue();

                    // Check if any candidate in the pool is a null object
                    for (Pair<CtTypeReference, CtElement> candidate : candidates) {
                        Set<List<CtElement>> sequences = baseVartypeToInputPool.get(candidate);
                        if (sequences != null) {
                            for (List<CtElement> sequence : sequences) {
                                if (!sequence.isEmpty()) {
                                    CtElement lastElement = sequence.get(sequence.size() - 1);
                                    if (lastElement instanceof CtLocalVariable<?>) {
                                        CtLocalVariable<?> var = (CtLocalVariable<?>) lastElement;
                                        CtExpression<?> defaultExpr = var.getDefaultExpression();

                                        // If the variable is initialized with null, it's a null object
                                        if (defaultExpr != null && isNullLiteral(defaultExpr)) {
                                            // Update cache
                                            nullObjectsRegisteredTypes.add(typeName);
                                            return true;
                                        }
                                    }
                                }
                            }
                        }
                    }
                    break; // Found the type, no need to continue
                }
            }
        }
        return false; // No null object found for this type
    }

    /**
     * Register a null object for the given type in CandidatePool if it doesn't
     * already exist
     * This is called during object creation to ensure null variants are available
     * for all types
     * 
     * @param typeRef The type to register a null object for
     * @param factory Spoon factory for creating elements
     */
    private static void registerNullObjectForType(CtTypeReference<?> typeRef, Factory factory) {
        createAndRegisterNullObject(typeRef, factory);
    }

    /**
     * Augment String values in the direct pool with variations
     * Only targets short strings (length <= 3) and randomly selects up to 10
     */
    public static void augmentStringDirectPool() {
        try {
            HashMap<CtTypeReference, Set<CtElement>> directToValues = CandidatePool.getDirectToValues();

            if (factory == null) {
                factory = new Launcher().getFactory();
            }

            int maxStringsToMutate = 10;
            int stringVariationsAdded = 0;

            // Find String type reference
            CtTypeReference<?> stringType = null;
            for (CtTypeReference<?> type : directToValues.keySet()) {
                if ("java.lang.String".equals(type.getQualifiedName())) {
                    stringType = type;
                    break;
                }
            }

            if (stringType == null) {
                // System.out.println("[INFO] No String values found in direct pool for
                // augmentation");
                return;
            }

            Set<CtElement> stringValues = directToValues.get(stringType);

            // Filter strings: prefer short strings (length <= 3), fallback to any strings
            List<CtElement> shortStringCandidates = new ArrayList<>();
            List<CtElement> allStringCandidates = new ArrayList<>();

            for (CtElement element : stringValues) {
                if (element instanceof CtLiteral<?>) {
                    CtLiteral<?> literal = (CtLiteral<?>) element;
                    Object value = literal.getValue();

                    if (value instanceof String && value != null && !((String) value).isEmpty()) {
                        String str = (String) value;
                        allStringCandidates.add(element);
                        if (str.length() <= 3) {
                            shortStringCandidates.add(element);
                        }
                    }
                }
            }

            // Select candidates: prefer short strings, fallback to any strings
            List<CtElement> selectedCandidates;
            int stringsToProcess;

            if (!shortStringCandidates.isEmpty()) {
                Collections.shuffle(shortStringCandidates);
                stringsToProcess = Math.min(maxStringsToMutate, shortStringCandidates.size());
                selectedCandidates = shortStringCandidates.subList(0, stringsToProcess);
                // System.out.println("[INFO] Found " + shortStringCandidates.size() + " short
                // strings (≤3 chars), randomly selected " + stringsToProcess + " for
                // augmentation");
            } else if (!allStringCandidates.isEmpty()) {
                Collections.shuffle(allStringCandidates);
                stringsToProcess = Math.min(maxStringsToMutate, allStringCandidates.size());
                selectedCandidates = allStringCandidates.subList(0, stringsToProcess);
                // System.out.println("[INFO] No short strings found, randomly selected " +
                // stringsToProcess + " from " + allStringCandidates.size() + " total strings
                // for augmentation");
            } else {
                // System.out.println("[INFO] No non-empty strings found for augmentation");
                return;
            }

            Set<CtElement> newVariations = new HashSet<>();

            for (CtElement element : selectedCandidates) {
                if (element instanceof CtLiteral<?>) {
                    CtLiteral<?> literal = (CtLiteral<?>) element;
                    Object value = literal.getValue();

                    if (value instanceof String) {
                        String originalString = (String) value;
                        List<String> variations = generateStringVariations(originalString);

                        for (String variation : variations) {
                            CtLiteral<String> newLiteral = factory.createLiteral(variation);
                            newVariations.add(newLiteral);
                            stringVariationsAdded++;
                        }
                    }
                }
            }

            // Add common boundary values
            newVariations.add(factory.createLiteral("0"));
            newVariations.add(factory.createLiteral(""));
            newVariations.add(factory.createLiteral(null));

            // Add new variations to the direct pool
            if (!newVariations.isEmpty()) {
                stringValues.addAll(newVariations);
                // System.out.println("[INFO] Added " + stringVariationsAdded + " String
                // variations to direct pool");
            }

        } catch (Exception e) {
            System.err.println("[ERROR] Failed to augment String direct pool: " + e.getMessage());
            // e.printStackTrace();
        }
    }

    // Static variable to store collected special characters (only collect once)
    private static Set<Character> collectedSpecialChars = null;

    /**
     * Extracts special characters (@, _) from directToValues strings
     * Only collects once, then reuses the collected characters
     * 
     * @return Set of special characters found in directToValues strings
     */
    private static Set<Character> getSpecialCharactersFromDirectToValues() {
        if (collectedSpecialChars != null) {
            return collectedSpecialChars; // Already collected, return cached result
        }

        collectedSpecialChars = new HashSet<>();

        try {
            HashMap<CtTypeReference, Set<CtElement>> directToValues = CandidatePool.getDirectToValues();

            // Find String type reference
            CtTypeReference<?> stringType = null;
            for (CtTypeReference<?> type : directToValues.keySet()) {
                if ("java.lang.String".equals(type.getQualifiedName())) {
                    stringType = type;
                    break;
                }
            }

            if (stringType != null) {
                Set<CtElement> stringElements = directToValues.get(stringType);

                for (CtElement element : stringElements) {
                    if (element instanceof CtLiteral) {
                        CtLiteral<?> literal = (CtLiteral<?>) element;
                        Object value = literal.getValue();
                        if (value instanceof String) {
                            String str = (String) value;
                            for (char c : str.toCharArray()) {
                                if (c == '@' || c == '_' || c == '!' || c == '?') {
                                    collectedSpecialChars.add(c);
                                    // Early exit if we found both special characters
                                    if (collectedSpecialChars.size() == 4) {
                                        return collectedSpecialChars;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        } catch (Exception e) {
            System.err.println("[ERROR] Failed to extract special characters from directToValues: " + e.getMessage());
        }

        return collectedSpecialChars;
    }

    /**
     * Generate String variations optimized for short strings
     */
    private static List<String> generateStringVariations(String original) {
        List<String> variations = new ArrayList<>();

        if (original == null) {
            return variations;
        }

        // Random single character case toggle for all strings
        if (!original.isEmpty()) {
            // Find characters that can be case-toggled
            List<Integer> toggleablePositions = new ArrayList<>();
            for (int i = 0; i < original.length(); i++) {
                char c = original.charAt(i);
                if (Character.isLetter(c)) {
                    toggleablePositions.add(i);
                }
            }

            // Randomly toggle one character's case
            if (!toggleablePositions.isEmpty()) {
                Random rand = new Random();
                int randomPos = toggleablePositions.get(rand.nextInt(toggleablePositions.size()));
                char[] chars = original.toCharArray();
                char c = chars[randomPos];

                if (Character.isLowerCase(c)) {
                    chars[randomPos] = Character.toUpperCase(c);
                } else if (Character.isUpperCase(c)) {
                    chars[randomPos] = Character.toLowerCase(c);
                }

                String singleCharToggle = new String(chars);
                if (!singleCharToggle.equals(original)) {
                    variations.add(singleCharToggle);
                    if (DEBUG_STRING_MUTATION) {
                        System.out.println("    [MUTATION] Single char case toggle at pos " + randomPos + ": \""
                                + original + "\" -> \"" + singleCharToggle + "\"");
                    }
                }
            }
        }

        // Add prefix/suffix variations using collected special characters
        if (!original.isEmpty()) {
            Set<Character> specialChars = getSpecialCharactersFromDirectToValues();

            // Ensure _ and @ are always included for string variations
            Set<Character> enhancedSpecialChars = new HashSet<>(specialChars);
            enhancedSpecialChars.add('_');
            if (!enhancedSpecialChars.isEmpty()) {

                for (Character specialChar : enhancedSpecialChars) {
                    String prefixed = specialChar + original;
                    variations.add(prefixed);
                    if (DEBUG_STRING_MUTATION) {
                        System.out.println("    [MUTATION] Special char prefix '" + specialChar + "': \"" + original
                                + "\" -> \"" + prefixed + "\"");
                    }

                    String suffixed = original + specialChar;
                    variations.add(suffixed);
                    if (DEBUG_STRING_MUTATION) {
                        System.out.println("    [MUTATION] Special char suffix '" + specialChar + "': \"" + original
                                + "\" -> \"" + suffixed + "\"");
                    }
                }
            }

        }

        // Additional variations for longer strings
        if (original.length() > 1) {

            String numbered = original + "0";
            variations.add(numbered);
            if (DEBUG_STRING_MUTATION) {
                System.out.println("    [MUTATION] Number suffix: \"" + original + "\" -> \"" + numbered + "\"");
            }

            // Randomly shuffle characters for all strings
            List<Character> charList = new ArrayList<>();
            for (char c : original.toCharArray()) {
                charList.add(c);
            }

            Collections.shuffle(charList);

            StringBuilder shuffled = new StringBuilder();
            for (char c : charList) {
                shuffled.append(c);
            }
            variations.add(shuffled.toString());

            if (DEBUG_STRING_MUTATION) {
                System.out.println("    [MUTATION] Shuffle characters: \"" + original + "\" -> \"" + shuffled + "\"");
            }

            // Space prefix (always add)
            String spaced = " " + original;
            variations.add(spaced);
            if (DEBUG_STRING_MUTATION) {
                System.out.println("    [MUTATION] Space prefix: \"" + original + "\" -> \"" + spaced + "\"");
            }
        }

        return variations;
    }

    /**
     * Augment primitive values in the direct pool with boundary values
     * Adds 0, MAX, MIN, -MAX, -MIN, -1 values for numeric types
     */
    public static void augmentPrimitiveDirectPool() {
        try {
            HashMap<CtTypeReference, Set<CtElement>> directToValues = CandidatePool.getDirectToValues();

            if (factory == null) {
                factory = new Launcher().getFactory();
            }

            int totalVariationsAdded = 0;
            String[] primitiveTypes = { "int", "java.lang.Integer", "long", "java.lang.Long",
                    "double", "java.lang.Double", "float", "java.lang.Float",
                    "short", "java.lang.Short", "byte", "java.lang.Byte" };

            // First check existing types in the pool
            for (Map.Entry<CtTypeReference, Set<CtElement>> entry : directToValues.entrySet()) {
                CtTypeReference<?> type = entry.getKey();
                Set<CtElement> values = entry.getValue();
                String typeName = type.getQualifiedName();

                Set<CtElement> newVariations = generateVariationsForType(typeName);

                if (!newVariations.isEmpty()) {
                    values.addAll(newVariations);
                    totalVariationsAdded += newVariations.size();
                    // System.out.println("[INFO] Added " + newVariations.size() + " " + typeName +
                    // " variations to existing pool");
                }
            }

            // Then add primitive types that don't exist in the pool
            for (String primitiveTypeName : primitiveTypes) {
                boolean typeExists = false;
                for (CtTypeReference<?> existingType : directToValues.keySet()) {
                    if (primitiveTypeName.equals(existingType.getQualifiedName())) {
                        typeExists = true;
                        break;
                    }
                }

                if (!typeExists) {
                    // Create new type reference and add variations
                    CtTypeReference<?> newTypeRef;
                    try {
                        if (primitiveTypeName.contains(".")) {
                            // Wrapper classes like java.lang.Integer
                            newTypeRef = factory.Type().createReference(Class.forName(primitiveTypeName));
                        } else {
                            // Primitive types like int
                            switch (primitiveTypeName) {
                                case "int":
                                    newTypeRef = factory.Type().createReference(int.class);
                                    break;
                                case "long":
                                    newTypeRef = factory.Type().createReference(long.class);
                                    break;
                                case "double":
                                    newTypeRef = factory.Type().createReference(double.class);
                                    break;
                                case "float":
                                    newTypeRef = factory.Type().createReference(float.class);
                                    break;
                                case "short":
                                    newTypeRef = factory.Type().createReference(short.class);
                                    break;
                                case "byte":
                                    newTypeRef = factory.Type().createReference(byte.class);
                                    break;
                                default:
                                    continue; // Skip unknown types
                            }
                        }

                        Set<CtElement> newVariations = generateVariationsForType(primitiveTypeName);

                        if (!newVariations.isEmpty()) {
                            directToValues.put(newTypeRef, newVariations);
                            totalVariationsAdded += newVariations.size();
                            // System.out.println("[INFO] Created new " + primitiveTypeName + " pool with "
                            // + newVariations.size() + " variations");
                        }
                    } catch (ClassNotFoundException e) {
                        System.err.println("[WARNING] Could not create type reference for: " + primitiveTypeName);
                    }
                }
            }

        } catch (Exception e) {
            System.err.println("[ERROR] Failed to augment primitive direct pool: " + e.getMessage());
            // e.printStackTrace();
        }
    }

    private static Set<CtElement> generateVariationsForType(String typeName) {
        switch (typeName) {
            case "int":
            case "java.lang.Integer":
                return generateIntVariations();
            case "long":
            case "java.lang.Long":
                return generateLongVariations();
            case "double":
            case "java.lang.Double":
                return generateDoubleVariations();
            case "float":
            case "java.lang.Float":
                return generateFloatVariations();
            case "short":
            case "java.lang.Short":
                return generateShortVariations();
            case "byte":
            case "java.lang.Byte":
                return generateByteVariations();
            default:
                return new HashSet<>();
        }
    }

    private static Set<CtElement> generateIntVariations() {
        Set<CtElement> variations = new HashSet<>();
        variations.add(factory.createLiteral(0));
        variations.add(factory.createLiteral(-1));
        variations.add(factory.createLiteral(1));
        variations.add(factory.createLiteral(Integer.MAX_VALUE));
        variations.add(factory.createLiteral(Integer.MIN_VALUE));
        variations.add(factory.createLiteral(-Integer.MAX_VALUE));
        return variations;
    }

    private static Set<CtElement> generateLongVariations() {
        Set<CtElement> variations = new HashSet<>();
        variations.add(factory.createLiteral(0L));
        variations.add(factory.createLiteral(-1L));
        variations.add(factory.createLiteral(1L));
        variations.add(factory.createLiteral(Long.MAX_VALUE));
        variations.add(factory.createLiteral(Long.MIN_VALUE));
        variations.add(factory.createLiteral(-Long.MAX_VALUE));
        return variations;
    }

    private static Set<CtElement> generateDoubleVariations() {
        Set<CtElement> variations = new HashSet<>();
        variations.add(factory.createLiteral(0.0));
        variations.add(factory.createLiteral(-1.0));
        variations.add(factory.createLiteral(1.0));
        variations.add(factory.createLiteral(Double.MAX_VALUE));
        variations.add(factory.createLiteral(Double.MIN_VALUE));
        variations.add(factory.createLiteral(-Double.MAX_VALUE));
        return variations;
    }

    private static Set<CtElement> generateFloatVariations() {
        Set<CtElement> variations = new HashSet<>();
        variations.add(factory.createLiteral(0.0f));
        variations.add(factory.createLiteral(-1.0f));
        variations.add(factory.createLiteral(1.0f));
        variations.add(factory.createLiteral(Float.MAX_VALUE));
        variations.add(factory.createLiteral(Float.MIN_VALUE));
        variations.add(factory.createLiteral(-Float.MAX_VALUE));
        return variations;
    }

    private static Set<CtElement> generateShortVariations() {
        Set<CtElement> variations = new HashSet<>();
        variations.add(factory.createLiteral((short) 0));
        variations.add(factory.createLiteral((short) -1));
        variations.add(factory.createLiteral((short) 1));
        variations.add(factory.createLiteral(Short.MAX_VALUE));
        variations.add(factory.createLiteral(Short.MIN_VALUE));
        variations.add(factory.createLiteral((short) -Short.MAX_VALUE));
        return variations;
    }

    private static Set<CtElement> generateByteVariations() {
        Set<CtElement> variations = new HashSet<>();
        variations.add(factory.createLiteral((byte) 0));
        variations.add(factory.createLiteral((byte) -1));
        variations.add(factory.createLiteral((byte) 1));
        variations.add(factory.createLiteral(Byte.MAX_VALUE));
        variations.add(factory.createLiteral(Byte.MIN_VALUE));
        variations.add(factory.createLiteral((byte) -Byte.MAX_VALUE));
        return variations;
    }

    /**
     * Print collected constructor information from ASTParser
     */
    public static void printConstructorMapSummary() {
        try {
            Map<String, Set<CtConstructor<?>>> constructorsMap = ASTParser.getAll_Constructors_Map();

            System.out.println("\n--- Constructor Map Summary ---");
            System.out.println("Total Types with Constructors: " + constructorsMap.size());

            if (constructorsMap.isEmpty()) {
                System.out.println("No constructors found in the collected map.");
                return;
            }

            // Sort types by name for consistent output
            List<String> sortedTypes = new ArrayList<>(constructorsMap.keySet());
            sortedTypes.sort(String::compareTo);

            int totalConstructors = 0;
            for (String typeName : sortedTypes) {
                Set<CtConstructor<?>> constructors = constructorsMap.get(typeName);
                if (constructors != null && !constructors.isEmpty()) {
                    totalConstructors += constructors.size();
                    System.out.println("  - Type: " + typeName);
                    System.out.println("    - Constructors: " + constructors.size());

                    // Sort constructors by parameter count
                    List<CtConstructor<?>> sortedConstructors = new ArrayList<>(constructors);
                    sortedConstructors.sort(Comparator.comparingInt(c -> c.getParameters().size()));

                    for (CtConstructor<?> constructor : sortedConstructors) {
                        StringBuilder signature = new StringBuilder();
                        signature.append("      * ").append(typeName.substring(typeName.lastIndexOf('.') + 1))
                                .append("(");

                        List<CtParameter<?>> params = constructor.getParameters();
                        for (int i = 0; i < params.size(); i++) {
                            if (i > 0)
                                signature.append(", ");
                            String paramType = params.get(i).getType().getQualifiedName();
                            signature.append(paramType.substring(paramType.lastIndexOf('.') + 1));
                        }
                        signature.append(")");

                        // Add visibility info
                        if (constructor.isPublic()) {
                            signature.append(" [public]");
                        } else if (constructor.isProtected()) {
                            signature.append(" [protected]");
                        } else if (constructor.isPrivate()) {
                            signature.append(" [private]");
                        } else {
                            signature.append(" [package-private]");
                        }

                        System.out.println(signature.toString());
                    }
                }
            }

            System.out.println("Total Constructors Found: " + totalConstructors);

        } catch (Exception e) {
            System.err.println("[ERROR] Failed to print constructor map summary: " + e.getMessage());
            // e.printStackTrace();
        }
    }

    // =================================================================
    // MUT-BASED POOL ANALYSIS AND AUGMENTATION METHODS
    // =================================================================

    /**
     * Analyze required types from all MUTs and identify which types need more
     * objects
     */
    private static void analyzeRequiredTypesFromMUTs() {
        long analysisStartTime = System.currentTimeMillis();

        Set<MUTInput> muts = InputCombinations.getMuts();
        if (muts == null || muts.isEmpty()) {

            return;
        }

        Map<String, Integer> typeRequirementCount = new HashMap<>();
        Map<String, Set<String>> typeToMutSignatures = new HashMap<>();

        // Analyze each MUT's parameter types
        int totalInputsAnalyzed = 0;
        for (MUTInput mut : muts) {
            String mutSignature = mut.getMethodSignature();
            LinkedHashMap<Integer, List<Input>> inputs = mut.getInputs();

            if (inputs != null) {
                int inputsForThisMut = 0;
                for (List<Input> inputList : inputs.values()) {
                    for (Input input : inputList) {
                        if (input.getType() != null) {
                            String typeName = input.getType().getQualifiedName();
                            typeRequirementCount.put(typeName, typeRequirementCount.getOrDefault(typeName, 0) + 1);

                            // Track which MUTs use this type
                            typeToMutSignatures.computeIfAbsent(typeName, k -> new HashSet<>()).add(mutSignature);

                            inputsForThisMut++;
                            totalInputsAnalyzed++;
                        }
                    }
                }

            }
        }

        // Analyze current pool sizes and identify insufficient types
        int typesNeedingAugmentationCount = 0;
        Map<String, Integer> poolAnalysisResults = new HashMap<>();

        for (Map.Entry<String, Integer> entry : typeRequirementCount.entrySet()) {
            String typeName = entry.getKey();
            int requirementCount = entry.getValue();

            // Find the type reference
            CtTypeReference<?> typeRef = findTypeReferenceByName(typeName);
            if (typeRef != null) {
                int currentPoolSize = analyzeCurrentPoolSizeForType(typeRef);
                typePoolSizeCache.put(typeRef, currentPoolSize);
                poolAnalysisResults.put(typeName, currentPoolSize);

                // Check if this type needs augmentation
                boolean isArray = typeRef.isArray();
                String typeKind = isArray ? "[ARRAY]" : "[SINGLE]";

                // Pool is insufficient if it's <= threshold (need more than 5)
                if (currentPoolSize <= MIN_POOL_SIZE_THRESHOLD) {
                    typesNeedingAugmentation.add(typeRef);
                    typesNeedingAugmentationCount++;

                    Set<String> usingMuts = typeToMutSignatures.get(typeName);
                    String mutInfo = usingMuts != null ? " (used by " + usingMuts.size() + " MUTs)" : "";

                }
            }
        }

        long analysisEndTime = System.currentTimeMillis();
        long analysisDuration = analysisEndTime - analysisStartTime;

        // Show types that need augmentation
        if (typesNeedingAugmentationCount > 0) {

            for (CtTypeReference<?> needingType : typesNeedingAugmentation) {
                String typeName = needingType.getQualifiedName();
                int poolSize = poolAnalysisResults.getOrDefault(typeName, -1);
                int requirementCount = typeRequirementCount.getOrDefault(typeName, 0);
                String typeKind = needingType.isArray() ? " [ARRAY]" : " [SINGLE]";
            }
        }

        // Always show top 5 most required types
        if (!typeRequirementCount.isEmpty()) {
            typeRequirementCount.entrySet().stream()
                    .sorted(Map.Entry.<String, Integer>comparingByValue().reversed())
                    .limit(5)
                    .forEach(e -> {
                        int poolSize = poolAnalysisResults.getOrDefault(e.getKey(), -1);
                        CtTypeReference<?> topTypeRef = findTypeReferenceByName(e.getKey());
                        String typeKind = "";
                        if (topTypeRef != null) {
                            typeKind = topTypeRef.isArray() ? " [ARRAY]" : " [SINGLE]";
                        }
                        String status = poolSize <= MIN_POOL_SIZE_THRESHOLD ? "⚠️ " : "✅ ";
                        String statusText = poolSize <= MIN_POOL_SIZE_THRESHOLD
                                ? (poolSize == MIN_POOL_SIZE_THRESHOLD ? " [BORDERLINE]" : " [INSUFFICIENT]")
                                : " [SUFFICIENT]";

                    });
        }
    }

    /**
     * Find CtTypeReference by qualified name from existing pools
     */
    private static CtTypeReference<?> findTypeReferenceByName(String qualifiedName) {
        // Search in baseVarTypeNamePoolAsList
        if (baseVarTypeNamePoolAsList != null) {
            for (CtTypeReference<?> typeRef : baseVarTypeNamePoolAsList.keySet()) {
                if (typeRef.getQualifiedName().equals(qualifiedName)) {
                    return typeRef;
                }
            }
        }

        // Search in baseDirectToValuesAsList
        if (baseDirectToValuesAsList != null) {
            for (CtTypeReference<?> typeRef : baseDirectToValuesAsList.keySet()) {
                if (typeRef.getQualifiedName().equals(qualifiedName)) {
                    return typeRef;
                }
            }
        }

        // If not found, try to create a new type reference
        if (factory != null) {
            try {
                return factory.Type().createReference(qualifiedName);
            } catch (Exception e) {
                // Failed to create type reference
            }
        }

        return null;
    }

    /**
     * Analyze current pool size for a specific type
     */
    private static int analyzeCurrentPoolSizeForType(CtTypeReference<?> targetType) {
        String targetTypeName = targetType.getQualifiedName();
        boolean targetIsArray = targetType.isArray();

        // Separate counting for different pool types
        int variablePoolSize = 0; // From baseVarTypeNamePoolAsList
        int directValuePoolSize = 0; // From baseDirectToValuesAsList

        // Check baseVarTypeNamePoolAsList
        if (baseVarTypeNamePoolAsList != null) {
            for (Map.Entry<CtTypeReference, List<Pair<CtTypeReference, CtElement>>> entry : baseVarTypeNamePoolAsList
                    .entrySet()) {
                CtTypeReference<?> poolType = entry.getKey();
                boolean poolIsArray = poolType.isArray();
                String poolTypeName = poolType.getQualifiedName();

                if (isCompatibleType(poolType, targetType)) {
                    List<Pair<CtTypeReference, CtElement>> candidates = entry.getValue();
                    variablePoolSize += candidates.size();

                }
            }
        }

        // Check baseDirectToValuesAsList
        if (baseDirectToValuesAsList != null) {
            for (Map.Entry<CtTypeReference<?>, List<CtElement>> entry : baseDirectToValuesAsList.entrySet()) {
                CtTypeReference<?> poolType = entry.getKey();
                boolean poolIsArray = poolType.isArray();
                String poolTypeName = poolType.getQualifiedName();

                if (isCompatibleType(poolType, targetType)) {
                    directValuePoolSize += entry.getValue().size();

                }
            }
        }

        // For MUT parameter filling, we should primarily consider variable pools
        // Direct values are useful but variables are more flexible for object creation
        int usablePoolSize = variablePoolSize; // Primary pool for object creation
        int totalPoolSize = variablePoolSize + directValuePoolSize; // For reference

        // Return usable pool size (variables) for augmentation decisions
        return usablePoolSize;
    }

    /**
     * Generate additional objects for types with insufficient pool size
     */
    private static void generateAdditionalObjectsForInsufficientTypes() {
        if (typesNeedingAugmentation.isEmpty()) {

            return;
        }

        int totalObjectsGenerated = 0;
        for (CtTypeReference<?> typeRef : typesNeedingAugmentation) {
            int currentSize = typePoolSizeCache.getOrDefault(typeRef, 0);
            int targetSize = SAFE_POOL_SIZE; // Generate to safe size (6)
            int objectsToGenerate = Math.max(0, targetSize - currentSize);

            if (objectsToGenerate > 0) {
                int generatedForType = generateAdditionalObjectsForType(typeRef, objectsToGenerate);
                totalObjectsGenerated += generatedForType;

            }
        }

    }

    /**
     * Generate additional objects for a specific type using various strategies
     */
    private static int generateAdditionalObjectsForType(CtTypeReference<?> typeRef, int targetCount) {
        long generationStartTime = System.currentTimeMillis();
        String typeName = typeRef.getQualifiedName();

        if (factory == null) {
            factory = new Launcher().getFactory();
        }

        int generatedCount = 0;
        int factoryAttempts = 0, factorySuccesses = 0;
        int constructorAttempts = 0, constructorSuccesses = 0;
        int methodAttempts = 0, methodSuccesses = 0;

        for (int i = 0; i < targetCount && generatedCount < targetCount; i++) {
            try {
                // Strategy 1: Try factory methods
                CtExpression<?> factoryResult = tryCreateFromFactoryMethod(typeRef, factory, factory.createBlock(), 0);
                if (factoryResult != null && addObjectToPool(typeRef, factoryResult, "factory_" + i)) {
                    generatedCount++;
                    continue;
                }

                // Strategy 2: Try constructors with different approaches
                CtExpression<?> constructorResult = tryCreateViaEnhancedConstructor(typeRef, i);
                if (constructorResult != null && addObjectToPool(typeRef, constructorResult, "constructor_" + i)) {
                    generatedCount++;
                    continue;
                }

                // Strategy 3: Try method invocations if recursive calls enabled
                if (recursiveMethodCalls) {
                    CtExpression<?> methodResult = tryCreateViaMethodInvocation(typeRef, i);
                    if (methodResult != null && addObjectToPool(typeRef, methodResult, "method_" + i)) {
                        generatedCount++;
                        continue;
                    }
                }

            } catch (Exception e) {

            }
        }

        long generationEndTime = System.currentTimeMillis();
        long generationDuration = generationEndTime - generationStartTime;
        totalGenerationTime += generationDuration;

        return generatedCount;
    }

    /**
     * Try creating object via enhanced constructor approach with variation
     */
    private static CtExpression<?> tryCreateViaEnhancedConstructor(CtTypeReference<?> typeRef, int variation) {
        Map<String, Set<CtConstructor<?>>> constructorsMap = ASTParser.getAll_Constructors_Map();
        Set<CtConstructor<?>> constructors = constructorsMap.get(typeRef.getQualifiedName());

        if (constructors != null && !constructors.isEmpty()) {
            List<CtConstructor<?>> constructorList = new ArrayList<>(constructors);
            // Use variation to select different constructors
            CtConstructor<?> selectedConstructor = constructorList.get(variation % constructorList.size());

            try {
                CtBlock<?> tempBody = factory.createBlock();
                CtConstructorCall<?> constructorCall = createConstructorCallFromConstructor(
                        selectedConstructor, factory, tempBody, 0, typeRef);

                if (constructorCall != null) {
                    return constructorCall;
                }
            } catch (Exception e) {
                // Failed with this constructor, try next approach
            }
        }

        return null;
    }

    /**
     * Try creating object via method invocation
     */
    private static CtExpression<?> tryCreateViaMethodInvocation(CtTypeReference<?> typeRef, int variation) {
        try {
            CtMethod<?> method = findMatchingMethod(typeRef, factory);
            if (method != null) {
                CtBlock<?> tempBody = factory.createBlock();
                return createMethodInvo(method, factory, tempBody, 0);
            }
        } catch (Exception e) {
            // Failed to create via method invocation
        }

        return null;
    }

    /**
     * Add generated object to the candidate pool
     */
    private static boolean addObjectToPool(CtTypeReference<?> typeRef, CtExpression<?> objectExpr, String nameSuffix) {
        try {
            // Get the actual type from the expression if possible
            CtTypeReference<?> actualType = objectExpr.getType();
            if (actualType == null || actualType.isImplicit() || actualType.getQualifiedName().equals("?")) {
                actualType = typeRef; // Fallback to requested type
            }

            // Create a variable to hold the object
            String varName = normalizeTypeNameForVariable(actualType) + "_" + nameSuffix + "_" + System.nanoTime();
            CtLocalVariable<?> objVar = factory.createLocalVariable();
            objVar.setSimpleName(varName);
            objVar.setType((CtTypeReference) actualType.clone());
            objVar.setDefaultExpression((CtExpression) objectExpr.clone());

            // Create the sequence
            List<CtElement> sequence = new ArrayList<>();
            sequence.add(objVar);

            // Add to CandidatePool with actual type
            CtElement varElement = objVar.getReference();
            Pair<CtTypeReference, CtElement> typeAndName = new Pair<>(actualType, varElement);

            boolean success = CandidatePool.insertVarTypeToInputPool(typeAndName, sequence);
            if (success) {
                // Also update local cache with actual type
                if (baseVarTypeNamePoolAsList.containsKey(actualType)) {
                    baseVarTypeNamePoolAsList.get(actualType).add(typeAndName);
                } else {
                    List<Pair<CtTypeReference, CtElement>> newList = new ArrayList<>();
                    newList.add(typeAndName);
                    baseVarTypeNamePoolAsList.put(actualType, newList);
                }
            }

            return success;
        } catch (Exception e) {
            return false;
        }
    }

    /**
     * Print detailed generation statistics for debugging
     */
    private static void printGenerationStatistics() {
        System.out.println("[STATS] 📈 Object Generation Statistics:");
        System.out.println("[STATS] ======================================");

        // Attempt vs Success stats
        int totalAttempts = generationAttemptStats.values().stream().mapToInt(Integer::intValue).sum();
        int totalSuccesses = generationSuccessStats.values().stream().mapToInt(Integer::intValue).sum();

        if (totalAttempts > 0) {
            double successRate = (double) totalSuccesses / totalAttempts * 100;
            System.out.println("[STATS] Overall Success Rate: " + String.format("%.1f%%", successRate) + " ("
                    + totalSuccesses + "/" + totalAttempts + ")");
        }

        // Strategy-specific stats
        for (String strategy : Arrays.asList("factory", "constructor", "method")) {
            int attempts = generationAttemptStats.getOrDefault(strategy, 0);
            int successes = generationSuccessStats.getOrDefault(strategy, 0);
            if (attempts > 0) {
                double rate = (double) successes / attempts * 100;
                System.out.println("[STATS] " + strategy.substring(0, 1).toUpperCase() + strategy.substring(1) +
                        " Strategy: " + String.format("%.1f%%", rate) + " (" + successes + "/" + attempts + ")");
            }
        }

        System.out.println("[STATS] Total Pool Augmentation Calls: " + totalPoolAugmentationCalls);
        System.out.println("[STATS] Total Generation Time: " + totalGenerationTime + " ms");

        if (totalGenerationTime > 0 && totalSuccesses > 0) {
            double avgTimePerObject = (double) totalGenerationTime / totalSuccesses;
            System.out.println("[STATS] Average Time per Object: " + String.format("%.1f", avgTimePerObject) + " ms");
        }

        System.out.println("[STATS] ======================================");
    }

    /**
     * Generate NULL objects for all MUT parameter types
     * This ensures that NULL objects are available in the pool before
     * InputCombinations processes them
     */
    private static void generateNullObjectsForAllMUTTypes() {
        if (factory == null) {
            factory = new Launcher().getFactory();
        }

        // Get all MUT parameters from ASTParser
        Map<String, CtMethod<?>> publicMethods = ASTParser.getCUT_PublicMethods_Map();
        Set<CtTypeReference<?>> allParamTypes = new HashSet<>();

        for (CtMethod<?> method : publicMethods.values()) {
            // Add receiver type
            CtTypeReference<?> receiverType = method.getDeclaringType().getReference();
            if (receiverType != null && !receiverType.isPrimitive()) {
                allParamTypes.add(receiverType);
            }

            // Add parameter types
            for (CtParameter<?> param : method.getParameters()) {
                CtTypeReference<?> paramType = param.getType();
                if (paramType != null && !paramType.isPrimitive()) {
                    allParamTypes.add(paramType);
                }
            }
        }

        int nullObjectsCreated = 0;
        for (CtTypeReference<?> typeRef : allParamTypes) {
            if (createAndRegisterNullObject(typeRef, factory)) {
                nullObjectsCreated++;
            }
        }

    }

    /**
     * Unified utility method to create and register a NULL object for a given type
     * This method encapsulates the common pattern used throughout SeedAugmentor
     * 
     * @param typeRef The type to create a null object for
     * @param factory Spoon factory for creating elements
     * @return true if a new null object was created and registered, false if it
     *         already existed
     */
    private static boolean createAndRegisterNullObject(CtTypeReference<?> typeRef, Factory factory) {
        if (typeRef == null || typeRef.isPrimitive()) {
            return false;
        }

        String typeName = typeRef.getQualifiedName();

        // Check cache first
        if (nullObjectsRegisteredTypes.contains(typeName)) {
            return false;
        }

        // Skip basic types
        if (shouldSkipNullObjectCreation(typeName)) {
            return false;
        }

        // Check if already in pool
        if (hasNullObjectInPool(typeRef)) {
            nullObjectsRegisteredTypes.add(typeName);
            return false;
        }

        try {
            CtLocalVariable<?> nullVar = createNullVariable(typeRef, factory);
            List<CtElement> nullStmts = new ArrayList<>();
            nullStmts.add(nullVar);

            // Register in CandidatePool
            Pair<CtTypeReference, CtElement> nullTypeAndName = new Pair<>(typeRef, nullVar.getReference());
            CandidatePool.insertVarTypeToInputPool(nullTypeAndName, nullStmts);

            // Mark as registered
            nullObjectsRegisteredTypes.add(typeName);

            return true;
        } catch (Exception e) {
            return false;
        }
    }

    /**
     * Create a null CtLocalVariable with NULL value
     * Used by multiple methods to avoid code duplication
     */
    private static CtLocalVariable<?> createNullVariable(CtTypeReference<?> typeRef, Factory factory) {
        String simpleTypeName = typeRef.getSimpleName();

        // Handle array types: replace [] with Array suffix
        if (typeRef.isArray()) {
            // Remove all [] from the type name
            simpleTypeName = simpleTypeName.replaceAll("\\[\\]", "");
            simpleTypeName = simpleTypeName + "Array";
        }

        String nullVarName = "null_" + simpleTypeName + "_" + System.currentTimeMillis() + "_" + dummyVarCounter++;
        CtLocalVariable<?> nullVar = factory.createLocalVariable();
        nullVar.setSimpleName(nullVarName);
        nullVar.setType((CtTypeReference) typeRef.clone());
        nullVar.setDefaultExpression(factory.createLiteral(null));
        return nullVar;
    }

    /**
     * Check if we should skip creating null objects for basic types
     */
    private static boolean shouldSkipNullObjectCreation(String typeName) {
        return typeName.equals("java.lang.String") ||
                typeName.equals("java.lang.Object") ||
                typeName.startsWith("java.lang.Integer") ||
                typeName.startsWith("java.lang.Long") ||
                typeName.startsWith("java.lang.Double") ||
                typeName.startsWith("java.lang.Float") ||
                typeName.startsWith("java.lang.Boolean");
    }

    /**
     * Create a null variable and register it in CandidatePool in one step
     * This is a simplified wrapper for common use cases
     */
    private static boolean createNullObjectIfAbsent(CtTypeReference<?> typeRef, Factory factory) {
        if (typeRef == null || typeRef.isPrimitive()) {
            return false;
        }

        if (shouldSkipNullObjectCreation(typeRef.getQualifiedName())) {
            return false;
        }

        if (hasNullObjectInPool(typeRef)) {
            return false;
        }

        try {
            CtLocalVariable<?> nullVar = createNullVariable(typeRef, factory);
            List<CtElement> nullStmts = new ArrayList<>();
            nullStmts.add(nullVar);

            Pair<CtTypeReference, CtElement> pair = new Pair<>(typeRef, nullVar.getReference());
            return CandidatePool.insertVarTypeToInputPool(pair, nullStmts);
        } catch (Exception e) {
            return false;
        }
    }

    /**
     * Augment the candidate pool with Class references (Void.class, String.class,
     * etc.)
     * This enables test methods with Class<?> parameters to have diverse class
     * inputs
     */
    public static void augmentClassDirectPool() {
        try {
            if (factory == null) {
                factory = new Launcher().getFactory();
            }

            CtTypeReference<?> classType = factory.Type().createReference("java.lang.Class");
            HashMap<CtTypeReference, Set<CtElement>> directToValues = CandidatePool.getDirectToValues();

            // Create .class references for essential types
            String[] classReferences = { "Void", "String", "Object" };

            int classReferencesAdded = 0;

            // Get or create the set for Class type in direct values
            Set<CtElement> classValues = directToValues.computeIfAbsent(
                    classType,
                    k -> new HashSet<>());

            for (String simpleClassName : classReferences) {
                try {
                    // Create a literal code snippet representing ClassName.class
                    // This generates code like: Void.class, String.class, Object.class
                    String classLiteralCode = simpleClassName + ".class";
                    CtExpression<?> classLiteral = factory.createCodeSnippetExpression(classLiteralCode);

                    // Add to the direct values pool
                    if (!classValues.contains(classLiteral)) {
                        classValues.add(classLiteral);
                        classReferencesAdded++;
                    }

                } catch (Exception e) {
                    // Class not available in test environment - skip it
                }
            }

        } catch (Exception e) {
            System.err.println("[ERROR] Failed to augment class direct pool: " + e.getMessage());
            e.printStackTrace();
        }
    }

}
