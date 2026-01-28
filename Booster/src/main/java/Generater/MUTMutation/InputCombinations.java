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
import spoon.support.reflect.code.CtVariableReadImpl;
import spoon.support.reflect.code.*;
import utils.Config;
import utils.Pair;
import java.util.Objects;

import javax.tools.*;
import java.io.*;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.net.URI;
import java.net.URLClassLoader;
import java.util.*;
import java.lang.reflect.Constructor;
import java.util.stream.Collectors;

public class InputCombinations {

    private Map<MUTInput, Set<List<Input>>> combinationsMap = new HashMap<>();

    private static Set<MUTInput> muts;

    private static boolean recursiveMethodCalls = Config.recursiveMethodCalls;

    private static final Map<String, List<CtTypeReference<?>>> suitableImplementationCache = new HashMap<>();

    // Performance optimization: Cache for processInputPool
    private static final Map<String, Set<CtTypeReference<?>>> typesToSearchCache = new HashMap<>();
    private static final Map<String, List<Input>> inputPoolResultCache = new HashMap<>();

    // Common super types that should match with their implementations
    private static final Set<String> COMMON_SUPER_TYPES = new HashSet<>(Arrays.asList(
            "java.lang.Object",
            "java.io.Serializable",
            "java.lang.Cloneable",
            "java.util.Collection",
            "java.util.List",
            "java.util.Set",
            "java.util.Map",
            "java.lang.CharSequence",
            "java.lang.Number",
            "java.lang.Comparable"));

    // New fields for collecting failed MUTs and retry logic
    private static Set<FailedMUT> failedMUTs = new HashSet<>();
    private static int maxRetryAttempts = 2;

    // Inner class to store information about failed MUTs
    public static class FailedMUT {
        private final CtMethod<?> method;
        private final CtTypeReference<?> failedType;
        private final int parameterIndex;
        private final String methodSignature;

        public FailedMUT(CtMethod<?> method, CtTypeReference<?> failedType, int parameterIndex,
                String methodSignature) {
            this.method = method;
            this.failedType = failedType;
            this.parameterIndex = parameterIndex;
            this.methodSignature = methodSignature;
        }

        public CtMethod<?> getMethod() {
            return method;
        }

        public CtTypeReference<?> getFailedType() {
            return failedType;
        }

        public int getParameterIndex() {
            return parameterIndex;
        }

        public String getMethodSignature() {
            return methodSignature;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (obj == null || getClass() != obj.getClass())
                return false;
            FailedMUT failedMUT = (FailedMUT) obj;
            return parameterIndex == failedMUT.parameterIndex &&
                    Objects.equals(methodSignature, failedMUT.methodSignature) &&
                    Objects.equals(failedType.getQualifiedName(), failedMUT.failedType.getQualifiedName());
        }

        @Override
        public int hashCode() {
            return Objects.hash(methodSignature, failedType.getQualifiedName(), parameterIndex);
        }
    }

    public static Set<MUTInput> getMuts() {
        return muts;
    }

    public Set<FailedMUT> getFailedMUTs() {
        return failedMUTs;
    }

    public void addMUTs(Set<MUTInput> newMUTs) {
        if (muts == null) {
            muts = new HashSet<>();
        }
        muts.addAll(newMUTs);
    }

    public Map<MUTInput, Set<List<Input>>> getCombinationsMap() {
        return combinationsMap;
    }

    private static void preProsess(long megaClassTime) {
        ASTParser.gatherConstructorsAndMethods(Config.PROJECT_DIR, Config.CUT_FILES);

    }

    public void run(String testFile, long startTime, List<String> baseTests) throws TimeoutException {
        long megaClassTime = System.currentTimeMillis() - startTime;

        preProsess(megaClassTime);

        Config.START_TIME = System.currentTimeMillis();
        try {
            ASTParser.parser(
                    Config.MEGAFILE_PATH);
        } catch (TimeoutException e) {
            System.out.println("Timeout detected during parser: " + e.getMessage());
            return;
        } catch (Exception e) {
            // e.printStackTrace();
        }
        if (Config.SEED_AUGMENTATION) {
            try {
                SeedAugmentor.augmentInitalSeed();
                SeedAugmentor.augmentStringDirectPool();
                SeedAugmentor.augmentPrimitiveDirectPool();
                SeedAugmentor.augmentClassDirectPool();
                SeedAugmentor.addNullObjectsForPublicAPITypes();
                muts = processMUTs();

                // Retry logic for failed MUTs using seed augmentation
                SeedAugmentor.retryFailedMUTsWithSeedAugmentation(this);

                // Reprocess MUTs with new inputs (String mutations, null objects, and recovered
                // types)
                int previousSize = muts != null ? muts.size() : 0;
                muts = processMUTs();
                int finalSize = muts != null ? muts.size() : 0;
                System.out.println("[INFO] MUT generation complete: " + previousSize + " -> " + finalSize
                        + " MUTs after String augmentation, null object generation, and retry logic");

                // Print final statistics
                printFinalStatistics();

            } catch (Exception e) {
                // e.printStackTrace();
            }
        } else {
            try {
                muts = processMUTs();
            } catch (Exception e) {

            }

        }
    }

    /**
     * Retry processing the specific failed MUTs after seed augmentation
     */
    public Set<MUTInput> retryFailedMUTs(Set<FailedMUT> currentFailures) throws Exception {
        Set<MUTInput> recoveredMUTs = new HashSet<>();

        for (FailedMUT failure : currentFailures) {
            try {
                MUTInput recoveredMUT = attemptToRecoverMUT(failure);
                if (recoveredMUT != null) {
                    recoveredMUTs.add(recoveredMUT);
                }
            } catch (Exception e) {
                System.err.println("[ERROR] Failed to recover MUT: " + failure.getMethodSignature());
                // e.printStackTrace();
            }
        }

        return recoveredMUTs;
    }

    /**
     * Attempt to recover a specific failed MUT
     */
    private MUTInput attemptToRecoverMUT(FailedMUT failure) throws Exception {
        CtMethod<?> method = failure.getMethod();
        CtInvocation<?> invocation = method.getFactory().createInvocation();
        invocation.setExecutable((CtExecutableReference) method.getReference());

        boolean isStatic = method.getModifiers().contains(spoon.reflect.declaration.ModifierKind.STATIC);

        List<CtTypeReference> originalTypes = new ArrayList<>();

        if (isStatic) {
            invocation.setTarget(method.getFactory().createTypeAccess(method.getDeclaringType().getReference()));
            originalTypes.add(null);
        } else {
            // Use the topmost declaring type (most abstract) for better compatibility
            CtTypeReference<?> receiverType = getTopmostDeclaringType(method);
            originalTypes.add(receiverType);
        }

        method.getParameters().forEach(p -> originalTypes.add(p.getType()));

        // Try to process inputs again
        LinkedHashMap<Integer, List<Input>> hashedInputPools = new LinkedHashMap<>();
        boolean isValidMUT = true;

        for (int i = 0; i < originalTypes.size(); i++) {
            // Try to infer the actual parameter type from method body usage
            CtTypeReference<?> paramType = originalTypes.get(i);

            // System.out.println("[DEBUG-PROCESS] param[" + i + "] type: " + (paramType !=
            // null ? paramType.getQualifiedName() : "null"));

            // Only try type inference if declared type is Object
            CtTypeReference<?> inferredType = null;
            if (paramType != null && "java.lang.Object".equals(paramType.getQualifiedName())) {
                System.out.println("[DEBUG-TYPEINF] === Processing parameter[" + i + "] ===");
                System.out.println("[DEBUG-TYPEINF] Method: " + method.getSignature());
                System.out.println("[DEBUG-TYPEINF] Declared type: java.lang.Object");

                inferredType = inferParameterActualType(method, i, paramType);

                if (inferredType != null) {
                    System.out.println("[DEBUG-TYPEINF] ✓ Inferred type: " + inferredType.getQualifiedName());
                } else {
                    System.out.println("[DEBUG-TYPEINF] ✗ Inference FAILED - using declared type");
                }
            }

            // Use inferred type if found, otherwise use declared type
            CtTypeReference<?> typeToUse = (inferredType != null) ? inferredType : paramType;

            List<Input> inputs = processInputPool(typeToUse, i == 0);

            if (inputs.isEmpty() && originalTypes.get(i) != null) {
                try {
                    List<Input> fallbackInputs = findFallbackInputsFromMUTPool(method, i, originalTypes.get(i));
                    if (!fallbackInputs.isEmpty()) {
                        inputs = fallbackInputs;
                    } else {
                        // Still failed, add back to failed MUTs for next attempt
                        failedMUTs.add(failure);
                        isValidMUT = false;
                        break;
                    }
                } catch (Exception e) {
                    System.err.println("[ERROR] Exception in fallback input search for " + failure.getMethodSignature()
                            + ": " + e.getMessage());
                    // Still failed, add back to failed MUTs for next attempt
                    failedMUTs.add(failure);
                    isValidMUT = false;
                    break;
                }
            }
            hashedInputPools.put(i, inputs);
        }

        if (isValidMUT) {
            // Use the same receiver type as in originalTypes for consistency
            String fqcn = isStatic ? method.getDeclaringType().getQualifiedName()
                    : originalTypes.get(0).getQualifiedName();
            String fullMethodSignature = fqcn + "." + method.getSignature();
            return new MUTInput(invocation, originalTypes, hashedInputPools, fullMethodSignature);
        }

        return null;
    }

    /**
     * Print final statistics about MUT generation and recovery
     */
    private void printFinalStatistics() {
        int totalMUTs = muts != null ? muts.size() : 0;
        int remainingFailures = failedMUTs.size();

        // Count both public methods and public constructors
        int totalPublicMethods = ASTParser.getCUT_PublicMethods_Map().size();
        int totalPublicConstructors = 0;
        Map<String, Set<CtConstructor<?>>> constructorsMap = ASTParser.getCUT_Constructors_Map();
        for (Set<CtConstructor<?>> constructors : constructorsMap.values()) {
            totalPublicConstructors += constructors.size();
        }
        int totalPublicAPIs = totalPublicMethods + totalPublicConstructors;

        double successRate = totalPublicAPIs > 0 ? (double) totalMUTs / totalPublicAPIs * 100 : 0;
        System.out.println("MUT Generation: " + totalMUTs + "/" + totalPublicAPIs + " (" + totalPublicMethods
                + " methods + " + totalPublicConstructors + " constructors, " + String.format("%.1f", successRate)
                + "% success)");

        if (remainingFailures > 0) {
            System.out.println("Failed to generate inputs for " + remainingFailures + " MUTs");
        }
    }

    private Set<MUTInput> processMUTs() throws Exception {
        Set<MUTInput> result = new HashSet<>();

        // Clear previous failed MUTs and caches at the start of processing
        failedMUTs.clear();
        suitableImplementationCache.clear();
        typesToSearchCache.clear();
        inputPoolResultCache.clear();

        HashMap<String, CtMethod<?>> publicAPIs = ASTParser.getCUT_PublicMethods_Map();

        // Count both methods and constructors
        int totalPublicConstructors = 0;
        Map<String, Set<CtConstructor<?>>> constructorsMap = ASTParser.getCUT_Constructors_Map();
        for (Set<CtConstructor<?>> constructors : constructorsMap.values()) {
            totalPublicConstructors += constructors.size();
        }
        int totalAPIs = publicAPIs.size() + totalPublicConstructors;

        System.out.println("# of Public+Protected APIs to be Tested : " + totalAPIs + " (" + publicAPIs.size()
                + " methods + " + totalPublicConstructors + " constructors)");

        // System.out.println("\n[DEBUG] Processing " + publicAPIs.size() + "
        // methods:");
        // 1. Public+Protected API (메소드) 처리
        for (CtMethod<?> method : publicAPIs.values()) {
            // System.out.println("[DEBUG] Processing method: " + method.getSignature());
            CtInvocation<?> invocation = method.getFactory().createInvocation();
            invocation.setExecutable((CtExecutableReference) method.getReference());
            boolean isStatic = method.getModifiers().contains(spoon.reflect.declaration.ModifierKind.STATIC);

            List<CtTypeReference> originalTypes = new ArrayList<>();

            if (isStatic) {
                invocation.setTarget(method.getFactory().createTypeAccess(method.getDeclaringType().getReference()));
                originalTypes.add(null);
            } else {
                // Use the topmost declaring type (most abstract) for better compatibility
                CtTypeReference<?> receiverType = getTopmostDeclaringType(method);
                originalTypes.add(receiverType);
            }

            method.getParameters().forEach(p -> originalTypes.add(p.getType()));

            LinkedHashMap<Integer, List<Input>> hashedInputPools = new LinkedHashMap<>();
            boolean isValidMUT = true;
            for (int i = 0; i < originalTypes.size(); i++) {
                CtTypeReference<?> paramType = originalTypes.get(i);

                // Only try type inference if declared type is Object
                CtTypeReference<?> inferredType = null;
                if (paramType != null && "java.lang.Object".equals(paramType.getQualifiedName())) {
                    // i=0은 receiver, i=1부터가 실제 파라미터이므로 i-1을 전달
                    int actualParamIndex = i - 1;
                    inferredType = inferParameterActualType(method, actualParamIndex, paramType);
                }

                // Use inferred type if found, otherwise use declared type
                CtTypeReference<?> typeToUse = (inferredType != null) ? inferredType : paramType;

                // 똑똑해진 processInputPool이 모든 것을 알아서 처리합니다.
                List<Input> inputs = processInputPool(typeToUse, i == 0);

                // static 리시버(null)가 아니고, Input을 전혀 찾지 못했다면 MUTnameToArgtypes에서 대안을 찾아봅니다.
                if (inputs.isEmpty() && originalTypes.get(i) != null) {
                    List<Input> fallbackInputs = findFallbackInputsFromMUTPool(method, i, originalTypes.get(i));
                    if (!fallbackInputs.isEmpty()) {
                        inputs = fallbackInputs;
                        System.out.println("[INFO] Found " + fallbackInputs.size() + " fallback inputs for type: "
                                + originalTypes.get(i).getQualifiedName() + " in MUT " + method.getSignature()
                                + " using MUTnameToArgtypes pool.");
                    } else {
                        if (Config.SEED_AUGMENTATION) {
                            System.out.println("[WARN] No inputs found for type: "
                                    + originalTypes.get(i).getQualifiedName() + " in MUT " + method.getSignature()
                                    + ". Collecting for seed augmentation.");

                            // Collect failed MUT information for seed augmentation
                            // Use the same receiver type as in originalTypes for consistency
                            String fqcn = isStatic ? method.getDeclaringType().getQualifiedName()
                                    : originalTypes.get(0).getQualifiedName();
                            String fullMethodSignature = fqcn + "." + method.getSignature();
                            FailedMUT failedMUT = new FailedMUT(method, originalTypes.get(i), i, fullMethodSignature);
                            failedMUTs.add(failedMUT);

                            isValidMUT = false;
                            break;
                        } else {
                            // Seed augmentation이 비활성화된 경우: 간단히 스킵
                            isValidMUT = false;
                            break;
                        }
                    }
                }
                hashedInputPools.put(i, inputs);
            }

            if (isValidMUT) {
                // Use the same receiver type as in originalTypes for consistency
                String fqcn = isStatic ? method.getDeclaringType().getQualifiedName()
                        : originalTypes.get(0).getQualifiedName();
                String fullMethodSignature = fqcn + "." + method.getSignature();
                result.add(new MUTInput(invocation, originalTypes, hashedInputPools, fullMethodSignature));
            }
        }

        // 2. Public 생성자 처리 (Abstract/Interface CUT의 구현체 생성자 포함)
        // Reuse constructorsMap from above
        for (Set<CtConstructor<?>> constructors : constructorsMap.values()) {
            for (CtConstructor<?> constructor : constructors) {
                CtType<?> declaringType = constructor.getDeclaringType();

                // ⭐ Abstract 또는 Interface인 경우, 자신의 생성자는 건너뛰고 구현체들의 생성자만 MUTInput으로 생성
                if (declaringType.isAbstract() || declaringType.isInterface()) {
                    String fqcn = declaringType.getQualifiedName();
                    Map<String, List<CtTypeReference<?>>> abstractToImplsMap = ASTParser.abstractToImplsMap;

                    System.out.println("[INFO] Abstract/Interface CUT detected: " + fqcn
                            + " - skipping abstract constructor, searching for implementations...");

                    List<CtTypeReference<?>> implementations = abstractToImplsMap.get(fqcn);
                    if (implementations != null && !implementations.isEmpty()) {
                        for (CtTypeReference<?> implType : implementations) {
                            CtType<?> implClass = implType.getTypeDeclaration();

                            if (implClass == null || implClass.isAbstract()) {
                                continue;
                            }

                            // 구현체의 생성자들 수집
                            List<CtConstructor<?>> implConstructors = implClass
                                    .getElements(new TypeFilter<>(CtConstructor.class));

                            for (CtConstructor<?> implConstructor : implConstructors) {
                                // 접근 가능한 생성자 처리
                                // public, protected (같은 패키지), 또는 package-private (같은 패키지)
                                boolean isAccessible = false;

                                if (implConstructor.isPublic()) {
                                    isAccessible = true;
                                } else if (!implConstructor.isPrivate()) {
                                    // protected 또는 package-private인 경우, 같은 패키지면 접근 가능
                                    isAccessible = isSamePackage(implConstructor, ASTParser.getPackageName());
                                }

                                if (isAccessible) {
                                    createConstructorMUTInput(implConstructor, result);
                                }
                            }
                        }
                    }
                    // ⭐ Abstract/Interface의 생성자는 MUTInput으로 만들지 않음 (직접 호출 불가)
                    continue;
                } else {
                    // 일반 클래스인 경우, 자신의 생성자로 MUTInput 생성
                    createConstructorMUTInput(constructor, result);
                }
            }
        }
        return result;
    }

    /**
     * Constructor를 MUTInput 객체로 변환하는 헬퍼 메서드
     * 
     * @param constructor 변환할 Constructor
     * @param result      MUTInput을 추가할 결과 Set
     */
    private static void createConstructorMUTInput(CtConstructor<?> constructor, Set<MUTInput> result) {
        try {
            CtConstructorCall<?> constructorCall = constructor.getFactory().createConstructorCall();
            constructorCall.setExecutable((CtExecutableReference) constructor.getReference());

            List<CtTypeReference> types = new ArrayList<>();
            types.add(null); // 생성자는 receiver가 없습니다.
            constructor.getParameters().forEach(p -> types.add(p.getType()));

            LinkedHashMap<Integer, List<Input>> hashedInputPools = new LinkedHashMap<>();
            for (int i = 0; i < types.size(); i++) {
                CtTypeReference type = types.get(i);
                List<Input> inputs = processInputPool(type, i == 0);
                hashedInputPools.put(i, inputs);
            }

            String declaringTypeName = constructor.getDeclaringType().getQualifiedName();
            MUTInput inst = new MUTInput(constructorCall, types, hashedInputPools,
                    declaringTypeName + "." + constructor.getSignature());
            result.add(inst);

            // System.out.println("[INFO] Created MUTInput for constructor: " +
            // declaringTypeName + "." + constructor.getSignature());
        } catch (Exception e) {
            System.err.println("[ERROR] Failed to create MUTInput for constructor: "
                    + constructor.getSignature() + " - " + e.getMessage());
        }
    }

    /**
     * Constructor가 targetPackage와 같은 패키지에 속하는지 확인
     * 
     * @param constructor   확인할 Constructor
     * @param targetPackage 대상 패키지명
     * @return 같은 패키지면 true
     */
    private static boolean isSamePackage(CtConstructor<?> constructor, String targetPackage) {
        CtType<?> declaringType = constructor.getDeclaringType();
        if (declaringType == null || declaringType.getPackage() == null) {
            return false;
        }
        String constructorPackage = declaringType.getPackage().getQualifiedName();
        return constructorPackage.equals(targetPackage);
    }

    public static CtTypeReference<?> findSuitableImplementation(CtTypeReference<?> abstractOrNonPublicType) {
        String typeName = abstractOrNonPublicType.getQualifiedName();

        // 1. 캐시를 먼저 확인합니다.
        if (suitableImplementationCache.containsKey(typeName)) {
            List<CtTypeReference<?>> cachedImplementations = suitableImplementationCache.get(typeName);
            if (cachedImplementations == null || cachedImplementations.isEmpty()) {
                return null;
            }
            Random rand = new Random();
            return cachedImplementations.get(rand.nextInt(cachedImplementations.size()));
        }

        // 2. 모든 잠재적 구현체 목록을 가져옵니다.
        List<CtTypeReference<?>> allImplementations = ASTParser.abstractToImplsMap.get(typeName);
        if (allImplementations == null || allImplementations.isEmpty()) {
            suitableImplementationCache.put(typeName, Collections.emptyList());
            return null;
        }

        // [핵심 로직] Pool에 아직 없는, 새로운 후보들만 담을 리스트
        List<CtTypeReference<?>> newCandidates = new ArrayList<>();

        String targetTestPackage = ASTParser.getPackageName();

        for (CtTypeReference<?> impl : allImplementations) {
            CtType<?> implDecl = impl.getTypeDeclaration();
            if (implDecl != null && !implDecl.isAbstract()) {
                String implPackageName = (implDecl.getPackage() != null) ? implDecl.getPackage().getQualifiedName()
                        : "";
                boolean isAccessible = implDecl.isPublic() || implPackageName.equals(targetTestPackage);

                if (isAccessible) {
                    // 이 구현체가 Pool에 이미 있는지 확인합니다.
                    if (CandidatePool.getVarTypeNamePool().containsKey(impl)) {

                        continue; // Pool에 이미 있으면 건너뜁니다.
                    } else {
                        // Pool에 없는 새로운 후보이므로 리스트에 추가합니다.

                        newCandidates.add(impl);
                    }
                }
            }
        }

        // 3. 최종 선택 및 캐싱
        CtTypeReference<?> chosenImplementation = null;
        if (!newCandidates.isEmpty()) {
            Random rand = new Random();
            chosenImplementation = newCandidates.get(rand.nextInt(newCandidates.size()));
        }

        // 캐시에는 "Pool에 없는 새로운 후보"들의 목록만 저장됩니다.
        suitableImplementationCache.put(typeName, newCandidates);

        return chosenImplementation;
    }

    /**
     * Get the topmost declaring type (most abstract) for a method.
     * This helps find the most general type that defines the method,
     * which is better for finding compatible receiver objects.
     * 
     * For example:
     * - NullPropertyPointer.createPath() -> NodePointer.createPath() if overridden
     */
    private static CtTypeReference<?> getTopmostDeclaringType(CtMethod<?> method) {
        CtTypeReference<?> currentType = method.getDeclaringType().getReference();

        try {
            CtType<?> typeDeclaration = method.getDeclaringType();

            // Check if this method overrides a parent method
            CtTypeReference<?> superClass = typeDeclaration.getSuperclass();
            while (superClass != null) {
                CtType<?> superTypeDecl = superClass.getTypeDeclaration();
                if (superTypeDecl == null)
                    break;

                // Check if parent has the same method
                for (CtMethod<?> parentMethod : superTypeDecl.getMethods()) {
                    if (methodSignaturesMatch(method, parentMethod)) {
                        currentType = superClass;
                        superClass = superTypeDecl.getSuperclass();
                        break;
                    }
                }

                // No matching method found in this parent
                if (currentType != superClass) {
                    break;
                }
            }

            // Also check interfaces, but prefer concrete classes over interfaces
            // Only use interface type if no concrete implementation was found
            CtTypeReference<?> interfaceType = null;
            for (CtTypeReference<?> iface : typeDeclaration.getSuperInterfaces()) {
                CtType<?> ifaceDecl = iface.getTypeDeclaration();
                if (ifaceDecl == null)
                    continue;

                for (CtMethod<?> ifaceMethod : ifaceDecl.getMethods()) {
                    if (methodSignaturesMatch(method, ifaceMethod)) {
                        // Keep the interface as backup, but don't override concrete class
                        if (interfaceType == null) {
                            interfaceType = iface;
                        }
                        break;
                    }
                }
            }
            // Only use interface type if current type is the original declaring type (no
            // concrete parent found)
            if (interfaceType != null && currentType.equals(method.getDeclaringType().getReference())) {
                currentType = method.getDeclaringType().getReference(); // Keep concrete class, not interface
            }
        } catch (Exception e) {
            // If anything fails, return the original declaring type
        }

        return currentType;
    }

    /**
     * Check if two methods have matching signatures (name and parameters)
     */
    private static boolean methodSignaturesMatch(CtMethod<?> method1, CtMethod<?> method2) {
        if (!method1.getSimpleName().equals(method2.getSimpleName())) {
            return false;
        }

        if (method1.getParameters().size() != method2.getParameters().size()) {
            return false;
        }

        for (int i = 0; i < method1.getParameters().size(); i++) {
            String type1 = method1.getParameters().get(i).getType().getQualifiedName();
            String type2 = method2.getParameters().get(i).getType().getQualifiedName();
            if (!type1.equals(type2)) {
                return false;
            }
        }

        return true;
    }

    /**
     * 주어진 타입에 대한 입력 풀을 반환하는 공개 메서드
     * RecursiveTestCaseGenerator에서 리터럴 대체에 사용
     * 
     * @param type 조회할 타입
     * @return 해당 타입의 입력값 목록
     */
    public static List<Input> getInputPoolForType(CtTypeReference type) {
        if (type == null) {
            return new ArrayList<>();
        }
        // receiver가 아닌 일반 파라미터로 처리
        return processInputPool(type, false);
    }

    private static List<Input> processInputPool(CtTypeReference type, boolean isReceiverObject) {
        List<Input> allFoundInputs = new ArrayList<>();

        if (isReceiverObject && type == null) {
            allFoundInputs.add(new Input(true));
            return allFoundInputs;
        }
        if (type == null) {
            return allFoundInputs;
        }

        // Special handling for Class<?> - all Class instances in pool are valid
        if (isClassType(type)) {
            return getAllClassInstancesFromPool();
        }

        // Check cache first for performance
        String typeCacheKey = type.getQualifiedName() + "_" + isReceiverObject;
        if (inputPoolResultCache.containsKey(typeCacheKey)) {
            return new ArrayList<>(inputPoolResultCache.get(typeCacheKey));
        }

        HashMap<CtTypeReference, Set<Pair<CtTypeReference, CtElement>>> pairsMap = CandidatePool.getVarTypeNamePool();
        HashMap<Pair<CtTypeReference, CtElement>, Set<List<CtElement>>> pairsToInputMap = CandidatePool
                .getVartypeToInputPool();
        HashMap<CtTypeReference, Set<CtElement>> directValuesMap = CandidatePool.getDirectToValues();

        // --- [캐싱된 타입 수집: 모든 호환 가능한 타입을 수집] ---
        Set<CtTypeReference<?>> typesToSearch = getTypesToSearch(type);

        // 수집된 모든 호환 타입에 대해 Pool을 검색하여 결과를 allFoundInputs에 누적
        for (CtTypeReference<?> currentType : typesToSearch) {
            if (isObjectType(type) && isPrimitiveOrString(currentType))
                continue;
            // 리터럴 값 처리
            if (directValuesMap.containsKey(currentType)) {
                Set<List<CtElement>> converted = convertPrimitiveStructure(directValuesMap.get(currentType));
                allFoundInputs.addAll(fillInputStructure(converted, type));
            }

            // 변수(객체) 처리
            for (Map.Entry<CtTypeReference, Set<Pair<CtTypeReference, CtElement>>> entry : pairsMap.entrySet()) {
                if (areTypesCompatible(entry.getKey(), currentType)) {
                    Set<Pair<CtTypeReference, CtElement>> pairs = entry.getValue();
                    for (Pair<CtTypeReference, CtElement> pair : pairs) {
                        if (areTypesCompatible(pair.getKey(), type)) {
                            Set<List<CtElement>> inputSet = pairsToInputMap.get(pair);

                            // [핵심 수정] Position 0 (리시버 객체)인 경우, null 초기화 객체는 제외
                            if (isReceiverObject && inputSet != null) {
                                // null 초기화 statement들을 필터링
                                Set<List<CtElement>> filteredInputSet = new HashSet<>();
                                for (List<CtElement> input : inputSet) {
                                    if (!isNullInitialization(input)) {
                                        filteredInputSet.add(input);
                                    }
                                }
                                allFoundInputs
                                        .addAll(fillInputStructure(filteredInputSet, pair.getKey(), pair.getValue()));
                            } else {
                                // Position이 0이 아니거나 일반 처리
                                allFoundInputs.addAll(fillInputStructure(inputSet, pair.getKey(), pair.getValue()));
                            }
                        }
                    }
                }
            }
        }

        // Aggressive search only if nothing found
        int initialSize = allFoundInputs.size();
        if (initialSize == 0) {
            for (Map.Entry<CtTypeReference, Set<Pair<CtTypeReference, CtElement>>> entry : pairsMap.entrySet()) {
                CtTypeReference<?> poolType = entry.getKey();
                if (isAssignableFrom(type, poolType)) {
                    Set<Pair<CtTypeReference, CtElement>> pairs = entry.getValue();
                    for (Pair<CtTypeReference, CtElement> pair : pairs) {
                        Set<List<CtElement>> inputSet = pairsToInputMap.get(pair);

                        // [핵심 수정] Position 0 (리시버 객체)인 경우, null 초기화 객체는 제외
                        if (isReceiverObject && inputSet != null) {
                            // null 초기화 statement들을 필터링
                            Set<List<CtElement>> filteredInputSet = new HashSet<>();
                            for (List<CtElement> input : inputSet) {
                                if (!isNullInitialization(input)) {
                                    filteredInputSet.add(input);
                                }
                            }
                            allFoundInputs.addAll(fillInputStructure(filteredInputSet, pair.getKey(), pair.getValue()));
                        } else {
                            // Position이 0이 아니거나 일반 처리
                            allFoundInputs.addAll(fillInputStructure(inputSet, pair.getKey(), pair.getValue()));
                        }
                    }
                }
            }
        }

        // [개선] Shuffle the input pool to avoid always selecting the same input at index
        // 0
        // This ensures variety in combinatorial test generation
        if (!allFoundInputs.isEmpty()) {
            // [디버깅] 섞기 전 Input 리스트 정보 출력
            StringBuilder beforeShuffle = new StringBuilder();
            for (int i = 0; i < Math.min(3, allFoundInputs.size()); i++) {
                if (i > 0)
                    beforeShuffle.append(", ");
                beforeShuffle.append(i).append(":").append(allFoundInputs.get(i).getInput().size()).append("elems");
            }
            if (allFoundInputs.size() > 3)
                beforeShuffle.append(", ...");

            int sizeBeforeShuffle = allFoundInputs.size();
            Collections.shuffle(allFoundInputs);

            // [디버깅] 섞은 후 Input 리스트 정보 출력
            StringBuilder afterShuffle = new StringBuilder();
            for (int i = 0; i < Math.min(3, allFoundInputs.size()); i++) {
                if (i > 0)
                    afterShuffle.append(", ");
                afterShuffle.append(i).append(":").append(allFoundInputs.get(i).getInput().size()).append("elems");
            }
            if (allFoundInputs.size() > 3)
                afterShuffle.append(", ...");

            // System.out.println("[InputPool] Type: " + type.getQualifiedName() + " |
            // isReceiver: " + isReceiverObject + " | Size: " + sizeBeforeShuffle);
            // System.out.println(" Before shuffle: " + beforeShuffle);
            // System.out.println(" After shuffle: " + afterShuffle);
        }

        // Cache the result for future use
        inputPoolResultCache.put(typeCacheKey, new ArrayList<>(allFoundInputs));

        return allFoundInputs;
    }

    /**
     * Get all types to search for a given type (cached for performance)
     */
    private static Set<CtTypeReference<?>> getTypesToSearch(CtTypeReference<?> type) {
        String typeKey = type.getQualifiedName();

        // Check cache first
        if (typesToSearchCache.containsKey(typeKey)) {
            return new HashSet<>(typesToSearchCache.get(typeKey));
        }

        Set<CtTypeReference<?>> typesToSearch = new HashSet<>();
        typesToSearch.add(type); // 원본 타입

        // 1. Primitive wrapper types 처리 (int ↔ Integer)
        CtTypeReference<?> wrapperType = getPrimitiveWrapperEquivalent(type);
        if (wrapperType != null) {
            typesToSearch.add(wrapperType);
        }

        // 2. abstractToImplsMap: 이 타입의 모든 구체적인 구현체/하위 클래스 추
        List<CtTypeReference<?>> implementations = ASTParser.abstractToImplsMap.get(typeKey);
        if (implementations != null) {
            for (CtTypeReference<?> impl : implementations) {
                if (isObjectType(type) && isPrimitiveOrString(impl))
                    continue; // ★ 추가
                typesToSearch.add(impl);
            }
        }

        // 3. Reverse lookup
        for (Map.Entry<String, List<CtTypeReference<?>>> entry : ASTParser.abstractToImplsMap.entrySet()) {
            List<CtTypeReference<?>> impls = entry.getValue();
            if (impls != null && impls.stream().anyMatch(impl -> areTypesCompatible(impl, type))) {
                for (CtTypeReference<?> impl : impls) {
                    if (isObjectType(type) && isPrimitiveOrString(impl))
                        continue; // ★ 추가
                    typesToSearch.add(impl);
                }
            }
        }

        // 4. Common super types (Object, Collection interfaces, etc.)
        if (isCommonSuperType(type)) {
            addCompatibleTypesFromPool(type, typesToSearch, CandidatePool.getVarTypeNamePool());
        }

        // 5. Array type 처리: String[] ↔ String 등
        if (type.isArray()) {
            try {
                CtTypeReference<?> componentType = ((spoon.reflect.reference.CtArrayTypeReference<?>) type)
                        .getComponentType();
                if (componentType != null) {
                    typesToSearch.add(componentType);
                }
            } catch (ClassCastException e) {
                // Ignore
            }
        }

        // Cache the result
        typesToSearchCache.put(typeKey, new HashSet<>(typesToSearch));

        return typesToSearch;
    }

    /**
     * For those arguments that have variable name.
     * In this case,
     *
     * @param inputs
     * @param type
     * @param varName
     * @return
     */
    private static List<Input> fillInputStructure(Set<List<CtElement>> inputs, CtTypeReference type,
            CtElement varName) {
        List<Input> result = new ArrayList<>();
        for (List<CtElement> input : inputs) {
            // Use the actual type of the variable if available (for better type
            // information)
            CtTypeReference<?> actualType = type;
            if (varName instanceof spoon.reflect.reference.CtVariableReference) {
                CtTypeReference<?> varType = ((spoon.reflect.reference.CtVariableReference<?>) varName).getType();
                if (varType != null) {
                    actualType = varType;
                }
            } else if (varName instanceof spoon.reflect.declaration.CtVariable) {
                CtTypeReference<?> varType = ((spoon.reflect.declaration.CtVariable<?>) varName).getType();
                if (varType != null) {
                    actualType = varType;
                }
            }

            Input inst = new Input(actualType, true, varName, input);
            result.add(inst);
        }
        return result;
    }

    /**
     * For those arguments that do not have variable name
     *
     * @param inputs
     * @param type
     * @return
     */
    private static List<Input> fillInputStructure(Set<List<CtElement>> inputs, CtTypeReference type) {
        List<Input> result = new ArrayList<>();

        for (List<CtElement> input : inputs) {
            CtElement directValue = null;
            if (input.size() == 1) {
                directValue = input.get(0);
            } else {
                System.err
                        .println("InputCombination.fillInputStructure: for directValue, input size should be 1. Type: "
                                + type + ", Input: " + input);
                continue;
            }
            Input inst = new Input(type, false, directValue, input);
            result.add(inst);
        }
        return result;
    }

    private static Set<List<CtElement>> convertPrimitiveStructure(Set<CtElement> elements) {
        Set<List<CtElement>> results = new HashSet<>();
        for (CtElement e : elements) {
            List<CtElement> list = new ArrayList<>();
            list.add(e);
            results.add(list);
        }
        return results;
    }

    /**
     * Attempts to find fallback inputs for a parameter type by searching through
     * MUTnameToArgtypes
     * for methods with matching method names that have compatible parameter types
     * at the same position.
     * 
     * @param targetMethod  The method we're trying to generate inputs for
     * @param paramPosition The parameter position we need inputs for (0 = receiver,
     *                      1+ = parameters)
     * @param targetType    The type we need inputs for
     * @return List of Input objects found from matching MUTs, or empty list if none
     *         found
     */
    private List<Input> findFallbackInputsFromMUTPool(CtMethod<?> targetMethod, int paramPosition,
            CtTypeReference targetType) {
        List<Input> fallbackInputs = new ArrayList<>();

        try {
            HashMap<CtAbstractInvocation, Set<List<CtTypeReference>>> mutPool = CandidatePool.getMUTnameToArgtypes();

            if (mutPool == null || mutPool.isEmpty() || targetMethod == null || targetType == null) {
                return fallbackInputs;
            }

            String targetMethodName = targetMethod.getSimpleName();
            if (targetMethodName == null) {
                return fallbackInputs;
            }

            // Search through all MUTs in the pool
            for (Map.Entry<CtAbstractInvocation, Set<List<CtTypeReference>>> entry : mutPool.entrySet()) {
                if (entry.getKey() == null || entry.getValue() == null) {
                    continue;
                }

                CtAbstractInvocation candidateMUT = entry.getKey();
                Set<List<CtTypeReference>> argTypeSets = entry.getValue();

                // Check if the method names match
                String candidateMethodName = extractMethodName(candidateMUT);
                if (candidateMethodName == null || !targetMethodName.equals(candidateMethodName)) {
                    continue;
                }

                // For each argument type list in this MUT
                for (List<CtTypeReference> argTypes : argTypeSets) {
                    // Check if this MUT has the same parameter position and the types are
                    // compatible
                    if (paramPosition < argTypes.size()) {
                        CtTypeReference candidateType = argTypes.get(paramPosition);

                        // Check if types are compatible (same type or candidate type is assignable to
                        // target type)
                        if (candidateType != null && areTypesCompatible(candidateType, targetType)) {
                            // Try to find inputs for this compatible type
                            List<Input> compatibleInputs = processInputPool(candidateType, paramPosition == 0);
                            if (!compatibleInputs.isEmpty()) {
                                // Convert the inputs to match our target type
                                for (Input input : compatibleInputs) {
                                    Input convertedInput = convertInputType(input, targetType);
                                    if (convertedInput != null) {
                                        fallbackInputs.add(convertedInput);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        } catch (Exception e) {
            System.err.println("[ERROR] Exception in findFallbackInputsFromMUTPool: " + e.getMessage());
            // e.printStackTrace();
            return fallbackInputs;
        }

        // Remove duplicates while preserving order
        return fallbackInputs.stream().distinct().collect(Collectors.toList());
    }

    /**
     * Extracts method name from a CtAbstractInvocation
     */
    private String extractMethodName(CtAbstractInvocation invocation) {
        if (invocation == null) {
            return "UNKNOWN";
        }

        try {
            if (invocation instanceof CtInvocation) {
                CtInvocation<?> inv = (CtInvocation<?>) invocation;
                if (inv.getExecutable() != null && inv.getExecutable().getSimpleName() != null) {
                    return inv.getExecutable().getSimpleName();
                }
            } else if (invocation instanceof CtConstructorCall) {
                CtConstructorCall<?> conCall = (CtConstructorCall<?>) invocation;
                if (conCall.getExecutable() != null &&
                        conCall.getExecutable().getDeclaringType() != null &&
                        conCall.getExecutable().getDeclaringType().getSimpleName() != null) {
                    return conCall.getExecutable().getDeclaringType().getSimpleName();
                }
            }
        } catch (Exception e) {
            // Log the error but don't fail completely
            System.err.println("[WARN] Error extracting method name from invocation: " + e.getMessage() +
                    " | Invocation type: " + (invocation != null ? invocation.getClass().getSimpleName() : "null"));
            return "UNKNOWN";
        }

        // Fallback - try to get toString safely
        try {
            String fallback = invocation.toString();
            return fallback != null ? fallback : "UNKNOWN";
        } catch (Exception e) {
            System.err.println("[WARN] Even toString() failed for invocation: " + e.getMessage());
            return "UNKNOWN";
        }
    }

    /**
     * Checks if two types are compatible (same type or assignable)
     */
    private static boolean areTypesCompatible(CtTypeReference candidateType, CtTypeReference targetType) {
        if (candidateType == null || targetType == null) {
            return false;
        }

        // For generic types, we need to check both the raw type and type arguments
        if (candidateType.getActualTypeArguments() != null && !candidateType.getActualTypeArguments().isEmpty() ||
                targetType.getActualTypeArguments() != null && !targetType.getActualTypeArguments().isEmpty()) {

            // Check if raw types are compatible (exact match or inheritance)
            if (!candidateType.getQualifiedName().equals(targetType.getQualifiedName())) {
                // If not exact match, check inheritance relationship
                try {
                    if (!candidateType.isSubtypeOf(targetType)) {
                        return false;
                    }
                } catch (Exception e) {
                    // If subtype checking fails, not compatible
                    return false;
                }
            }

            // Check if both have type arguments
            List<CtTypeReference<?>> candidateArgs = candidateType.getActualTypeArguments();
            List<CtTypeReference<?>> targetArgs = targetType.getActualTypeArguments();

            // If one has type arguments and the other doesn't, they're not compatible
            if ((candidateArgs == null || candidateArgs.isEmpty()) != (targetArgs == null || targetArgs.isEmpty())) {
                return false;
            }

            // If both have type arguments, they must match
            if (candidateArgs != null && targetArgs != null &&
                    candidateArgs.size() == targetArgs.size()) {
                for (int i = 0; i < candidateArgs.size(); i++) {
                    if (!areTypesCompatible(candidateArgs.get(i), targetArgs.get(i))) {
                        return false;
                    }
                }
                return true;
            }

            // If type arguments don't match in size, not compatible
            return false;
        }

        // Exact match for non-generic types
        if (candidateType.getQualifiedName().equals(targetType.getQualifiedName())) {
            return true;
        }

        // Object type cannot be used where a specific type is expected
        // candidateType=Object, targetType=SerializedString → false (Object cannot be
        // converted to SerializedString)
        // candidateType=SerializedString, targetType=Object → true (SerializedString
        // can be used as Object)
        if ("java.lang.Object".equals(candidateType.getQualifiedName()) &&
                !targetType.isPrimitive() &&
                !"java.lang.Object".equals(targetType.getQualifiedName())) {
            return false;
        }

        // Check if candidate type is a subtype of target type
        try {
            return candidateType.isSubtypeOf(targetType);
        } catch (Exception e) {
            // If subtype checking fails, fall back to simple name comparison
            return candidateType.getSimpleName().equals(targetType.getSimpleName());
        }
    }

    /**
     * Converts an Input object to match a different target type
     */
    private static Input convertInputType(Input originalInput, CtTypeReference targetType) {
        if (originalInput == null) {
            return null;
        }

        // Create a new Input with the target type but keeping the same variable name
        // and input sequence
        if (originalInput.isVar()) {
            return new Input(targetType, true, originalInput.getVarName(), originalInput.getInput());
        } else {
            // --- [핵심 수정: 잘못된 메소드 호출 수정] ---
            // originalInput.getDirectValue() -> originalInput.getVarName()
            return new Input(targetType, false, originalInput.getVarName(), originalInput.getInput());
        }
    }

    /**
     * Checks if the given type is a common super type that should match with its
     * implementations
     */
    private static boolean isCommonSuperType(CtTypeReference<?> type) {
        if (type == null)
            return false;

        String typeName = type.getQualifiedName();

        // Check exact matches for common super types
        if (COMMON_SUPER_TYPES.contains(typeName)) {
            return true;
        }

        // Check patterns for java standard library types
        return typeName.startsWith("java.util.") ||
                typeName.startsWith("java.lang.") ||
                typeName.startsWith("java.io.");
    }

    /**
     * Get primitive wrapper equivalent type (int ↔ Integer, boolean ↔ Boolean,
     * etc.)
     */
    private static CtTypeReference<?> getPrimitiveWrapperEquivalent(CtTypeReference<?> type) {
        if (type == null)
            return null;

        String typeName = type.getQualifiedName();
        Launcher launcher = new Launcher();
        spoon.reflect.factory.Factory factory = launcher.getFactory();

        // Primitive to Wrapper
        switch (typeName) {
            case "int":
                return factory.Type().createReference(Integer.class);
            case "long":
                return factory.Type().createReference(Long.class);
            case "short":
                return factory.Type().createReference(Short.class);
            case "byte":
                return factory.Type().createReference(Byte.class);
            case "float":
                return factory.Type().createReference(Float.class);
            case "double":
                return factory.Type().createReference(Double.class);
            case "boolean":
                return factory.Type().createReference(Boolean.class);
            case "char":
                return factory.Type().createReference(Character.class);
        }

        // Wrapper to Primitive
        switch (typeName) {
            case "java.lang.Integer":
                return factory.Type().createReference(int.class);
            case "java.lang.Long":
                return factory.Type().createReference(long.class);
            case "java.lang.Short":
                return factory.Type().createReference(short.class);
            case "java.lang.Byte":
                return factory.Type().createReference(byte.class);
            case "java.lang.Float":
                return factory.Type().createReference(float.class);
            case "java.lang.Double":
                return factory.Type().createReference(double.class);
            case "java.lang.Boolean":
                return factory.Type().createReference(boolean.class);
            case "java.lang.Character":
                return factory.Type().createReference(char.class);
        }

        return null;
    }

    /**
     * Check if targetType can accept poolType (poolType is assignable to
     * targetType)
     * Returns true if poolType is a subtype of targetType
     */
    private static boolean isAssignableFrom(CtTypeReference<?> targetType, CtTypeReference<?> poolType) {
        if (targetType == null || poolType == null)
            return false;

        // Array types must match exactly (String[] != String)
        if (targetType.isArray() != poolType.isArray()) {
            return false;
        }

        // For array types, check component type compatibility
        if (targetType.isArray() && poolType.isArray()) {
            try {
                CtArrayTypeReference<?> targetArray = (CtArrayTypeReference<?>) targetType;
                CtArrayTypeReference<?> poolArray = (CtArrayTypeReference<?>) poolType;
                return areTypesCompatible(targetArray.getComponentType(), poolArray.getComponentType());
            } catch (Exception e) {
                return targetType.getQualifiedName().equals(poolType.getQualifiedName());
            }
        }

        // Same type
        if (areTypesCompatible(targetType, poolType)) {
            return true;
        }

        // Check if poolType is in the implementations of targetType (subtype)
        List<CtTypeReference<?>> impls = ASTParser.abstractToImplsMap.get(targetType.getQualifiedName());
        if (impls != null && impls.stream().anyMatch(impl -> areTypesCompatible(impl, poolType))) {
            return true;
        }

        // Check primitive wrapper compatibility
        CtTypeReference<?> targetWrapper = getPrimitiveWrapperEquivalent(targetType);
        if (targetWrapper != null && areTypesCompatible(targetWrapper, poolType)) {
            return true;
        }

        // targetType이 Object면, 모든 참조 타입 할당 가능
        if ("java.lang.Object".equals(targetType.getQualifiedName()) && !poolType.isPrimitive()) {
            if ("java.lang.String".equals(poolType.getQualifiedName()))
                return false;
            return true;
        }

        // poolType이 Object면, targetType에 할당 불가능 (더 구체적인 타입 필요)
        // 예: SerializedString이 필요한데 Object는 사용 불가
        if ("java.lang.Object".equals(poolType.getQualifiedName()) && !targetType.isPrimitive()) {
            return false;
        }

        return false;
    }

    /**
     * Adds compatible types from the pool for common super types
     */
    private static void addCompatibleTypesFromPool(CtTypeReference<?> targetType,
            Set<CtTypeReference<?>> typesToSearch,
            HashMap<CtTypeReference, Set<Pair<CtTypeReference, CtElement>>> pairsMap) {

        // For Object type, add all non-primitive types from the pool
        if ("java.lang.Object".equals(targetType.getQualifiedName())) {
            for (CtTypeReference<?> poolType : pairsMap.keySet()) {
                if (!isPrimitiveOrString(poolType)) { // ★ Object일 때만 primitive/String 제외
                    typesToSearch.add(poolType);
                }
            }
            return;
        }

        // For other common super types, check actual inheritance relationships
        for (CtTypeReference<?> poolType : pairsMap.keySet()) {
            try {
                // Use the improved areTypesCompatible method for generic types
                if (areTypesCompatible(poolType, targetType)) {
                    typesToSearch.add(poolType);
                }
            } catch (Exception e) {
                // If inheritance checking fails, skip this type
                continue;
            }
        }
    }

    private static boolean isPrimitiveOrString(CtTypeReference<?> t) {
        if (t == null)
            return false;
        if (t.isPrimitive())
            return true;
        return "java.lang.String".equals(t.getQualifiedName());
    }

    private static boolean isObjectType(CtTypeReference<?> t) {
        return t != null && "java.lang.Object".equals(t.getQualifiedName());
    }

    /**
     * Infer the actual type of a parameter from its usage in the method body
     * Example: parameter "Object object" but body has "(NodePointer) object" ->
     * infer NodePointer
     * 
     * @param method       The method to analyze
     * @param paramIndex   The parameter index to analyze
     * @param declaredType The declared parameter type
     * @return The inferred actual type, or null if cannot infer
     */
    private static CtTypeReference<?> inferParameterActualType(CtMethod<?> method, int paramIndex,
            CtTypeReference<?> declaredType) {
        if (method == null || method.getBody() == null || paramIndex < 0
                || paramIndex >= method.getParameters().size()) {
            return null;
        }

        String paramName = method.getParameters().get(paramIndex).getSimpleName();
        String bodyStr = method.getBody().toString();

        // Look for all occurrences of pattern like "(SomeType) paramName"
        String pattern = "(" + paramName + ")";
        int index = bodyStr.indexOf(pattern);

        while (index > 0) {
            // Look backwards to find the cast type
            int castStart = index - 1;
            while (castStart >= 0 && bodyStr.charAt(castStart) == ' ') {
                castStart--;
            }

            // Find the opening paren of the cast
            int parenPos = castStart;
            while (parenPos >= 0 && bodyStr.charAt(parenPos) != '(') {
                parenPos--;
            }

            if (parenPos >= 0) {
                // Extract the cast type name - remove trailing whitespace and closing paren
                String castTypeStr = bodyStr.substring(parenPos + 1, index).trim();

                // Remove closing paren if present
                if (castTypeStr.endsWith(")")) {
                    castTypeStr = castTypeStr.substring(0, castTypeStr.length() - 1).trim();
                }

                if (!castTypeStr.isEmpty() && !castTypeStr.contains("(")) {
                    // Try to resolve the cast type name to a CtTypeReference
                    try {
                        CtType<?> declaringType = method.getDeclaringType();
                        if (declaringType != null && declaringType.getFactory() != null) {
                            CtType<?> castTypeDecl = declaringType.getFactory().Type().get(castTypeStr);
                            if (castTypeDecl != null) {
                                CtTypeReference<?> castType = castTypeDecl.getReference();
                                return castType;
                            }
                        }
                    } catch (Exception e) {
                        // Ignore resolution errors
                    }
                }
            }

            // Look for next occurrence
            index = bodyStr.indexOf(pattern, index + 1);
        }

        return null;
    }

    /**
     * Check if the given type is java.lang.Class or Class<?>
     */
    private static boolean isClassType(CtTypeReference<?> type) {
        if (type == null)
            return false;
        String typeName = type.getQualifiedName();
        return "java.lang.Class".equals(typeName);
    }

    /**
     * Get all Class instances from the candidate pool
     * For Class<?> parameters, any Class instance is valid (e.g., String.class,
     * Integer.class, etc.)
     * Priority: direct Class values > explicit Class<?> variables > generated
     * .class references
     */
    private static List<Input> getAllClassInstancesFromPool() {
        List<Input> result = new ArrayList<>();
        HashMap<CtTypeReference, Set<Pair<CtTypeReference, CtElement>>> pairsMap = CandidatePool.getVarTypeNamePool();
        HashMap<Pair<CtTypeReference, CtElement>, Set<List<CtElement>>> pairsToInputMap = CandidatePool
                .getVartypeToInputPool();
        HashMap<CtTypeReference, Set<CtElement>> directToValues = CandidatePool.getDirectToValues();
        Launcher launcher = new Launcher();
        spoon.reflect.factory.Factory factory = launcher.getFactory();
        CtTypeReference<?> classType = factory.Type().createReference("java.lang.Class");

        // Priority 1: Check DirectToValues for Class type (contains Void.class,
        // String.class, etc. from augmentation)
        if (directToValues.containsKey(classType)) {
            Set<CtElement> classValues = directToValues.get(classType);
            for (CtElement classValue : classValues) {
                try {
                    Input classInput = new Input(classType, false, classValue, null);
                    result.add(classInput);
                } catch (Exception e) {
                    // Ignore if we can't create the input
                }
            }
        }

        // Priority 2: Find explicit Class<?> variables in the pool
        for (Map.Entry<CtTypeReference, Set<Pair<CtTypeReference, CtElement>>> entry : pairsMap.entrySet()) {
            CtTypeReference<?> poolType = entry.getKey();

            // Check if this is a Class type
            if (isClassType(poolType)) {
                Set<Pair<CtTypeReference, CtElement>> pairs = entry.getValue();
                for (Pair<CtTypeReference, CtElement> pair : pairs) {
                    Set<List<CtElement>> inputSet = pairsToInputMap.get(pair);
                    if (inputSet != null) {
                        result.addAll(fillInputStructure(inputSet, pair.getKey(), pair.getValue()));
                    }
                }
            }
        }

        // Priority 3: Generate .class references from all types in pool
        // For example: String.class, Integer.class, List.class, etc.
        if (result.isEmpty()) {
            @SuppressWarnings("unchecked")
            Set<CtTypeReference<?>> typesInPool = new HashSet<>((Set) pairsMap.keySet());

            // Sort to prioritize common types like String, Integer, List, etc.
            List<CtTypeReference<?>> sortedTypes = new ArrayList<>(typesInPool);
            sortedTypes.sort((a, b) -> {
                String aName = a.getQualifiedName();
                String bName = b.getQualifiedName();

                // Common types get priority
                boolean aIsCommon = isCommonType(aName);
                boolean bIsCommon = isCommonType(bName);

                if (aIsCommon && !bIsCommon)
                    return -1;
                if (!aIsCommon && bIsCommon)
                    return 1;
                return 0;
            });

            for (CtTypeReference<?> typeInPool : sortedTypes) {
                // Skip null types but include primitives and all object types
                if (typeInPool == null)
                    continue;

                // Create Input representing TypeName.class expression
                // Generate code like: String.class, Integer.class, etc.
                try {
                    CtTypeAccess<?> typeAccess = factory.createTypeAccess(typeInPool);
                    Input classInput = new Input(classType, false, typeAccess, null);
                    result.add(classInput);
                } catch (Exception e) {
                    // Ignore if we can't create the input
                }
            }
        }

        return result;
    }

    /**
     * Check if a type is a commonly used type (useful for test generation)
     */
    private static boolean isCommonType(String qualifiedName) {
        Set<String> commonTypes = new HashSet<>(Arrays.asList(
                "java.lang.String",
                "java.lang.Integer",
                "java.lang.Long",
                "java.lang.Double",
                "java.lang.Boolean",
                "java.lang.Object",
                "java.util.List",
                "java.util.ArrayList",
                "java.util.Map",
                "java.util.HashMap",
                "java.util.Set",
                "java.util.HashSet",
                "int",
                "long",
                "double",
                "boolean",
                "java.io.File"));
        return commonTypes.contains(qualifiedName);
    }

    /**
     * Check if a statement list represents null initialization (e.g., Object obj =
     * null)
     * This checks the last statement in the list to see if it initializes a
     * variable to null
     * 
     * @param stmtList The list of statements representing an initialization
     *                 sequence
     * @return true if the last statement initializes a variable to null, false
     *         otherwise
     */
    private static boolean isNullInitialization(List<CtElement> stmtList) {
        if (stmtList == null || stmtList.isEmpty()) {
            return false;
        }

        // Check the last statement
        CtElement lastElement = stmtList.get(stmtList.size() - 1);

        // Case 1: Variable declaration with null initialization (Object obj = null;)
        if (lastElement instanceof CtLocalVariable) {
            CtLocalVariable<?> localVar = (CtLocalVariable<?>) lastElement;
            CtExpression<?> defaultExpr = localVar.getDefaultExpression();

            if (defaultExpr != null) {
                String exprStr = defaultExpr.toString().trim();
                // Check if the default expression is literally "null"
                if ("null".equals(exprStr)) {
                    return true;
                }
            }
        }

        // Case 2: Assignment to null (obj = null;)
        if (lastElement instanceof CtAssignment) {
            CtAssignment<?, ?> assignment = (CtAssignment<?, ?>) lastElement;
            CtExpression<?> rightHandSide = assignment.getAssignment();

            if (rightHandSide != null) {
                String rhsStr = rightHandSide.toString().trim();
                // Check if the right-hand side is literally "null"
                if ("null".equals(rhsStr)) {
                    return true;
                }
            }
        }

        // Case 3: Check if all statements are variable declarations with no
        // initialization
        // (e.g., just "Object obj;" without assignment)
        if (stmtList.size() == 1 && lastElement instanceof CtLocalVariable) {
            CtLocalVariable<?> localVar = (CtLocalVariable<?>) lastElement;
            // Variable declared but not initialized (no default expression)
            if (localVar.getDefaultExpression() == null) {
                return true; // Uninitialized variable is treated as null initialization
            }
        }

        return false;
    }

}