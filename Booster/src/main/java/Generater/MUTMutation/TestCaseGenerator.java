package Generater.MUTMutation;

import RegressionOracles.Analyzer;
import RegressionOracles.ObserverInstrumenter;
import spoon.Launcher;
import spoon.reflect.CtModel;
import spoon.reflect.code.*;
import spoon.reflect.declaration.*;
import spoon.reflect.factory.Factory;
import spoon.reflect.reference.CtExecutableReference;
import spoon.reflect.reference.CtTypeReference;
import spoon.reflect.reference.CtVariableReference;
import spoon.reflect.reference.CtFieldReference;
import spoon.reflect.visitor.DefaultJavaPrettyPrinter;
import java.util.concurrent.TimeoutException;
import spoon.reflect.visitor.filter.TypeFilter;
import spoon.reflect.visitor.CtScanner;
import spoon.support.reflect.code.*;
import utils.Config;
import utils.Pair;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.lang.annotation.Annotation;
import java.util.*;

public class TestCaseGenerator {
    private InputCombinations inputCombinations;
    private String testClassName;
    private String packageAndImport;
    private List<CtClass<Object>> generatedTests;
    private List<CtClass<Object>> observerAddedTests = new ArrayList<>(); // only for regression mode
    private final Analyzer analyzer;
    private final ObserverInstrumenter collector;
    private final Random RANDOM = new Random();
    private Map<String, Integer> mutCountMap;
    private Set<CtMethod> testCases;
    private Map<Integer, Map<Integer, Set<Integer>>> picked_map = new HashMap<>();
    private Map<Integer, Integer> upperBounds = new HashMap<>();
    private Map<Integer, Set<List<Integer>>> results = new HashMap<>();
    private Launcher launcher;
    private Map<MUTInput, Set<List<Integer>>> usedCombinations = new HashMap<>();
    private Map<MUTInput, CombinationGenerator> combinationGenerators = new HashMap<>();// For Combinatorial Testing
                                                                                        // handles combination
                                                                                        // generators per MUT

    private static long overhead = 0;
    public static int duplicateCount = 0;
    private static final boolean DEBUG = false; // Debug flag for duplicate definition handling

    /**
     * init test case with input combinations
     */
    public TestCaseGenerator(String testFile, long startTime, List<String> baseTests) {
        inputCombinations = new InputCombinations();
        try {
            initInputCombinations(testFile, startTime, baseTests);
            testClassName = extractFileName(Config.TEST_FILE, ".java");
        } catch (TimeoutException e) {
            // e.printStackTrace();
        }
        getImportAndPackage(Config.TEST_FILE);
        generatedTests = new ArrayList<>();
        mutCountMap = new HashMap<>();
        launcher = new Launcher();
        analyzer = new Analyzer();
        collector = new ObserverInstrumenter(launcher.getFactory());
        
    }

    public long getOverhead() {
        return overhead;
    }

    public static CtAbstractInvocation getMUT(CtStatement lastStmt) {
        CtAbstractInvocation invoke = null;
        if (lastStmt instanceof CtInvocationImpl) {
            invoke = (CtInvocationImpl) lastStmt;
        } else if (lastStmt.getElements(new TypeFilter<>(CtInvocationImpl.class)).size() == 1) {
            invoke = lastStmt.getElements(new TypeFilter<>(CtInvocationImpl.class)).get(0);
        } else if (lastStmt instanceof CtConstructorCallImpl) {
            invoke = (CtConstructorCallImpl) lastStmt;
        } else if (lastStmt.getElements(new TypeFilter<>(CtConstructorCallImpl.class)).size() == 1) {
            invoke = lastStmt.getElements(new TypeFilter<>(CtConstructorCallImpl.class)).get(0);
        } else {
            return null;
        }
        return invoke;
    }

    private static CtStatement getLastMUTStatement(CtMethod testcase) {
        List<CtStatement> stmts = testcase.getBody().getStatements();
        return stmts.get(stmts.size() - 1);
    }

    public void initMap(int size) {
        for (int i = 0; i < size; i++) {
            picked_map.put(i, new HashMap<>());
            results.put(i, new HashSet<>());
        }
    }

    public Launcher getLauncher() {
        return launcher;
    }

    public List<CtClass<Object>> getObserverAddedTests() {
        return observerAddedTests;
    }

    public String getPackageAndImport() {
        return packageAndImport;
    }

    public String getTestClassName() {
        return testClassName;
    }

    public List<CtClass<Object>> getGeneratedTests() {
        return generatedTests;
    }

    public Set<CtMethod> getTestCases() {
        return testCases;
    }

    // Cache pruned inputs to avoid duplicate pruning
    private Set<MUTInput> cachedPrunedInputs = null;
    
     public Set<MUTInput> getMutInputs() {
         Set<MUTInput> originalMutInputs = inputCombinations.getMuts();
         // [수정] null 체크 - getMuts()가 null을 반환할 경우 빈 Set 반환
         if (originalMutInputs == null) {
             System.err.println("[WARNING] getMutInputs() returned null from InputCombinations");
             return new HashSet<>();
         }
         return originalMutInputs;
     }
    
    /**
     * Get original unpruned MUT inputs for analysis purposes
     */
    public Set<MUTInput> getOriginalMutInputs() {
        return inputCombinations.getMuts();
    }

    /**
     * Analyze combination explosion in current MUT inputs and candidate pool
     * This method provides detailed insights into potential performance bottlenecks
     * 
     * @return PoolAnalysisReport with comprehensive statistics
     */
    public CombinationAnalyzer.PoolAnalysisReport analyzeCombinationExplosion() {
        System.out.println("\n🔍 ANALYZING COMBINATION EXPLOSION FOR TEST CASE GENERATION...");
        
        // Always analyze original inputs for accurate explosion analysis
        Set<MUTInput> mutInputs = getOriginalMutInputs();
        CombinationAnalyzer.PoolAnalysisReport report = 
            CombinationAnalyzer.analyzeCombinationExplosion(mutInputs);
        
        // Print the comprehensive report
        report.printSummary();
        
        return report;
    }

    /**
     * Quick method to identify and print only the most problematic MUTs
     */
    public void printExplosiveMUTs() {
        Set<MUTInput> mutInputs = getOriginalMutInputs();
        CombinationAnalyzer.printExplosiveMUTs(mutInputs);
    }

    /**
     * Quick method to print average combinations statistics for all MUTs
     */
    public void printAverageStats() {
        Set<MUTInput> mutInputs = getOriginalMutInputs();
        CombinationAnalyzer.printAverageStats(mutInputs);
    }

    /**
     * Print detailed analysis for a specific MUT by method signature
     * 
     * @param methodSignature The method signature to analyze in detail
     */
    public void analyzeMUT(String methodSignature) {
        Set<MUTInput> mutInputs = getOriginalMutInputs();
        
        Optional<MUTInput> targetMUT = mutInputs.stream()
            .filter(mut -> mut.getMethodSignature().equals(methodSignature))
            .findFirst();
        
        if (targetMUT.isPresent()) {
            CombinationAnalyzer.printMUTDetails(targetMUT.get());
        } else {
            System.out.println("❌ MUT not found: " + methodSignature);
            System.out.println("Available MUTs:");
            mutInputs.stream()
                .map(MUTInput::getMethodSignature)
                .sorted()
                .limit(10)
                .forEach(sig -> System.out.println("   • " + sig));
        }
    }

    /**
     * get the import and package and set it as packageAndImport
     *
     * @param testFile
     */

    private void getImportAndPackage(String testFile) {
        try (BufferedReader bufferedReader = new BufferedReader(new FileReader(testFile))) {
            String line = null;
            StringBuilder sb = new StringBuilder();

            while ((line = bufferedReader.readLine()) != null) {
                String trimmed = line.trim();

                // 1) package 라인은 그대로 추가
                if (trimmed.startsWith("package ")) {
                    sb.append(line).append("\n");
                }
                // 2) import 라인
                else if (trimmed.startsWith("import ")) {
                    // (a) JUnit 3 import가 들어있으면 skip
                    if (trimmed.contains("junit.framework")) {
                        // do nothing (skip)
                    }
                    // 그 외 일반 import는 그대로 삽입
                    else {
                        sb.append(line).append("\n");
                    }
                }
            }

            // 3) JUnit 4 import 추가
            // 필요에 따라 원하는 어노테이션 / Assert / Before / After 등을 넣어도 됨
            sb.append("import java.lang.*;\n");
            sb.append("import org.junit.Test;\n");
            sb.append("import org.junit.Assert;\n");

            packageAndImport = sb.toString();
        } catch (Exception e) {
            // e.printStackTrace();
        }
    }

    private String extractFileName(String path, String ext) {
        String separator;
        if (System.getProperty("os.name").contains("Window")) {
            separator = "\\\\";
        } else
            separator = File.separator;
        String[] elements = path.split(separator);
        String lastEle = elements[elements.length - 1];
        return lastEle.substring(0, lastEle.length() - ext.length());
    }

    public Pair<CtClass, String> generateTest(MUTInput mutInput, int index, boolean allStacked) {
        LinkedHashMap<Integer, List<Input>> inputPools = mutInput.getInputs();
        Map<Integer, Set<Integer>> picked = picked_map.get(index);
        List<Integer> combi = new ArrayList<>();

        String gen_mode = Config.ASSEMBLE_MODE;
        // System.out.println("Current Combinatorial : " + gen_mode);

        long startTime = System.currentTimeMillis();
        // 각 파라미터 위치와 그 입력 풀의 크기를 저장

        if (mutInput.getSortedInputPools() == null) {
            mutInput.initSortedInputPools(inputPools);
        }
        int tWay = mutInput.getTWay();
        List<Map.Entry<Integer, List<Input>>> sortedInputPools = mutInput.getSortedInputPools();
        if (sortedInputPools == null) {
            if (DEBUG)
                System.out.println("[DEBUG] Sorted InputPool is null; returning null");
            return null;
        }

        // If there are no input pools (e.g., no parameters or all parameters have no inputs), skip test generation
        if (sortedInputPools.isEmpty()) {
            if (DEBUG)
                System.out.println("[DEBUG] No input pools available (sortedInputPools.size() = 0); returning null");
            return null;
        }
        
        if (tWay < 1) {
            if (DEBUG)
                System.out.println("[DEBUG] Issue with Tway: " + tWay + " is less than 1; returning null");
            return null;
        }
        
        // If tWay is greater than the number of parameters, adjust it to match
        if (tWay > sortedInputPools.size()) {
            if (DEBUG)
                System.out.println("[DEBUG] Tway: " + tWay + " > sortedInputPools.size(): "
                        + sortedInputPools.size() + "; adjusting tWay to " + sortedInputPools.size());
            tWay = sortedInputPools.size();
            mutInput.setTWay(tWay);
        }

        // 가장 큰 두 개의 입력 풀의 파라미터 위치를 가져옴
        List<Integer> largestPositions = new ArrayList<>();
        CombinationGenerator combiGenerator = combinationGenerators.get(mutInput);
        if (combiGenerator == null) {
            mutInput.initTwayCandidates();
            mutInput.setCurrentPositions(0);
            LinkedHashMap<Integer, List<Input>> selectedPools = new LinkedHashMap<>();
            for (Integer pos : mutInput.getCurrentPositions()) {
                if (mutInput.isStatic() && pos == 0) {
                    continue;
                }
                List<Input> pool = inputPools.get(pos);
                if (pool != null && !pool.isEmpty()) {
                    selectedPools.put(pos, pool);
                }
            }
            
            if (selectedPools.isEmpty()) {
                if (DEBUG)
                    System.out.println("[DEBUG] No valid input pools available for MUT: " + mutInput.getMethodSignature());
                return null;
            }
            
            int adjustedTWay = Math.min(mutInput.getTWay(), selectedPools.size());
            combiGenerator = new CombinationGenerator(selectedPools, adjustedTWay);
            combinationGenerators.put(mutInput, combiGenerator);
            mutInput.setIsFull(false);
        }

        // pair의 모든 조합을 다 소진했을 경우 다음 pair로 넘어가는 로직
        if (!combiGenerator.hasNext()) {
            if (!mutInput.getIsFull()) {
                mutInput.setIsFull(true);
                if (DEBUG)
                    System.out.println("[DEBUG] Used up all Combinations for current Tway; returning null");
                return null;
            } else {
                // 다음 t-Way 조합이 있는지 확인
                if (mutInput.getTotalTWayCandidates() <= 1) {
                    mutInput.setIsStacked(true);
                }
                boolean hasNextCombination = mutInput.setNextTWayCombination();
                if (!hasNextCombination) { // 다음 조합이 없는 경우
                    mutInput.setIsStacked(true);
                    if (allStacked) {
                        // System.out.println("Increasing Tway for : " + mutInput.getMethodSignature());
                        // 더 이상 현재 t-Way로 만들 수 있는 조합이 없음. tWay를 증가
                        int newTway = mutInput.getTWay() + 1;
                        if (newTway <= sortedInputPools.size()) {
                            mutInput.setTWay(newTway);
                            mutInput.initTwayCandidates();
                            mutInput.setIsStacked(false);
                            mutInput.setCurrentPositions(0);
                            LinkedHashMap<Integer, List<Input>> newSelectedPools = new LinkedHashMap<>();
                            for (Integer pos : mutInput.getCurrentPositions()) {
                                if (mutInput.isStatic() && pos == 0) {
                                    continue;
                                }
                                List<Input> pool = inputPools.get(pos);
                                if (pool != null && !pool.isEmpty()) {
                                    newSelectedPools.put(pos, pool);
                                }
                            }
                            if (newSelectedPools.isEmpty()) {
                                return null;
                            }
                            int adjustedNewTWay = Math.min(newTway, newSelectedPools.size());
                            combiGenerator = new CombinationGenerator(newSelectedPools, adjustedNewTWay);
                            combinationGenerators.put(mutInput, combiGenerator);
                        }
                    }
                    return null;
                }
                // 새로운 t-Way 조합으로 다시 CombinationGenerator를 만든다
                combinationGenerators.remove(mutInput);
                LinkedHashMap<Integer, List<Input>> newSelectedPools = new LinkedHashMap<>();
                for (Integer pos : mutInput.getCurrentPositions()) {
                    if (mutInput.isStatic() && pos == 0) {
                        continue;
                    }
                    List<Input> pool = inputPools.get(pos);
                    if (pool != null && !pool.isEmpty()) {
                        newSelectedPools.put(pos, pool);
                    }
                }
                if (newSelectedPools.isEmpty()) {
                    if (DEBUG)
                        System.out.println("[DEBUG] No valid pools for new tWay combination for MUT: " + mutInput.getMethodSignature());
                    return null;
                }
                int adjustedTWay = Math.min(mutInput.getTWay(), newSelectedPools.size());
                combiGenerator = new CombinationGenerator(newSelectedPools, adjustedTWay);
                combinationGenerators.put(mutInput, combiGenerator);
                if (!combiGenerator.hasNext()) {
                    if (DEBUG)
                        System.out.println(
                                "[DEBUG] After reinitializing CombinationGenerator, no combinations available; returning null");
                    return null;
                }
            }
        }

        // 생성가능한 조합이 아직 남아 있는 경우
        Map<Integer, Integer> combiMap = combiGenerator.nextCombination();
        if (combiMap == null) {
            if (DEBUG)
                System.out.println("[DEBUG] CombinationGenerator returned null combination map; returning null");
            return null;
        }
        if (combiMap != null) {
            if (DEBUG)
                System.out.println("[DEBUG] Attempting combination " + combiGenerator.getCurrentIndex() + " / " + combiGenerator.getTotalCombinations() + " for MUT: " + mutInput.getMethodSignature());
        }
        // combi 초기화
        for (int i = 0; i < inputPools.size(); i++) {
            combi.add(-1);
        }
        // 가장 큰 두 개의 파라미터 위치에 대해 조합 적용
        for (Map.Entry<Integer, Integer> entry : combiMap.entrySet()) {
            combi.set(entry.getKey(), entry.getValue());
        }
        for (Integer pos : inputPools.keySet()) {
            if (mutInput.getCurrentPositions().contains(pos)) {
                continue; // 이미 combiMap에서 결정된 위치
            }
            List<Input> pool = inputPools.get(pos);
            if (pool.isEmpty()) {
                // 해당 위치에 들어갈 Input이 없다면 -1 그대로 두고 넘어감 (컴파일 안될 수도 있으니 주의)
                continue;
            }
            int rndIdx = RANDOM.nextInt(pool.size());
            combi.set(pos, rndIdx);

        }

        // if (isDuplicate(mutInput, combi)) {
        //     duplicateCount++;
        //     return null;
        // }

        List<CtExpression> types = new LinkedList<>();
        List<Input> insertStmt = new ArrayList<>();
        CtAbstractInvocation invoke = null;
        CtAbstractInvocation mutInvo = mutInput.getMUTInvocation();
        if (mutInvo instanceof CtInvocationImpl) {
            invoke = (CtInvocationImpl) mutInvo.clone();
        } else if (mutInvo instanceof CtConstructorCallImpl) {
            invoke = (CtConstructorCallImpl) mutInvo.clone();
        }
        Input receiverObj = null;
        boolean isConstructor = (mutInvo instanceof CtConstructorCallImpl);
        boolean isStaticMethod = mutInput.isStatic();

         for (int i = 0; i < combi.size(); i++) {
             Input par;
             if (combi.get(i).equals(-1)) {
                 par = new Input(false);
             } else {
                 par = inputPools.get(i).get(combi.get(i));
                 String parType = par.getType() != null ? par.getType().getQualifiedName() : "null";
                //  System.out.println("[INPUT-SELECT] pos[" + i + "] selected: " + parType + " | pool size: " + inputPools.get(i).size());
             }

            if (i == 0) {
                if (isConstructor) {
                    if (par.isVar()) {
                        insertStmt.add(par);
                    }
                    try {
                        types.add((CtExpression) par.getVarName());
                    } catch (Exception e) {
                        CtExpression variableAccess = par.getVarName().getFactory().createVariableRead();
                        try {
                            ((CtVariableRead) variableAccess).setVariable((CtVariableReference) par.getVarName());
                        } catch (Exception gg) {
                            gg.printStackTrace();
                        }
                        types.add(variableAccess);
                    }
                    continue;
                } else if (isStaticMethod) {
                    types.add(null);
                    continue;
                } else {
                    if (par.isMUTStatic()) {
                        if (DEBUG)
                            System.out.println("[DEBUG] Instance method but position 0 has static placeholder; returning null");
                        return null;
                    }

                    if (par.isVar()) {
                        receiverObj = par;
                    } else {
                        String targetReceiverName = null;
                        if (mutInvo instanceof CtInvocation) {
                            CtInvocation<?> originalInvocation = (CtInvocation<?>) mutInvo;
                            CtExpression<?> receiverExpr = originalInvocation.getTarget();
                            if (receiverExpr instanceof CtVariableRead) {
                                targetReceiverName = ((CtVariableRead<?>) receiverExpr).getVariable().getSimpleName();
                            }
                        }

                        if (targetReceiverName != null) {
                            Input outcome = findReplacableInput(targetReceiverName, mutInput);
                            if (outcome != null) {
                                par = outcome;
                                receiverObj = par;
                            }
                        }
                    }
                }
            }

            if (i > 0 || (!isConstructor && !isStaticMethod)) {
                if (par.isVar()) {
                    insertStmt.add(par);
                }
                try {
                    types.add((CtExpression) par.getVarName());
                } catch (Exception e) {
                    // par.getVarName()이 CtExpression이 아닌 경우 처리
                    CtElement varElement = par.getVarName();
                    Factory factory = varElement.getFactory();
                    
                    if (varElement instanceof CtLocalVariable) {
                        // CtLocalVariable인 경우 변수명 스트링으로 코드 스니펫 생성
                        CtLocalVariable<?> localVar = (CtLocalVariable<?>) varElement;
                        String varName = localVar.getSimpleName();
                        CtExpression variableAccess = factory.Code().createCodeSnippetExpression(varName);
                        types.add(variableAccess);
                    } else if (varElement instanceof CtVariableReference) {
                        // CtVariableReference인 경우 변수명 추출하여 코드 스니펫 생성
                        CtVariableReference<?> varRef = (CtVariableReference<?>) varElement;
                        String varName = varRef.getSimpleName();
                        CtExpression variableAccess = factory.Code().createCodeSnippetExpression(varName);
                        types.add(variableAccess);
                    } else {
                        // 다른 타입의 경우 CtExpression으로 직접 캐스팅 시도
                        try {
                            types.add((CtExpression) varElement);
                        } catch (Exception gg) {
                            gg.printStackTrace();
                        }
                    }
                }
            }
        }
        RawTestCase testCase = new RawTestCase(insertStmt, types, invoke);
        
        if (!isStaticMethod && !isConstructor && receiverObj == null) {
            if (DEBUG)
                System.out.println("[DEBUG] Instance method but no receiver object found; returning null");
            return null;
        }
        
        if (receiverObj != null && invoke instanceof CtInvocationImpl) {
            CtElement var = receiverObj.getVarName();

            // Null 체크
            if (var == null) {
                if (DEBUG)
                    System.out.println("[DEBUG] Receiver object variable is null; returning null");
                return null;
            }

            // 타입 캐스팅 체크
            if (isVarTypeCased(var)) {
                if (DEBUG)
                    System.out.println("[DEBUG] Receiver object variable type is casted; returning null");
                return null;
            }

            Factory factory = var.getFactory();
            CtInvocationImpl invocation = (CtInvocationImpl) invoke;
            CtVariableReference<?> varRef;
            if (var instanceof CtVariableReference) {
                varRef = (CtVariableReference<?>) var;
            } else if (var instanceof CtLiteralImpl) {
                String varName = ((CtLiteralImpl<?>) var).getValue().toString();
                if (DEBUG)
                    System.out.println("[DEBUG] varName from CtLiteralImpl: " + varName);
                varRef = factory.createLocalVariableReference();
                varRef.setSimpleName(varName);
            } else {
                if (DEBUG)
                    System.out.println("[DEBUG] Unexpected var type: " + var.getClass().getName() + "; returning null");
                return null;
            }
            CtVariableReadImpl variableRead = (CtVariableReadImpl) factory.createVariableRead();
            variableRead.setVariable(varRef);
            invocation.setTarget(variableRead);
        }

        List<CtStatement> stmts = null;
        try {
            stmts = processMutate2(testCase);
        } catch (Exception e) {
            if (DEBUG)
                System.out.println("[DEBUG] Exception in processMutate2: " + e.getMessage());
            return null;
        }
        if (stmts == null) {
            if (DEBUG)
                System.out.println("[DEBUG] Result of processMutate2(testCase) is null; returning null");
            return null;
        }
        CtAbstractInvocation lastStmt = getMUT(stmts);
        if (lastStmt == null) {
            // DEBUG: stmts 리스트에 invocation이 하나도 없었던 경우
            if (DEBUG)
                System.out.println("[DEBUG] getMUT returned null; stmts = " + stmts);
            return null;
        }
        if (lastStmt.getExecutable() == null) {
            if (DEBUG)
                System.out.println("[DEBUG] lastStmt has no executable: " + lastStmt);
            return null;
        }
        String mutName = lastStmt.getExecutable().getSimpleName();
        if (mutName.contains("<init>")) { // <> 기호는 클래스 이름으로 사용할 수 없음
            mutName = "init";
        }
        // Use index parameter to ensure unique method names across both generators
        // This prevents duplicate method names when multiple tests are merged into MegaClass
        String testNameId = mutName + "_" + index;
        // Handle duplicate variable definitions with iterative fixing
        stmts = handleDuplicateDefinitions(stmts);
        if (stmts == null) {

            return null;
        }

        if (Config.REGRESSION_MODE) {
            Pair<CtClass, List<String>> mutatedTestAndStringPair = null;
            try {
                mutatedTestAndStringPair = generateMethodsWithoutCodeSnippet(stmts,
                        testClassName + "_M_" + testNameId);
            } catch (Exception e) {
                if (DEBUG)
                    System.out.println("[DEBUG] Exception in generateMethodsWithoutCodeSnippet: " + e.getMessage());
                return null;
            }
            Pair<CtClass, List<String>> observerAddedTestAndStringPair = addRegressionOracleToTest(
                    mutatedTestAndStringPair.getKey());
            String clazzStr = mutatedTestAndStringPair.getValue().get(0);
            String methodStr = mutatedTestAndStringPair.getValue().get(1);

            for (String oracle : observerAddedTestAndStringPair.getValue()) {
                if (!oracle.contains("RegressionOracles.RegressionUtil.Logger.observe")) {
                    oracle = oracle.trim() + " // if statement for MUT null check";
                    methodStr = methodStr.substring(0, methodStr.lastIndexOf("}"));
                    methodStr = methodStr + "\t" + oracle + "\n}";
                } else {
                    methodStr = methodStr.substring(0, methodStr.lastIndexOf("}"));
                    methodStr = methodStr + "\t\t" + oracle.trim() + "\n}";
                }
            }
            methodStr = "\t" + methodStr.replaceAll("\n", "\n\t");
            String finalStr = clazzStr.substring(0, clazzStr.lastIndexOf("}")) + "\n" + methodStr + "\n}";
            return new Pair<CtClass, String>(observerAddedTestAndStringPair.getKey(), finalStr);
        } else {
            CtClass<Object> newTestCase = generateMethods(stmts, testClassName + "_M_" + testNameId);
            return new Pair<CtClass, String>(newTestCase, newTestCase.toString());
        }
    }

    private Input findReplacableInput(String targetName, MUTInput mutInput) {
        Map<String, Input> receiverMap = mutInput.getReceiverInputMap();
        Input foundCandidate = receiverMap.get(targetName);

        // if (foundCandidate != null) {
        // System.out.println("[DEBUG] Found matching replacable input for: " +
        // targetName);
        // }

        return foundCandidate;
    }

    public List<CtStatement> processMutToOracle(List<CtStatement> stmts, CtTypeReference returnType) {
        CtStatement lastStmt = stmts.get(stmts.size() - 1);
        String fixedLastStmt = returnType.getQualifiedName() + " returnValue = " + lastStmt.toString();
        Factory facotry = new Launcher().getFactory();
        CtStatement returnMut = facotry.Core().createCodeSnippetStatement();
        ((CtCodeSnippetStatement) returnMut).setValue(fixedLastStmt);
        stmts.set(stmts.size() - 1, returnMut);

        CtStatement assertOracle = facotry.Core().createCodeSnippetStatement();
        ((CtCodeSnippetStatement) assertOracle).setValue("assertFalse(true)");
        stmts.add(assertOracle);

        return stmts;
    }

    private boolean isDuplicate(MUTInput mutInput, List<Integer> combi) {
        long overheadTime = System.currentTimeMillis();
        
        // this.usedCombinations를 사용하고, mutInput 객체를 직접 키로 사용
        Set<List<Integer>> invocationSet = this.usedCombinations.computeIfAbsent(mutInput, k -> new HashSet<>());
        
        boolean isDuplicate = !invocationSet.add(combi);
        long endTime = System.currentTimeMillis();
        overhead += (endTime - overheadTime); // overhead는 여전히 static 필드로 관리 가능
        return isDuplicate;
    }

    private List<CtStatement> processMutate2(RawTestCase testCase) {
        // 최종적으로 반환할 테스트 스테이트먼트 리스트
        List<CtStatement> stmts = new LinkedList<>();

        // 1. 입력 준비 스테이트먼트 삽입
        // testCase.getInsertStmts()에는 MUT 호출 전에 필요한 객체 생성/필드 초기화/메서드 호출 등이 담겨 있음
        List<Input> insertStmts = testCase.getInsertStmts();
        for (Input insert : insertStmts) {
            List<CtElement> mutateStmts = insert.getInput();
            for (CtElement element : mutateStmts) {
                // insert.getInput()에서 얻은 CtElement를 CtStatement로 캐스팅하여 stmts에 추가
                if (element instanceof CtVariableReadImpl) {
                    System.out.println("Element : " + element.toString());
                    continue;
                }
                stmts.add((CtStatement) element);
            }
        }

        // 2. RawTestCase에 추가된 로컬 변수 선언(dummyVar 등)을 stmts에 추가
        List<CtLocalVariable<?>> localVars = testCase.getLocalVariables();
        for (CtLocalVariable<?> localVar : localVars) {
            stmts.add(localVar); // CtLocalVariable<?>는 CtStatement를 구현하므로 바로 add 가능
        }

        // 3. MUT 호출 구문 준비
        CtAbstractInvocation mut = testCase.getMut();
        CtAbstractInvocation mutant = null;
        CtLocalVariable mutant_assign = null;

         // MUT가 메서드 호출(CtInvocationImpl)인지, 생성자 호출(CtConstructorCallImpl)인지에 따라 처리
         if (mut instanceof CtInvocationImpl) {
             // MUT를 복제한 뒤, RawTestCase에 저장된 arguments를 셋팅
             List<CtExpression> args = testCase.getArguments();
             
             // Varargs 처리
             List<CtTypeReference<?>> formalParamTypes = mut.getExecutable().getParameters();
             if (!formalParamTypes.isEmpty()) {
                 CtTypeReference<?> lastParamType = formalParamTypes.get(formalParamTypes.size() - 1);
                 if (lastParamType.isArray()) {
                     int lastParamIndex = formalParamTypes.size() - 1;
                     int regularArgCount = lastParamIndex;
                     
                     if (args.size() > regularArgCount) {
                         Factory factory = new Launcher().getFactory();
                         List<CtExpression> newArgs = new ArrayList<>();
                         
                         for (int i = 0; i < regularArgCount; i++) {
                             newArgs.add(args.get(i));
                         }
                         
                         List<CtExpression<?>> varargElements = new ArrayList<>();
                         for (int i = regularArgCount; i < args.size(); i++) {
                             varargElements.add((CtExpression<?>) args.get(i));
                         }
                         
                         CtNewArray<?> newArray = factory.createNewArray();
                         newArray.setType((CtTypeReference) lastParamType);
                         newArray.setElements((List) varargElements);
                         
                         newArgs.add((CtExpression) newArray);
                         args = newArgs;
                     }
                 }
             }
             
             mutant = ((CtInvocationImpl) mut).clone().setArguments(args);

            if (Config.REGRESSION_MODE) {
                CtTypeReference<?> returnType = ((CtInvocationImpl) mut).getType();
                if (returnType != null
                        && !returnType.getSimpleName().equals("void")
                        && !mut.getExecutable().getSimpleName().equals("hashCode")) {

                    Factory factory = new Launcher().getFactory();
                    String name = returnType.getSimpleName().toLowerCase().replace("[", "").replace("]", "");

                    // Handle generic types: use Object if type variable detected
                    String qualifiedName = returnType.getQualifiedName();
                    
                    // Check if this is a generic type variable (single uppercase letter or TypeVariable)
                    if (isTypeVariable(qualifiedName)) {
                        qualifiedName = "java.lang.Object";
                    }
                    
                    CtTypeReference<?> fqnTypeRef = factory.createReference(qualifiedName);
                    
                    // FQN이 강제로 사용되도록 타입 참조에 설정
                    fqnTypeRef.setImplicit(false);

                    mutant_assign = factory.createLocalVariable(
                            fqnTypeRef,
                            name + "_mut",
                            (CtInvocationImpl) mutant);
                }
            }
         } else if (mut instanceof CtConstructorCallImpl) {
             // 생성자 호출 형태의 MUT 처리
             List<CtExpression> args = testCase.getArguments();
             
             // Varargs 처리
             List<CtTypeReference<?>> formalParamTypes = mut.getExecutable().getParameters();
             if (!formalParamTypes.isEmpty()) {
                 CtTypeReference<?> lastParamType = formalParamTypes.get(formalParamTypes.size() - 1);
                 if (lastParamType.isArray()) {
                     int lastParamIndex = formalParamTypes.size() - 1;
                     int regularArgCount = lastParamIndex;
                     
                     if (args.size() > regularArgCount) {
                         Factory factory = new Launcher().getFactory();
                         List<CtExpression> newArgs = new ArrayList<>();
                         
                         for (int i = 0; i < regularArgCount; i++) {
                             newArgs.add(args.get(i));
                         }
                         
                         List<CtExpression<?>> varargElements = new ArrayList<>();
                         for (int i = regularArgCount; i < args.size(); i++) {
                             varargElements.add((CtExpression<?>) args.get(i));
                         }
                         
                         CtNewArray<?> newArray = factory.createNewArray();
                         newArray.setType((CtTypeReference) lastParamType);
                         newArray.setElements((List) varargElements);
                         
                         newArgs.add((CtExpression) newArray);
                         args = newArgs;
                     }
                 }
             }
             
             mutant = ((CtConstructorCallImpl) mut).clone().setArguments(args);
         }

        // 4. 최종 MUT 호출 구문 삽입
        if (mutant != null) {
            if (mutant_assign != null) {
                stmts.add(mutant_assign);
            } else {
                stmts.add((CtStatement) mutant);
            }
            return stmts; // 완성된 스테이트먼트 리스트 반환
        } else {
            // MUT를 제대로 생성하지 못한 경우 null 반환
            return null;
        }
    }


    public CtClass<Object> generateMethods(List<CtStatement> stmts, String newClassName) {
        Factory facotry = new Launcher().getFactory();
        facotry.getEnvironment().disableConsistencyChecks(); // setSelfChecks(true);
        facotry.getEnvironment().setAutoImports(true); // Enable auto imports for proper simple names

        /*
         * Set up Class: new class name is original_MUT_MUTcount (e.g.,
         * XYSeries_ESTest_addOrUpdate_1)
         */
        CtClass<Object> clazz = facotry.Core().createClass();
        clazz.setSimpleName(newClassName);
        Set<ModifierKind> modifiers = new HashSet<>();
        modifiers.add(ModifierKind.PUBLIC);
        clazz.setModifiers(modifiers);

        /*
         * add throwable
         */
        CtTypeReference<? extends Throwable> throwable = facotry.createTypeReference();
        throwable.setSimpleName("Throwable");
        Set<CtTypeReference<? extends Throwable>> throwsExp = new HashSet<>();
        throwsExp.add(throwable);

        /*
         * Set up Method: only one method for each TestClass to skip possible compile
         * errors during javac
         */
        CtMethod<Object> newTestCase = facotry.createMethod();
        CtBlock<Object> methodBody = facotry.createBlock();
        List<CtStatement> reloads = new ArrayList<>();
        for (CtStatement stmt : stmts) {
            CtStatement ctStatement = facotry.Core().createCodeSnippetStatement();
            // Use autoImports to generate proper simple names with imports
            Launcher tempLauncher = new Launcher();
            spoon.compiler.Environment tempEnv = tempLauncher.getEnvironment();
            tempEnv.setAutoImports(true); // Enable auto imports for proper simple names
            tempEnv.setNoClasspath(true); // Don't try to resolve classpath
            DefaultJavaPrettyPrinter printer = new DefaultJavaPrettyPrinter(tempEnv);
            String stmtStr = printer.prettyprint(stmt);
            ((CtCodeSnippetStatement) ctStatement).setValue(stmtStr);
            reloads.add(ctStatement);
        }
        methodBody.setStatements(reloads);
        newTestCase.setBody(methodBody);
        newTestCase.setSimpleName("test");
        CtTypeReference<Object> returnValue = facotry.createTypeReference();
        returnValue.setSimpleName("void");
        newTestCase.setType(returnValue);
        newTestCase.setModifiers(modifiers);
        clazz.addMethod(newTestCase);
        newTestCase.setThrownTypes(throwsExp);

        /*
         * Set up Annotation
         */
        CtAnnotationType testRefer = facotry.createAnnotationType("Test");
        CtAnnotation<Annotation> testAnno = facotry.createAnnotation();
        testAnno.setAnnotationType(testRefer.getReference());
        testAnno.addValue("timeout", 1000);
        List<CtAnnotation<? extends Annotation>> annotation = new LinkedList<>();
        annotation.add(testAnno);
        newTestCase.setAnnotations(annotation);
        // System.out.println("Generated Test Class");
        // System.out.println(clazz);
        return clazz;
    }

    /**
     * Same as generateMethods method except that this method does not reload
     * CtNodeSnippetStatement that was added to avoid class.toString crash
     *
     * @param stmts
     * @param newClassName
     * @return
     */
    public Pair<CtClass, List<String>> generateMethodsWithoutCodeSnippet(List<CtStatement> stmts, String newClassName) {
        Factory facotry = new Launcher().getFactory();
        facotry.getEnvironment().disableConsistencyChecks(); // setSelfChecks(true);
        /**
         * Set up Class: new class name is original_MUT_MUTcount (e.g.,
         * XYSeries_ESTest_addOrUpdate_1)
         */
        /**
         * Set up Class: new class name is original_MUT_MUTcount (e.g.,
         * XYSeries_ESTest_addOrUpdate_1)
         */
        CtClass<Object> clazz = facotry.Core().createClass();
        clazz.setSimpleName(newClassName);
        Set<ModifierKind> modifiers = new HashSet<>();
        modifiers.add(ModifierKind.PUBLIC);
        clazz.setModifiers(modifiers);

        /*
         * add throwable
         */
        CtTypeReference<? extends Throwable> throwable = facotry.createTypeReference();
        throwable.setSimpleName("Throwable");
        Set<CtTypeReference<? extends Throwable>> throwsExp = new HashSet<>();
        throwsExp.add(throwable);

        /*
         * Set up Method: only one method for each TestClass to skip possible compile
         * errors during javac
         */
        CtMethod<Object> newTestCase = facotry.createMethod();
        CtBlock<Object> methodBody = facotry.createBlock();
        // List<CtStatement> reloads = new ArrayList<>();
        // for (CtStatement stmt : stmts) {
        // CtStatement ctStatement = facotry.Core().createCodeSnippetStatement();
        // ((CtCodeSnippetStatement) ctStatement).setValue(stmt.toString());
        // reloads.add(ctStatement);
        // }
        // methodBody.setStatements(reloads);
        methodBody.setStatements(stmts);
        newTestCase.setBody(methodBody);
        newTestCase.setSimpleName("test");
        CtTypeReference<Object> returnValue = facotry.createTypeReference();
        returnValue.setSimpleName("void");
        newTestCase.setType(returnValue);
        newTestCase.setModifiers(modifiers);
        newTestCase.setThrownTypes(throwsExp);

        /*
         * Set up Annotation
         */
        CtAnnotationType testRefer = facotry.createAnnotationType("org.junit.Test");
        CtAnnotation<Annotation> testAnno = facotry.createAnnotation();
        testAnno.setAnnotationType(testRefer.getReference());
        testAnno.addValue("timeout", 1000);
        List<CtAnnotation<? extends Annotation>> annotation = new LinkedList<>();
        annotation.add(testAnno);
        newTestCase.setAnnotations(annotation);

        List<String> classAndMethodStringPair = new ArrayList<>();
        // Use custom pretty printer to preserve FQNs
        Launcher tempLauncher = new Launcher();
        spoon.compiler.Environment tempEnv = tempLauncher.getEnvironment();
        tempEnv.setAutoImports(false); // Disable auto imports to force FQNs
        tempEnv.setNoClasspath(true); // Don't try to resolve classpath
        DefaultJavaPrettyPrinter printer = new DefaultJavaPrettyPrinter(tempEnv);
        classAndMethodStringPair.add(printer.prettyprint(clazz));
        classAndMethodStringPair.add(printer.prettyprint(newTestCase));

        clazz.addMethod(newTestCase);
        return new Pair(clazz, classAndMethodStringPair);
    }

    private boolean isVarTypeCased(CtElement var) {
        if (var instanceof CtVariableReadImpl ||
                var instanceof CtArrayReadImpl) { // there are some cases where var is type casted. we ignore this case.
            List<CtTypeReference> casts = ((CtExpression) var).getTypeCasts();
            if (casts.size() > 0)
                return true;
        }
        return false;
    }

    private MUTInput getMUT(CtAbstractInvocation methodName, List<CtTypeReference> argumentsTypes) {
        Set<MUTInput> muts = inputCombinations.getCombinationsMap().keySet();
        for (MUTInput mut : muts) {
            if (mut.getMUTInvocation().equals(methodName) && mut.equals(argumentsTypes)) {
                return mut;
            }
        }
        throw new RuntimeException("no match mut found for " + methodName.getExecutable().getSimpleName());
    }

    public CtAbstractInvocation getMUT(List<CtStatement> stmts) {
        CtStatement lastStmt = stmts.get(stmts.size() - 1);
        return getMUT(lastStmt);
    }

    public CtAbstractInvocation getMUT(CtMethod testcase) {
        CtStatement stmt = getLastMUTStatement(testcase);
        CtAbstractInvocation invoke = null;
        if (stmt instanceof CtInvocationImpl) {
            invoke = (CtInvocationImpl) stmt;
        } else if (stmt.getElements(new TypeFilter<>(CtInvocationImpl.class)).size() == 1) {
            invoke = stmt.getElements(new TypeFilter<>(CtInvocationImpl.class)).get(0);
        } else if (stmt instanceof CtConstructorCallImpl) {
            invoke = (CtConstructorCallImpl) stmt;
        } else if (stmt.getElements(new TypeFilter<>(CtConstructorCallImpl.class)).size() == 1) {
            invoke = stmt.getElements(new TypeFilter<>(CtConstructorCallImpl.class)).get(0);
        } else {
            return null;
        }
        return invoke;
    }

    /**
     * init input combinations
     */
    private void initInputCombinations(String testFile,long startTime, List<String> baseTests)
            throws TimeoutException {
        inputCombinations.run(testFile, startTime, baseTests);
    }

    public Pair<CtClass, List<String>> addRegressionOracleToTest(CtClass<Object> generatedTest) {
        // Analyze
        Map<CtMethod, List<CtLocalVariable>> localVariablesPerTestMethod = analyzer.analyze(generatedTest, false);
        Map<CtMethod, List<CtLocalVariable>> localVariablesPrimitive = analyzer.analyze(generatedTest, true);
        // Collect
        Set<CtMethod<?>> methods = generatedTest.getMethods();
        if (methods.size() != 1) {
            System.out.println("The number of method in class is not 1.");
            System.exit(1);
        }
        for (CtMethod<?> ctMethod : methods) {
            Pair<CtClass, List<String>> observerAddedClassAndStringPair = collector.instrumentObserver(ctMethod,
                    localVariablesPerTestMethod, localVariablesPrimitive);
            CtClass<Object> observerAddedClass = observerAddedClassAndStringPair.getKey();
            // observerAddedTests.add(observerAddedClass);
            return observerAddedClassAndStringPair;
        }
        return null;
    }
    
    /**
     * Handle duplicate variable definitions with optimized single-pass detection and fixing
     * Flow: 1. Single pass to collect all variables, 2. Fix conflicts in-place, 3. Done
     */
    private List<CtStatement> handleDuplicateDefinitions(List<CtStatement> stmts) {
        // Early exit if no statements
        if (stmts == null || stmts.isEmpty()) {
            return stmts;
        }
        
        // Single pass collection of all variables with their locations
        Map<String, List<VarInfo>> varCollector = new HashMap<>();
        boolean hasDuplicates = false;
        
        for (int stmtIndex = 0; stmtIndex < stmts.size(); stmtIndex++) {
            CtStatement stmt = stmts.get(stmtIndex);
            List<CtLocalVariable> vars = stmt.getElements(new TypeFilter<>(CtLocalVariable.class));
            
            for (CtLocalVariable var : vars) {
                String varName = var.getSimpleName();
                VarInfo info = new VarInfo(var, stmt, stmtIndex);
                
                List<VarInfo> existingVars = varCollector.get(varName);
                if (existingVars == null) {
                    existingVars = new ArrayList<>(2); // Most cases will have ≤2 duplicates
                    varCollector.put(varName, existingVars);
                }
                existingVars.add(info);
                
                if (existingVars.size() > 1) {
                    hasDuplicates = true;
                }
            }
        }
        
        // Early exit if no duplicates found
        if (!hasDuplicates) {
            return stmts;
        }else{
            // System.out.println("Duplicate variable definitions found, fixing...");
            // Fix duplicates in-place (avoid cloning unless necessary)
            return fixDuplicatesOptimized(stmts, varCollector);
        }
    }
    
    /**
     * Helper class to store variable information for efficient processing
     */
    private static class VarInfo {
        final CtLocalVariable variable;
        final CtStatement statement;
        final int statementIndex;
        
        VarInfo(CtLocalVariable variable, CtStatement statement, int statementIndex) {
            this.variable = variable;
            this.statement = statement;
            this.statementIndex = statementIndex;
        }
    }
    
    /**
     * Optimized duplicate fixing - only clone statements that need modification
     */
    private List<CtStatement> fixDuplicatesOptimized(List<CtStatement> stmts, 
                                                    Map<String, List<VarInfo>> varCollector) {
        Set<Integer> stmtsToModify = new HashSet<>();
        Map<String, String> renameMap = new HashMap<>();
        
        // Determine which statements need modification and create rename mappings
        for (Map.Entry<String, List<VarInfo>> entry : varCollector.entrySet()) {
            String varName = entry.getKey();
            List<VarInfo> varInfos = entry.getValue();
            
            if (varInfos.size() > 1) {
                // Keep first occurrence, rename others
                for (int i = 1; i < varInfos.size(); i++) {
                    VarInfo varInfo = varInfos.get(i);
                    String newName = "fixed_" + i + "_" + varName;
                    renameMap.put(varName + "_" + varInfo.statementIndex, newName);
                    stmtsToModify.add(varInfo.statementIndex);
                
                }
            }
        }
        
        // Only process statements that need modification
        if (stmtsToModify.isEmpty()) {
            return stmts;
        }
        
        
        List<CtStatement> result = new ArrayList<>(stmts.size());
        int modifiedCount = 0;
        for (int i = 0; i < stmts.size(); i++) {
            if (stmtsToModify.contains(i)) {
                CtStatement cloned = stmts.get(i).clone();
                applyRenames(cloned, renameMap, i);
                result.add(cloned);
                modifiedCount++;
            } else {
                result.add(stmts.get(i)); // No cloning needed
            }
        }
    
        return result;
    }
    
    /**
     * Apply variable renames to a statement efficiently
     * @param statement Statement to modify (already cloned)
     * @param renameMap Map of rename patterns
     * @param statementIndex Index of the statement for mapping lookup
     */
    private void applyRenames(CtStatement statement, Map<String, String> renameMap, int statementIndex) {
        // Single pass through all elements to minimize AST traversals
        statement.accept(new CtScanner() {
            @Override
            public <T> void visitCtLocalVariable(CtLocalVariable<T> localVariable) {
                String oldName = localVariable.getSimpleName();
                String key = oldName + "_" + statementIndex;
                String newName = renameMap.get(key);
                if (newName != null) {
                    localVariable.setSimpleName(newName);
                }
                super.visitCtLocalVariable(localVariable);
            }
            
            @Override
            public <T> void visitCtVariableRead(CtVariableRead<T> variableRead) {
                String oldName = variableRead.getVariable().getSimpleName();
                String key = oldName + "_" + statementIndex;
                String newName = renameMap.get(key);
                if (newName != null) {
                    CtVariableReference<T> newVarRef = variableRead.getVariable().clone();
                    newVarRef.setSimpleName(newName);
                    variableRead.setVariable(newVarRef);
                }
                super.visitCtVariableRead(variableRead);
            }
            
            @Override
            public <T> void visitCtVariableWrite(CtVariableWrite<T> variableWrite) {
                String oldName = variableWrite.getVariable().getSimpleName();
                String key = oldName + "_" + statementIndex;
                String newName = renameMap.get(key);
                if (newName != null) {
                    CtVariableReference<T> newVarRef = variableWrite.getVariable().clone();
                    newVarRef.setSimpleName(newName);
                    variableWrite.setVariable(newVarRef);
                }
                super.visitCtVariableWrite(variableWrite);
            }
        });
    }
    
    /**
     * Check if a type name is a type variable (generic type like T, E, K, V)
     * Type variables are typically single uppercase letters or start with TypeVariable
     */
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
}