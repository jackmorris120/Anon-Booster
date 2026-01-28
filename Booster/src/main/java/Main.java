import Compiler.Compiler;
import Generater.MUTMutation.ASTParser;
import Generater.MUTMutation.CandidatePool;
import Generater.MUTMutation.SeedAugmentor;
import Generater.MUTMutation.Input;
import Generater.MUTMutation.MUTInput;
import Generater.MUTMutation.TestCaseGenerator;
import Generater.MUTMutation.RecursiveTestCaseGenerator;
import Generater.PrimitiveMutation.PrimitiveParser;
import Generater.PrimitiveMutation.PrimitiveTwayTestGenerator;
import dk.brics.automaton.RegExp;
import Generater.MUTMutation.Inlining.*;

import org.evosuite.PackageInfo;
import org.junit.runner.Result;
import javax.tools.Diagnostic;
import javax.tools.JavaFileObject;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import utils.RelevantExtenderGetter;
import utils.RelevantRefGetter;
import spoon.reflect.declaration.CtAnnotation;
import spoon.reflect.declaration.CtClass;
import spoon.reflect.declaration.CtCompilationUnit;
import spoon.reflect.declaration.CtConstructor;
import spoon.reflect.declaration.CtMethod;
import spoon.reflect.declaration.CtPackage;
import spoon.reflect.declaration.CtPackageDeclaration;
import spoon.reflect.declaration.CtParameter;
import spoon.reflect.declaration.CtType;
import spoon.reflect.declaration.ModifierKind;
import spoon.Launcher;
import spoon.reflect.CtModel;
import utils.Config;
import utils.Pair;
import utils.RunStat;
import utils.TestFilter;
import utils.TryCatchWrapper;
import spoon.reflect.reference.CtTypeReference;
import spoon.reflect.visitor.DefaultJavaPrettyPrinter;
import spoon.reflect.visitor.filter.TypeFilter;
import spoon.reflect.visitor.CtScanner;
import spoon.reflect.code.CtAbstractInvocation;
import spoon.reflect.code.CtBlock;
import spoon.reflect.code.CtExpression;
import spoon.reflect.code.CtFieldRead;
import spoon.reflect.code.CtFieldWrite;
import spoon.reflect.code.CtInvocation;
import spoon.reflect.code.CtSuperAccess;
import spoon.reflect.code.CtThisAccess;
import spoon.reflect.code.CtCatch;
import spoon.reflect.code.CtCatchVariable;
import spoon.reflect.declaration.CtElement;
import spoon.reflect.declaration.CtImport;
import spoon.reflect.code.CtLiteral;
import spoon.reflect.code.CtStatement;
import spoon.reflect.code.CtTry;

import java.io.*;
import java.lang.annotation.Annotation;
import java.lang.reflect.Modifier;
import java.net.URLClassLoader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.Map;
import java.util.HashSet;
import java.util.Collections;
import java.util.HashMap;
import java.util.concurrent.TimeoutException;
import java.util.Stack;
import spoon.reflect.factory.MethodFactory;
import spoon.reflect.factory.CoreFactory;
import spoon.reflect.factory.Factory;
import java.util.regex.Pattern;
import java.util.regex.Matcher;

public class Main {
    public static String outputClassName;
    public static long time_budget;
    public static int num_split_output_tests;
    public static String ASSEMBLE_MODE = "";
    public static Map<String, Set<String>> additionalImports = new HashMap<>();
    private static int numOfLessThanTwo = 0;

    public static void main(String[] args) throws Exception {
         // [NEW] UTF-8 인코딩 설정
         System.setOut(new java.io.PrintStream(System.out, true, "UTF-8"));
         System.setErr(new java.io.PrintStream(System.err, true, "UTF-8"));
         
         // Suppress stderr to hide Spoon internal error traces
        final java.io.PrintStream originalErr = System.err;
        System.setErr(new java.io.PrintStream(new java.io.OutputStream() {
            private StringBuilder buffer = new StringBuilder();

            @Override
            public void write(int b) {
                buffer.append((char) b);
                if (b == '\n') {
                    String line = buffer.toString();
                    // Only suppress Spoon-related stack traces
                    if (!line.contains("spoon.support.reflect.reference.CtTypeReferenceImpl.getAccessType") &&
                        !line.contains("spoon.reflect.visitor.ImportAnalyzer") &&
                        !line.contains("spoon.reflect.visitor.EarlyTerminatingScanner")) {
                        originalErr.print(line);
                    }
                    buffer.setLength(0);
                }
            }
        }));

        /*
         * return illegal parameter
         */
        if (args.length < 6) {
            System.err.println(
                    // "The command should be : java Main <class path> <path to generated testcase
                    // file> <full class name> <.class output folder> <path to output file>
                    // <time_budget> <number_of_split_test_file> <thread number> <MUT|P|BOTH>
                    // <REGRESSION_MODE>");
                    "The command should be : Usage: java Main <class path> <output folder> <time_budget> <num_split_tests> <CUT_path> <ASSEMBLE_MODE> <initial_tests...>");
            for(String arg : args){
                System.out.println(" - "+arg);
            }
                    return;
        }
        /*
         * initial arguments
         */
        System.out.println("===================================================================");
        initParams(args);

        if (ASSEMBLE_MODE.equalsIgnoreCase("seqc")) {
            /*
             * handle mut testcases
             */

            System.out.println("Invoking inlineRecurTestCases");
            inlineRecurTestCases();
        } else if (ASSEMBLE_MODE.equalsIgnoreCase("seqp")) {
            /*
             * handle mut testcases
             */

            handlePrimitiveTestCases();
            //
        } else{
            System.out.println("Invalid Generation Method : "+ASSEMBLE_MODE.toString());
            return ;
        }
    }

    private static void inlineRecurTestCases() throws Exception {
        System.out.println("handleRecurTestCases : Recursive Test Generation (RecursiveTestCaseGenerator)");
        long totalTime = System.currentTimeMillis();
        long inLineTime = System.currentTimeMillis();
        
        // Filter BaseTests to get only actual CUT-calling tests for inlining
        TestFilter.FilterResult filterResult = TestFilter.filterTests(Config.BASE_TESTS, Config.OUTPUT_PATH);
        List<String> actualBaseTests = filterResult.getBaseTests();
        List<String> helperTests = filterResult.getExtendedTests();
        
        // System.out.println("[TestFilter] Inlining " + actualBaseTests.size() + " actual base tests");
        // System.out.println("[TestFilter] " + helperTests.size() + " helper/extended tests excluded from inlining");
        
        try {
            TestTransformer transformer = new TestTransformer();
            transformer.transformAndSave(actualBaseTests);
        } catch (Exception e) {
            // System.err.println("ERROR in transformAndSave:");
            // e.printStackTrace();
        }
        inLineTime = System.currentTimeMillis() - inLineTime;
        System.out.println("Inlining Time + MegaClassGenTime : " + inLineTime + " ms");

        RunStat runStat = new RunStat(Config.FULL_CLASS_NAME);
        long generationTime = 0;
        long compileTime = 0;
        long runTime = 0;
        long collectingTime = 0;
        List<List<String>> testList = new ArrayList<>(num_split_output_tests);
        int testSplitNum = 1;
        long startTime = System.currentTimeMillis();
        utils.TestMinimizer sharedMinimizer = new utils.TestMinimizer("seqc");
        // Use original Config.BASE_TESTS for TestCaseGenerator since TestTransformer already filtered the files
        TestCaseGenerator testCaseGenerator = new TestCaseGenerator(Config.TEST_FILE, startTime, Config.BASE_TESTS);
        
        outputClassName = testCaseGenerator.getTestClassName();
        String fileName = outputClassName + "_" + "C";
    
        
        RecursiveTestCaseGenerator recursiveGen = new RecursiveTestCaseGenerator(
            testCaseGenerator.getTestClassName(),
            testCaseGenerator.getPackageAndImport()
        );
        
         Compiler compiler = new Compiler(testCaseGenerator.getPackageAndImport(), ASTParser.getPackageName(),sharedMinimizer);

         Set<MUTInput> mutInputsSet = testCaseGenerator.getMutInputs();
         
         // [수정] null 체크 추가
         if (mutInputsSet == null) {
             System.out.println("[ERROR] getMutInputs() returned null - no MUT inputs available");
             System.out.println("[ERROR] This may indicate that InputCombinations was not properly initialized");
             return;
         }
         
         System.out.println("Time Budget : " + time_budget + " ms");
         System.out.println("# of Muts " + mutInputsSet.size());
         
         List<MUTInput> mutInputs = new ArrayList<>(mutInputsSet);
         Collections.shuffle(mutInputs);
         System.out.println("[RANDOMIZED] Shuffled " + mutInputs.size() + " MUTs for diverse exploration");
         
         if (mutInputs.isEmpty()) {
             System.out.println("[DEBUG] No MUTs found - terminating early");
             return;
         }
        
        if (Config.ENABLE_COMBINATION_ANALYSIS) {
            String analysisSeperator = "============================================================";
            System.out.println("\n" + analysisSeperator);
            System.out.println("PERFORMING COMBINATION EXPLOSION ANALYSIS...");
            System.out.println(analysisSeperator);
            
            CandidatePool.printPoolSummary();
            SeedAugmentor.printConstructorMapSummary();
            CandidatePool.addExtremeValuesForPrimitiveTypes();
            CandidatePool.printTopObjectsWithMostInputs(10);
            CandidatePool.printSequenceLimitationStats();
            testCaseGenerator.analyzeCombinationExplosion();

            System.out.println("=========================MUT INPUTS ===========================");
            for (MUTInput mp : mutInputs) {
                System.out.println(mp);
                System.out.println();
            }
        }

        int count = 0;
        int index = 0;
        collectingTime += System.currentTimeMillis() - Config.START_TIME;
        startTime = System.currentTimeMillis();
        
        breakPoint: while (true) {
            if (System.currentTimeMillis() - startTime > time_budget) {
                break breakPoint;
            }

            if ((System.currentTimeMillis() - startTime) >= ((time_budget / num_split_output_tests) * testSplitNum)) {
                if (testSplitNum != num_split_output_tests) {
                    List<String> splitTestList = new ArrayList<>(compiler.getRunnableTestStringList());
                    testList.add(splitTestList);
                    compiler.setRunnableTestStringListEmpty();
                    testSplitNum++;
                }
            }

            for (MUTInput mutInput : mutInputs) {
                if (System.currentTimeMillis() - startTime > time_budget) {
                    break breakPoint;
                }

                // 1️⃣ RecursiveTestCaseGenerator: Generate test for current MUT
                long generationStart = System.currentTimeMillis();
                Pair<CtClass, String> generatedTestAndStringPair = null;
                if(Config.BUILD_UP_GEN){
                    generatedTestAndStringPair = recursiveGen.generateTest(mutInput, index, true);
                }else{
                    generatedTestAndStringPair = testCaseGenerator.generateTest(mutInput, index, true);
                }
                
                generationTime += System.currentTimeMillis() - generationStart;

                if (generatedTestAndStringPair == null) {
                    index++;
                    continue;
                } else {
                    // System.out.println("=======================");
                    // System.out.println("[RecursiveGen] Generated TEST (index=" + index + "):");
                    // System.out.println(generatedTestAndStringPair.getKey());
                }
                
                long compileStart = System.currentTimeMillis();
                Pair<CtMethod, String> compiledTestAndStringPair = compiler.compileEach(generatedTestAndStringPair);
                compileTime += System.currentTimeMillis() - compileStart;
                
                if (compiledTestAndStringPair == null) {
                    deleteClassFile(generatedTestAndStringPair.getKey().getSimpleName(), compiler.getPackageName());
                    index++;
                    continue;
                }else{
                    // System.out.println("=======================");
                    // System.out.println("[RecursiveGen] Compiled TEST (index=" + index + "):");
                    // System.out.println(compiledTestAndStringPair.getKey());
                }
                
                long runStart = System.currentTimeMillis();
                try {
                    Result result = compiler.runCompiledTestCase(compiledTestAndStringPair);
                    // DEBUG: Print the oracle-transformed test that was added to runnableTestStringList
                } catch (NoSuchMethodError e) {
                    // Ignore
                } catch (Exception e) {
                    // Ignore
                }
                runTime += System.currentTimeMillis() - runStart;

                deleteClassFile(compiledTestAndStringPair.getKey().getSimpleName(), compiler.getPackageName());
                index++;  // ✅ Increment after successful RecursiveGen test

                // 2️⃣ TestCaseGenerator: Generate test for the SAME MUT (but with new index)
                if(Config.ENABLE_HYBRID_GEN){
                    generationStart = System.currentTimeMillis();
                    generatedTestAndStringPair = testCaseGenerator.generateTest(mutInput, index, true);
                    generationTime += System.currentTimeMillis() - generationStart;

                    if (generatedTestAndStringPair == null) {
                        index++;
                        continue;
                    } 
                    
                    compileStart = System.currentTimeMillis();
                    compiledTestAndStringPair = compiler.compileEach(generatedTestAndStringPair);
                    compileTime += System.currentTimeMillis() - compileStart;
                    
                    if (compiledTestAndStringPair == null) {
                        deleteClassFile(generatedTestAndStringPair.getKey().getSimpleName(), compiler.getPackageName());
                        index++;
                        continue;
                    }
                    
                    runStart = System.currentTimeMillis();
                    try {
                        Result result = compiler.runCompiledTestCase(compiledTestAndStringPair);
                        // DEBUG: Print the oracle-transformed test that was added to runnableTestStringList
                    } catch (NoSuchMethodError e) {
                        // Ignore
                    } catch (Exception e) {
                        // Ignore
                    }
                    runTime += System.currentTimeMillis() - runStart;

                    deleteClassFile(compiledTestAndStringPair.getKey().getSimpleName(), compiler.getPackageName());
                    index++;  // ✅ Increment after successful TestCaseGen test
                }
            }
            count++;
        }

        testList.add(new ArrayList<>(compiler.getRunnableTestStringList()));
        int listCount = 1;
        int numTotalTest = 0;
        for (List<String> test : testList) {
            System.out.println("Split " + listCount + ":");
            System.out.println("# of Tests : " + test.size());
            numTotalTest += test.size();
            listCount++;
            System.out.println();
        }
         System.out.println("Total Tests: ");
         System.out.println("# of Total Tests : " + numTotalTest);
         System.out.println("");
          
           // [NEW] Bucketing 모드: Exception별 그룹화 준비
           if (Config.ENABLE_TEST_BUCKETING) {
               compiler.organizeBucketsFromMinimizer();
           }
           
           compiler.setRunnableTestStringListEmpty();
           for (int i = 0; i < testList.size(); i++) {
               String testString = compiler.testStringListToFile(testList.get(i), fileName + "_" + (i + 1));
               
               writeFile(fileName + "_" + (i + 1), testString);
              boolean errorFree = compiler.compileFile(fileName + "_" + (i + 1), testString);
              if (!errorFree) {
                  System.out.println("Output class " + fileName + "_" + (i + 1) + " is not compiled.");
              }
          }
         
         long overhead = recursiveGen.getOverhead();
          System.out.println("Duplicated Tests : " + recursiveGen.duplicateCount);
          System.out.println("Overhead : " + overhead + " ms");
          
           // [NEW] Test Minimization 상세 통계 출력 (Minimization 또는 Bucketing 활성화 시에만)
           if (Config.ENABLE_TEST_MINIMIZATION || Config.ENABLE_TEST_BUCKETING) {
               sharedMinimizer.printDetailedStats("SeqC");
           }
        runStat.setCollectingTime(collectingTime);
        runStat.setGenerateTime(generationTime);
        runStat.setCompileTime(compileTime);
        runStat.setRunningTime(runTime);

        runStat.setType("Seq-R");
        runStat.setTestId(Config.BUILD_PATH);
        runStat.setTotalTime(System.currentTimeMillis() - startTime);
        System.out.println("Num of Compile Fail Tests : " + Config.NUM_COMPILE_FAIL);
        File f = new File(Config.BUILD_PATH + File.separator + "dive_log.csv");
        if (!f.exists()) {
            writeLog("dive_log.csv", runStat.getHead() + "\n");
        }
        writeLog("dive_log.csv", runStat.getStat() + "\n");

        System.out.println("[DEBUG] inlineRecurTestCases completed - exiting program");
        System.exit(0);
    }


    private static void handlePrimitiveTestCases() throws Exception {
        RunStat runStat = new RunStat(Config.FULL_CLASS_NAME);
        long generationTime = 0;
        long compileTime = 0;
        long runTime = 0;
        long collectingTime = 0;
         List<List<String>> testList = new ArrayList<>(num_split_output_tests);
         int testSplitNum = 1;
         long startTime = System.currentTimeMillis();
         Map<String, PrimitiveTwayTestGenerator> testGeneratorMap = new LinkedHashMap<>();
         Map<String, Compiler> compilerMap = new LinkedHashMap<>();
         Map<String, Integer> generationAttemptMap = new LinkedHashMap<>();
         utils.TestMinimizer sharedMinimizer = new utils.TestMinimizer("seqp");
         // Convert extended tests BEFORE parsing to ensure JXPathTestCase etc. are converted
         convertExtendedTestsToJUnit4();
        
        // Apply round-robin method selection for seqp mode with upper limit of 500
        Map<String, List<String>> selectedMethodsMap = null;
        if (Config.ASSEMBLE_MODE.equals("seqp")) {
            // Extract bug-triggering class names from Config.BUGTRIGGERRING_TESTS
            Set<String> bugTriggeringClasses = new HashSet<>();
            if (Config.BUGTRIGGERRING_TESTS != null && !Config.BUGTRIGGERRING_TESTS.isEmpty()) {
                // Format: "org.joda.time.TestPartial_Constructors::testConstructorEx7_TypeArray_intArray"
                // Extract class name (part before ::)
                int separatorIndex = Config.BUGTRIGGERRING_TESTS.indexOf("::");
                if (separatorIndex > 0) {
                    bugTriggeringClasses.add(Config.BUGTRIGGERRING_TESTS.substring(0, separatorIndex));
                } else {
                    bugTriggeringClasses.add(Config.BUGTRIGGERRING_TESTS);
                }
            }
            
            TestFilter.MethodSelectionResult selectionResult = 
                TestFilter.selectTestMethodsRoundRobin(Config.BASE_TESTS, bugTriggeringClasses, 500);
            selectedMethodsMap = selectionResult.getSelectedMethods();
            
        }
        
        PrimitiveParser.parse(Config.BASE_TESTS, selectedMethodsMap);

        System.out.println("Done Parsing");
        Map<String, Set<CtElement>> primMap = PrimitiveParser.getPrimitiveTypeAndVal();
        for (Map.Entry<String, Set<CtElement>> item : primMap.entrySet()) {
            String type = item.getKey();
            Set<CtElement> vals = item.getValue();
            System.out.println("Parsed Type : " + type + " Pool size : " + vals.size());
        }
        // (1) 기존에 받아오던 맵들
        Map<String, List<CtMethod<?>>> baseTestMethodMap = PrimitiveParser.getBaseTestMethodMap();
        Map<String, CtClass<?>> skeletalTestClassMap = PrimitiveParser.getSkeletalTestClassMap();
        Map<String, List<CtMethod<?>>> finalTestMethodStringMap = new LinkedHashMap<>();
        List<Map<String, List<CtMethod<?>>>> splitedTestList = new ArrayList<>();
        
        Set<String> zeroMaskes = new HashSet<>();
        // (2) split 결과를 저장할 리스트

         // (3) Round Robin으로 생성된 queue를 받아와서 섞기
         List<Map<String, CtMethod<?>>> queue = PrimitiveParser.generateQueue(baseTestMethodMap);
       

         // (4) queue를 순환할 때 사용할 인덱스
         int queueIndex = 0;
         // (5) 메서드 네이밍 등에 사용할 전역 인덱스
         int index = 0;
         
         // [수정] 각 메서드별 exhausted 상태 추적 (methodSignature → true/false)
         Map<String, Boolean> methodExhaustedMap = new HashMap<>();

         collectingTime += System.currentTimeMillis() - Config.START_TIME;
         startTime = System.currentTimeMillis();
         System.out.println("Generation Time Remaining : "+ time_budget + " ms");

         // Early termination if no test methods found
         if (queue.isEmpty()) {
             System.out.println("No test methods found in queue - terminating early");
             // Continue with the rest of the method (statistics and file output)
         } else {
             // -------------------------------
             // (7) 시간 예산 내에서 queue 순서대로 처리
              System.out.println("Starting test generation with " + queue.size() + " test methods in queue");
              System.out.println("Time budget: " + time_budget + " ms");
              int consecutiveSkips = 0; // Track consecutive skips to prevent infinite loops
              // [수정] maxConsecutiveSkips: 하나의 메서드가 여러 attemptNumber를 시도할 수 있도록 충분히 큼
              int maxConsecutiveSkips = Math.max(50, queue.size() * 10); // At least 50 skips allowed

            breakPoint: while (true) {
            // 7-0) 매 루프마다 skip 카운터 증가 (성공 시에만 리셋됨)
            consecutiveSkips++;

            // 7-1) 전체 시간 예산 초과 시 종료
            if (System.currentTimeMillis() - startTime > time_budget) {
                System.out.println("Time budget exceeded - terminating");
                break breakPoint;
            }

             // 7-1-b) 무한 루프 방지: 너무 많은 연속 skip이 발생하면 종료
             if (consecutiveSkips >= maxConsecutiveSkips) {
                 System.out.println("[TERMINATION] Too many consecutive skips (" + consecutiveSkips + " >= " + maxConsecutiveSkips + ")");
                 System.out.println("[TERMINATION] Queue size: " + queue.size());
                 System.out.println("[TERMINATION] Exhausted methods: " + methodExhaustedMap.values().stream().filter(b -> b).count() + " / " + queue.size());
                 System.out.println("[TERMINATION] generationAttemptMap: " + generationAttemptMap);
                 System.out.println("[TERMINATION] All tests exhausted, terminating");
                 break breakPoint;
             }

            // 7-2) split 로직: 일정 구간마다 finalTestMethodStringMap을 splitedTestList에 추가
            if ((System.currentTimeMillis() - startTime) >= ((time_budget / num_split_output_tests) * testSplitNum)) {
                if (testSplitNum != num_split_output_tests) {
                    splitedTestList.add(finalTestMethodStringMap);
                    finalTestMethodStringMap = new LinkedHashMap<>();
                    testSplitNum++;
                }
            }

            // 7-3) queue에서 현재 엔트리 꺼내기
            Map<String, CtMethod<?>> entry = queue.get(queueIndex);
            queueIndex = (queueIndex + 1) % queue.size();

            String testClassPath = entry.keySet().iterator().next();
            CtMethod<?> testCase = entry.get(testClassPath);
            String checkString = testClassPath + testCase.getSignature();
            if (zeroMaskes.contains(checkString)) {
                continue;
            }
            String methodSignature = testCase.getSignature(); // 메서드를 고유하게 식별할 키

            // 7-5) PrimitiveTwayTestGenerator 준비
            PrimitiveTwayTestGenerator generator = testGeneratorMap.get(testClassPath);
            if (generator == null) {
                generator = new PrimitiveTwayTestGenerator(testClassPath);
                testGeneratorMap.put(testClassPath, generator);
            }

            // 7-6) skeletal 클래스 및 import/package 정보
            CtClass<?> skeletalClass = skeletalTestClassMap.get(testClassPath);

            String pkgAndImport = PrimitiveParser.getImportMap().get(testClassPath);
            String pkgName = PrimitiveParser.getPackageMap().get(testClassPath);

             // 7-7) Compiler 준비
             Compiler compiler = compilerMap.get(testClassPath);
             if (compiler == null) {
                 compiler = new Compiler(pkgAndImport, pkgName, sharedMinimizer);
                 compilerMap.put(testClassPath, compiler);
             }
             int attemptNumber = generationAttemptMap.getOrDefault(methodSignature, 0);
             
             //  현재 mutate하려는 테스트 정보 출력
             String testMethodName = testCase.getSimpleName();
            //  System.out.println("\n[MUTATE #" + (index + 1) + "] " + testClassPath + " :: " + testMethodName + "()");
             
             // 7-8) 실제 테스트 케이스 생성
             long genStart = System.currentTimeMillis();
             PrimitiveTwayTestGenerator.TwayGenerationResult genResult;
             try {
                 // generateTwayTestCases 메서드에 attemptNumber를 전달하도록 시그니처를 변경해야 합니다.
                 genResult = generator.generateTwayTestCases(testCase, index, testClassPath, skeletalClass,
                         attemptNumber);
             } catch (Exception e) {
                //  System.out.println("Error Occured While Generating Test : " + testClassPath);
                 // // e.printStackTrace(); // 디버깅을 위해 스택 트레이스 출력
                 continue;
             }
             generationTime += System.currentTimeMillis() - genStart;

             //  생성 결과 상태 출력
            //  System.out.println("  → Generation Status: " + genResult.status);

             // 7-9) 생성 결과가 성공인 경우 컴파일 및 실행
             if (genResult.status == PrimitiveTwayTestGenerator.TwayStatus.SUCCESS) {
                //  System.out.println("  → SUCCESS: Compiling and running...");
                 long compStart = System.currentTimeMillis();
                 String simpleName = extractClassName(testClassPath);
                 String newClassName = simpleName + "_P_" + testCase.getSimpleName() + "_" + index;
                 String newMethodName = newClassName.substring(0, 1).toLowerCase() + newClassName.substring(1);
                 generationAttemptMap.put(methodSignature, attemptNumber + 1);
                 Pair<CtMethod, String> compiledPair = compiler.compileEachForPrim(genResult.testPair, newMethodName);
                 compileTime += System.currentTimeMillis() - compStart;

                 if (compiledPair != null) {
                    //  System.out.println("  → Compilation SUCCESS");
                     long runStart = System.currentTimeMillis();
                     CtMethod<?> resultMethod = compiler.runCompiledTestCaseForPrim(compiledPair);
                     if (resultMethod != null) {
                        //  System.out.println("  → Execution SUCCESS - Test saved!");
                         finalTestMethodStringMap
                                 .computeIfAbsent(testClassPath, k -> new ArrayList<>())
                                 .add(resultMethod);
                         parseExceptionalImports(resultMethod, testClassPath);
                         consecutiveSkips = 0; // Reset counter on successful test generation

                         // Print progress every 200 tests
                         if ((index + 1) % 200 == 0) {
                             long elapsed = System.currentTimeMillis() - startTime;
                             long remaining = time_budget - elapsed;
                             System.out.println("[Progress] Generated " + (index + 1) + " tests | " +
                                              "Time: " + elapsed + "ms / " + time_budget + "ms | " +
                                              "Remaining: " + remaining + "ms");
                         }
                     } else {
                        //  System.out.println("  → Execution FAILED - resultMethod is null");
                     }

                     runTime += System.currentTimeMillis() - runStart;
                     // Get class name from the method's parent class
                     String classNameForDeletion = compiledPair.getKey().getParent(CtClass.class).getSimpleName();
                     deleteClassFile(classNameForDeletion, compiler.getPackageName());
                 } else {
                    //  System.out.println("  → Compilation FAILED - compiledPair is null");
                     deleteClassFile(genResult.testPair.getKey().getSimpleName(), compiler.getPackageName());
                 }
                 index++;
              } else {
                  if (genResult.status == PrimitiveTwayTestGenerator.TwayStatus.ALL_COMBINATIONS_EXHAUSTED_FOR_T) {
                      int nextAttemptNumber = attemptNumber + 1;
                      generationAttemptMap.put(methodSignature, nextAttemptNumber);
                      
                      if (consecutiveSkips % 20 == 0) { 
                          System.out.println("[DEBUG-SKIP] Method: " + testMethodName + " | Attempt: " + attemptNumber + " -> " + nextAttemptNumber + " | consecutiveSkips: " + consecutiveSkips + "/" + maxConsecutiveSkips);
                      }
                      
                      continue;
                  } else if (genResult.status == PrimitiveTwayTestGenerator.TwayStatus.DUPLICATE) {
            
                      continue;
                  } else if (genResult.status == PrimitiveTwayTestGenerator.TwayStatus.ERROR) {
                      zeroMaskes.add(testClassPath + testCase.getSignature());
                      continue;
                  }
              }
            // 7-11) 다시 while 반복으로 돌아가 시간 체크 후 다음 queue 항목 처리
        }

        // Print final generation statistics
        long totalElapsed = System.currentTimeMillis() - startTime;
        System.out.println("\n=== Test Generation Completed ===");
        System.out.println("Total tests generated: " + index);
        System.out.println("Total time elapsed: " + totalElapsed + " ms");
        System.out.println("=================================\n");

        } // End of else block for non-empty queue

        // -------------------------------
        // (8) 마지막 남은 finalTestMethodStringMap을 splitedTestList에 추가
        splitedTestList.add(finalTestMethodStringMap);

        // -------------------------------
        // (9) 통계 출력 및 결과 집계
        int listCount = 1;
        int numTotalTest = 0;
        for (Map<String, List<CtMethod<?>>> testContent : splitedTestList) {
            int tempCount = testContent.values().stream().mapToInt(List::size).sum();
            System.out.println("Split " + listCount + ":");
            System.out.println("# of Tests : " + tempCount);
            System.out.println();
            numTotalTest += tempCount;
            listCount++;
        }

         System.out.println("Total Tests: ");
         System.out.println("# of Total Tests : " + numTotalTest);
         System.out.println("");
         System.out.println("Duplicated Tests : " + PrimitiveTwayTestGenerator.dupTests);
         System.out.println("");

         long overhead = PrimitiveTwayTestGenerator.overheadTime;
         System.out.println("Overhead : " + overhead + " ms");
         System.out.println("Num of Compile Fail Tests : " + Config.NUM_COMPILE_FAIL);
         
          // [NEW] Test Minimization 상세 통계 출력 (Minimization 또는 Bucketing 활성화 시에만)
          if (Config.ENABLE_TEST_MINIMIZATION || Config.ENABLE_TEST_BUCKETING) {
              sharedMinimizer.printDetailedStats("SeqP");
          }
        System.out.println("");
        System.out.println("");
        // -------------------------------
        // (10) 각 split별로 실제 파일로 출력 및 컴파일 체크
        for (int i = 0; i < splitedTestList.size(); i++) {
            Map<String, List<CtMethod<?>>> writeMap = splitedTestList.get(i);

            for (Map.Entry<String, List<CtMethod<?>>> entry : writeMap.entrySet()) {
                String testClassKey = entry.getKey();
                CtClass<?> skeletal = skeletalTestClassMap.get(testClassKey).clone();
                String originalName = skeletal.getSimpleName();
                String outputName = originalName + "_P_" + (i + 1);
                skeletal.setSimpleName(outputName);
                
                // Apply normalization to fix nested class this references
                normalizeThisAccessInClass(skeletal);

                // [NEW] Apply bucketing to methods before adding to skeletal
                List<CtMethod<?>> methodsToAdd = entry.getValue();
                if (Config.ENABLE_TEST_BUCKETING && sharedMinimizer != null) {
                    methodsToAdd = applyBucketingToMethodList(methodsToAdd, sharedMinimizer);
                }
                
                for (CtMethod<?> newTestMethod : methodsToAdd) {
                    if (newTestMethod != null) {
                        skeletal.addMethod(newTestMethod.clone());
                    }
                }

                Set<String> allImportsInSet = new LinkedHashSet<>();
                String pkgImport = PrimitiveParser.getImportMap().get(testClassKey);
                if (pkgImport != null && !pkgImport.isEmpty()) {
                    allImportsInSet.addAll(Arrays.asList(pkgImport.split("\\n")));
                }
                Set<String> newImports = additionalImports.get(testClassKey);
                if (newImports != null) {
                    allImportsInSet.addAll(newImports);
                }

                // Collect missing imports from skeletal class (nested class fields, etc.)
                Set<String> missingImports = collectMissingImportsFromSkeletal(skeletal);
                if (missingImports != null && !missingImports.isEmpty()) {
                    allImportsInSet.addAll(missingImports);
                }

                // 4. 중복이 제거된 Set을 다시 하나의 문자열로 합침
                String finalPkgImport = String.join("\n", allImportsInSet);

                fixNullThisAccessElements(skeletal);
                
                System.out.println("[INFO] Applying removeProblematicThisAccess for: " + skeletal.getSimpleName());
                Generater.PrimitiveMutation.PrimitiveTwayTestGenerator.removeProblematicThisAccess(skeletal);
            
                // nested class 참조 분석
                analyzeNestedClassReferences(skeletal);
                
                String skeletalSource;
                try {
                    skeletalSource = skeletal.toString();
                    skeletalSource = fixEmptyConstructors(skeletalSource, skeletal);
                } catch (spoon.SpoonException e) {
                    if (e.getMessage() != null && e.getMessage().contains("Cannot compute access path to type")) {
                        System.err.println("[INFO] Using smart FQN conversion due to nested class issue: " + e.getMessage());         
                        skeletalSource = generateSourceCodeWithSmartFQN(skeletal);     
                    } else {
                        throw e; 
                    }
                }
                
                 // Note: Bucketing is now applied at method list level (before adding to skeletal)
                 // No need to apply bucketing here - methods are already in correct order

                 String finalSourceCode = (finalPkgImport != null ? finalPkgImport + "\n" : "") + skeletalSource;

                 // Apply bucketing headers to source code
                 if (Config.ENABLE_TEST_BUCKETING && sharedMinimizer != null) {
                     finalSourceCode = addBucketingHeadersToSource(finalSourceCode, sharedMinimizer);
                 }

                // Replace Logger.observe with fully qualified name for primitive tests
                finalSourceCode = finalSourceCode.replace("Logger.observe(", "RegressionOracles.RegressionUtil.Logger.observe(");

                String lineToReplaceOriginalDynamic = "return new TestSuite(" + originalName + ".class);";
                String replacementLine = "return new TestSuite(" + outputName + ".class);";
                finalSourceCode = finalSourceCode.replace(lineToReplaceOriginalDynamic, replacementLine);
                
                // FQN 변환 및 CtThisAccess 수정 적용
                finalSourceCode = applySafeCodeGeneration(finalSourceCode, skeletal);

                // Apply final string-level normalization before writing file
                if (finalSourceCode.contains(".this")) {
                    java.util.regex.Pattern pattern = java.util.regex.Pattern.compile(
                        "\\b[A-Za-z_][A-Za-z0-9_]*(?:\\.[A-Za-z_][A-Za-z0-9_]*)+\\.this\\b"
                    );
                    finalSourceCode = pattern.matcher(finalSourceCode).replaceAll("this");
                    java.util.regex.Pattern assignmentPattern = java.util.regex.Pattern.compile(
                        "\\b[A-Za-z_][A-Za-z0-9_]*(?:\\.[A-Za-z_][A-Za-z0-9_]*)+\\.this\\s*[=;]"
                    );
                    finalSourceCode = assignmentPattern.matcher(finalSourceCode).replaceAll("this$1");
                    java.util.regex.Pattern specificPattern = java.util.regex.Pattern.compile(
                        "(\\w+\\s*=\\s*)[A-Za-z_][A-Za-z0-9_]*(?:\\.[A-Za-z_][A-Za-z0-9_]*)+\\.this"
                    );
                    finalSourceCode = specificPattern.matcher(finalSourceCode).replaceAll("$1this");
                }

                CtClass<?> originalSkeletal = skeletalTestClassMap.get(testClassKey);
                finalSourceCode = fixConstructorCallsInMain(finalSourceCode, originalSkeletal);

    
                if (!originalName.equals(outputName) && originalName != null && outputName != null) {
                    // Replace constructor calls: "new OriginalClass(" -> "new NewClass("
                    java.util.regex.Pattern constructorPattern = java.util.regex.Pattern.compile(
                        "\\bnew\\s+" + java.util.regex.Pattern.quote(originalName) + "\\s*\\("
                    );
                    finalSourceCode = constructorPattern.matcher(finalSourceCode).replaceAll("new " + outputName + "(");

                    // Replace variable declarations: "OriginalClass var = " -> "NewClass var = "
                    java.util.regex.Pattern variablePattern = java.util.regex.Pattern.compile(
                        "\\b" + java.util.regex.Pattern.quote(originalName) + "\\s+([a-zA-Z_][a-zA-Z0-9_]*)\\s*="
                    );
                    finalSourceCode = variablePattern.matcher(finalSourceCode).replaceAll(outputName + " $1 =");

                    // Replace class references in nested class access: "OriginalClass.NestedClass" -> "NewClass.NestedClass"
                    java.util.regex.Pattern nestedClassPattern = java.util.regex.Pattern.compile(
                        "\\b" + java.util.regex.Pattern.quote(originalName) + "\\.([A-Z][a-zA-Z0-9_]*)"
                    );
                    finalSourceCode = nestedClassPattern.matcher(finalSourceCode).replaceAll(outputName + ".$1");

                    String baseClassName = originalName;
                    if (originalName.contains("_P_")) {
                        baseClassName = originalName.substring(0, originalName.indexOf("_P_"));
                    }
                    
                    // Capitalize first letter to match class name in assertions
                    if (baseClassName.length() > 0 && Character.isLowerCase(baseClassName.charAt(0))) {
                        baseClassName = Character.toUpperCase(baseClassName.charAt(0)) + baseClassName.substring(1);
                    }
                    
                    // Pattern to match: Assert.method("...baseClassName_P_anything_number..." where anything can include $ for inner classes
                    // This will match: TestScalars_P_testMethod_123, TestScalars_P_testMethod_123$InnerClass, etc.
                    java.util.regex.Pattern assertionStringPattern = java.util.regex.Pattern.compile(
                        "(Assert\\.[a-zA-Z]+\\s*\\(\\s*[\"'])([^\"']*?)" + 
                        java.util.regex.Pattern.quote(baseClassName) + "_P_[a-zA-Z0-9_]+?" +
                        "([\\$][a-zA-Z0-9_]+)?([^\"']*?[\"'])"
                    );
                    finalSourceCode = assertionStringPattern.matcher(finalSourceCode).replaceAll("$1$2" + outputName + "$3$4");
                }

                // Preserve FQN from original source file
                finalSourceCode = preserveFQNFromOriginalInMain(finalSourceCode, originalSkeletal);

                writeFile(outputName, finalSourceCode, testClassKey);
                Compiler compiler2 = compilerMap.get(testClassKey);
                boolean errorFree = compiler2.compileFile(outputName, finalSourceCode);
                if (!errorFree) {
                    // 컴파일 실패 시, import 관련 에러인지 확인하고 제거 후 재시도 (1회)
                    System.out.println("Output class " + outputName + " is not compiled. Checking for import-related errors...");
                    String fixedSourceCode = removeProblematicImports(finalSourceCode);
                    if (!fixedSourceCode.equals(finalSourceCode)) {
                        // import가 제거되었으면 파일 다시 쓰고 컴파일 재시도
                        System.out.println("Attempting recompilation after removing problematic imports...");
                        writeFile(outputName, fixedSourceCode, testClassKey);
                        errorFree = compiler2.compileFile(outputName, fixedSourceCode);
                        if (errorFree) {
                            System.out.println("Output class " + outputName + " compiled successfully after removing problematic imports.");
                        } else {
                            System.out.println("Output class " + outputName + " is still not compiled even after fixing imports.");
                        }
                    } else {
                        System.out.println("Output class " + outputName + " compilation failed. Could not identify problematic imports.");
                    }
                }
            }
        }

         // ========================================
         // (11) Queue에 있던 원본 baseTestPath 파일들을 컴파일
         // ========================================
        //  System.out.println("\n[PRE-COMPILATION] Compiling base test files from queue before finalizing stats...");
         Set<String> baseTestPathsToCompile = collectBaseTestPathsFromQueue(queue);
         if (!baseTestPathsToCompile.isEmpty()) {
             compileBaseTestFiles(baseTestPathsToCompile);
         }

         runStat.setCollectingTime(collectingTime);
         runStat.setGenerateTime(generationTime);
         runStat.setCompileTime(compileTime);
         runStat.setRunningTime(runTime);
         runStat.setType("Seq-P");
         runStat.setTestId(Config.BUILD_PATH);
         runStat.setTotalTime(System.currentTimeMillis() - startTime);

         // Extended tests already converted before parsing
         // Compile extended test files before writing dive_log.csv
         compileExtendedTests();

        File f = new File(Config.BUILD_PATH + File.separator + "dive_log.csv");
        if (!f.exists()) {
            writeLog("dive_log.csv", runStat.getHead() + "\n");
        }
        writeLog("dive_log.csv", runStat.getStat() + "\n");

        System.out.println("[DEBUG] handlePrimitiveTestCases completed - exiting program");
        System.exit(0);
    }

    private static void convertExtendedTestsToJUnit4() {
        Set<String> allExtendedTests = new HashSet<>();
        
        if (Config.EXTENDED_TESTS != null && !Config.EXTENDED_TESTS.isEmpty()) {
            allExtendedTests.addAll(Config.EXTENDED_TESTS);
        }
        
        if (allExtendedTests.isEmpty()) {
            System.out.println("No extended tests to convert.");
            return;
        }
        
        System.out.println("\n================================================================");
        System.out.println("       CONVERTING EXTENDED CLASSES TO JUNIT 4                  ");
        System.out.println("================================================================");
        System.out.println("Extended classes to convert: " + allExtendedTests.size());
        
        Launcher launcher = new Launcher();
        launcher.getEnvironment().setNoClasspath(true);
        launcher.getEnvironment().setAutoImports(true);
        launcher.getEnvironment().setCommentEnabled(true);
        
        int convertedCount = 0;
        int skippedCount = 0;
        List<String> failedCompilations = new ArrayList<>();
        Map<String, String> convertedFiles = new HashMap<>();  // Track converted files (class -> fullPath)
        
        for (String extendedClass : allExtendedTests) {
            extendedClass = extendedClass.trim();
            if (extendedClass.isEmpty()) {
                continue;
            }
            
            String filePath = extendedClass.replace('.', File.separatorChar) + ".java";
            String fullPath = Config.BUILD_PATH + File.separator + filePath;
            File file = new File(fullPath);
            
            if (!file.exists()) {
                // System.out.println("  [SKIP] File not found: " + fullPath);
                skippedCount++;
                continue;
            }
            
            convertedFiles.put(extendedClass, fullPath);
            
            try {
                launcher.addInputResource(fullPath);
                CtModel model = launcher.buildModel();
                
                boolean wasConverted = false;
                
                for (CtType<?> type : model.getAllTypes()) {
                    if (!(type instanceof CtClass)) {
                        continue;
                    }
                    
                    CtClass<?> ctClass = (CtClass<?>) type;
                    CtTypeReference<?> superClass = ctClass.getSuperclass();
                    
                    // Only convert if extends TestCase directly
                    boolean extendsTestCase = superClass != null && 
                                             "junit.framework.TestCase".equals(superClass.getQualifiedName());
                    boolean isAbstract = ctClass.hasModifier(ModifierKind.ABSTRACT);
                    
                    if (extendsTestCase) {
                        System.out.println("  [CONVERT] " + extendedClass + " (abstract: " + isAbstract + ")");
                        
                        // Remove TestCase superclass
                        ctClass.setSuperclass(null);
                        
                        // Remove suite() and main() methods
                        for (CtMethod<?> m : new ArrayList<>(ctClass.getMethods())) {
                            if (("suite".equals(m.getSimpleName()) && m.isStatic() && m.getParameters().isEmpty())
                                    || "main".equals(m.getSimpleName())) {
                                ctClass.removeMethod(m);
                            }
                        }
                        
                        // Convert JUnit 3 style constructors (String name parameter) to default constructor
                        // Both abstract and concrete classes get zero-param constructors
                        boolean hasDefaultConstructor = false;
                        CtBlock<?> savedBodyForAbstract = null;
                        
                        // First pass: save body from String constructor
                        for (CtConstructor<?> ctor : ctClass.getConstructors()) {
                            List<CtParameter<?>> params = ctor.getParameters();
                            
                            // Check if already has a default constructor
                            if (params.isEmpty()) {
                                hasDefaultConstructor = true;
                            }
                            
                            // Save body from String constructor before removing
                            if (isAbstract && extendsTestCase && 
                                params.size() == 1 && 
                                "java.lang.String".equals(params.get(0).getType().getQualifiedName())) {
                                
                                CtBlock<?> oldBody = ctor.getBody();
                                List<CtStatement> statementsToKeep = new ArrayList<>();
                                
                                if (oldBody != null) {
                                    for (CtStatement stmt : oldBody.getStatements()) {
                                        // Skip super() or super(name) calls
                                        boolean isSuperCall = false;
                                        
                                        if (stmt instanceof CtInvocation) {
                                            CtInvocation<?> invocation = (CtInvocation<?>) stmt;
                                            if (invocation.getTarget() instanceof CtSuperAccess) {
                                                isSuperCall = true;
                                            }
                                        }
                                        
                                        String stmtStr = stmt.toString();
                                        if (stmtStr.contains("super(")) {
                                            isSuperCall = true;
                                        }
                                        
                                        if (!isSuperCall) {
                                            statementsToKeep.add(stmt);
                                        }
                                    }
                                }
                                
                                if (!statementsToKeep.isEmpty()) {
                                    savedBodyForAbstract = launcher.getFactory().createBlock();
                                    for (CtStatement stmt : statementsToKeep) {
                                        savedBodyForAbstract.addStatement(stmt.clone());
                                    }
                                }
                            }
                        }
                        
                        // Second pass: remove String constructors
                        for (CtConstructor<?> ctor : new ArrayList<>(ctClass.getConstructors())) {
                            List<CtParameter<?>> params = ctor.getParameters();
                            
                            if (extendsTestCase && 
                                params.size() == 1 && 
                                "java.lang.String".equals(params.get(0).getType().getQualifiedName()) &&
                                ctor.getModifiers().contains(ModifierKind.PUBLIC)) {
                                
                                ctClass.removeConstructor((CtConstructor) ctor);
                            }
                        }
                        
                        // Remove class-level annotations
                        for (CtAnnotation<?> ann : new ArrayList<>(ctClass.getAnnotations())) {
                            ctClass.removeAnnotation(ann);
                        }
                        
                        // Process setUp/tearDown methods
                        for (CtMethod<?> method : new ArrayList<>(ctClass.getMethods())) {
                            String methodName = method.getSimpleName();
                            boolean isSetUp = "setUp".equals(methodName) && method.getParameters().isEmpty();
                            boolean isTearDown = "tearDown".equals(methodName) && method.getParameters().isEmpty();
                            
                            if (isSetUp || isTearDown) {
                                // Remove super.setUp() or super.tearDown() calls
                                CtBlock<?> body = method.getBody();
                                if (body != null) {
                                    for (Iterator<CtStatement> iterator = body.getStatements().iterator(); iterator.hasNext();) {
                                        CtStatement stmt = iterator.next();
                                        if (stmt instanceof CtInvocation) {
                                            CtInvocation<?> invocation = (CtInvocation<?>) stmt;
                                            if (invocation.getTarget() instanceof CtSuperAccess
                                                    && invocation.getArguments().isEmpty()) {
                                                if (methodName.equals(invocation.getExecutable().getSimpleName())) {
                                                    iterator.remove();
                                                    break;
                                                }
                                            }
                                        }
                                    }
                                }
                                
                                // Remove @Override annotation
                                for (CtAnnotation<?> ann : new ArrayList<>(method.getAnnotations())) {
                                    if (ann.getAnnotationType().getQualifiedName().equals(Override.class.getName())) {
                                        method.removeAnnotation(ann);
                                    }
                                }
                                
                                // Make public if not already
                                Set<ModifierKind> modifiers = new HashSet<>(method.getModifiers());
                                if (!modifiers.contains(ModifierKind.PUBLIC)) {
                                    modifiers.remove(ModifierKind.PROTECTED);
                                    modifiers.remove(ModifierKind.PRIVATE);
                                    modifiers.add(ModifierKind.PUBLIC);
                                    method.setModifiers(modifiers);
                                }
                                
                                // Add @Before or @After annotation if not already present
                                boolean alreadyHasAnnotation = method.getAnnotations().stream()
                                        .anyMatch(a -> a.getAnnotationType().getSimpleName().equals("Before") ||
                                                      a.getAnnotationType().getSimpleName().equals("After"));
                                
                                if (!alreadyHasAnnotation) {
                                    String annotationName = isSetUp ? "Before" : "After";
                                    String annotationType = isSetUp ? "org.junit.Before" : "org.junit.After";
                                    CtAnnotation annotation = launcher.getFactory().Core().createAnnotation();
                                    CtTypeReference<?> annotationRef = launcher.getFactory().Code().createCtTypeReference(
                                        launcher.getFactory().Type().get(annotationType).getActualClass());
                                    annotation.setAnnotationType(annotationRef);
                                    method.addAnnotation(annotation);
                                }
                            }
                        }
                        
                        // Add default constructor if needed
                        if (!hasDefaultConstructor) {
                            CtConstructor defaultCtor = launcher.getFactory().createConstructor();
                            
                            // For abstract classes, use saved body; for concrete, use empty body
                            if (isAbstract && savedBodyForAbstract != null) {
                                defaultCtor.setBody(savedBodyForAbstract);
                            } else {
                                defaultCtor.setBody(launcher.getFactory().createBlock());
                            }
                            
                            defaultCtor.addModifier(ModifierKind.PUBLIC);
                            ctClass.addConstructor(defaultCtor);
                        }
                        
                        wasConverted = true;
                    }
                }
                
                if (wasConverted) {
                    // Save the converted file using PrettyPrinter
                    for (CtClass<?> ctClass : model.getElements(new TypeFilter<>(CtClass.class))) {
                        if (ctClass.getPosition() == null || ctClass.getPosition().getFile() == null) {
                            continue;
                        }
                        File original = ctClass.getPosition().getFile();
                        if (!original.getAbsolutePath().equals(fullPath)) {
                            continue;
                        }
                        
                        DefaultJavaPrettyPrinter printer = new DefaultJavaPrettyPrinter(launcher.getEnvironment());
                        String finalSrc = printer.printTypes(ctClass);
                        
                        // Add JUnit4 imports if needed
                        boolean extendsTestBase = ctClass.getSuperclass() != null &&
                                                 ctClass.getSuperclass().getQualifiedName() != null &&
                                                 (ctClass.getSuperclass().getQualifiedName().contains("TestCase") ||
                                                  ctClass.getSuperclass().getQualifiedName().contains("TestBase"));
                        
                        if (!extendsTestBase && !finalSrc.contains("import static org.junit.Assert.*;")) {
                            finalSrc = finalSrc.replaceFirst("(package [^;]+;\\s*)", "$1\n\nimport static org.junit.Assert.*;\nimport org.junit.Test;\n");
                        } else if (extendsTestBase && !finalSrc.contains("import org.junit.Test;")) {
                            finalSrc = finalSrc.replaceFirst("(package [^;]+;\\s*)", "$1\n\nimport org.junit.Test;\n");
                        }
                        
                        // Post-process: Remove any remaining super() calls that Spoon might have added
                        finalSrc = finalSrc.replaceAll("super\\([^)]*\\);\\s*", "");
                        
                        try (FileWriter writer = new FileWriter(fullPath)) {
                            writer.write(finalSrc);
                        }
                        
                        // Compile the converted file
                        try {
                            String simpleName = ctClass.getSimpleName();
                            String packageName = ctClass.getPackage() != null ? ctClass.getPackage().getQualifiedName() : "";
                            
                            System.out.println("  [COMPILE] Compiling " + simpleName + "...");
                            Compiler compiler = new Compiler("", packageName, null);
                            boolean compiled = compiler.compileFile(simpleName, finalSrc);
                            
                            if (compiled) {
                                System.out.println("  [SUCCESS] Compiled successfully");
                            } else {
                                System.err.println("  [WARNING] Compilation failed for " + simpleName);
                                // Add to failed list for retry (might depend on other extended classes)
                                failedCompilations.add(extendedClass);
                            }
                        } catch (Exception compileEx) {
                            System.err.println("  [WARNING] Compilation error: " + compileEx.getMessage());
                            failedCompilations.add(extendedClass);
                        }
                        
                        break;
                    }
                    convertedCount++;
                } else {
                    System.out.println("  [SKIP] Not a TestCase subclass: " + extendedClass);
                    skippedCount++;
                }
                
                // Clear launcher for next file
                launcher = new Launcher();
                launcher.getEnvironment().setNoClasspath(true);
                launcher.getEnvironment().setAutoImports(true);
                launcher.getEnvironment().setCommentEnabled(true);
                
            } catch (Exception e) {
                System.err.println("  [ERROR] Failed to convert " + extendedClass + ": " + e.getMessage());
                skippedCount++;
            }
        }
        
        System.out.println("----------------------------------------------------------------");
        System.out.println("Conversion complete:");
        System.out.println("  Converted: " + convertedCount);
        System.out.println("  Skipped: " + skippedCount);
        System.out.println("  Failed compilations: " + failedCompilations.size());
        System.out.println("================================================================");
        
        // If any classes were converted, prepend BUILD_PATH to classpath
        // This ensures generated tests use the converted JUnit4 versions
        if (convertedCount > 0) {
            String pathSeparator = System.getProperty("path.separator");
            String oldClassPath = Config.CLASS_PATH;
            Config.CLASS_PATH = Config.BUILD_PATH + pathSeparator + oldClassPath;
            System.out.println("\n[CLASSPATH] Prepended BUILD_PATH to classpath for converted classes");
            System.out.println("[CLASSPATH] BUILD_PATH: " + Config.BUILD_PATH);
            System.out.println("[CLASSPATH] Updated CLASS_PATH (first 200 chars): " + 
                Config.CLASS_PATH.substring(0, Math.min(200, Config.CLASS_PATH.length())) + "...");
        }
        
        // Pass 2: Retry failed compilations (they might depend on other extended classes)
        if (!failedCompilations.isEmpty()) {
            System.out.println("\n================================================================");
            System.out.println("       RETRYING FAILED COMPILATIONS (PASS 2)                   ");
            System.out.println("================================================================");
            System.out.println("Retrying " + failedCompilations.size() + " failed compilations...\n");
            
            int retrySuccessCount = 0;
            int retryFailCount = 0;
            
            for (String extendedClass : failedCompilations) {
                // Only retry if file was actually converted (not skipped due to file not found)
                if (!convertedFiles.containsKey(extendedClass)) {
                    continue;
                }
                
                String fullPath = convertedFiles.get(extendedClass);
                File file = new File(fullPath);
                
                try {
                    System.out.println("  [RETRY] " + extendedClass);
                    
                    // Read the already-converted source
                    String finalSrc = new String(Files.readAllBytes(file.toPath()));
                    
                    // Extract class name and package
                    String simpleName = extendedClass.substring(extendedClass.lastIndexOf('.') + 1);
                    String packageName = extendedClass.contains(".") ? 
                        extendedClass.substring(0, extendedClass.lastIndexOf('.')) : "";
                    
                    // Retry compilation
                    Compiler compiler = new Compiler("", packageName, null);
                    boolean compiled = compiler.compileFile(simpleName, finalSrc);
                    
                    if (compiled) {
                        System.out.println("  [SUCCESS] Compiled successfully on retry");
                        retrySuccessCount++;
                    } else {
                        System.err.println("  [FAIL] Still failed on retry");
                        retryFailCount++;
                    }
                    
                } catch (Exception e) {
                    System.err.println("  [ERROR] Retry failed: " + e.getMessage());
                    retryFailCount++;
                }
            }
            
            System.out.println("\n----------------------------------------------------------------");
            System.out.println("Retry complete:");
            System.out.println("  Successful: " + retrySuccessCount);
            System.out.println("  Failed: " + retryFailCount);
            System.out.println("================================================================");
        }
        
        System.out.println("\n");
    }

    private static Set<String> collectBaseTestPathsFromQueue(List<Map<String, CtMethod<?>>> queue) {
         Set<String> baseTestPaths = new LinkedHashSet<>();
         
         if (queue == null || queue.isEmpty()) {
             System.out.println("[INFO] queue is empty - no base test paths to collect");
             return baseTestPaths;
         }
         
         for (Map<String, CtMethod<?>> entry : queue) {
             for (String testClassPath : entry.keySet()) {
                 baseTestPaths.add(testClassPath);
             }
         }
         
         
         return baseTestPaths;
    }
     

    private static void compileBaseTestFiles(Set<String> baseTestPaths) {
         if (baseTestPaths == null || baseTestPaths.isEmpty()) {
             System.out.println("[INFO] No base test files to compile");
             return;
         }
         
         System.out.println("\n================================================================");
         System.out.println("       COMPILING BASE TEST FILES FROM QUEUE               ");
         System.out.println("================================================================");
         System.out.println("Base test files to compile: " + baseTestPaths.size() + "\n");
         
         int successCount = 0;
         int failCount = 0;
         List<String> failedFiles = new ArrayList<>();
         
         for (String baseTestPath : baseTestPaths) {
             try {
                 File testFile = new File(baseTestPath);
                 
                 if (!testFile.exists()) {
                    //  System.out.println("  [SKIP] File not found: " + baseTestPath);
                     failCount++;
                     failedFiles.add(baseTestPath);
                     continue;
                 }
                 
                 // 파일 내용 읽기
                 String sourceCode = new String(Files.readAllBytes(testFile.toPath()));
                 
                 String fileName = testFile.getName();
                 String className = fileName.replace(".java", "");
                 
                 // 패키지 이름은 파일 내용에서 추출
                 String packageName = extractPackageNameFromSource(sourceCode);
                 if (packageName == null || packageName.isEmpty()) {
                     packageName = "";
                 }
                 
                 System.out.println("  [COMPILE] " + className + " (package: " + (packageName.isEmpty() ? "default" : packageName) + ")");
                 
                  // 컴파일
                  Compiler compiler = new Compiler("", packageName, null);
                  boolean compiled = compiler.compileFile(className, sourceCode);
                 
                 if (compiled) {
                     System.out.println("  [SUCCESS] Compiled: " + className);
                     successCount++;
                 } else {
                     System.out.println("  [FAIL] Failed to compile: " + className);
                     failCount++;
                     failedFiles.add(baseTestPath);
                 }
                 
             } catch (Exception e) {
                 System.out.println("  [ERROR] Exception while compiling " + baseTestPath + ": " + e.getMessage());
                 failCount++;
                 failedFiles.add(baseTestPath);
             }
         }
         
         System.out.println("\n================================================================");
         System.out.println("Compilation Results:");
         System.out.println("  Successful: " + successCount);
         System.out.println("  Failed: " + failCount);
         System.out.println("================================================================\n");
         
         if (!failedFiles.isEmpty()) {
             System.out.println("Failed files:");
             for (String file : failedFiles) {
                 System.out.println("  - " + file);
             }
         }
    }
     

    private static String extractPackageNameFromSource(String sourceCode) {
         if (sourceCode == null || sourceCode.isEmpty()) {
             return "";
         }
         
         java.util.regex.Pattern pattern = java.util.regex.Pattern.compile(
             "^\\s*package\\s+([a-zA-Z_][a-zA-Z0-9_.]*);", 
             java.util.regex.Pattern.MULTILINE
         );
         java.util.regex.Matcher matcher = pattern.matcher(sourceCode);
         
         if (matcher.find()) {
             return matcher.group(1);
         }
         
         return "";
    }

    private static void compileExtendedTests() {
         // Combine REFERENCE_LISTS and EXTENDED_TESTS to compile all necessary files
         Set<String> allTestsToCompile = new HashSet<>();

         if (Config.REFERENCE_LISTS != null && !Config.REFERENCE_LISTS.isEmpty()) {
             allTestsToCompile.addAll(Config.REFERENCE_LISTS);
         }

         if (Config.EXTENDED_TESTS != null && !Config.EXTENDED_TESTS.isEmpty()) {
             allTestsToCompile.addAll(Config.EXTENDED_TESTS);
         }

        if (allTestsToCompile.isEmpty()) {
            System.out.println("No extended tests to compile.");
            return;
        }

        System.out.println("Compiling referenced files...");

        for (String extendedTestClass : allTestsToCompile) {
            extendedTestClass = extendedTestClass.trim();
            if (extendedTestClass.isEmpty()) {
                continue;
            }

            // Convert class name to file path
            String filePath = extendedTestClass.replace('.', File.separatorChar) + ".java";
            String fullPath = Config.BUILD_PATH + File.separator + filePath;

            // Check if .class file already exists
            String classFilePath = extendedTestClass.replace('.', File.separatorChar) + ".class";
            String fullClassPath = Config.BUILD_PATH + File.separator + classFilePath;
            File classFile = new File(fullClassPath);

            if (classFile.exists()) {
                continue;
            }

            File testFile = new File(fullPath);
            if (!testFile.exists()) {
                continue;
            }

            try {
                // Read the file content
                String sourceCode = new String(java.nio.file.Files.readAllBytes(testFile.toPath()));

                // Extract class name from file path
                String className = extendedTestClass.substring(extendedTestClass.lastIndexOf('.') + 1);

                // Use compileWholeClassFileForPrim which handles package and dependencies properly
                List<Diagnostic<? extends JavaFileObject>> errorMessage = Compiler.compileWholeClassFileForPrim(className, sourceCode);

                boolean compiled = true;
                for (Diagnostic e : errorMessage) {
                    if (e.getKind() == Diagnostic.Kind.ERROR) {
                        compiled = false;
                        break;
                    }
                }

                if (!compiled) {
                    for (Diagnostic<? extends JavaFileObject> diagnostic : errorMessage) {
                        if (diagnostic.getKind() == Diagnostic.Kind.ERROR) {
                            System.out.println(diagnostic.toString());
                        }
                    }
                }

            } catch (Exception e) {
                // Handle exception silently
            }
        }
    }

    private static void parseExceptionalImports(CtMethod<?> method, String testClassPath) {
        List<CtTry> tryBlocks = method.getElements(new TypeFilter<>(CtTry.class));

        for (CtTry tryBlock : tryBlocks) {
            for (CtCatch catcher : tryBlock.getCatchers()) {
                CtTypeReference<?> typeRef = catcher.getParameter().getType();
                String qualifiedName = typeRef.getQualifiedName();

                if (isValidSource(qualifiedName)) {
                    additionalImports.computeIfAbsent(testClassPath, k -> new HashSet<>())
                            .add("import " + qualifiedName + ";");
                }
            }
        }
    }

    private static boolean isValidSource(String sourceClass) {
        return !(sourceClass.startsWith("java.lang.System") ||
                sourceClass.startsWith("java.lang.") ||
                sourceClass.startsWith("java.lang.Class") ||
                sourceClass.startsWith("sun.") ||
                sourceClass.startsWith("com.sun.") ||
                sourceClass.startsWith("jdk.internal.") ||
                sourceClass.startsWith("<evosuite>"));
    }

    /**
     * write to file
     *
     * @param fileName
     * @param clazz
     * @throws Exception
     */
    /**
     * Unified method to write test files.
     * Route to appropriate output directory based on ASSEMBLE_MODE:
     * - seqc: Uses Config.OUTPUT_PATH
     * - seqp: Uses directory extracted from testClassKey
     *
     * @param fileName Name of the test file (without .java extension)
     * @param clazz Source code content
     * @param testClassKey Optional key for seqp mode (can be null for seqc mode)
     * @throws Exception if file writing fails
     */
    private static void writeFile(String fileName, String clazz, String testClassKey) throws Exception {
        String outputPath;

        // Determine output path based on ASSEMBLE_MODE
        if (ASSEMBLE_MODE.equalsIgnoreCase("seqp") && testClassKey != null) {
            // seqp mode: extract directory from testClassKey
            outputPath = extractDirPath(testClassKey);
            System.out.println("fileName: " + fileName);
            System.out.println("testClassKey: " + testClassKey);
            System.out.println("finalPath: " + outputPath + File.separator + fileName + ".java");
        } else {
            // seqc mode or others: use Config.OUTPUT_PATH
            outputPath = Config.OUTPUT_PATH;
        }

        String finalPath = outputPath + File.separator + fileName + ".java";
        File sourceFile = new File(finalPath);

        try {
            System.out.println("[MegaTest Generated] " + sourceFile.getAbsolutePath());
            sourceFile.createNewFile();
        } catch (IOException e) {
            System.out.println("File Name : " + fileName);
        }

        FileWriter fileWriter = new FileWriter(sourceFile.getAbsoluteFile());
        PrintWriter printWriter = new PrintWriter(fileWriter);
        printWriter.print(clazz);

        if (ASSEMBLE_MODE.equalsIgnoreCase("seqp")) {
            System.out.println("File Written : " + finalPath);
            System.out.println("==============================");
        }

        printWriter.close();
    }

    /**
     * Overloaded method for backward compatibility (2-argument version).
     * Calls unified writeFile method with testClassKey = null.
     * Used for seqc mode where testClassKey is not needed.
     */
    private static void writeFile(String fileName, String clazz) throws Exception {
        writeFile(fileName, clazz, null);
    }


    private static String extractDirPath(String classPath) {
        int lastSeparatorIndex = classPath.lastIndexOf(File.separator);
        if (lastSeparatorIndex != -1) {
            return classPath.substring(0, lastSeparatorIndex);
        } else {
            return "";
        }
    }

    /**
     * Fix empty constructors in skeletal classes that extend custom TestCase classes
     * Note: After conversion, abstract TestCase classes should have zero-param constructors,
     * so child classes no longer need super("") calls
     */
    private static String fixEmptyConstructors(String sourceCode, spoon.reflect.declaration.CtClass<?> skeletal) {
        // No longer needed - abstract TestCase classes now have zero-param constructors
        // Child classes can use implicit super() call
        return sourceCode;
    }

    /**
     * CtThisAccess 요소의 null 타겟 문제를 수정 (PrimitiveTwayTestGenerator에서 복사)
     */
    private static void fixNullThisAccessElements(spoon.reflect.declaration.CtElement element) {
        element.accept(new spoon.reflect.visitor.CtScanner() {
            @Override
            public <T> void visitCtThisAccess(spoon.reflect.code.CtThisAccess<T> thisAccess) {
                if (thisAccess.getTarget() == null) {
                    // null 타겟을 가진 CtThisAccess를 암시적 this로 설정
                    thisAccess.setImplicit(true);
                }
                super.visitCtThisAccess(thisAccess);
            }
        });
    }

    /**
     * _mut 변수의 타입을 FQN으로 변환 (PrimitiveTwayTestGenerator에서 복사)
     */
    private static String convertMutVariablesToFQN(String sourceCode, spoon.reflect.declaration.CtClass<?> clazz) {
        if (sourceCode == null || clazz == null) return sourceCode;
        
        // _mut로 끝나는 변수 선언을 찾아서 타입을 FQN으로 변경
        java.util.regex.Pattern pattern = java.util.regex.Pattern.compile(
            "\\b([A-Za-z_][A-Za-z0-9_]*(?:\\.[A-Za-z_][A-Za-z0-9_]*)*(?:\\[\\])?)\\s+(\\w+_mut)\\s*="
        );
        java.util.regex.Matcher matcher = pattern.matcher(sourceCode);
        StringBuffer sb = new StringBuffer();
        
        while (matcher.find()) {
            String typeName = matcher.group(1);
            String variableName = matcher.group(2);
            
            // 이미 FQN(점을 포함)인 경우는 변환하지 않음
            if (typeName.contains(".")) {
                matcher.appendReplacement(sb, matcher.group());
            } else {
                // 클래스의 모든 변수에서 해당 타입의 FQN을 찾기
                String fqnTypeName = findFQNForType(clazz, typeName);
                if (fqnTypeName != null && !fqnTypeName.equals(typeName)) {
                    matcher.appendReplacement(sb, fqnTypeName + " " + variableName + " =");
                } else {
                    matcher.appendReplacement(sb, matcher.group());
                }
            }
        }
        matcher.appendTail(sb);
        
        return sb.toString();
    }
    
    /**
     * 클래스에서 simple type name에 해당하는 FQN을 찾기 (PrimitiveTwayTestGenerator에서 복사)
     */
    private static String findFQNForType(spoon.reflect.declaration.CtClass<?> clazz, String simpleTypeName) {
        try {
            // 클래스 내의 모든 로컬 변수를 스캔하여 타입 정보 수집
            final java.util.Map<String, String> typeMap = new java.util.HashMap<>();
            
            clazz.accept(new spoon.reflect.visitor.CtScanner() {
                @Override
                public <T> void visitCtLocalVariable(spoon.reflect.code.CtLocalVariable<T> localVar) {
                    if (localVar.getType() != null) {
                        String simple = localVar.getType().getSimpleName();
                        String qualified = localVar.getType().getQualifiedName();
                        if (!simple.equals(qualified)) {
                            typeMap.put(simple, qualified);
                        }
                    }
                    super.visitCtLocalVariable(localVar);
                }
            });
            
            return typeMap.get(simpleTypeName);
        } catch (Exception e) {
            return null;
        }
    }

    /**
     * nested class 참조를 스마트하게 FQN으로 변환 (일반화된 방법) - PrimitiveTwayTestGenerator에서 복사
     */
    private static String generateSourceCodeWithSmartFQN(spoon.reflect.declaration.CtClass<?> clazz) {
        System.err.println("\n[DEBUG] Using smart FQN conversion for " + clazz.getSimpleName());
        
        try {
            spoon.reflect.declaration.CtClass<?> workingClazz = clazz.clone();
            
            workingClazz.accept(new spoon.reflect.visitor.CtScanner() {
                @Override
                public <T> void visitCtTypeReference(spoon.reflect.reference.CtTypeReference<T> reference) {
                    try {
                        String qualifiedName = reference.getQualifiedName();
                        
                        // 모든 nested class 참조를 처리하되, 접근성 문제가 있을 것 같은 것들만
                        if (qualifiedName != null && qualifiedName.contains("$")) {
                            
                            // 접근성 문제가 있을 법한 패턴들 체크
                            boolean isProblematic = isProblematicNestedClass(qualifiedName, clazz);
                            
                            if (isProblematic) {
                                System.err.println("  Converting problematic nested class: " + qualifiedName);
                                
                                // FQN으로 변환
                                String fqnDotNotation = qualifiedName.replace("$", ".");
                                reference.setSimpleName(fqnDotNotation);
                                reference.setPackage(null);
                                reference.setDeclaringType(null);
                                
                                System.err.println("  -> Converted to FQN: " + fqnDotNotation);
                            } else {
                                System.err.println("  Skipping non-problematic nested class: " + qualifiedName);
                            }
                        }
                    } catch (Exception e) {
                        System.err.println("  Exception: " + e.getMessage());
                    }
                    super.visitCtTypeReference(reference);
                }
            });
            
            String result = workingClazz.toString();
            System.err.println("  Successfully generated source code with smart FQN");
            return result;
            
        } catch (Exception e) {
            System.err.println("  Failed smart FQN approach: " + e.getMessage());
            throw e;
        }
    }
    
    /**
     * nested class가 접근성 문제를 일으킬 가능성이 있는지 판단 - PrimitiveTwayTestGenerator에서 복사
     */
    private static boolean isProblematicNestedClass(String qualifiedName, spoon.reflect.declaration.CtClass<?> contextClass) {
        // 1. 다른 패키지의 nested class인 경우
        String contextPackage = contextClass.getPackage().getQualifiedName();
        if (!qualifiedName.startsWith(contextPackage + ".")) {
            System.err.println("    -> Different package, likely problematic");
            return true;
        }
        
        // 2. 특정 알려진 문제 패턴들
        String[] problematicPatterns = {
            "DataFlowAnalysis$", 
            "ControlFlowGraph$",
            "CompilerOptions$",
            "CodingConvention$"
        };
        
        for (String pattern : problematicPatterns) {
            if (qualifiedName.contains(pattern)) {
                System.err.println("    -> Matches problematic pattern: " + pattern);
                return true;
            }
        }
        
        // 3. 깊이 중첩된 클래스 ($ 기호가 2개 이상)
        long dollarCount = qualifiedName.chars().filter(ch -> ch == '$').count();
        if (dollarCount >= 2) {
            System.err.println("    -> Deeply nested class, likely problematic");
            return true;
        }
        
        // 4. 기본적으로는 문제없다고 가정
        return false;
    }
    
    /**
     * 클래스 내에서 nested class 타입 참조를 분석하고 디버그 정보 출력
     */
    private static void analyzeNestedClassReferences(spoon.reflect.declaration.CtClass<?> clazz) {
        // System.err.println("\n[DEBUG] Analyzing nested class references in " + clazz.getSimpleName() + ":");
        
        try {
            // 모든 타입 참조 수집
            final java.util.Set<String> allTypeReferences = new java.util.HashSet<>();
            final java.util.Set<String> nestedClassReferences = new java.util.HashSet<>();
            
            clazz.accept(new spoon.reflect.visitor.CtScanner() {
                @Override
                public <T> void visitCtTypeReference(spoon.reflect.reference.CtTypeReference<T> reference) {
                    try {
                        String qualifiedName = reference.getQualifiedName();
                        allTypeReferences.add(qualifiedName);
                        
                        // nested class 체크 ($ 포함하는 경우)
                        if (qualifiedName != null && qualifiedName.contains("$")) {
                            nestedClassReferences.add(qualifiedName);
                            // System.err.println("  Found nested class reference: " + qualifiedName);
                        }
                    } catch (Exception e) {
                        // System.err.println("  Exception while processing type reference: " + e.getMessage());
                    }
                    super.visitCtTypeReference(reference);
                }
            });
            
            // System.err.println("  Total type references: " + allTypeReferences.size());
            // System.err.println("  Nested class references: " + nestedClassReferences.size());
            
            if (!nestedClassReferences.isEmpty()) {
                // System.err.println("  All nested class references:");
                for (String ref : nestedClassReferences) {
                    // System.err.println("    - " + ref);
                }
            }
            
        } catch (Exception e) {
            // System.err.println("  Exception during analysis: " + e.getMessage());
        }
    }

    /**
     * Collect missing imports from skeletal class
     * Scans all type references in the class and collects FQN types that need imports
     */
    private static Set<String> collectMissingImportsFromSkeletal(spoon.reflect.declaration.CtClass<?> skeletal) {
        Set<String> imports = new LinkedHashSet<>();

        if (skeletal == null) {
            return imports;
        }

        try {
            // Get the package of the skeletal class
            String skeletalPackage = skeletal.getPackage() != null ?
                skeletal.getPackage().getQualifiedName() : "";

            String skeletalQualifiedName = skeletal.getQualifiedName();

            // Scan all type references
            skeletal.accept(new spoon.reflect.visitor.CtScanner() {
                @Override
                public <T> void visitCtTypeReference(spoon.reflect.reference.CtTypeReference<T> reference) {
                    try {
                        String qualifiedName = reference.getQualifiedName();

                        if (qualifiedName != null && !qualifiedName.isEmpty()) {
                            // Skip primitive types
                            if (reference.isPrimitive()) {
                                super.visitCtTypeReference(reference);
                                return;
                            }

                            // Skip arrays - component type will be handled separately
                            if (reference instanceof spoon.reflect.reference.CtArrayTypeReference) {
                                super.visitCtTypeReference(reference);
                                return;
                            }

                            // Skip types with $ (nested classes) - they cannot be directly imported
                            if (qualifiedName.contains("$")) {
                                super.visitCtTypeReference(reference);
                                return;
                            }

                            // Skip skeletal class itself and its nested types
                            if (qualifiedName.equals(skeletalQualifiedName) ||
                                qualifiedName.startsWith(skeletalQualifiedName + "$")) {
                                super.visitCtTypeReference(reference);
                                return;
                            }

                            // Skip types without package (primitives, type parameters, etc.)
                            if (!qualifiedName.contains(".")) {
                                super.visitCtTypeReference(reference);
                                return;
                            }

                            // Skip java.lang package (automatically imported)
                            if (qualifiedName.startsWith("java.lang.")) {
                                String afterLang = qualifiedName.substring("java.lang.".length());
                                if (!afterLang.contains(".")) {
                                    super.visitCtTypeReference(reference);
                                    return;
                                }
                            }

                            // Skip same package as skeletal class
                            String typePackage = qualifiedName.contains(".") ?
                                qualifiedName.substring(0, qualifiedName.lastIndexOf(".")) : "";
                            if (typePackage.equals(skeletalPackage)) {
                                super.visitCtTypeReference(reference);
                                return;
                            }

                            // Add import statement for external types
                            String importType = qualifiedName.replace(',', '.');
                            importType = importType.replace("[]", "");
                            String importStatement = "import " + importType + ";";
                            imports.add(importStatement);
                        }
                    } catch (Exception e) {
                        // Ignore exceptions during type reference scanning
                    }
                    super.visitCtTypeReference(reference);
                }
            });

        } catch (Exception e) {
            // Ignore errors during import collection
        }

        return imports;
    }

    /**
     * 소스 코드에 FQN 변환 및 CtThisAccess 수정 적용
     */
    private static String applySafeCodeGeneration(String sourceCode, spoon.reflect.declaration.CtClass<?> clazz) {
        try {
            if (clazz != null) {
                // CtThisAccess 문제 수정
                fixNullThisAccessElements(clazz);
                
                // _mut 변수의 타입만 FQN으로 변환
                sourceCode = convertMutVariablesToFQN(sourceCode, clazz);
            }
            
            return sourceCode;
        } catch (Exception e) {
            System.err.println("[WARN] Failed to apply safe code generation: " + e.getMessage());
            return sourceCode;
        }
    }

    private static void writeLog(String fileName, String msg) throws Exception {
        // Try block to check for exceptions
        try {

            // Open given file in append mode by creating an
            // object of BufferedWriter class
            BufferedWriter out = new BufferedWriter(
                    new FileWriter(Config.BUILD_PATH + File.separator + fileName, true));

            // Writing on output stream
            out.write(msg);
            // Closing the connection
            out.close();
        }

        // Catch block to handle the exceptions
        catch (IOException e) {

            // Display message when exception occurs
            System.out.println("exception occoured" + e);
        }
    }

    private static void deleteClassFile(String methodName, String packageName) {
        // Calculate exact directory path using package name
        String packagePath = packageName.replace('.', File.separatorChar);
        File targetDir = new File(Config.BUILD_PATH + File.separator + packagePath);

        if (!targetDir.exists() || !targetDir.isDirectory()) {
            return;
        }

        try {
            File[] files = targetDir.listFiles((dir, name) ->
                name.equals(methodName + ".class") ||
                (name.startsWith(methodName + "$") && name.endsWith(".class")));

            if (files != null) {
                for (File file : files) {
                    if (file.delete()) {
                        // System.out.println("Deleted File: " + file.getAbsolutePath());
                    } else {
                        // System.err.println("Failed to delete file: " + file.getAbsolutePath());
                    }
                }
            }
        } catch (SecurityException e) {
            // System.err.println("Security exception accessing file: " + e.getMessage());
        }
    }

    private static HashSet<String> getAllSourceCodeFiles(String rootDir) {
        HashSet<String> javaFilePaths = new HashSet<>();
        File root = new File(rootDir);
        if (!root.exists() || !root.isDirectory()) {
            System.err.println("Invalid Dir: " + rootDir);
            return javaFilePaths;
        }

        Stack<File> stack = new Stack<>();
        stack.push(root);

        while (!stack.isEmpty() && javaFilePaths.size() < 1000) { 
            File current = stack.pop();
            if (current.isDirectory()) {
                File[] files = current.listFiles();
                if (files != null) {
                    for (File f : files) {
                        stack.push(f);
                    }
                }
            } else if (current.isFile()
                    && current.getName().endsWith(".java")
                    && !current.getName().toLowerCase().contains("test")) {
                javaFilePaths.add(current.getAbsolutePath());
            }
        }

        return javaFilePaths;
    }



    private static String extractClassName(String fullPath) {
        if (fullPath == null) {
            return "";
        }

        int lastSlashIdx = fullPath.lastIndexOf('/');
        String name = (lastSlashIdx != -1) ? fullPath.substring(lastSlashIdx + 1) : fullPath;

        int lastDotIdx = name.lastIndexOf('.');
        return (lastDotIdx != -1) ? name.substring(0, lastDotIdx) : name;
    }


    private static String filePathToFQN(String filePath) {
        if (filePath == null || filePath.isEmpty()) {
            return null;
        }

        // .java 확장자 제거
        String path = filePath;
        if (path.endsWith(".java")) {
            path = path.substring(0, path.length() - 5);
        }

        // 경로를 슬래시로 정규화
        path = path.replace('\\', '/');

        // 패키지 구조 추출: /(0\d{1,2})/ (즉, /00/, /01/, ..., /099/) 이후의 경로를 사용
        Pattern testIdPattern = Pattern.compile("/(0\\d{1,2})/");
        Matcher matcher = testIdPattern.matcher(path);

        if (matcher.find()) {
            path = path.substring(matcher.end());
        } else {
            // 패턴을 못 찾은 경우, src/test/java, src/main/java 등의 표준 경로 찾기
            String[] standardPaths = {"src/test/java/", "src/main/java/", "test/", "main/"};
            for (String standardPath : standardPaths) {
                int idx = path.indexOf(standardPath);
                if (idx != -1) {
                    path = path.substring(idx + standardPath.length());
                    break;
                }
            }
        }

        // 슬래시를 점으로 변환하여 FQN 생성
        String fqn = path.replace('/', '.');

        // $ 기호 제거 (내부 클래스 제외)
        int dollarIdx = fqn.indexOf('$');
        if (dollarIdx >= 0) {
            fqn = fqn.substring(0, dollarIdx);
        }

        // 패키지가 없는 경우 (점이 없으면) null 반환
        if (!fqn.contains(".")) {
            return null;
        }

        return fqn;
    }

    private static String fqnToSimpleName(String fqn) {
        if (fqn == null || fqn.isEmpty()) {
            return null;
        }

        // $ 기호 제거 (내부 클래스)
        int dollarIdx = fqn.indexOf('$');
        if (dollarIdx >= 0) {
            fqn = fqn.substring(0, dollarIdx);
        }

        // 마지막 점 이후의 문자열 반환
        int lastDotIdx = fqn.lastIndexOf('.');
        return (lastDotIdx >= 0) ? fqn.substring(lastDotIdx + 1) : fqn;
    }

    private static int parseTestfiles(String[] args, int idx) {
        int ret = 0;
        Config.BASE_TESTS = new ArrayList<>();
        for (int i = idx; i < args.length; i++) {
            ret = i;
            if (args[i].equals("<sep>")) {
                ret = ++i;
                return ret;
            }
            Config.BASE_TESTS.add(args[i]);
        }
        System.out.println("# of Initial Test Files : " + Config.BASE_TESTS.size());
        if (Config.BASE_TESTS.isEmpty()) {
            System.out.println("No initial tests provided.");
            System.exit(1);
        }
        return ret;
    }

    private static void initParams(String[] args) {
        int idx = 7;
        if (args.length < 7) {
            System.err.println(
                    "Usage: java Main <class path> <output folder> <time_budget> <num_split_tests> <ASSEMBLE_MODE> <CUT_path> <ASSEMBLE_MODE> <project_dir> <initial_tests...>");
            System.exit(1);
        }

        String pathSeparator = System.getProperty("path.separator");
        System.out.println("args [0] : " + args[0]);
        Config.BUILD_PATH = args[1];
        System.out.println("Config.BUILD_PATH: " + Config.BUILD_PATH);
        time_budget = Long.parseLong(args[2]);
        num_split_output_tests = Integer.parseInt(args[3]);
        ASSEMBLE_MODE = args[4]; // seqc or seqp
        Config.ASSEMBLE_MODE = ASSEMBLE_MODE;

        Config.CLASS_PATH = args[0] + pathSeparator;
        Config.CLASS_PATH = Config.CLASS_PATH.replace("::", ":");
        System.out.println("Config.CLASS_PATH: " + Config.CLASS_PATH);
        Config.CUT_FILES = new ArrayList<>();
        // idx starts at 5 (since args[0-4] are already processed)
        idx = 5;
        while (true) {
            if (args[idx].equals("regression") || args[idx].equals("non_regression")) {
                break;
            }
            if (args[idx] == null) {
                System.out.println("Invalid Arguement : " + args[idx] + " arguement  " + idx);
            }
            System.out.println("CUT FILE : " + args[idx]);

            Config.CUT_FILES.add(args[idx]);

            idx++;
        }
        System.out.println("Config.CUT_FILES: " + Config.CUT_FILES);
        if (args[idx].equals("regression")) {
            Config.REGRESSION_MODE = true;

        } else if (args[idx].equals("non_regression")) {
            Config.REGRESSION_MODE = false;
        } else {
            System.out.println("Invalid Regression Mode : " + args[idx]);
            System.exit(1);
        }
        idx++;
        Config.PROJECT_DIR = args[idx];
        if (Config.PROJECT_DIR == "") {
            System.out.println("Invalid Project DIR : " + args[idx]);
            System.exit(1);
        } else {
            System.out.println("Config.PROJECT_DIR: " + Config.PROJECT_DIR);
        }
        idx++;
        idx = parseTestfiles(args, idx);
        Config.EXTENDED_TESTS = new ArrayList<>();
        int nextInt = idx;
        // System.out.println("EXTENDED_LISTS: ");
        for (int i = idx; i < args.length; i++) {
            if (args[i].equals("<sep>")) {
                nextInt = i + 1;
                break;
            }
            Config.EXTENDED_TESTS.add(args[i]);
            // System.out.println(" - " + args[i]);
            nextInt++;
        }

        // Check if nextInt is within bounds before accessing args[nextInt]
        if (nextInt >= args.length) {
            System.err.println("Error: Missing bug triggering tests argument");
            System.exit(1);
        }
        Config.BUGTRIGGERRING_TESTS = args[nextInt];
        System.out.println("Config.BUGTRIGGERRING_TESTS: " + Config.BUGTRIGGERRING_TESTS);
        nextInt++;

        // Initialize REFERENCE_LISTS if not already initialized
        if (Config.REFERENCE_LISTS == null) {
            Config.REFERENCE_LISTS = new ArrayList<>();
        }
        // System.out.println("REFERENCE_LISTS: ");
        for (int i = nextInt; i < args.length; i++) {
            if (args[i].equals("<sep>")) {
                break;
            }
            Config.REFERENCE_LISTS.add(args[i]);
            // System.out.println(" - " + args[i]);
        }
        
        // REFERENCE_LISTS를 Set으로 변환 (빠른 검색을 위해)
        Set<String> referenceFQNs = new HashSet<>(Config.REFERENCE_LISTS);
        
        // REFERENCE_LISTS의 simple name도 수집 (FQN 변환 실패 시 fallback)
        Set<String> referenceSimpleNames = new HashSet<>();
        for (String fqn : Config.REFERENCE_LISTS) {
            String simpleName = fqnToSimpleName(fqn);
            if (simpleName != null) {
                referenceSimpleNames.add(simpleName);
            }
        }
        
        // Find tests that will be removed
        List<String> testsToRemove = new ArrayList<>();
        for (String baseTest : Config.BASE_TESTS) {
            // 1차 시도: 파일 경로를 FQN으로 변환하여 비교
            String fqn = filePathToFQN(baseTest);
            if (fqn != null && referenceFQNs.contains(fqn)) {
                testsToRemove.add(baseTest);
                continue;
            }
            
            // 2차 시도: simple name으로 비교 (fallback)
            String simpleName = extractClassName(baseTest);
            if (simpleName != null && referenceSimpleNames.contains(simpleName)) {
                testsToRemove.add(baseTest);
            }
        }
        
        Config.BASE_TESTS.removeAll(testsToRemove);

        // Check if BASE_TESTS is empty after deduplication
        if (Config.BASE_TESTS.isEmpty()) {
            System.out.println("========================================");
            System.out.println("WARNING: All tests have been removed from BASE_TESTS.");
            System.out.println("Only tests already in REFERENCE_LISTS were provided.");
            System.out.println("Exiting program normally.");
            System.out.println("========================================");
            System.exit(0);
        }

        List<String> shuffledList = new ArrayList<>(Config.BASE_TESTS);
        Collections.shuffle(shuffledList);
        Config.BASE_TESTS = shuffledList;

        String initialTest = Config.BASE_TESTS.get(0);

        // Extract package path: find the part after test ID directory (/00/ to /099/)
        String ESTestFile;
        Pattern testIdPattern = Pattern.compile("/(0\\d{1,2})/");
        Matcher matcher = testIdPattern.matcher(initialTest);

        if (matcher.find()) {
            // Found pattern like /00/, /01/, ..., /099/
            ESTestFile = initialTest.substring(matcher.end());
        } else {
            // Fallback: use original logic
            ESTestFile = initialTest.substring(2);
        }

        Config.TEST_FILE = initialTest;
        String ESTestFilePath = Config.OUTPUT_PATH + "/" + ESTestFile;
        String fullyQualifiedClassName = ESTestFile.replace("/", ".").replace(".java", "");
        Config.FULL_CLASS_NAME = fullyQualifiedClassName;
        String fileSeparator = System.getProperty("file.separator").toLowerCase();
        int lastIndex = Config.TEST_FILE.lastIndexOf(fileSeparator);
        Config.OUTPUT_PATH = Config.TEST_FILE.substring(0, lastIndex);
        System.out.println("Config.OUTPUT_PATH: " + Config.OUTPUT_PATH);

    }

    /**
     * New unified argument parser using file paths instead of inline content.
     * All test lists (CUT, Extended, BugTests, Reference) are provided as file paths.
     *
     * Argument order (12 arguments total):
     * 0: classpath (colon-separated JAR files)
     * 1: output_folder (where generated tests are saved)
     * 2: time_budget (in milliseconds)
     * 3: num_split_tests (number of test splits)
     * 4: ASSEMBLE_MODE (seqc, seqp, recur, BOTH)
     * 5: cut_files_path (file containing CUT FQNs)
     * 6: regression_mode (regression or non_regression)
     * 7: project_dir (source code directory)
     * 8: initial_tests_path (file containing initial test paths)
     * 9: extended_tests_path (file containing extended test FQNs)
     * 10: bug_tests_path (file containing bug triggering test methods)
     * 11: reference_tests_path (file containing reference test FQNs)
     *
     * @param args Command line arguments
     * @throws IOException if file reading fails
     */
    private static void parseArguments(String[] args) throws IOException {
        if (args.length < 12) {
            System.err.println(
                "Usage: java Main <classpath> <output_folder> <time_budget> <num_split> <gen_method> " +
                "<cut_files_path> <regression_mode> <project_dir> " +
                "<initial_tests_path> <extended_tests_path> <bug_tests_path> <reference_tests_path>");
            System.exit(1);
        }

        String pathSeparator = System.getProperty("path.separator");

        // 0: Classpath
        System.out.println("args [0] : " + args[0]);
        Config.CLASS_PATH = args[0] + pathSeparator;
        Config.CLASS_PATH = Config.CLASS_PATH.replace("::", ":");
        System.out.println("Config.CLASS_PATH: " + Config.CLASS_PATH);

        // 1: Output Folder
        Config.BUILD_PATH = args[1];
        System.out.println("Config.BUILD_PATH: " + Config.BUILD_PATH);

        // 2: Time Budget
        time_budget = Long.parseLong(args[2]);

        // 3: Number of Splits
        num_split_output_tests = Integer.parseInt(args[3]);

        // 4: Generation Method
        ASSEMBLE_MODE = args[4];
        Config.ASSEMBLE_MODE = ASSEMBLE_MODE;
        System.out.println("Generation Method: " + ASSEMBLE_MODE);

        // 5: CUT Files (from file)
        Config.CUT_FILES = new ArrayList<>(Files.readAllLines(Paths.get(args[5])));
        System.out.println("Config.CUT_FILES: " + Config.CUT_FILES);

        // 6: Regression Mode
        if (args[6].equals("regression")) {
            Config.REGRESSION_MODE = true;
        } else if (args[6].equals("non_regression")) {
            Config.REGRESSION_MODE = false;
        } else {
            System.out.println("Invalid Regression Mode : " + args[6]);
            System.exit(1);
        }

        // 7: Project Directory
        Config.PROJECT_DIR = args[7];
        System.out.println("Config.PROJECT_DIR: " + Config.PROJECT_DIR);
        long curr = System.currentTimeMillis();
        Config.SOURCE_CODE_FILES = getAllSourceCodeFiles(Config.PROJECT_DIR);
        long endtime = System.currentTimeMillis() - curr;
        System.out.println("Time it Took : " + endtime);
        if (Config.SOURCE_CODE_FILES == null) {
            System.out.println("Did not parse any source code files");
        } else {
            System.out.println("# of Source Code Files : " + Config.SOURCE_CODE_FILES.size());
        }

        // 8: Initial Tests (from file)
        Path initialTestsPath = Paths.get(args[8]);
        if (Files.exists(initialTestsPath)) {
            Config.BASE_TESTS = new ArrayList<>(Files.readAllLines(initialTestsPath));
        } else {
            System.err.println("Error: Initial tests file not found: " + args[8]);
            System.exit(1);
        }

        // 9: Extended Tests (from file)
        Config.EXTENDED_TESTS = new ArrayList<>();
        Path extendedPath = Paths.get(args[9]);
        if (Files.exists(extendedPath)) {
            Config.EXTENDED_TESTS.addAll(Files.readAllLines(extendedPath));
            System.out.println("Config.EXTENDED_TESTS: " + Config.EXTENDED_TESTS);
        } else {
            System.out.println("Warning: Extended tests file not found: " + args[9]);
        }

        // 10: Bug Triggering Tests (from file)
        Path bugTestsPath = Paths.get(args[10]);
        if (Files.exists(bugTestsPath)) {
            List<String> bugTestsList = Files.readAllLines(bugTestsPath);
            Config.BUGTRIGGERRING_TESTS = String.join(";", bugTestsList);
            System.out.println("Config.BUGTRIGGERRING_TESTS: " + Config.BUGTRIGGERRING_TESTS);
        } else {
            System.out.println("Warning: Bug tests file not found: " + args[10]);
            Config.BUGTRIGGERRING_TESTS = "";
        }

        // 11: Reference Lists (from file)
        Config.REFERENCE_LISTS = new ArrayList<>();
        Path referencePath = Paths.get(args[11]);
        if (Files.exists(referencePath)) {
            Config.REFERENCE_LISTS.addAll(Files.readAllLines(referencePath));
            System.out.println("Config.REFERENCE_LISTS: " + Config.REFERENCE_LISTS);
        } else {
            System.out.println("Warning: Reference tests file not found: " + args[11]);
        }

        // Perform deduplication between BASE_TESTS and REFERENCE_LISTS
        performDeduplication();

        // Shuffle BASE_TESTS
        List<String> shuffledList = new ArrayList<>(Config.BASE_TESTS);
        Collections.shuffle(shuffledList);
        Config.BASE_TESTS = shuffledList;

        // Extract and set CONFIG values from first initial test
        if (Config.BASE_TESTS.isEmpty()) {
            System.err.println("Error: No initial tests available after deduplication");
            System.exit(1);
        }

        String initialTest = Config.BASE_TESTS.get(0);
        Config.TEST_FILE = initialTest;

        // Extract package path: find the part after test ID directory (/00/ to /099/)
        String ESTestFile;
        Pattern testIdPattern = Pattern.compile("/(0\\d{1,2})/");
        Matcher matcher = testIdPattern.matcher(initialTest);

        if (matcher.find()) {
            ESTestFile = initialTest.substring(matcher.end());
        } else {
            ESTestFile = initialTest.substring(2);
        }

        String fullyQualifiedClassName = ESTestFile.replace("/", ".").replace(".java", "");
        Config.FULL_CLASS_NAME = fullyQualifiedClassName;

        String fileSeparator = System.getProperty("file.separator").toLowerCase();
        int lastIndex = Config.TEST_FILE.lastIndexOf(fileSeparator);
        Config.OUTPUT_PATH = Config.TEST_FILE.substring(0, lastIndex);
        System.out.println("Config.OUTPUT_PATH: " + Config.OUTPUT_PATH);
    }

    /**
     * Performs deduplication between BASE_TESTS and REFERENCE_LISTS.
     * Removes tests from BASE_TESTS that are already in REFERENCE_LISTS.
     */
    private static void performDeduplication() {
        Set<String> referenceFQNs = new HashSet<>(Config.REFERENCE_LISTS);

        Set<String> referenceSimpleNames = new HashSet<>();
        for (String fqn : Config.REFERENCE_LISTS) {
            String simpleName = fqnToSimpleName(fqn);
            if (simpleName != null) {
                referenceSimpleNames.add(simpleName);
            }
        }

        List<String> testsToRemove = new ArrayList<>();
        for (String baseTest : Config.BASE_TESTS) {
            String fqn = filePathToFQN(baseTest);
            if (fqn != null && referenceFQNs.contains(fqn)) {
                testsToRemove.add(baseTest);
                continue;
            }

            String simpleName = extractClassName(baseTest);
            if (simpleName != null && referenceSimpleNames.contains(simpleName)) {
                testsToRemove.add(baseTest);
            }
        }

        Config.BASE_TESTS.removeAll(testsToRemove);

        if (Config.BASE_TESTS.isEmpty()) {
            System.out.println("========================================");
            System.out.println("WARNING: All tests have been removed from BASE_TESTS.");
            System.out.println("Only tests already in REFERENCE_LISTS were provided.");
            System.out.println("Exiting program normally.");
            System.out.println("========================================");
            System.exit(0);
        }
    }

    /**
     * Normalizes CtThisAccess references in a class to use simple names
     * instead of fully qualified names for nested classes.
     */
    private static void normalizeThisAccessInClass(CtClass<?> ctClass) {
        if (ctClass == null) {
            return;
        }

        // Create a scanner to traverse all elements
        ctClass.accept(new CtScanner() {
            @Override
            public <T> void visitCtThisAccess(CtThisAccess<T> thisAccess) {
                super.visitCtThisAccess(thisAccess);
                
                // Get the type reference of this access
                CtTypeReference<T> targetType = thisAccess.getType();
                if (targetType != null) {
                    // If the target type is qualified, replace it with simple name
                    String qualifiedName = targetType.getQualifiedName();
                    String simpleName = targetType.getSimpleName();
                    
                    if (!qualifiedName.equals(simpleName) && qualifiedName.contains("$")) {
                        // Create a new type reference with simple name only for nested classes
                        spoon.reflect.factory.Factory factory = thisAccess.getFactory();
                        CtTypeReference<T> simpleTypeRef = factory.createTypeReference();
                        simpleTypeRef.setSimpleName(simpleName);
                        simpleTypeRef.setPackage(null); // Remove package qualification
                        thisAccess.setType(simpleTypeRef);
                    }
                }
            }
            
            @Override
            public <T> void visitCtFieldWrite(CtFieldWrite<T> fieldWrite) {
                super.visitCtFieldWrite(fieldWrite);
                
                // Handle field writes with qualified this access  
                CtExpression<?> target = fieldWrite.getTarget();
                if (target instanceof CtThisAccess) {
                    CtThisAccess<?> thisAccess = (CtThisAccess<?>) target;
                    
                    // Check if we need to replace with a simple this access
                    CtTypeReference<?> targetType = thisAccess.getType();
                    if (targetType != null) {
                        String qualifiedName = targetType.getQualifiedName();
                        String simpleName = targetType.getSimpleName();
                        
                        if (!qualifiedName.equals(simpleName) && qualifiedName.contains("$")) {
                            // Create a simple this access
                            spoon.reflect.factory.Factory factory = fieldWrite.getFactory();
                            CtThisAccess<?> simpleThisAccess = factory.createThisAccess();
                            fieldWrite.setTarget(simpleThisAccess);
                        }
                    }
                }
            }
            
            @Override
            public <T> void visitCtFieldRead(CtFieldRead<T> fieldRead) {
                super.visitCtFieldRead(fieldRead);
                
                // Handle field reads with qualified this access
                CtExpression<?> target = fieldRead.getTarget();
                if (target instanceof CtThisAccess) {
                    CtThisAccess<?> thisAccess = (CtThisAccess<?>) target;
                    
                    // Check if we need to replace with a simple this access
                    CtTypeReference<?> targetType = thisAccess.getType();
                    if (targetType != null) {
                        String qualifiedName = targetType.getQualifiedName();
                        String simpleName = targetType.getSimpleName();
                        
                        if (!qualifiedName.equals(simpleName) && qualifiedName.contains("$")) {
                            // Create a simple this access
                            spoon.reflect.factory.Factory factory = fieldRead.getFactory();
                            CtThisAccess<?> simpleThisAccess = factory.createThisAccess();
                            fieldRead.setTarget(simpleThisAccess);
                        }
                    }
                }
            }
            
            @Override
            public <T> void visitCtInvocation(CtInvocation<T> invocation) {
                super.visitCtInvocation(invocation);
                
                // Handle method invocations with qualified this access
                CtExpression<?> target = invocation.getTarget();
                if (target instanceof CtThisAccess) {
                    CtThisAccess<?> thisAccess = (CtThisAccess<?>) target;
                    
                    // Check if we need to replace with a simple this access
                    CtTypeReference<?> targetType = thisAccess.getType();
                    if (targetType != null) {
                        String qualifiedName = targetType.getQualifiedName();
                        String simpleName = targetType.getSimpleName();
                        
                        if (!qualifiedName.equals(simpleName) && qualifiedName.contains("$")) {
                            // Create a simple this access
                            spoon.reflect.factory.Factory factory = invocation.getFactory();
                            CtThisAccess<?> simpleThisAccess = factory.createThisAccess();
                            invocation.setTarget(simpleThisAccess);
                        }
                    }
                }
            }
        });
    }


    /**
     * Preserves fully qualified names (FQN) from the original source file
     * Spoon's pretty printer may shorten FQNs, so we restore them from the original source
     */
    private static String preserveFQNFromOriginalInMain(String sourceCode, CtClass<?> skeletalClass) {
        if (skeletalClass == null) {
            return sourceCode;
        }

        // Get the source file path from the skeletal class
        spoon.reflect.cu.SourcePosition position = skeletalClass.getPosition();
        if (position == null || position.getFile() == null) {
            return sourceCode;
        }

        java.io.File sourceFile = position.getFile();

        try {
            // Read original source file
            String originalSource = new String(java.nio.file.Files.readAllBytes(sourceFile.toPath()));

            // Pattern to find FQN in extends/implements clauses
            // Matches: extends/implements followed by package.Class
            java.util.regex.Pattern fqnPattern = java.util.regex.Pattern.compile(
                "(?:extends|implements)\\s+([a-z][a-z0-9_]*(?:\\.[a-z][a-z0-9_]*)+\\.[A-Z][a-zA-Z0-9_]*)",
                java.util.regex.Pattern.MULTILINE
            );

            java.util.regex.Matcher matcher = fqnPattern.matcher(originalSource);
            java.util.Set<String> fqnSet = new java.util.HashSet<>();

            while (matcher.find()) {
                String fqn = matcher.group(1);
                fqnSet.add(fqn);
            }

            // Restore each FQN in the generated source code
            for (String fqn : fqnSet) {
                String simpleClassName = fqn.substring(fqn.lastIndexOf('.') + 1);
                // Replace "extends SimpleClass" with "extends full.package.SimpleClass"
                sourceCode = sourceCode.replaceAll(
                    "\\b(extends|implements)\\s+" + java.util.regex.Pattern.quote(simpleClassName) + "\\b",
                    "$1 " + fqn
                );
            }

        } catch (Exception e) {
            System.err.println("[ERROR] Error reading source file in preserveFQNFromOriginalInMain: " + e.getMessage());
        }

        return sourceCode;
    }

    /**
     * Fixes Spoon bug where nested class constructors with this() calls are output as super()
     * Since Spoon already converts this() to super() in the AST, we need to check the original source file
     */
    private static String fixConstructorCallsInMain(String sourceCode, CtClass<?> skeletalClass) {
        if (skeletalClass == null) {
            return sourceCode;
        }

        // Get the source file path from the skeletal class
        spoon.reflect.cu.SourcePosition position = skeletalClass.getPosition();
        if (position == null || position.getFile() == null) {
            return sourceCode;
        }

        java.io.File sourceFile = position.getFile();

        try {
            // Read original source file
            String originalSource = new String(java.nio.file.Files.readAllBytes(sourceFile.toPath()));

            // Find all nested classes and check their constructors in the original source
            for (CtType<?> nestedType : skeletalClass.getNestedTypes()) {
                if (!(nestedType instanceof CtClass)) {
                    continue;
                }

                String nestedClassName = nestedType.getSimpleName();

                // Pattern to find constructors with this() calls in the original source
                // Matches: ClassName(...) { this(...); or ClassName(...) { \n this(...);
                String thisCallPattern = "\\b" + nestedClassName + "\\s*\\([^)]*\\)\\s*\\{[^}]*?\\bthis\\s*\\(";
                java.util.regex.Pattern pattern = java.util.regex.Pattern.compile(thisCallPattern, java.util.regex.Pattern.DOTALL);
                java.util.regex.Matcher matcher = pattern.matcher(originalSource);

                if (matcher.find()) {
                    // Replace all super(...) with this(...) for this nested class
                    // Pattern: NestedClassName(...) { ... super(...); -> NestedClassName(...) { ... this(...);
                    String replacePattern = "(\\b" + nestedClassName + "\\s*\\([^)]*\\)\\s*\\{[^}]*?)\\bsuper\\s*\\(";
                    java.util.regex.Pattern replacePatternCompiled = java.util.regex.Pattern.compile(replacePattern, java.util.regex.Pattern.DOTALL);
                    sourceCode = replacePatternCompiled.matcher(sourceCode).replaceAll("$1this(");
                }
            }

        } catch (Exception e) {
            System.err.println("[ERROR] Error reading source file in fixConstructorCallsInMain: " + e.getMessage());
        }

        return sourceCode;
    }
    
    
    
    /**
     * Remove problematic import statements from source code
     * 
     * Strategy: Remove duplicate imports where the same simple class name is imported from different packages
     * Example: If both "import java.util.Date;" and "import java.sql.Date;" exist, remove the second one
     * 
     * Also removes "wildcard" imports (import java.util.*;) if they conflict with explicit imports
     * 
     * @param sourceCode Source code with potentially problematic imports
     * @return Source code with problematic imports removed
     */
    private static String removeProblematicImports(String sourceCode) {
        java.util.Map<String, String> simpleNameToFullImport = new java.util.LinkedHashMap<>();
        java.util.List<String> linesToKeep = new java.util.ArrayList<>();
        
        String[] lines = sourceCode.split("\n");
        
        // First pass: identify all imports and track duplicates
        for (String line : lines) {
            String trimmedLine = line.trim();
            if (trimmedLine.startsWith("import ") && trimmedLine.endsWith(";")) {
                // Extract the full import path and simple class name
                String importPath = trimmedLine.substring(7, trimmedLine.length() - 1).trim(); // remove "import " and ";"
                
                // Skip wildcard imports for now
                if (importPath.endsWith(".*")) {
                    continue;
                }
                
                // Get simple class name (last part)
                String[] parts = importPath.split("\\.");
                String simpleClassName = parts[parts.length - 1];
                
                // If we've already seen this simple name, it's a duplicate - skip this one
                if (simpleNameToFullImport.containsKey(simpleClassName)) {
                    System.out.println("[DEBUG] Removing duplicate import: " + trimmedLine);
                    continue;
                }
                
                // Record this import
                simpleNameToFullImport.put(simpleClassName, importPath);
            }
        }
        
        // Second pass: keep only non-duplicate imports
        for (String line : lines) {
            String trimmedLine = line.trim();
            if (trimmedLine.startsWith("import ") && trimmedLine.endsWith(";")) {
                String importPath = trimmedLine.substring(7, trimmedLine.length() - 1).trim();
                
                // Skip wildcard imports
                if (importPath.endsWith(".*")) {
                    continue;
                }
                
                String[] parts = importPath.split("\\.");
                String simpleClassName = parts[parts.length - 1];
                
                // Keep only if this is the first (recorded) import for this simple name
                if (simpleNameToFullImport.containsKey(simpleClassName) && 
                    simpleNameToFullImport.get(simpleClassName).equals(importPath)) {
                    linesToKeep.add(line);
                    simpleNameToFullImport.remove(simpleClassName); // Mark as processed
                }
            } else {
                // Non-import lines always kept
                linesToKeep.add(line);
            }
        }
        
        return String.join("\n", linesToKeep);
    }
    
    /**
     * Apply bucketing to method list - reorder methods by Signature before adding to skeletal
     * 
     * This ensures:
     * 1. Methods with same Exception signature are grouped together
     * 2. Passing tests (not in buckets) come at the end
     * 3. Methods are already in correct order when added to skeletal
     */
    private static List<CtMethod<?>> applyBucketingToMethodList(
            List<CtMethod<?>> methods, 
            utils.TestMinimizer testMinimizer) {
        
        Map<String, List<String>> buckets = testMinimizer.getExceptionBuckets();
        if (buckets.isEmpty()) {
            return methods;  // No bucketing data
        }
        
        // Create method name -> method map
        Map<String, CtMethod<?>> methodNameToMethod = new HashMap<>();
        for (CtMethod<?> method : methods) {
            methodNameToMethod.put(method.getSimpleName(), method);
        }
        
        // Reorder methods according to buckets
        List<CtMethod<?>> orderedMethods = new ArrayList<>();
        Set<String> addedMethodNames = new HashSet<>();
        
        // Add bucketed methods first (in bucket order)
        for (Map.Entry<String, List<String>> entry : buckets.entrySet()) {
            for (String methodName : entry.getValue()) {
                CtMethod<?> method = methodNameToMethod.get(methodName);
                if (method != null && !addedMethodNames.contains(methodName)) {
                    orderedMethods.add(method);
                    addedMethodNames.add(methodName);
                }
            }
        }
        
        // Add passing tests (methods not in buckets)
        for (CtMethod<?> method : methods) {
            if (!addedMethodNames.contains(method.getSimpleName())) {
                orderedMethods.add(method);
            }
        }
        
        if (Config.DEBUG_TEST_BUCKETING) {
            System.out.println("[Bucketing-MethodList] Reordered " + orderedMethods.size() + " methods, " + 
                             addedMethodNames.size() + " bucketed");
        }
        
        return orderedMethods;
    }
    
    /**
     * Add bucketing comment headers to source code
     * Inserts "// SIGNATURE BUCKET: ..." headers before @Test methods
     */
    private static String addBucketingHeadersToSource(String sourceCode, utils.TestMinimizer testMinimizer) {
        Map<String, List<String>> buckets = testMinimizer.getExceptionBuckets();
        if (buckets.isEmpty()) {
            return sourceCode;
        }
        
        // Build method name -> signature map
        Map<String, String> methodToSignature = new HashMap<>();
        for (Map.Entry<String, List<String>> entry : buckets.entrySet()) {
            String signature = entry.getKey();
            for (String methodName : entry.getValue()) {
                methodToSignature.put(methodName, signature);
            }
        }
        
        // Split into lines and process
        String[] lines = sourceCode.split("\n", -1);
        StringBuilder result = new StringBuilder();
        String currentSignature = null;
        boolean addedPassingHeader = false;
        
        for (int i = 0; i < lines.length; i++) {
            String line = lines[i];
            String trimmed = line.trim();
            
            // Check if this is a @Test annotation
            if (trimmed.startsWith("@Test")) {
                // Look ahead to find method name
                String methodName = null;
                for (int j = i + 1; j < Math.min(i + 4, lines.length); j++) {
                    String nextLine = lines[j].trim();
                    if (nextLine.startsWith("public void ")) {
                        int startIdx = nextLine.indexOf("public void ") + 12;
                        int endIdx = nextLine.indexOf('(', startIdx);
                        if (endIdx > startIdx) {
                            methodName = nextLine.substring(startIdx, endIdx).trim();
                        }
                        break;
                    }
                }
                
                // If method has signature, add header
                if (methodName != null && methodToSignature.containsKey(methodName)) {
                    String signature = methodToSignature.get(methodName);
                    
                    if (!signature.equals(currentSignature)) {
                        result.append("    // ============================================================\n");
                        result.append("    // SIGNATURE BUCKET: ").append(signature).append("\n");
                        result.append("    // ============================================================\n");
                        currentSignature = signature;
                    }
                } else if (methodName != null && !addedPassingHeader) {
                    // First passing test - add header
                    result.append("    // ============================================================\n");
                    result.append("    // PASSING TESTS\n");
                    result.append("    // ============================================================\n");
                    addedPassingHeader = true;
                    currentSignature = null;
                }
            }
            
            result.append(line).append("\n");
        }
        
        String resultStr = result.toString();
        if (resultStr.endsWith("\n")) {
            resultStr = resultStr.substring(0, resultStr.length() - 1);
        }
        
        return resultStr;
    }

}