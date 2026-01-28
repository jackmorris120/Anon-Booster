package PreProcessor.TestFilter;

import spoon.reflect.CtModel;
import spoon.reflect.declaration.*;
import spoon.reflect.code.*;
import spoon.reflect.reference.*;
import spoon.reflect.visitor.filter.TypeFilter;
import java.util.*;
import java.io.File;


public class TestFilter {
    private int argIdx = 0;
    
    public static void main(String args[]) throws Exception {
        long startTime = System.currentTimeMillis();
        
        TestFilter filter = new TestFilter();
        filter.parseParam(args);
        
        SpoonBuilder.initModel();
        CtModel model = SpoonBuilder.getModel();
        
        System.out.println("\nBuilding call graph for reachability analysis...");
        CallGraphBuilder callGraphBuilder = new CallGraphBuilder(model);
        callGraphBuilder.buildCallGraph();
        System.out.println();
        callGraphBuilder.printStatistics();
        System.out.println();
        
        Set<String> cutClassNames = filter.getCUTClassNames(model);
        System.out.println("CUT Classes: " + cutClassNames);
        System.out.println("Relevant Test Files: " + Config.baseTestFilePaths.size());
        System.out.println("Bug Triggering Tests: " + Config.bugTriggeringTests.size());
        System.out.println("Analysis Mode: " + (Config.useRelevantTestsOnly ? "Relevant Tests Only" : "All Tests"));
        
        System.out.println("\nDEBUG: CUT Files in Config:");
        for (String cutPath : Config.CUTFilePaths) {
            System.out.println("  - " + cutPath);
        }
        
        System.out.println("\nDEBUG: All types in model:");
        int typeCount = 0;
        boolean foundDateTimeFormatter = false;
        for (CtType<?> type : model.getAllTypes()) {
            typeCount++;
            String typeName = type.getQualifiedName();
            if (typeCount <= 10) {
                System.out.println("  - " + typeName + " (file: " + 
                    (type.getPosition().getFile() != null ? type.getPosition().getFile().getName() : "null") + ")");
            }
            if (typeName.contains("TestDateTimeFormatter")) {
                foundDateTimeFormatter = true;
                System.out.println("  *** FOUND TestDateTimeFormatter: " + typeName);
            }
        }
        System.out.println("  Total types: " + typeCount);
        if (!foundDateTimeFormatter) {
            System.out.println("  *** WARNING: TestDateTimeFormatter NOT FOUND in model!");
        }
        
        System.out.println("\nDEBUG: Sample call graph for bug-triggering test:");
        String sampleTest = "testParseLocalDate_weekyear";
        for (String sig : callGraphBuilder.getCallGraph().keySet()) {
            if (sig.contains(sampleTest)) {
                System.out.println("  Found: " + sig);
                Set<String> callees = callGraphBuilder.getCallGraph().get(sig);
                System.out.println("  Callees (" + callees.size() + "):");
                int count = 0;
                for (String callee : callees) {
                    if (count++ < 10) {
                        System.out.println("    -> " + callee);
                    }
                }
                break;
            }
        }
        

        
        List<CtMethod<?>> relevantTestMethods = filter.filterRelevantTests(model, cutClassNames, callGraphBuilder);
        
        System.out.println("\nFound " + relevantTestMethods.size() + " test methods reaching CUT methods");
        
        for (CtMethod<?> testMethod : relevantTestMethods) {
            String className = testMethod.getParent(CtClass.class).getQualifiedName();
            String methodName = testMethod.getSimpleName();
            
            StringBuilder signature = new StringBuilder();
            signature.append(className).append(".").append(methodName).append("(");
            
            List<CtParameter<?>> params = testMethod.getParameters();
            for (int i = 0; i < params.size(); i++) {
                if (i > 0) signature.append(",");
                CtTypeReference<?> typeRef = params.get(i).getType();
                if (typeRef != null) {
                    signature.append(typeRef.getQualifiedName());
                }
            }
            signature.append(")");
            
            System.out.println("  - " + signature.toString());
        }
        
        long endTime = System.currentTimeMillis();
        long totalTime = endTime - startTime;
        
        System.out.println("\n================================================================");
        System.out.println("                    EXECUTION REPORT                        ");
        System.out.println("================================================================");
        System.out.println(" Analysis Scope:     " + (Config.useRelevantTestsOnly ? "Relevant Tests Only" : "All Tests"));
        System.out.println(" CUT Classes:        " + cutClassNames.size() + " classes");
        System.out.println(" Test Files Parsed:  " + (Config.useRelevantTestsOnly ? Config.baseTestFilePaths.size() + " relevant files" : "All test files"));
        if (Config.keepBugTriggeringTests) {
            System.out.println(" Bug-Triggering:     " + Config.bugTriggeringTests.size() + " tests (KEPT)");
        } else {
            System.out.println(" Bug-Triggering:     " + Config.bugTriggeringTests.size() + " tests (EXCLUDED)");
        }
        System.out.println("----------------------------------------------------------------");
        System.out.println(" Tests Found:        " + relevantTestMethods.size() + " methods");
        System.out.println(" Total Time:         " + totalTime + "ms (" + String.format("%.2f", totalTime / 1000.0) + "s)");
        System.out.println("================================================================");
        
        System.out.flush();
        System.err.flush();
        System.exit(0);
    }

    private void parseParam(String args[]) {
        Config.CLASS_PATH = args[argIdx++];
        Config.rootSrcDir = args[argIdx++];
        Config.rootTestDir = args[argIdx++];
        Config.baseTestFilePaths = parseArgs(args);
        Config.CUTFilePaths = parseArgs(args);
        Config.bugTriggeringTests = parseArgs(args);
        
        if (argIdx < args.length && !args[argIdx].equals("<SEP>")) {
            String useRelevantFlag = args[argIdx++];
            Config.useRelevantTestsOnly = useRelevantFlag.equalsIgnoreCase("true") || 
                                          useRelevantFlag.equalsIgnoreCase("relevant");
        }

        while (argIdx < args.length) {
            String tok = args[argIdx++];
            if (tok == null || tok.trim().isEmpty()) continue;

            if (tok.equalsIgnoreCase("--keep-reachable")) {
                // 비도달 테스트 메서드를 소스에서 즉시 제거
                Config.keepReachablePruneOthers = true;

            } else if (tok.equalsIgnoreCase("--keep-bug-triggering")) {
                // 버그 트리거링 테스트를 keep 대상에 포함
                Config.keepBugTriggeringTests = true;

            } else if (tok.equalsIgnoreCase("--exclude-bug-triggering")) {
                // 버그 트리거링 테스트를 제외 대상에 포함
                Config.keepBugTriggeringTests = false;

            } else if (tok.startsWith("--dataset-manifest=")) {
                Config.datasetManifest = tok.substring("--dataset-manifest=".length()).trim();

            } else if (tok.startsWith("--dataset-dir=")) {
                Config.datasetOutputDir = tok.substring("--dataset-dir=".length()).trim();

            } else {
                System.out.println("[WARN] Unknown flag: " + tok);
            }
        }
    }

    private ArrayList<String> parseArgs(String args[]) {
        ArrayList<String> returnList = new ArrayList<>();
        while (argIdx < args.length && !args[argIdx].equals("<SEP>")) {
            if (args[argIdx] == null) {
                System.out.println("Invalid Argument : " + args[argIdx] + " at index " + argIdx);
                return null;
            }
            returnList.add(args[argIdx++]);
        }
        argIdx++;
        return returnList;
    }
    
    private Set<String> getCUTClassNames(CtModel model) {
        Set<String> cutClassNames = new HashSet<>();
        
        for (String cutPath : Config.CUTFilePaths) {
            for (CtType<?> type : model.getAllTypes()) {
                if (type.getPosition().getFile() != null && 
                    type.getPosition().getFile().getAbsolutePath().equals(cutPath)) {
                    cutClassNames.add(type.getQualifiedName());
                }
            }
        }
        
        return cutClassNames;
    }
    
    private List<CtMethod<?>> filterRelevantTests(CtModel model, Set<String> cutClassNames, CallGraphBuilder callGraphBuilder) {
        List<CtMethod<?>> relevantTests = new ArrayList<>();
        List<CtMethod<?>> irrelevantTests = new ArrayList<>();
        
        Set<String> bugTriggeringTestSet = new HashSet<>();
        for (String btTest : Config.bugTriggeringTests) {
            String normalized = btTest.replace("::", ".");
            bugTriggeringTestSet.add(normalized);
        }
        
        System.out.println("Analyzing all test methods in relevant test classes for CUT reachability");
        if (!bugTriggeringTestSet.isEmpty()) {
            if (Config.keepBugTriggeringTests) {
                System.out.println("Keeping " + bugTriggeringTestSet.size() + " bug-triggering tests (--keep-bug-triggering enabled)");
            } else {
                System.out.println("Excluding " + bugTriggeringTestSet.size() + " bug-triggering tests (--exclude-bug-triggering or default)");
            }
        }
        
        int totalTestClasses = 0;
        int relevantTestClasses = 0;
        int totalTestMethods = 0;
        int reachableMethods = 0;
        int unreachableMethods = 0;
        int excludedMethods = 0;
        
        Set<String> relevantClassNames = new HashSet<>();
        
        for (CtType<?> type : model.getAllTypes()) {
            if (isTestClass(type)) {
                totalTestClasses++;
                String className = type.getQualifiedName();
                
                // Debug: Check if methods are loaded
                if (type.getMethods().isEmpty() && className.contains("DateTimeFormatter")) {
                    System.out.println("[DEBUG] !!! TestDateTimeFormatter has NO METHODS in Spoon model!");
                    System.out.println("[DEBUG]   Type class: " + type.getClass().getName());
                    System.out.println("[DEBUG]   Is CtClass: " + (type instanceof CtClass));
                }
                
                boolean classHasReachableMethod = false;
                int testMethodCount = 0;
                for (CtMethod<?> method : type.getMethods()) {
                    if (isTestMethod(method)) {
                        testMethodCount++;
                        if (callGraphBuilder.isReachable(method, cutClassNames)) {
                            classHasReachableMethod = true;
                            break;
                        }
                    }
                }
                
                if (className.contains("DateTimeFormatter")) {
                    System.out.println("[DEBUG] TestDateTimeFormatter analysis:");
                    System.out.println("[DEBUG]   Total methods in class: " + type.getMethods().size());
                    System.out.println("[DEBUG]   Test methods found: " + testMethodCount);
                    System.out.println("[DEBUG]   Has reachable method: " + classHasReachableMethod);
                }
                
                if (testMethodCount == 0 && className.contains("DateTimeFormatter")) {
                    System.out.println("[DEBUG] No test methods found in: " + className);
                    System.out.println("[DEBUG]   Total methods: " + type.getMethods().size());
                    int sampleCount = 0;
                    for (CtMethod<?> m : type.getMethods()) {
                        if (sampleCount++ < 5) {
                            System.out.println("[DEBUG]     Method: " + m.getSimpleName() + 
                                " public=" + m.hasModifier(ModifierKind.PUBLIC) +
                                " hasBody=" + (m.getBody() != null) +
                                " bodyStatements=" + (m.getBody() != null ? m.getBody().getStatements().size() : 0) +
                                " hasParams=" + !m.getParameters().isEmpty() +
                                " startsWithTest=" + m.getSimpleName().startsWith("test"));
                        }
                    }
                }
                
                if (classHasReachableMethod) {
                    relevantTestClasses++;
                    relevantClassNames.add(className);
                    
                    int methodsInClass = 0;
                    for (CtMethod<?> method : type.getMethods()) {
                        if (isTestMethod(method)) {
                            methodsInClass++;
                            totalTestMethods++;
                            
                            String testName = className + "." + method.getSimpleName();
                            String altTestName = className + "::" + method.getSimpleName();
                            boolean isBugTriggering = bugTriggeringTestSet.contains(testName) || 
                                                     bugTriggeringTestSet.contains(altTestName);
                            
                            if (callGraphBuilder.isReachable(method, cutClassNames)) {
                                reachableMethods++;
                                if (Config.keepBugTriggeringTests) {
                                    // Keep bug-triggering tests mode: include all reachable tests
                                    relevantTests.add(method);
                                    if (isBugTriggering) {
                                        excludedMethods++; // Count for statistics but still keep
                                    }
                                } else {
                                    // Exclude bug-triggering tests mode (default): filter out bug-triggering tests
                                    if (!isBugTriggering) {
                                        relevantTests.add(method);
                                    } else {
                                        excludedMethods++;
                                    }
                                }
                            } else {
                                unreachableMethods++;
                                if (Config.keepBugTriggeringTests) {
                                    // Keep bug-triggering tests mode: only add non-bug-triggering to irrelevant
                                    if (!isBugTriggering) {
                                        irrelevantTests.add(method);
                                    }
                                } else {
                                    // Exclude bug-triggering tests mode: add all unreachable to irrelevant
                                    if (!isBugTriggering) {
                                        irrelevantTests.add(method);
                                    }
                                    // Bug-triggering unreachable tests are simply not included anywhere
                                }
                            }
                        }
                    }
                }
            }
        }
        
        System.out.println("Analysis summary:");
        System.out.println("  Total test classes: " + totalTestClasses);
        System.out.println("  Test classes with CUT reachability: " + relevantTestClasses);
        System.out.println("  Total test methods (in relevant classes): " + totalTestMethods);
        System.out.println("  Methods reaching CUT: " + reachableMethods);
        System.out.println("  Methods NOT reaching CUT: " + unreachableMethods);
        if (Config.keepBugTriggeringTests) {
            System.out.println("  Bug-triggering tests: " + excludedMethods + " (KEPT in result)");
        } else {
            System.out.println("  Bug-triggering tests: " + excludedMethods + " (EXCLUDED from result)");
        }
        System.out.println("  Final result (to KEEP): " + relevantTests.size());
        System.out.println("  Final result (to REMOVE): " + irrelevantTests.size());
        
        System.out.println("\n<<RELEVANT_TEST_CLASSES>>");
        for (String className : relevantClassNames) {
            System.out.println("  - " + className);
        }
        System.out.println("<<END_RELEVANT_TEST_CLASSES>>");
        
        System.out.println("\n<<METHODS_TO_KEEP>>");
        for (CtMethod<?> method : relevantTests) {
            String className = method.getParent(CtClass.class).getQualifiedName();
            String methodName = method.getSimpleName();
            
            StringBuilder signature = new StringBuilder();
            signature.append(className).append(".").append(methodName).append("(");
            
            List<CtParameter<?>> params = method.getParameters();
            for (int i = 0; i < params.size(); i++) {
                if (i > 0) signature.append(",");
                CtTypeReference<?> typeRef = params.get(i).getType();
                if (typeRef != null) {
                    signature.append(typeRef.getQualifiedName());
                }
            }
            signature.append(")");
            
            System.out.println("  - " + signature.toString());
        }
        System.out.println("<<END_METHODS_TO_KEEP>>");
        
        System.out.println("\n<<METHODS_TO_REMOVE>>");
        for (CtMethod<?> method : irrelevantTests) {
            String className = method.getParent(CtClass.class).getQualifiedName();
            String methodName = method.getSimpleName();
            
            StringBuilder signature = new StringBuilder();
            signature.append(className).append(".").append(methodName).append("(");
            
            List<CtParameter<?>> params = method.getParameters();
            for (int i = 0; i < params.size(); i++) {
                if (i > 0) signature.append(",");
                CtTypeReference<?> typeRef = params.get(i).getType();
                if (typeRef != null) {
                    signature.append(typeRef.getQualifiedName());
                }
            }
            signature.append(")");
            
            System.out.println("  - " + signature.toString());
        }
        System.out.println("<<END_METHODS_TO_REMOVE>>");
        
        return relevantTests;
    }
    
    private boolean isTestClass(CtType<?> type) {
        if (type.getPosition().getFile() == null) {
            return false;
        }
        
        String filePath = type.getPosition().getFile().getAbsolutePath();
        
        if (Config.useRelevantTestsOnly && !Config.baseTestFilePaths.isEmpty()) {
            return Config.baseTestFilePaths.stream().anyMatch(testPath -> filePath.equals(testPath));
        }
        
        return type.getSimpleName().contains("Test");
    }
    
    private static boolean isTestMethod(CtMethod<?> method) {
        if (!method.hasModifier(ModifierKind.PUBLIC)) {
            return false;
        }
        
        if (method.getBody() == null || method.getBody().getStatements().isEmpty()) {
            return false;
        }
        
        boolean hasTestAnnotation = method.getAnnotations().stream()
                .anyMatch(a -> a.getAnnotationType().getSimpleName().equals("Test"));
        
        if (hasTestAnnotation) {
            return true;
        }
        
        boolean startsWithTest = method.getSimpleName().startsWith("test");
        boolean hasNoParameters = method.getParameters().isEmpty();
        
        return startsWithTest && hasNoParameters;
    }

}
