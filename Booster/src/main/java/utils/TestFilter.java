package utils;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class TestFilter {

    public static class FilterResult {
        private List<String> baseTests;
        private List<String> extendedTests;

        public FilterResult(List<String> baseTests, List<String> extendedTests) {
            this.baseTests = baseTests;
            this.extendedTests = extendedTests;
        }

        public List<String> getBaseTests() {
            return baseTests;
        }

        public List<String> getExtendedTests() {
            return extendedTests;
        }
    }

    public static class MethodSelectionResult {
        private Map<String, List<String>> selectedMethods;
        private int totalMethodCount;

        public MethodSelectionResult(Map<String, List<String>> selectedMethods, int totalMethodCount) {
            this.selectedMethods = selectedMethods;
            this.totalMethodCount = totalMethodCount;
        }

        public Map<String, List<String>> getSelectedMethods() {
            return selectedMethods;
        }

        public int getTotalMethodCount() {
            return totalMethodCount;
        }
    }

    public static FilterResult filterTests(List<String> allTestPaths, String outputPath) {
        String filteredClassesPath = findFilteredTestClassesFile(outputPath);

        if (filteredClassesPath == null) {
            // System.out.println("[TestFilter] filtered_test_classes.txt not found, using
            // all tests");
            return new FilterResult(new ArrayList<>(allTestPaths), new ArrayList<>());
        }

        Set<String> filteredClassNames = loadFilteredClassNames(filteredClassesPath);

        if (filteredClassNames.isEmpty()) {
            System.out.println("[TestFilter] No filtered class names found, using all tests");
            return new FilterResult(new ArrayList<>(allTestPaths), new ArrayList<>());
        }

        List<String> baseTests = new ArrayList<>();
        List<String> extendedTests = new ArrayList<>();

        for (String testPath : allTestPaths) {
            String className = extractClassNameFromPath(testPath);

            if (className != null && filteredClassNames.contains(className)) {
                baseTests.add(testPath);
            } else {
                extendedTests.add(testPath);
            }
        }

        System.out.println("[TestFilter] Total tests: " + allTestPaths.size());
        System.out.println("[TestFilter] Base tests (calling CUT): " + baseTests.size());
        System.out.println("[TestFilter] Extended tests (helpers): " + extendedTests.size());

        return new FilterResult(baseTests, extendedTests);
    }

    public static String findFilteredTestClassesFile(String outputPath) {
        // Support both Unix (/) and Windows (\) path separators
        String normalizedPath = outputPath.replace(File.separator, "/");
        // Pattern supports 1-4 hex digits for both directories (e.g., 1f/00, 24f/0a,
        // 100f/ff)
        Pattern pattern = Pattern.compile("tar_extracted/[0-9a-f]{1,4}/[0-9a-f]{1,4}");
        Matcher matcher = pattern.matcher(normalizedPath);

        if (!matcher.find()) {
            // System.out.println("[TestFilter] Could not find tar_extracted pattern in: " +
            // outputPath);
            // System.out.println("[TestFilter] Normalized path: " + normalizedPath);
            return null;
        }

        // Extract the base path up to tar_extracted/XX/XX
        String tarExtractedPart = matcher.group();
        int startIndex = normalizedPath.indexOf(tarExtractedPart);
        int endIndex = startIndex + tarExtractedPart.length();

        // Convert back to original path with proper separators
        String beforePattern = outputPath.substring(0, outputPath.indexOf("tar_extracted"));
        String basePath = beforePattern + tarExtractedPart.replace("/", File.separator);

        // System.out.println("[TestFilter] Detected base path: " + basePath);

        // Try to find filtered_test_classes.txt in the base path
        String filteredClassesPath = basePath + File.separator + "filtered_test_classes.txt";
        File file = new File(filteredClassesPath);

        if (file.exists()) {
            // System.out.println("[TestFilter] Found filtered_test_classes.txt at: " +
            // filteredClassesPath);
            return filteredClassesPath;
        }

        // If not found, walk up the directory tree to find it
        // System.out.println("[TestFilter] Not found at expected location, walking up
        // directory tree...");
        File currentDir = new File(outputPath);
        while (currentDir != null && currentDir.getAbsolutePath().contains("tar_extracted")) {
            File testFile = new File(currentDir, "filtered_test_classes.txt");
            // System.out.println("[TestFilter] Checking: " + testFile.getAbsolutePath());
            if (testFile.exists()) {
                // System.out.println("[TestFilter] Found filtered_test_classes.txt at: " +
                // testFile.getAbsolutePath());
                return testFile.getAbsolutePath();
            }
            currentDir = currentDir.getParentFile();
        }

        // System.out.println("[TestFilter] File not found after walking up from: " +
        // outputPath);
        return null;
    }

    public static Set<String> loadFilteredClassNames(String filePath) {
        Set<String> classNames = new HashSet<>();

        try (BufferedReader reader = new BufferedReader(new FileReader(filePath))) {
            String line;
            while ((line = reader.readLine()) != null) {
                line = line.trim();
                if (!line.isEmpty() && !line.startsWith("#")) {
                    classNames.add(line);
                }
            }
        } catch (IOException e) {
            // System.err.println("[TestFilter] Error reading filtered_test_classes.txt: " +
            // e.getMessage());
        }

        return classNames;
    }

    public static String extractClassNameFromPath(String testPath) {
        if (testPath == null || testPath.isEmpty()) {
            return null;
        }

        testPath = testPath.replace(File.separatorChar, '/');
        // System.err.println("[DEBUG-extractClassNameFromPath] Processing path: " +
        // testPath);

        // Try pattern 1: tar_extracted/[hex]/[hex]/path (defects4j extracted format)
        // Pattern supports 1-4 hex digits for both directories (e.g., 1f/00, 24f/0a,
        // 100f/ff)
        Pattern pattern1 = Pattern.compile("tar_extracted/[0-9a-f]{1,4}/[0-9a-f]{1,4}/(.+)\\.java$");
        Matcher matcher1 = pattern1.matcher(testPath);

        if (matcher1.find()) {
            String relativePath = matcher1.group(1);
            String className = relativePath.replace('/', '.');
            // System.err.println("[DEBUG-extractClassNameFromPath] Pattern 1
            // (tar_extracted) matched: " + className);
            return className;
        }

        // Try pattern 2: booster_output/path (regular package structure)
        // e.g., /path/booster_output/org/apache/commons/lang3/math/NumberUtilsTest.java
        Pattern pattern2 = Pattern.compile("booster_output/(.+)\\.java$");
        Matcher matcher2 = pattern2.matcher(testPath);

        if (matcher2.find()) {
            String relativePath = matcher2.group(1);
            String className = relativePath.replace('/', '.');
            // System.err.println("[DEBUG-extractClassNameFromPath] Pattern 2
            // (booster_output) matched: " + className);
            return className;
        }

        // Try pattern 3: src/main/java or src/test/java format
        Pattern srcPattern = Pattern.compile("src/(main|test)/java/(.+)\\.java$");
        Matcher srcMatcher = srcPattern.matcher(testPath);
        if (srcMatcher.find()) {
            String relativePath = srcMatcher.group(2);
            String className = relativePath.replace('/', '.');
            // System.err.println("[DEBUG-extractClassNameFromPath] Pattern 3
            // (src/main/java) matched: " + className);
            return className;
        }

        // System.err.println("[DEBUG-extractClassNameFromPath] No pattern matched for:
        // " + testPath);
        return null;
    }

    /**
     * Select test methods using round-robin strategy with upper limit
     * 
     * Stage 1: Bug-triggering test classes
     * Stage 2: Same package as bug-triggering classes
     * Stage 3: All test methods in project
     * 
     * @param allTestPaths         All test file paths
     * @param bugTriggeringClasses Set of bug-triggering class names
     * @param upperLimit           Maximum number of test methods to select (e.g.,
     *                             500)
     * @return Map of test class path -> list of selected method signatures
     */
    public static MethodSelectionResult selectTestMethodsRoundRobin(
            List<String> allTestPaths,
            Set<String> bugTriggeringClasses,
            int upperLimit) {

        // Parse all test files to get method information
        Map<String, TestClassInfo> allTestClassInfo = parseAllTestClasses(allTestPaths);

        // Count total methods
        int totalMethods = 0;
        for (TestClassInfo info : allTestClassInfo.values()) {
            totalMethods += info.methodSignatures.size();
        }

        // System.out.println("[MethodSelection] Total test methods in project: " +
        // totalMethods);
        // System.out.println("[MethodSelection] Upper limit: " + upperLimit);

        // If total is less than limit, return all methods
        if (totalMethods <= upperLimit) {
            // System.out.println("[MethodSelection] Total methods <= upper limit, using all
            // methods");
            Map<String, List<String>> allMethods = new LinkedHashMap<>();
            for (Map.Entry<String, TestClassInfo> entry : allTestClassInfo.entrySet()) {
                allMethods.put(entry.getKey(), new ArrayList<>(entry.getValue().methodSignatures));
            }
            return new MethodSelectionResult(allMethods, totalMethods);
        }

        // Stage-based selection
        Map<String, List<String>> selectedMethods = new LinkedHashMap<>();
        int selectedCount = 0;

        // Stage 1: Bug-triggering test classes
        List<TestClassInfo> stage1Classes = new ArrayList<>();
        List<TestClassInfo> stage2Classes = new ArrayList<>();
        List<TestClassInfo> stage3Classes = new ArrayList<>();

        Set<String> bugTriggeringPackages = new HashSet<>();
        for (String className : bugTriggeringClasses) {
            int lastDot = className.lastIndexOf('.');
            if (lastDot > 0) {
                bugTriggeringPackages.add(className.substring(0, lastDot));
            }
        }

        for (Map.Entry<String, TestClassInfo> entry : allTestClassInfo.entrySet()) {
            TestClassInfo info = entry.getValue();
            if (bugTriggeringClasses.contains(info.className)) {
                stage1Classes.add(info);
            } else if (bugTriggeringPackages.contains(info.packageName)) {
                stage2Classes.add(info);
            } else {
                stage3Classes.add(info);
            }
        }

        // Count methods per stage
        int stage1MethodCount = countTotalMethods(stage1Classes);
        int stage2MethodCount = countTotalMethods(stage2Classes);
        int stage3MethodCount = countTotalMethods(stage3Classes);

        // System.out.println("[MethodSelection] Stage 1 (bug-triggering classes): " +
        // stage1Classes.size() + " classes, " + stage1MethodCount + " methods");
        // System.out.println("[MethodSelection] Stage 2 (same package): " +
        // stage2Classes.size() + " classes, " + stage2MethodCount + " methods");
        // System.out.println("[MethodSelection] Stage 3 (all others): " +
        // stage3Classes.size() + " classes, " + stage3MethodCount + " methods");

        // Stage 1: Add classes one by one until we would exceed limit
        selectedCount = processStage(stage1Classes, selectedMethods, selectedCount, upperLimit, "Stage 1");
        if (selectedCount >= upperLimit) {
            return new MethodSelectionResult(selectedMethods, selectedCount);
        }

        // Stage 2: Add classes one by one until we would exceed limit
        selectedCount = processStage(stage2Classes, selectedMethods, selectedCount, upperLimit, "Stage 2");
        if (selectedCount >= upperLimit) {
            return new MethodSelectionResult(selectedMethods, selectedCount);
        }

        // Stage 3: Add classes one by one until we would exceed limit
        selectedCount = processStage(stage3Classes, selectedMethods, selectedCount, upperLimit, "Stage 3");

        // System.out.println("[MethodSelection] Final selection: " + selectedCount + "
        // methods from " + selectedMethods.size() + " classes");

        return new MethodSelectionResult(selectedMethods, selectedCount);
    }

    private static int countTotalMethods(List<TestClassInfo> classes) {
        int count = 0;
        for (TestClassInfo info : classes) {
            count += info.methodSignatures.size();
        }
        return count;
    }

    private static int processStage(
            List<TestClassInfo> stageClasses,
            Map<String, List<String>> selectedMethods,
            int currentCount,
            int upperLimit,
            String stageName) {

        if (stageClasses.isEmpty()) {
            return currentCount;
        }

        // Calculate total methods in this stage
        int stageTotalMethods = countTotalMethods(stageClasses);
        int remainingQuota = upperLimit - currentCount;

        // If stage total methods <= remaining quota, select all
        if (stageTotalMethods <= remainingQuota) {
            // System.out.println("[MethodSelection] " + stageName + ": Stage has " +
            // stageTotalMethods + " methods, selecting all");
            for (TestClassInfo info : stageClasses) {
                selectedMethods.put(info.testPath, new ArrayList<>(info.methodSignatures));
                currentCount += info.methodSignatures.size();
            }
            // System.out.println("[MethodSelection] " + stageName + ": Completed, total so
            // far: " + currentCount);
            return currentCount;
        }

        // Stage total methods > remaining quota, use round-robin from the start
        // System.out.println("[MethodSelection] " + stageName + ": Stage has " +
        // stageTotalMethods + " methods but only " + remainingQuota + " quota
        // remaining, using round-robin");
        currentCount = roundRobinSelect(stageClasses, selectedMethods, currentCount, upperLimit);
        // System.out.println("[MethodSelection] " + stageName + ": Reached upper limit
        // with round-robin (total: " + currentCount + ")");
        return currentCount;
    }

    private static int selectAllMethods(
            List<TestClassInfo> classes,
            Map<String, List<String>> selectedMethods,
            int currentCount) {

        for (TestClassInfo info : classes) {
            selectedMethods.put(info.testPath, new ArrayList<>(info.methodSignatures));
            currentCount += info.methodSignatures.size();
        }

        return currentCount;
    }

    private static int roundRobinSelect(
            List<TestClassInfo> classes,
            Map<String, List<String>> selectedMethods,
            int currentCount,
            int upperLimit) {

        if (classes.isEmpty()) {
            return currentCount;
        }

        // Create iterators for each class
        Map<String, Iterator<String>> iterators = new LinkedHashMap<>();
        for (TestClassInfo info : classes) {
            iterators.put(info.testPath, info.methodSignatures.iterator());
        }

        // Round-robin selection
        boolean hasMore = true;
        while (hasMore && currentCount < upperLimit) {
            hasMore = false;

            for (Map.Entry<String, Iterator<String>> entry : iterators.entrySet()) {
                if (currentCount >= upperLimit) {
                    break;
                }

                Iterator<String> iter = entry.getValue();
                if (iter.hasNext()) {
                    hasMore = true;
                    String method = iter.next();

                    selectedMethods.putIfAbsent(entry.getKey(), new ArrayList<>());
                    selectedMethods.get(entry.getKey()).add(method);
                    currentCount++;
                }
            }
        }

        return currentCount;
    }

    private static Map<String, TestClassInfo> parseAllTestClasses(List<String> testPaths) {
        Map<String, TestClassInfo> result = new LinkedHashMap<>();

        for (String testPath : testPaths) {
            TestClassInfo info = parseTestClass(testPath);
            if (info != null && !info.methodSignatures.isEmpty()) {
                result.put(testPath, info);
            }
        }

        return result;
    }

    private static TestClassInfo parseTestClass(String testPath) {
        File file = new File(testPath);
        if (!file.exists()) {
            return null;
        }

        String className = extractClassNameFromPath(testPath);
        if (className == null) {
            return null;
        }

        String packageName = "";
        int lastDot = className.lastIndexOf('.');
        if (lastDot > 0) {
            packageName = className.substring(0, lastDot);
        }

        List<String> methodSignatures = new ArrayList<>();

        // Use Spoon to parse and find test methods
        try {
            spoon.Launcher launcher = new spoon.Launcher();
            launcher.addInputResource(testPath);
            launcher.getEnvironment().setNoClasspath(true);
            launcher.getEnvironment().setAutoImports(true);
            launcher.getEnvironment().setComplianceLevel(8);
            launcher.getEnvironment().setCommentEnabled(false);

            spoon.reflect.CtModel model = launcher.buildModel();

            // Get all methods in the model
            List<spoon.reflect.declaration.CtMethod<?>> allMethods = model.getElements(
                    new spoon.reflect.visitor.filter.TypeFilter<>(spoon.reflect.declaration.CtMethod.class));

            // Filter test methods using isTestMethod logic
            for (spoon.reflect.declaration.CtMethod<?> method : allMethods) {
                if (isTestMethod(method)) {
                    methodSignatures.add(method.getSimpleName());
                }
            }

        } catch (Exception e) {
            // System.err.println("[TestFilter] Error parsing test class with Spoon " +
            // testPath + ": " + e.getMessage());
            return null;
        }

        return new TestClassInfo(testPath, className, packageName, methodSignatures);
    }

    private static boolean isTestMethod(spoon.reflect.declaration.CtMethod<?> method) {
        // JUnit 3 style: public void testXXX()
        boolean j3 = method.getSimpleName().startsWith("test");

        // JUnit 4 style: @Test annotation
        boolean j4 = method.getAnnotations().stream()
                .anyMatch(a -> a.getAnnotationType().getSimpleName().equals("Test"));

        boolean isPublic = method.hasModifier(spoon.reflect.declaration.ModifierKind.PUBLIC);
        boolean noParams = method.getParameters().isEmpty();
        boolean hasBody = method.getBody() != null && !method.getBody().getStatements().isEmpty();

        return isPublic && (j3 || j4) && noParams && hasBody;
    }

    private static class TestClassInfo {
        String testPath;
        String className;
        String packageName;
        List<String> methodSignatures;

        TestClassInfo(String testPath, String className, String packageName, List<String> methodSignatures) {
            this.testPath = testPath;
            this.className = className;
            this.packageName = packageName;
            this.methodSignatures = methodSignatures;
        }
    }
}
