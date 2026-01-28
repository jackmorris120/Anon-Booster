package Generater.PrimitiveMutation;

import Compiler.Compiler;
import spoon.Launcher;
import spoon.reflect.CtModel;
import spoon.reflect.code.*;
import spoon.reflect.declaration.*;
import spoon.reflect.factory.Factory;
import spoon.reflect.reference.CtArrayTypeReference;
import spoon.reflect.reference.CtExecutableReference;
import spoon.reflect.reference.CtLocalVariableReference;
import spoon.reflect.reference.CtTypeReference;
import spoon.reflect.reference.CtVariableReference;
import spoon.reflect.visitor.DefaultJavaPrettyPrinter;
import spoon.reflect.visitor.ImportScanner;
import spoon.reflect.visitor.ImportScannerImpl;
import spoon.reflect.visitor.filter.TypeFilter;
import spoon.support.reflect.code.*;
import spoon.support.reflect.declaration.CtMethodImpl;
import spoon.support.reflect.declaration.CtParameterImpl;
import spoon.support.reflect.reference.CtExecutableReferenceImpl;
import spoon.support.reflect.reference.CtFieldReferenceImpl;
import spoon.support.reflect.reference.CtLocalVariableReferenceImpl;
import spoon.support.reflect.reference.CtParameterReferenceImpl;
import spoon.support.sniper.SniperJavaPrettyPrinter;
import spoon.support.reflect.declaration.CtFieldImpl;
import utils.Config;
import utils.TestFilter;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.*;
import javax.tools.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import org.apache.commons.lang3.tuple.Pair;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import spoon.reflect.reference.CtFieldReference;
import spoon.reflect.visitor.CtScanner;

import spoon.compiler.Environment;

public class PrimitiveParser {
    private static Map<String, Set<CtElement>> primitiveTypeAndVal = new HashMap<>();
    private static Map<String, List<CtMethod<?>>> baseTestMethodMap = new HashMap<>();
    private static Map<String, CtClass<?>> skeletalTestClassMap = new HashMap<>();
    private static Map<String, String> packageMap = new HashMap<>();
    private static Map<String, String> importMap = new HashMap<>();
    private static List<String> bugTriggeringTestFilePaths = new ArrayList<>();
    private static Map<String, List<String>> selectedTestMethodsMap = null;
    private static int currTestIdx = 0;
    private static int totalBaseTests = 0;
    private static boolean DEBUG = false;
    private static final boolean DEBUG_STRING_MUTATION = false;
    private static boolean LIMIT_TO_PUBLIC_APIS = false;

    public static Map<String, CtClass<?>> getSkeletalTestClassMap() {
        return skeletalTestClassMap;
    }

    public static Map<String, String> getImportMap() {
        return importMap;
    }

    public static Map<String, String> getPackageMap() {
        return packageMap;
    }

    public static Map<String, Set<CtElement>> getPrimitiveTypeAndVal() {
        return primitiveTypeAndVal;
    }

    public static Map<String, List<CtMethod<?>>> getBaseTestMethodMap() {
        return baseTestMethodMap;
    }

    private static boolean insertPrimitiveTypeAndVal(CtTypeReference<?> type, CtElement val) {
        if (type == null || val == null) {
            return false;
        }

        String key = type.getQualifiedName();
        CtElement clonedVal = val.clone();

        if ("java.lang.String".equals(key) && clonedVal instanceof CtLiteral) {
            Object v = ((CtLiteral<?>) clonedVal).getValue();
            if (v instanceof String) {
                Factory f = clonedVal.getFactory();
                CtLiteral<String> safe = createSafeStringLiteral(f, (String) v);
                clonedVal = safe;
            }
        }
        primitiveTypeAndVal.computeIfAbsent(key, k -> new HashSet<>());

        if (clonedVal.toString().startsWith("java.lang.Double.NaN")) {
            if (clonedVal.isParentInitialized() && !(clonedVal.getParent() instanceof CtInvocation)) {
                return primitiveTypeAndVal.get(key).add(clonedVal);
            }
        }

        return primitiveTypeAndVal.get(key).add(clonedVal);
    }

    public static void parse(List<String> testFilePaths) {
        parse(testFilePaths, null);
    }

    public static void parse(List<String> testFilePaths, Map<String, List<String>> selectedMethodsMap) {
        selectedTestMethodsMap = selectedMethodsMap;
        List<String> targets = convertClassToPath(Config.BUGTRIGGERRING_TESTS);
        bugTriggeringTestFilePaths = new ArrayList<>(targets);
        Set<String> targetPackages = extractPackageNamesFromBugTriggeringTests(Config.BUGTRIGGERRING_TESTS);

        // ★ CUT 공개 API 수집
        // NOTE: Config.CUT_FILES 는 List<String> 이라고 가정합니다.
        Set<String> cutPublicApis = null;
        if (LIMIT_TO_PUBLIC_APIS) {
            System.out.println("[Public API] Limiting base tests to those invoking CUT public APIs from files ");
            cutPublicApis = extractCutPublicApis(Config.CUT_FILES);
        }

        Set<String> bugTriggeringFilePathSet = new HashSet<>(targets);

        // 1) 모든 테스트 파일에서 primitive 값 수집
        // System.out.println("[PRIMITIVE] Collecting primitive values from all " +
        // testFilePaths.size() + " test files");
        collectPrimitiveValues(testFilePaths);

        // ★ NOTE: applyTwoSwitchFiltering 제거
        // TestFilter가 base/extended를 분리하므로, 단순 파일 레벨 필터링은 불필요
        // 대신 모든 테스트 파일을 TestFilter에 전달하고, 그 후 bug triggering 우선순위는
        // generatePriorityQueue에서 처리함
        System.out.println("[PRIMITIVE] Generating base tests from " + testFilePaths.size() + " test files");

        // 2.1) TestFilter를 사용하여 실제 CUT를 호출하는 baseTest와 extended test 분리
        TestFilter.FilterResult filterResult = TestFilter.filterTests(testFilePaths, Config.OUTPUT_PATH);
        
        List<String> actualBaseTests = filterResult.getBaseTests();
        List<String> helperTests = filterResult.getExtendedTests();


        // ★ Bug Triggering 파일 중 실제 base test인 것들만 필터링
        List<String> bugTriggeringBaseTests = new ArrayList<>();
        for (String basePath : actualBaseTests) {
            // 경로 정규화를 통한 매칭
            String normalizedPath = normalizePath(basePath);
            for (String bugPath : bugTriggeringTestFilePaths) {
                String normalizedBugPath = normalizePath(bugPath);
                if (normalizedPath.equals(normalizedBugPath)) {
                    bugTriggeringBaseTests.add(basePath);
                    break;
                }
            }
        }

        System.out.println("[PRIMITIVE] Bug triggering base tests: " + bugTriggeringBaseTests.size() + " / "
                + actualBaseTests.size());

        // Config.EXTENDED_TESTS에 새로 발견된 helper tests 추가 (중복 방지)
        if (Config.EXTENDED_TESTS == null) {
            Config.EXTENDED_TESTS = new ArrayList<>();
        }

        // 기존 EXTENDED_TESTS를 Set으로 변환 (중복 체크용)
        Set<String> existingExtended = new HashSet<>(Config.EXTENDED_TESTS);

        for (String helperPath : helperTests) {
            String className = TestFilter.extractClassNameFromPath(helperPath);
            if (className != null && !existingExtended.contains(className)) {
                Config.EXTENDED_TESTS.add(className);
                existingExtended.add(className);
            }
        }

        System.out.println(
                "[TestFilter] Total EXTENDED_TESTS (original + filtered helpers): " + Config.EXTENDED_TESTS.size());

        // 2.5) Extended tests를 JUnit4로 변환 (but not included in base test generation)
        convertExtendedTestsToJUnit4(testFilePaths, actualBaseTests);

        // 3) 베이스 모델 초기화 + ★ 메소드 레벨 필터 적용
        Set<String> bugTriggeringBaseTestsSet = new HashSet<>(bugTriggeringBaseTests);
        initBaseModels(actualBaseTests, targets, targetPackages, bugTriggeringBaseTestsSet, cutPublicApis);

        // ★ 마지막에 bugTriggeringTestFilePaths를 실제 경로로 업데이트 (generatePriorityQueue에서 사용)
        bugTriggeringTestFilePaths = bugTriggeringBaseTests;
        Config.START_TIME = System.currentTimeMillis();

        // System.out.println("\n============================================");
        // System.out.println("Base Tests Summary");
        // System.out.println("============================================");

        for (Map.Entry<String, List<CtMethod<?>>> entry : baseTestMethodMap.entrySet()) {
            String path = entry.getKey();
            List<CtMethod<?>> methods = entry.getValue();

            // System.out.println("\n[" + path + "]");
            for (CtMethod<?> method : methods) {
                // System.out.println(" - " + method.getSimpleName());
                totalBaseTests++;
            }
        }

        System.out.println("\n============================================");
        System.out.println("Total number of base tests collected: " + totalBaseTests);
        System.out.println("============================================");
    }

    /**
     * Extended tests를 JUnit3에서 JUnit4로 변환하되, base test 생성에는 포함하지 않음
     */
    private static void convertExtendedTestsToJUnit4(List<String> allTestFilePaths,
            List<String> filteredTestFilePaths) {
        if (Config.EXTENDED_TESTS == null || Config.EXTENDED_TESTS.isEmpty()) {
            System.out.println("[DEBUG] EXTENDED_TESTS is empty, skipping removeExtension");
            return;
        }

        System.out.println("[DEBUG] EXTENDED_TESTS count: " + Config.EXTENDED_TESTS.size());

        Set<String> filteredSet = new HashSet<>(filteredTestFilePaths);
        int processedCount = 0;

        for (String testFilePath : allTestFilePaths) {
            // Check for NodeTestBase specifically
            if (testFilePath.contains("NodeTestBase")) {
                System.out.println("[DEBUG] Found NodeTestBase path: " + testFilePath);
                System.out.println("[DEBUG] Is in filteredSet: " + filteredSet.contains(testFilePath));
            }

            // Skip if already included in filtered files (will be processed by
            // initBaseModels)
            if (filteredSet.contains(testFilePath)) {
                if (testFilePath.contains("NodeTestBase")) {
                    System.out.println("[DEBUG] NodeTestBase skipped - already in filteredSet");
                }
                continue;
            }

            // Check if this file is an extended test
            boolean isExtendedTest = false;
            for (String extendedTest : Config.EXTENDED_TESTS) {
                String className = extendedTest.substring(extendedTest.lastIndexOf('.') + 1);
                if (testFilePath.contains(className)) {
                    isExtendedTest = true;
                    break;
                }
            }

            if (!isExtendedTest) {
                if (testFilePath.contains("NodeTestBase")) {
                    System.out.println("[DEBUG] NodeTestBase not matched as extended test");
                }
                continue;
            }

            processedCount++;
            System.out.println("[DEBUG] Processing extended test #" + processedCount + ": " + testFilePath);

            // Convert JUnit3 to JUnit4 for this extended test file
            Launcher launcher = new Launcher();
            Pair<CtModel, Factory> mf = initModel(testFilePath, launcher);
            CtModel ctModel = mf.getLeft();
            Factory factory = mf.getRight();

            if (ctModel == null || factory == null) {
                continue;
            }

            boolean modified = removeExtension(ctModel, testFilePath, launcher);
            if (modified) {
                System.out.println("[DEBUG] Modified and overwriting: " + testFilePath);
                overwriteOriginalFile(ctModel, testFilePath, launcher);
            }
        }
    }

    private static List<String> filterTargetPkgs(List<String> CUT_FILES) {
        Set<String> packageNames = new HashSet<>();
        for (String cutFile : CUT_FILES) {
            try (BufferedReader reader = new BufferedReader(new FileReader(cutFile))) {
                String line;
                while ((line = reader.readLine()) != null) {
                    String trimmedLine = line.trim();
                    if (trimmedLine.startsWith("package ")) {
                        int startIndex = "package ".length();
                        int endIndex = trimmedLine.indexOf(';');

                        if (endIndex != -1) {
                            String packageName = trimmedLine.substring(startIndex, endIndex).trim();
                            packageNames.add(packageName);
                            break;
                        }
                    }
                }
            } catch (IOException e) {
                System.err.println("Error reading file: " + cutFile);
                // // e.printStackTrace();
            }
        }
        return new ArrayList<>(packageNames);
    }

    private static String normalizePath(String path) {
        if (path == null) {
            return "";
        }
        try {
            return new File(path).getAbsolutePath();
        } catch (Exception e) {
            return path;
        }
    }

    private static List<String> convertClassToPath(String BTTests) {
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

    /**
     * Collect primitive values from all test files (no filtering applied)
     */
    private static void collectPrimitiveValues(List<String> testFilePaths) {
        System.out.println("[PRIMITIVE] Starting primitive value collection from " + testFilePaths.size() + " files");
        int processedFiles = 0;
        int collectedValues = 0;

        for (String path : testFilePaths) {
            try {
                Launcher launcher = new Launcher();
                Pair<CtModel, Factory> mf = initModel(path, launcher);
                CtModel ctModel = mf.getLeft();
                Factory factory = mf.getRight();
                if (ctModel == null || factory == null) {
                    continue;
                }

                List<CtMethod<?>> testMethods = getTestCases(ctModel);
                if (testMethods.isEmpty()) {
                    continue;
                }

                int beforeSize = getTotalPrimitiveValueCount();
                collectPrimitiveAndStringValues(testMethods);
                int afterSize = getTotalPrimitiveValueCount();

                collectedValues += (afterSize - beforeSize);
                processedFiles++;

            } catch (Exception e) {
                System.err.println("[PRIMITIVE] Error collecting from file: " + path + " - " + e.getMessage());
            }
        }

        if (Config.SEED_AUGMENTATION) {
            augmentExtremeSeeds();
            augmentStringValues();
        }

        System.out.println("[PRIMITIVE] Collected " + collectedValues + " primitive values from " +
                processedFiles + " files");
    }

    private static int getTotalPrimitiveValueCount() {
        return primitiveTypeAndVal.values().stream()
                .mapToInt(Set::size)
                .sum();
    }

    private static List<String> filterBugTriggeringTestFiles(List<String> testFilePaths,
            List<String> bugTriggeringTestFilePaths) {
        List<String> ret = new ArrayList<>();
        if (bugTriggeringTestFilePaths == null || bugTriggeringTestFilePaths.isEmpty()) {
            return ret;
        }

        Set<String> bugTriggeringFileSet = new HashSet<>(bugTriggeringTestFilePaths);

        for (String testFilePath : testFilePaths) {
            if (bugTriggeringFileSet.contains(testFilePath)) {
                ret.add(testFilePath);
            }
        }

        return ret;
    }

    private static List<String> filterTestFilesByPackage(List<String> testFilePaths, Set<String> targetPackages) {
        List<String> ret = new ArrayList<>();
        if (targetPackages == null || targetPackages.isEmpty()) {
            return ret;
        }

        for (String path : testFilePaths) {
            File file = new File(path);

            try (BufferedReader br = new BufferedReader(new FileReader(file))) {
                String line;
                while ((line = br.readLine()) != null) {
                    line = line.trim();

                    if (line.startsWith("package ")) {
                        String pkgLine = line;
                        String parsedPkg = pkgLine.substring("package ".length()).trim();

                        if (parsedPkg.endsWith(";")) {
                            parsedPkg = parsedPkg.substring(0, parsedPkg.length() - 1).trim();
                        }

                        if (targetPackages.contains(parsedPkg)) {
                            ret.add(path);
                        }
                        break;
                    }
                }
            } catch (IOException e) {
                System.err.println("Error reading file: " + path);
                // // e.printStackTrace();
            }
        }

        return ret;
    }

    private static List<String> applyTwoSwitchFiltering(List<String> testFilePaths, List<String> bugTriggeringTestFiles,
            Set<String> targetPackages) {
        boolean enableFileFiltering = Config.LIMIT_TO_BUG_TRIGGERING_TESTS;
        boolean enablePackageFiltering = Config.LIMIT_TO_BUG_TRIGGERING_PACKAGES && !targetPackages.isEmpty();

        System.out.println("PrimitiveParser Filtering Configuration:");
        System.out.println("  LIMIT_TO_BUG_TRIGGERING_TESTS (file-level): " + enableFileFiltering);
        System.out.println("  LIMIT_TO_BUG_TRIGGERING_PACKAGES (package-level): " + enablePackageFiltering);
        System.out.println("  Total input test files: " + testFilePaths.size());

        List<String> filteredFiles;

        if (enableFileFiltering && enablePackageFiltering) {
            System.out.println("BOTH FILTERS ENABLED: Applying file-level then package-level filtering...");
            List<String> fileFiltered = filterBugTriggeringTestFiles(testFilePaths, bugTriggeringTestFiles);
            filteredFiles = filterTestFilesByPackage(fileFiltered, targetPackages);
            System.out.println("File-level filter: " + testFilePaths.size() + " -> " + fileFiltered.size() + " files");
            System.out
                    .println("Package-level filter: " + fileFiltered.size() + " -> " + filteredFiles.size() + " files");

        } else if (enableFileFiltering && !enablePackageFiltering) {
            System.out.println("FILE-LEVEL FILTERING ONLY: Filtering to bug triggering test files...");
            filteredFiles = filterBugTriggeringTestFiles(testFilePaths, bugTriggeringTestFiles);
            System.out.println("Filtered " + testFilePaths.size() + " files down to " + filteredFiles.size()
                    + " bug triggering test files");

        } else if (!enableFileFiltering && enablePackageFiltering) {
            System.out.println("PACKAGE-LEVEL FILTERING ONLY: Filtering to bug triggering packages...");
            filteredFiles = filterTestFilesByPackage(testFilePaths, targetPackages);
            System.out.println("Filtered " + testFilePaths.size() + " files down to " + filteredFiles.size()
                    + " files in target packages: " + targetPackages);

        } else {
            filteredFiles = new ArrayList<>(testFilePaths);
            System.out.println("NO FILTERING: Using all test files (" + testFilePaths.size() + " files)");
        }

        System.out.println("Final # of test files for primitive parsing: " + filteredFiles.size());
        return filteredFiles;
    }

    private static Set<String> extractPackageNamesFromBugTriggeringTests(String BTTests) {
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

            int lastDotIndex = className.lastIndexOf('.');
            if (lastDotIndex > 0) {
                String packageName = className.substring(0, lastDotIndex);
                packageNames.add(packageName);
            }
        }

        return packageNames;
    }

    public static void collectPrimitiveAndStringValues(List<CtMethod<?>> methods) {
        for (CtMethod<?> method : methods) {
            for (CtLocalVariable<?> local : method.getElements(new TypeFilter<>(CtLocalVariable.class))) {
                CtExpression<?> init = local.getDefaultExpression();
                if (init instanceof CtLiteral<?> && isPrimitiveOrString(local.getType())) {
                    insertPrimitiveTypeAndVal(local.getType(), init);
                }
            }

            for (CtLiteral<?> literal : method.getElements(new TypeFilter<>(CtLiteral.class))) {
                if (literal.getParent(CtLocalVariable.class) != null) {
                    continue;
                }
                if (!literal.getTypeCasts().isEmpty()) {
                    continue;
                }
                if (isPrimitiveOrString(literal.getType())) {
                    insertPrimitiveTypeAndVal(literal.getType(), literal);
                }
            }

            for (CtExpression<?> expr : method.getElements(new TypeFilter<>(CtExpression.class))) {
                if (!(expr instanceof CtLiteral<?>)) {
                    continue;
                }
                for (CtTypeReference<?> castType : expr.getTypeCasts()) {
                    if (isPrimitiveOrString(castType)) {
                        insertPrimitiveTypeAndVal(castType, expr);
                    }
                }
            }
        }

    }

    private static void augmentExtremeSeeds() {
        Factory factory = new Launcher().getFactory();

        if (primitiveTypeAndVal.containsKey("int")) {
            Set<CtElement> seeds = primitiveTypeAndVal.get("int");
            seeds.add(factory.createLiteral(0));
            seeds.add(factory.createLiteral(Integer.MAX_VALUE));
            seeds.add(factory.createLiteral(Integer.MIN_VALUE));
        }

        if (primitiveTypeAndVal.containsKey("long")) {
            Set<CtElement> seeds = primitiveTypeAndVal.get("long");
            seeds.add(factory.createLiteral(0L));
            seeds.add(factory.createLiteral(Long.MAX_VALUE));
            seeds.add(factory.createLiteral(Long.MIN_VALUE));
        }

        if (primitiveTypeAndVal.containsKey("double")) {
            Set<CtElement> seeds = primitiveTypeAndVal.get("double");
            seeds.add(factory.createLiteral(0.0));
            seeds.add(factory.createLiteral(Double.MAX_VALUE));
            seeds.add(factory.createLiteral(Double.MIN_VALUE));
        }

        if (primitiveTypeAndVal.containsKey("float")) {
            Set<CtElement> seeds = primitiveTypeAndVal.get("float");
            seeds.add(factory.createLiteral(0.0f));
            seeds.add(factory.createLiteral(Float.MAX_VALUE));
            seeds.add(factory.createLiteral(Float.MIN_VALUE));
        }

        if (primitiveTypeAndVal.containsKey("short")) {
            Set<CtElement> seeds = primitiveTypeAndVal.get("short");
            seeds.add(factory.createLiteral((short) 0));
            seeds.add(factory.createLiteral(Short.MAX_VALUE));
            seeds.add(factory.createLiteral(Short.MIN_VALUE));
        }

        if (primitiveTypeAndVal.containsKey("byte")) {
            Set<CtElement> seeds = primitiveTypeAndVal.get("byte");
            seeds.add(factory.createLiteral((byte) 0));
            seeds.add(factory.createLiteral(Byte.MAX_VALUE));
            seeds.add(factory.createLiteral(Byte.MIN_VALUE));
        }

        if (primitiveTypeAndVal.containsKey("char")) {
            Set<CtElement> seeds = primitiveTypeAndVal.get("char");
            seeds.add(factory.createLiteral('\u0000'));
            seeds.add(factory.createLiteral(Character.MAX_VALUE));
            seeds.add(factory.createLiteral(Character.MIN_VALUE));
        }

        if (primitiveTypeAndVal.containsKey("java.lang.String")) {
            Set<CtElement> seeds = primitiveTypeAndVal.get("java.lang.String");
            seeds.add(factory.createLiteral(null));
            seeds.add(factory.createLiteral(""));
            seeds.add(factory.createLiteral("0"));
        }
    }

    // Static variable to store collected special characters (only collect once)
    private static Set<Character> collectedSpecialChars = null;

    /**
     * Extract special characters (_ and @) from primitiveTypeAndVal pool
     */
    private static Set<Character> getSpecialCharactersFromPrimitivePool() {
        if (collectedSpecialChars != null) {
            return collectedSpecialChars;
        }

        collectedSpecialChars = new HashSet<>();

        try {
            if (primitiveTypeAndVal.containsKey("java.lang.String")) {
                Set<CtElement> stringElements = primitiveTypeAndVal.get("java.lang.String");

                for (CtElement element : stringElements) {
                    if (element instanceof CtLiteral) {
                        CtLiteral<?> literal = (CtLiteral<?>) element;
                        Object value = literal.getValue();
                        if (value instanceof String) {
                            String str = (String) value;
                            for (char c : str.toCharArray()) {
                                if (c == '@' || c == '_' || c == '!' || c == '?') {
                                    collectedSpecialChars.add(c);
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
            System.err.println(
                    "[ERROR] Failed to extract special characters from primitiveTypeAndVal: " + e.getMessage());
        }

        return collectedSpecialChars;
    }

    /**
     * Augments String values with various mutations for better test coverage
     */
    private static void augmentStringValues() {
        if (!primitiveTypeAndVal.containsKey("java.lang.String")) {
            return;
        }

        Set<CtElement> stringSeeds = primitiveTypeAndVal.get("java.lang.String");
        Set<CtElement> augmentedValues = new HashSet<>();
        Factory factory = new Launcher().getFactory();

        List<String> shortStrings = new ArrayList<>();
        List<String> allStrings = new ArrayList<>();

        for (CtElement element : stringSeeds) {
            if (element instanceof CtLiteral<?>) {
                CtLiteral<?> literal = (CtLiteral<?>) element;
                Object value = literal.getValue();
                if (value instanceof String && value != null && !((String) value).isEmpty()) {
                    String str = (String) value;
                    allStrings.add(str);
                    if (str.length() <= 3) {
                        shortStrings.add(str);
                    }
                }
            }
        }

        List<String> selectedStrings;
        if (!shortStrings.isEmpty()) {
            Collections.shuffle(shortStrings);
            selectedStrings = shortStrings.subList(0, Math.min(10, shortStrings.size()));
            System.out.println("[PRIMITIVE] Found " + shortStrings.size()
                    + " short strings (≤3 chars), randomly selected " + selectedStrings.size() + " for augmentation");
        } else if (!allStrings.isEmpty()) {
            Collections.shuffle(allStrings);
            selectedStrings = allStrings.subList(0, Math.min(10, allStrings.size()));
            System.out.println("[PRIMITIVE] No short strings found, randomly selected " + selectedStrings.size()
                    + " from " + allStrings.size() + " total strings for augmentation");
        } else {
            selectedStrings = new ArrayList<>();
            System.out.println("[PRIMITIVE] No non-empty strings found for augmentation");
        }

        if (selectedStrings.isEmpty()) {
            return;
        }

        for (String original : selectedStrings) {
            if (DEBUG_STRING_MUTATION) {
                System.out.println("[DEBUG] Mutating string: \"" + original + "\" (length: " + original.length() + ")");
            }

            if (!original.isEmpty()) {
                List<Integer> toggleablePositions = new ArrayList<>();
                for (int i = 0; i < original.length(); i++) {
                    char c = original.charAt(i);
                    if (Character.isLetter(c)) {
                        toggleablePositions.add(i);
                    }
                }

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
                        augmentedValues.add(factory.createLiteral(singleCharToggle));
                        if (DEBUG_STRING_MUTATION) {
                            System.out.println("    [MUTATION] Single char case toggle at pos " + randomPos + ": \""
                                    + original + "\" -> \"" + singleCharToggle + "\"");
                        }
                    }
                }
            }

            Set<Character> specialChars = getSpecialCharactersFromPrimitivePool();

            Set<Character> enhancedSpecialChars = new HashSet<>(specialChars);
            enhancedSpecialChars.add('_');
            enhancedSpecialChars.add('@');

            for (Character specialChar : enhancedSpecialChars) {
                String prefixed = specialChar + original;
                augmentedValues.add(factory.createLiteral(prefixed));
                if (DEBUG_STRING_MUTATION) {
                    System.out.println("    [MUTATION] Special char prefix '" + specialChar + "': \"" + original
                            + "\" -> \"" + prefixed + "\"");
                }

                String suffixed = original + specialChar;
                augmentedValues.add(factory.createLiteral(suffixed));
                if (DEBUG_STRING_MUTATION) {
                    System.out.println("    [MUTATION] Special char suffix '" + specialChar + "': \"" + original
                            + "\" -> \"" + suffixed + "\"");
                }
            }

            if (original.length() == 1) {
                char c = original.charAt(0);
                if (Character.isLetter(c)) {
                    String upperChar = String.valueOf(Character.toUpperCase(c));
                    if (!upperChar.equals(original)) {
                        augmentedValues.add(factory.createLiteral(upperChar));
                        if (DEBUG_STRING_MUTATION) {
                            System.out.println("    [MUTATION] Char case variation: \"" + original + "\" -> \""
                                    + upperChar + "\"");
                        }
                    }

                    String lowerChar = String.valueOf(Character.toLowerCase(c));
                    if (!lowerChar.equals(original)) {
                        augmentedValues.add(factory.createLiteral(lowerChar));
                        if (DEBUG_STRING_MUTATION) {
                            System.out.println("    [MUTATION] Char case variation: \"" + original + "\" -> \""
                                    + lowerChar + "\"");
                        }
                    }
                }
                if (Character.isDigit(c)) {
                    augmentedValues.add(factory.createLiteral("0"));
                    augmentedValues.add(factory.createLiteral("1"));
                    if (DEBUG_STRING_MUTATION) {
                        System.out.println("    [MUTATION] Digit replacement: \"" + original + "\" -> \"0\", \"1\"");
                    }
                }
            }

            String exclaim = original + "!";
            augmentedValues.add(factory.createLiteral(exclaim));

            String question = original + "?";
            augmentedValues.add(factory.createLiteral(question));
        }

        stringSeeds.addAll(augmentedValues);

        System.out.println("[PRIMITIVE] Augmented " + augmentedValues.size() +
                " String values from " + selectedStrings.size() + " original strings (≤3 chars)");
    }

    private static String extractPackageName(String trimmedLine) {
        if (trimmedLine == null || !trimmedLine.startsWith("package ")) {
            return "";
        }
        int start = "package ".length();
        int end = trimmedLine.indexOf(';', start);
        if (end == -1) {
            end = trimmedLine.length();
        }
        return trimmedLine.substring(start, end).trim();
    }

    private static String getImportAndPackage(String testFile) {
        String packageAndImport = "";

        try (BufferedReader bufferedReader = new BufferedReader(new FileReader(testFile))) {
            String line = null;
            Set<String> importSet = new LinkedHashSet<>();
            StringBuilder sb = new StringBuilder();

            importSet.add("import org.junit.*;");
            importSet.add("import java.util.*;");
            importSet.add("import junit.textui.*;");
            importSet.add("import static org.junit.Assert.*;");

            while ((line = bufferedReader.readLine()) != null) {
                String trimmed = line.trim();

                if (trimmed.startsWith("package ")) {
                    sb.append(line).append("\n");
                    String extractedPkg = extractPackageName(trimmed);
                    packageMap.put(testFile, extractedPkg);
                } else if (trimmed.startsWith("import ")) {
                    if (trimmed.contains("import junit.framework.Test;")) {
                        continue;
                    }
                    importSet.add(trimmed);
                }
            }

            for (String importLine : importSet) {
                sb.append(importLine).append("\n");
            }

            packageAndImport = sb.toString();
            return packageAndImport;
        } catch (Exception e) {
            // // e.printStackTrace();
        }

        return packageAndImport;
    }

    public static void renameVariable(CtModel model) {
        int index = 0;
        List<CtMethod<?>> testMethods = getTestCases(model);

        for (CtMethod<?> method : testMethods) {
            List<CtVariableReference<?>> refs = method.getElements(
                    new TypeFilter<>(CtVariableReference.class));

            Map<CtVariable<?>, List<CtVariableReference<?>>> defUse = new LinkedHashMap<>();
            for (CtVariableReference<?> ref : refs) {
                CtVariable<?> def = ref.getDeclaration();
                if (def == null) {
                    continue;
                }
                if (def instanceof CtField) {
                    continue;
                }

                defUse.computeIfAbsent(def, k -> new ArrayList<>()).add(ref);
            }

            for (Map.Entry<CtVariable<?>, List<CtVariableReference<?>>> e : defUse.entrySet()) {
                CtVariable<?> def = e.getKey();
                String newName = def.getSimpleName() + "_" + (index++);
                def.setSimpleName(newName);
                for (CtVariableReference<?> ref : e.getValue()) {
                    if (!ref.getModifiers().contains(ModifierKind.STATIC)) {
                        ref.setSimpleName(newName);
                    }
                }
            }
        }
    }

    // ★★★ 변경: initBaseModels 에 필터 인자 추가
    private static void initBaseModels(List<String> testFilePaths,
            List<String> targets,
            Set<String> targetPackages,
            Set<String> bugTriggeringTestFilePaths,
            Set<String> cutPublicApis) {

        for (String path : testFilePaths) {
            if (path.contains("TestObjectNode.java") && !path.contains("_P_")) {
                System.out.println("[DEBUG] Processing TestObjectNode in initBaseModels: " + path);
            }

            Launcher launcher = new Launcher();
            Pair<CtModel, Factory> mf = initModel(path, launcher);
            CtModel ctModel = mf.getLeft();
            Factory factory = mf.getRight();
            if (ctModel == null || factory == null) {
                if (path.contains("TestObjectNode.java") && !path.contains("_P_")) {
                    System.out.println("[DEBUG] TestObjectNode - ctModel or factory is null");
                }
                continue;
            }

            String packageAndImports = getImportAndPackage(path);
            String Pkg = packageMap.get(path);

            boolean modified = removeExtension(ctModel, path, launcher);
            if (path.contains("TestObjectNode.java") && !path.contains("_P_")) {
                System.out.println("[DEBUG] TestObjectNode - removeExtension returned: " + modified);
            }

            if (modified) {
                for (String extender : Config.EXTENDED_TESTS) {
                    String tmpName = extender.substring(extender.lastIndexOf('.') + 1);
                    if (!path.contains(tmpName)) {
                        continue;
                    }

                    overwriteOriginalFile(ctModel, path, launcher);
                    packageAndImports = getImportAndPackage(path);

                    CtClass<?> target = ctModel.getElements(new TypeFilter<>(CtClass.class)).stream()
                            .filter(c -> {
                                if (c.getPosition() == null || c.getPosition().getFile() == null)
                                    return false;
                                return c.getPosition().getFile().getAbsolutePath().equals(path);
                            })
                            .findFirst()
                            .orElse(null);

                    if (target == null) {
                        break;
                    }

                    File sourceFile = target.getPosition().getFile();
                    String javaFilePath = sourceFile.getAbsolutePath();

                    String classString;
                    try {
                        classString = new String(Files.readAllBytes(sourceFile.toPath()));
                    } catch (IOException e) {
                        // // e.printStackTrace();
                        break;
                    }
                    String simpleName = sourceFile.getName().replaceFirst("\\.java$", "");
                    Compiler compiler = new Compiler(packageAndImports, packageMap.get(javaFilePath), null);
                    boolean ok = compiler.compileFile(simpleName, classString);
                    if (!ok) {
                        System.err.println("Compilation failed for: " + javaFilePath);
                    }
                    break;
                }
            }
            importMap.put(path, packageAndImports);

            // 모든 테스트 메소드(스켈레톤 제거용)
            List<CtMethod<?>> allTestMethods = getTestCases(ctModel);
            List<CtMethod<?>> selectedBaseTests = null;
            // ★ 여기서 "베이스 테스트로 포함할 메소드"를 선별
            if (LIMIT_TO_PUBLIC_APIS) {
                selectedBaseTests = filterTestMethodsForBaseTest(allTestMethods, path, bugTriggeringTestFilePaths,
                        cutPublicApis);
            } else {
                selectedBaseTests = allTestMethods;
            }

            // ★ Round-robin selection으로 선택된 메서드만 포함 (seqp 모드 + upper limit 적용시)
            if (selectedTestMethodsMap != null) {
                if (selectedTestMethodsMap.containsKey(path)) {
                    List<String> allowedMethodNames = selectedTestMethodsMap.get(path);
                    Set<String> allowedMethodSet = new HashSet<>(allowedMethodNames);
                    List<CtMethod<?>> finalSelection = new ArrayList<>();
                    for (CtMethod<?> method : selectedBaseTests) {
                        if (allowedMethodSet.contains(method.getSimpleName())) {
                            finalSelection.add(method);
                        }
                    }
                    selectedBaseTests = finalSelection;
                    // System.out.println("[MethodFilter] " + path + ": " + finalSelection.size() +
                    // " / " + allTestMethods.size() + " methods selected");
                } else {
                    // Map에 없는 클래스는 선택되지 않은 것이므로 제외
                    selectedBaseTests = new ArrayList<>();
                    // System.out.println("[MethodFilter] " + path + ": 0 / " +
                    // allTestMethods.size() + " methods selected (not in selection)");
                }
            }

            // 스켈레톤은 기존처럼 "모든 테스트 메소드" 제거 유지 (헬퍼만 남김)
            CtClass<?> skeletal = getSkeletalCtClass(allTestMethods, ctModel, packageAndImports, factory);
            skeletalTestClassMap.put(path, skeletal);

            // ★ 선별된 메소드만 baseTestMethodMap 에 등록
            baseTestMethodMap.put(path, selectedBaseTests);
        }
    }

    public static List<Map<String, CtMethod<?>>> generateQueue(Map<String, List<CtMethod<?>>> baseTestMethodMap) {
        int roundCount = 0;
        List<Map<String, CtMethod<?>>> queue = new ArrayList<>();
        for (List<CtMethod<?>> methods : baseTestMethodMap.values()) {
            if (methods.size() > roundCount) {
                roundCount = methods.size();
            }
        }
        for (int i = 0; i < roundCount; i++) {
            for (Map.Entry<String, List<CtMethod<?>>> entry : baseTestMethodMap.entrySet()) {
                String className = entry.getKey();
                List<CtMethod<?>> methods = entry.getValue();

                if (i < methods.size()) {
                    CtMethod<?> method = methods.get(i);

                    // 클래스 이름을 키로, 메서드를 값으로 하는 단일 Map 생성
                    Map<String, CtMethod<?>> singleEntry = new LinkedHashMap<>();
                    singleEntry.put(className, method);

                    queue.add(singleEntry);
                }
            }
        }
        Collections.shuffle(queue);
        return queue;
    }

    private static List<Map<String, CtMethod<?>>> generateQueueForSingleClass(String className,
            List<CtMethod<?>> methods) {
        List<Map<String, CtMethod<?>>> queue = new ArrayList<>();
        for (CtMethod<?> method : methods) {
            Map<String, CtMethod<?>> singleEntry = new LinkedHashMap<>();
            singleEntry.put(className, method);
            queue.add(singleEntry);
        }
        return queue;
    }

    /**
     * ★ DEPRECATED: 더 이상 사용되지 않음
     * Bug Triggering 테스트 우선순위 처리는 parse() 메서드에서 수행됨
     * 시간 제약이 있는 경우에만 필요할 때 사용 가능
     * 
     * 현재는 generateQueue()를 사용하므로 이 메서드는 필요 없음
     */
    @Deprecated
    public static List<Map<String, CtMethod<?>>> generatePriorityQueue(
            Map<String, List<CtMethod<?>>> baseTestMethodMap) {

        List<Map<String, CtMethod<?>>> queue = new ArrayList<>();
        LinkedHashMap<String, List<CtMethod<?>>> remaining = new LinkedHashMap<>();
        // final int portion = Math.max(1, totalBaseTests / 10);
        int portion = 1;

        // ★ Bug Triggering 테스트는 이미 parse()에서 필터링되어 bugTriggeringTestFilePaths에 저장됨
        // 경로가 정확히 일치하므로 Set 사용 가능
        Set<String> bugTriggeringSet = new HashSet<>(bugTriggeringTestFilePaths);

        System.out.println("\n[PRIORITY_QUEUE] Bug triggering tests: " + bugTriggeringSet.size());
        System.out.println("[PRIORITY_QUEUE] Total base tests: " + baseTestMethodMap.size());

        int bugTriggeringCount = 0;
        for (Map.Entry<String, List<CtMethod<?>>> e : baseTestMethodMap.entrySet()) {
            String path = e.getKey();
            List<CtMethod<?>> methods = e.getValue();

            if (bugTriggeringSet.contains(path)) {
                bugTriggeringCount++;
                System.out.println(
                        "[PRIORITY_QUEUE] Adding bug triggering test: " + path + " (" + methods.size() + " methods)");
                for (int i = 0; i < portion; i++) {
                    queue.addAll(generateQueueForSingleClass(path, methods));
                }
            } else {
                remaining.put(path, methods);
            }
        }

        System.out.println("[PRIORITY_QUEUE] Bug triggering tests in queue: " + bugTriggeringCount);

        List<Map<String, CtMethod<?>>> remainingQueue = generateQueue(remaining);
        Collections.shuffle(remainingQueue);
        queue.addAll(remainingQueue);

        System.out.println("[PRIORITY_QUEUE] Final queue size: " + queue.size());

        return queue;
    }

    /**
     * Check if a class likely extends junit.framework.TestCase based on its direct
     * superclass
     * This is a heuristic approach that avoids expensive recursive traversal
     */
    private static boolean likelyExtendsTestCase(CtClass<?> ctClass) {
        CtTypeReference<?> superRef = ctClass.getSuperclass();
        if (superRef == null) {
            return false;
        }

        String superQName = superRef.getQualifiedName();
        if (superQName == null) {
            return false;
        }

        // 1. Direct TestCase extension
        if ("junit.framework.TestCase".equals(superQName)) {
            return true;
        }

        // 2. Custom TestCase class (naming convention)
        String simpleName = superRef.getSimpleName();
        if (simpleName != null && simpleName.endsWith("TestCase")) {
            return true;
        }

        // 3. Known custom test base classes from Config.EXTENDED_TESTS
        if (Config.EXTENDED_TESTS != null) {
            for (String extendedTest : Config.EXTENDED_TESTS) {
                // Extract simple class name from fully qualified name
                String extendedClassName = extendedTest.contains(".")
                        ? extendedTest.substring(extendedTest.lastIndexOf('.') + 1)
                        : extendedTest;

                if (superQName.endsWith("." + extendedClassName) || superQName.equals(extendedClassName)) {
                    return true;
                }
            }
        }

        // 4. Other known test base classes
        if (superQName.contains("BaseMapTest") ||
                superQName.contains("BaseTest") ||
                superQName.endsWith("TestBase")) {
            return true;
        }

        return false;
    }

    private static boolean removeExtension(CtModel model, String path, Launcher launcher) {
        boolean isJ3 = false;
        List<CtClass<?>> allClasses = model.getElements(new TypeFilter<>(CtClass.class));

        for (CtClass<?> ctClass : allClasses) {
            String className = ctClass.getSimpleName();
            boolean isDebug = className != null && (className.contains("BeanModel") || className.contains("JXPath"));

            if (isDebug) {
                System.out.println("[DEBUG] removeExtension processing: " + className);
                System.out.println("[DEBUG] Path: " + path);
            }

            CtTypeReference<?> superRef = ctClass.getSuperclass();

            if (isDebug) {
                System.out.println("[DEBUG] Superclass: " + (superRef != null ? superRef.getQualifiedName() : "null"));
            }

            // Check BEFORE removing superclass
            boolean likelyExtendsTestCase = likelyExtendsTestCase(ctClass);

            if (superRef != null && ("junit.framework.TestCase".equals(superRef.getQualifiedName()) ||
                    "com.fasterxml.jackson.databind.BaseMapTest".equals(superRef.getQualifiedName()) ||
                    "com.fasterxml.jackson.test.BaseTest".equals(superRef.getQualifiedName()))) {
                // Only remove TestCase superclass, not BaseMapTest/BaseTest since they provide
                // utility methods
                if ("junit.framework.TestCase".equals(superRef.getQualifiedName())) {
                    ctClass.setSuperclass(null);
                }
                isJ3 = true;
            }

            for (CtMethod<?> m : new ArrayList<>(ctClass.getMethods())) {
                if (("suite".equals(m.getSimpleName()) && m.isStatic() && m.getParameters().isEmpty())
                        || "main".equals(m.getSimpleName())) {
                    ctClass.removeMethod(m);
                }
            }
            // Handle String constructors for TestCase-extending classes
            // likelyExtendsTestCase already computed before removing superclass
            boolean isAbstract = ctClass.hasModifier(ModifierKind.ABSTRACT);

            if (isDebug) {
                System.out.println("[DEBUG] Constructor processing for: " + className);
                System.out.println("  Direct superclass: " + (superRef != null ? superRef.getQualifiedName() : "null"));
                System.out.println("  likelyExtendsTestCase: " + likelyExtendsTestCase);
                System.out.println("  isAbstract: " + isAbstract);
                System.out.println("  Number of constructors: " + ctClass.getConstructors().size());
            }

            // First pass: Save body from String constructor for abstract classes
            CtBlock<?> savedBodyForAbstract = null;
            if (isAbstract && likelyExtendsTestCase) {
                for (CtConstructor<?> ctor : ctClass.getConstructors()) {
                    List<CtParameter<?>> params = ctor.getParameters();
                    if (params.size() == 1 &&
                            "java.lang.String".equals(params.get(0).getType().getQualifiedName()) &&
                            ctor.getBody() != null) {
                        savedBodyForAbstract = ctor.getBody().clone();
                        if (isDebug) {
                            System.out.println("[DEBUG] Saved constructor body with "
                                    + savedBodyForAbstract.getStatements().size() + " statements");
                        }
                        break;
                    }
                }
            }

            // Second pass: Remove String constructors
            for (CtConstructor<?> ctor : new ArrayList<>(ctClass.getConstructors())) {
                List<CtParameter<?>> params = ctor.getParameters();

                if (isDebug && params.size() == 1) {
                    System.out.println("[DEBUG] Constructor param: " + params.get(0).getType().getQualifiedName());
                    System.out.println("[DEBUG] Constructor signature: " + ctor.getSignature());
                }

                if (params.size() == 1
                        && "java.lang.String".equals(params.get(0).getType().getQualifiedName())
                        && ctor.getModifiers().contains(ModifierKind.PUBLIC)) {

                    if (likelyExtendsTestCase) {
                        if (isDebug) {
                            System.out.println("[DEBUG] Removing String constructor");
                        }
                        ctClass.removeConstructor((CtConstructor) ctor);
                    }
                }
            }

            // Third pass: Add zero-param constructor if needed
            if (likelyExtendsTestCase) {
                boolean hasZeroParamConstructor = false;
                for (CtConstructor<?> ctor : ctClass.getConstructors()) {
                    if (ctor.getParameters().isEmpty()) {
                        hasZeroParamConstructor = true;
                        break;
                    }
                }

                if (!hasZeroParamConstructor) {
                    CtConstructor<?> defaultCtor = ctClass.getFactory().createConstructor();

                    // For abstract classes, use saved body; for concrete, use empty body
                    if (isAbstract && savedBodyForAbstract != null && !savedBodyForAbstract.getStatements().isEmpty()) {
                        defaultCtor.setBody(savedBodyForAbstract);
                        if (isDebug) {
                            System.out.println("[DEBUG] Added zero-param constructor with saved body (" +
                                    savedBodyForAbstract.getStatements().size() + " statements)");
                        }
                    } else {
                        defaultCtor.setBody(ctClass.getFactory().createBlock());
                        if (isDebug) {
                            System.out.println("[DEBUG] Added empty zero-param constructor");
                        }
                    }

                    defaultCtor.addModifier(ModifierKind.PUBLIC);
                    ctClass.addConstructor((CtConstructor) defaultCtor);
                }
            }
            for (CtAnnotation<?> ann : new ArrayList<>(ctClass.getAnnotations())) {
                ctClass.removeAnnotation(ann);
            }
            for (CtMethod<?> method : new ArrayList<>(ctClass.getMethods())) {
                String methodName = method.getSimpleName();

                boolean isSetUp = "setUp".equals(methodName) && method.getParameters().isEmpty();
                boolean isTearDown = "tearDown".equals(methodName) && method.getParameters().isEmpty();

                if (isSetUp || isTearDown) {
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

                    for (CtAnnotation<?> ann : new ArrayList<>(method.getAnnotations())) {
                        if (ann.getAnnotationType().getQualifiedName().equals(Override.class.getName())) {
                            method.removeAnnotation(ann);
                        }
                    }

                    Set<ModifierKind> modifiers = new HashSet<>(method.getModifiers());
                    if (!modifiers.contains(ModifierKind.PUBLIC)) {
                        modifiers.remove(ModifierKind.PROTECTED);
                        modifiers.remove(ModifierKind.PRIVATE);
                        modifiers.add(ModifierKind.PUBLIC);
                        method.setModifiers(modifiers);
                    }

                    boolean alreadyHasJunit4Annotation = method.getAnnotations().stream()
                            .map(a -> a.getAnnotationType().getQualifiedName())
                            .anyMatch(
                                    name -> name.equals(Before.class.getName()) || name.equals(After.class.getName()));

                    if (!alreadyHasJunit4Annotation) {
                        if (isSetUp) {
                            CtAnnotation<?> beforeAnn = launcher.getFactory().Core().createAnnotation();
                            beforeAnn.setAnnotationType(launcher.getFactory().Type().createReference(Before.class));
                            method.addAnnotation(beforeAnn);
                        } else if (isTearDown) {
                            CtAnnotation<?> afterAnn = launcher.getFactory().Core().createAnnotation();
                            afterAnn.setAnnotationType(launcher.getFactory().Type().createReference(After.class));
                            method.addAnnotation(afterAnn);
                        }
                    }
                }

                for (CtAnnotation<?> ann : new ArrayList<>(method.getAnnotations())) {
                    String annType = ann.getAnnotationType().getQualifiedName();
                    if (!annType.equals(Before.class.getName()) &&
                            !annType.equals(After.class.getName()) &&
                            !annType.equals(Test.class.getName())) {
                        method.removeAnnotation(ann);
                    }
                }
            }

            for (CtMethod<?> method : new ArrayList<>(ctClass.getMethods())) {
                String methodName = method.getSimpleName();
                if (methodName.startsWith("test") &&
                        method.getParameters().isEmpty() &&
                        method.hasModifier(ModifierKind.PUBLIC)) {

                    boolean hasTestAnnotation = method.getAnnotations().stream()
                            .anyMatch(a -> a.getAnnotationType().getQualifiedName().equals(Test.class.getName()));

                    if (!hasTestAnnotation) {
                        CtAnnotation<?> testAnn = launcher.getFactory().Core().createAnnotation();
                        testAnn.setAnnotationType(launcher.getFactory().Type().createReference(Test.class));
                        method.addAnnotation(testAnn);
                    }
                }
            }

            // Convert JUnit3 assertion method calls to JUnit4 style - with Java 8
            // compatibility
            List<CtInvocation<?>> invocations = ctClass.getElements(new TypeFilter<>(CtInvocation.class));
            for (CtInvocation<?> invocation : new ArrayList<>(invocations)) {
                if (invocation.getExecutable() != null &&
                        invocation.getExecutable().getDeclaringType() != null &&
                        "junit.framework.TestCase"
                                .equals(invocation.getExecutable().getDeclaringType().getQualifiedName())) {

                    String methodName = invocation.getExecutable().getSimpleName();
                    if (methodName.startsWith("assert") || "fail".equals(methodName)) {
                        // Remove the target to make it a static method call
                        invocation.setTarget(null);

                        // Convert JUnit3 assertion method calls to JUnit4 style
                        // Just remove the target to make it a static method call
                    }
                }
            }

            break;
        }

        // JUnit4 imports will be handled by overwriteOriginalFile method

        return isJ3;
    }

    /**
     * Add missing super() calls to constructors
     * Spoon's pretty printer omits implicit super() calls, but we need them
     * explicit
     * for non-TestCase superclasses that require String parameters
     */
    private static String addMissingSuperCalls(String source, String className) {
        // Debug: check if we're processing the right class

        // Pattern: public ClassName(java.lang.String param) {
        // }
        // Need to match across multiple lines with any whitespace/newlines
        String pattern = "(public\\s+" + Pattern.quote(className)
                + "\\s*\\(\\s*java\\.lang\\.String\\s+(\\w+)\\s*\\)\\s*\\{)\\s*(\\})";

        if (className.contains("BeanModelTestCase")) {
            java.util.regex.Pattern p = java.util.regex.Pattern.compile(pattern, java.util.regex.Pattern.DOTALL);
            java.util.regex.Matcher m = p.matcher(source);
            System.out.println("[DEBUG] Pattern matches: " + m.find());
            m.reset();
        }

        String replacement = "$1\n        super($2);\n    $3";
        source = source.replaceAll(pattern, replacement);

        return source;
    }

    /**
     * Replace assertion method calls with fully qualified names to avoid conflicts
     * with overloaded methods in parent classes like
     * BaseMapTest.assertEquals(int[], int[])
     */
    private static String replaceAssertionsWithFQN(String source) {
        // List of common JUnit assertion methods
        String[] assertMethods = {
                "assertEquals", "assertNotEquals", "assertTrue", "assertFalse",
                "assertNull", "assertNotNull", "assertSame", "assertNotSame",
                "assertArrayEquals", "assertThat", "fail"
        };

        for (String method : assertMethods) {
            // Replace method calls that are not already qualified
            // Match: methodName( but not org.junit.Assert.methodName(
            source = source.replaceAll(
                    "(?<!org\\.junit\\.Assert\\.)\\b" + method + "\\s*\\(",
                    "org.junit.Assert." + method + "(");
        }

        return source;
    }

    private static void overwriteOriginalFile(CtModel model, String path, Launcher launcher) {
        for (CtClass<?> ctClass : model.getElements(new TypeFilter<>(CtClass.class))) {
            if (ctClass.getPosition() == null || ctClass.getPosition().getFile() == null) {
                continue;
            }
            File original = ctClass.getPosition().getFile();
            if (!original.getAbsolutePath().equals(path)) {
                continue;
            }

            if (path.contains("BeanModelTestCase")) {
                System.out.println("[DEBUG] overwriteOriginalFile for: " + ctClass.getSimpleName());
                System.out
                        .println("[DEBUG] Number of constructors before printing: " + ctClass.getConstructors().size());
                for (CtConstructor<?> ctor : ctClass.getConstructors()) {
                    System.out.println("  Constructor: " + ctor.getSignature());
                    if (ctor.getBody() != null) {
                        System.out.println("  Body statements: " + ctor.getBody().getStatements().size());
                    }
                }
            }

            DefaultJavaPrettyPrinter printer = new DefaultJavaPrettyPrinter(launcher.getEnvironment());
            String finalSrc = printer.printTypes(ctClass);

            if (path.contains("BeanModelTestCase")) {
                System.out.println("[DEBUG] Pretty printed source (constructor part):");
                String[] lines = finalSrc.split("\n");
                boolean inConstructor = false;
                for (String line : lines) {
                    if (line.contains("BeanModelTestCase(")) {
                        inConstructor = true;
                    }
                    if (inConstructor) {
                        System.out.println("  " + line);
                        if (line.trim().equals("}") && !line.contains("{")) {
                            break;
                        }
                    }
                }
            }

            // Fix constructors that need super() calls but Spoon omitted them
            CtTypeReference<?> superRef = ctClass.getSuperclass();
            boolean needsSuperCall = superRef != null &&
                    !"junit.framework.TestCase".equals(superRef.getQualifiedName()) &&
                    (superRef.getQualifiedName().contains("TestCase") ||
                            superRef.getQualifiedName().contains("TestBase"));

            if (needsSuperCall) {
                // Find String parameter constructors with empty bodies and add super(param)
                // call
                finalSrc = addMissingSuperCalls(finalSrc, ctClass.getSimpleName());
            }

            // Special handling for NodeTestBase - it needs static imports despite extending
            // BaseMapTest
            // because it's an abstract helper class that uses assertion methods in
            // protected helper methods
            boolean isNodeTestBase = ctClass.getSimpleName() != null &&
                    ctClass.getSimpleName().equals("NodeTestBase");

            // Add JUnit4 imports only if the class doesn't extend a test base class
            // Classes that extend test base classes (like BaseMapTest) inherit assertion
            // methods
            boolean extendsTestBase = ctClass.getSuperclass() != null &&
                    ctClass.getSuperclass().getQualifiedName() != null &&
                    (ctClass.getSuperclass().getQualifiedName().contains("BaseMapTest") ||
                            ctClass.getSuperclass().getQualifiedName().contains("TestCase") ||
                            ctClass.getSuperclass().getQualifiedName().contains("TestBase"));

            if (isNodeTestBase) {
                // NodeTestBase needs special handling: replace assertion methods with FQN to
                // avoid conflicts
                // with BaseMapTest's assertEquals(int[], int[]) overload
                finalSrc = replaceAssertionsWithFQN(finalSrc);
                // Remove static import since we're using FQN
                finalSrc = finalSrc.replaceAll("import static org\\.junit\\.Assert\\.\\*;\\s*", "");
            } else if (!extendsTestBase && !finalSrc.contains("import static org.junit.Assert.*;")) {
                finalSrc = finalSrc.replaceFirst("(package [^;]+;\\s*)",
                        "$1\n\nimport static org.junit.Assert.*;\nimport org.junit.Test;\n");
            } else if (extendsTestBase && !finalSrc.contains("import org.junit.Test;")) {
                // If it extends a test base, only add @Test import if missing
                finalSrc = finalSrc.replaceFirst("(package [^;]+;\\s*)", "$1\n\nimport org.junit.Test;\n");
            }

            try {
                Files.write(Paths.get(path), finalSrc.getBytes(StandardCharsets.UTF_8));
            } catch (IOException e) {
                // // e.printStackTrace();
            }
            break;
        }
    }

    private static CtClass<?> getSkeletalCtClass(
            List<CtMethod<?>> testMethods,
            CtModel ctModel,
            String packageAndImports,
            Factory factory) {
        if (testMethods == null || testMethods.isEmpty()) {
            return null;
        }

        // Find the actual concrete class that owns these test methods
        // Not the declaring type (which might be an abstract parent)
        CtMethod<?> firstMethod = testMethods.get(0);
        CtType<?> declaringType = firstMethod.getDeclaringType();

        String testClassQName;

        // Check if declaring type is abstract
        if (declaringType instanceof CtClass && ((CtClass<?>) declaringType).hasModifier(ModifierKind.ABSTRACT)) {
            // Find concrete subclass in model that has this method
            String concreteClassName = null;
            List<CtClass<?>> allClasses = ctModel.getElements(new TypeFilter<>(CtClass.class));
            for (CtClass<?> clazz : allClasses) {
                if (clazz.hasModifier(ModifierKind.ABSTRACT)) {
                    continue; // Skip abstract classes
                }

                // Check if this class has the test method (inherited or direct)
                for (CtMethod<?> method : clazz.getMethods()) {
                    if (method.getSignature().equals(firstMethod.getSignature())) {
                        concreteClassName = clazz.getQualifiedName();
                        break;
                    }
                }

                if (concreteClassName != null) {
                    break;
                }
            }

            // Use concrete class if found, otherwise fall back to declaring type
            testClassQName = (concreteClassName != null) ? concreteClassName : declaringType.getQualifiedName();
        } else {
            // Not abstract, use declaring type directly
            testClassQName = declaringType.getQualifiedName();
        }

        final String finalTestClassQName = testClassQName;
        CtClass<?> originalClass = ctModel.getAllTypes().stream()
                .filter(t -> t instanceof CtClass<?>)
                .map(t -> (CtClass<?>) t)
                .filter(c -> c.getQualifiedName().equals(finalTestClassQName))
                .findFirst()
                .orElseThrow(() -> new IllegalArgumentException(
                        "Unable to find TestClass: " + finalTestClassQName));

        CtClass<?> skeletalClass = originalClass.clone();

        // ★ 스켈레톤 생성 전에 모든 @Test 어노테이션의 중복 제거
        removeTestAnnotationDuplicates(skeletalClass);

        Set<String> testSignatures = testMethods.stream()
                .map(CtMethod::getSignature)
                .collect(Collectors.toSet());
        for (CtMethod<?> m : new ArrayList<>(skeletalClass.getMethods())) {
            if (testSignatures.contains(m.getSignature())) {
                skeletalClass.removeMethod(m);
            }
        }

        // Remove JUnit 3 methods (suite(), main())
        for (CtMethod<?> m : new ArrayList<>(skeletalClass.getMethods())) {
            String methodName = m.getSimpleName();
            // Remove suite() method
            if (methodName.equals("suite") && m.getParameters().isEmpty()) {
                skeletalClass.removeMethod(m);
            }
            // Remove main(String[]) method
            if (methodName.equals("main") && m.getParameters().size() == 1) {
                CtParameter<?> param = m.getParameters().get(0);
                if (param.getType().getQualifiedName().equals("java.lang.String[]")) {
                    skeletalClass.removeMethod(m);
                }
            }
        }

        // Convert JUnit 3 style constructors to JUnit 4 style
        // Both abstract and concrete classes need zero-param constructors for JUnit4
        boolean isAbstract = skeletalClass.hasModifier(ModifierKind.ABSTRACT);
        boolean likelyExtendsTestCase = likelyExtendsTestCase(skeletalClass);

        if (likelyExtendsTestCase) {
            // Any class extending TestCase (abstract or concrete) needs zero-param
            // constructor
            boolean hasDefaultConstructor = false;
            for (CtConstructor<?> ctor : new ArrayList<>(skeletalClass.getConstructors())) {
                List<CtParameter<?>> params = ctor.getParameters();

                // Check if already has a default constructor
                if (params.isEmpty()) {
                    hasDefaultConstructor = true;
                }

                // Remove String parameter constructor (JUnit3 style)
                if (params.size() == 1 &&
                        "java.lang.String".equals(params.get(0).getType().getQualifiedName()) &&
                        ctor.getModifiers().contains(ModifierKind.PUBLIC)) {
                    skeletalClass.removeConstructor((CtConstructor) ctor);
                }
            }

            // Add default constructor if needed (no super() call needed - implicit)
            if (!hasDefaultConstructor && skeletalClass.getConstructors().isEmpty()) {
                CtConstructor defaultCtor = factory.createConstructor();
                defaultCtor.setBody(factory.createBlock());
                defaultCtor.addModifier(ModifierKind.PUBLIC);
                skeletalClass.addConstructor(defaultCtor);
            }
        }

        normalizeThisAccessInSkeletalClass(skeletalClass);
        return skeletalClass;
    }

    /**
     * ★ @Test 어노테이션 중복 제거
     * 같은 메서드에 @Test가 여러 개 있으면 하나만 남기고 제거
     * 원본 클래스(removeExtension)에서 JUnit4로 변환할 때
     * 중복 @Test가 생길 수 있으므로 스켈레톤 생성 전에 미리 정리
     */
    private static void removeTestAnnotationDuplicates(CtClass<?> skeletalClass) {
        for (CtMethod<?> method : skeletalClass.getMethods()) {
            List<CtAnnotation<?>> annotations = new ArrayList<>(method.getAnnotations());
            List<CtAnnotation<?>> testAnnotations = new ArrayList<>();

            // @Test 어노테이션들만 수집
            for (CtAnnotation<?> ann : annotations) {
                if (ann.getAnnotationType().getQualifiedName().equals(Test.class.getName())) {
                    testAnnotations.add(ann);
                }
            }

            // @Test가 2개 이상이면 첫 번째를 제외한 나머지 제거
            if (testAnnotations.size() > 1) {
                for (int i = 1; i < testAnnotations.size(); i++) {
                    method.removeAnnotation(testAnnotations.get(i));
                }
                // System.out.println("[DEBUG] Removed " + (testAnnotations.size() - 1) + "
                // duplicate @Test annotations from method: " + method.getSimpleName());
            }
        }
    }

    /**
     * Normalizes CtThisAccess references in the skeletal class
     */
    private static void normalizeThisAccessInSkeletalClass(CtClass<?> skeletalClass) {
        if (skeletalClass == null)
            return;

        skeletalClass.accept(new CtScanner() {

            @Override
            public <T> void visitCtThisAccess(spoon.reflect.code.CtThisAccess<T> thisAccess) {
                // 먼저 우리 로직 수행
                CtTypeReference<T> targetType = thisAccess.getType();
                if (targetType != null) {
                    String qn = targetType.getQualifiedName();
                    String sn = targetType.getSimpleName();
                    if (qn != null && sn != null && !qn.equals(sn)) {
                        Factory factory = thisAccess.getFactory();
                        CtTypeReference<T> simpleTypeRef = factory.createTypeReference();
                        simpleTypeRef.setSimpleName(sn);
                        thisAccess.setType(simpleTypeRef);
                    }
                }
                // 그 다음 부모 로직
                super.visitCtThisAccess(thisAccess);
            }

            @Override
            public <T> void visitCtFieldRead(spoon.reflect.code.CtFieldRead<T> fieldRead) {
                // target이 qualified this 면 단순 this로 바꾸기
                CtExpression<?> target = fieldRead.getTarget();
                if (target instanceof spoon.reflect.code.CtThisAccess) {
                    normalizeFieldAccessTarget(fieldRead);
                }
                super.visitCtFieldRead(fieldRead);
            }

            @Override
            public <T> void visitCtFieldWrite(spoon.reflect.code.CtFieldWrite<T> fieldWrite) {
                CtExpression<?> target = fieldWrite.getTarget();
                if (target instanceof spoon.reflect.code.CtThisAccess) {
                    normalizeFieldAccessTarget(fieldWrite);
                }
                super.visitCtFieldWrite(fieldWrite);
            }

            @Override
            public <T> void visitCtInvocation(CtInvocation<T> invocation) {
                CtExpression<?> target = invocation.getTarget();
                if (target instanceof spoon.reflect.code.CtThisAccess) {
                    normalizeInvocationTarget(invocation);
                }
                super.visitCtInvocation(invocation);
            }

            private <T> void normalizeFieldAccessTarget(spoon.reflect.code.CtFieldAccess<T> fieldAccess) {
                CtExpression<?> target = fieldAccess.getTarget();
                if (!(target instanceof spoon.reflect.code.CtThisAccess))
                    return;

                spoon.reflect.code.CtThisAccess<?> thisAccess = (spoon.reflect.code.CtThisAccess<?>) target;
                CtTypeReference<?> targetType = thisAccess.getType();
                if (targetType == null)
                    return;

                String qn = targetType.getQualifiedName();
                String sn = targetType.getSimpleName();
                if (qn != null && sn != null && !qn.equals(sn)) {
                    Factory factory = fieldAccess.getFactory();
                    spoon.reflect.code.CtThisAccess<?> simpleThisAccess = factory.createThisAccess();
                    CtTypeReference<?> simpleTypeRef = factory.createTypeReference();
                    simpleTypeRef.setSimpleName(sn);
                    // noinspection unchecked
                    simpleThisAccess.setType((CtTypeReference) simpleTypeRef);
                    fieldAccess.setTarget(simpleThisAccess);
                }
            }

            private <T> void normalizeInvocationTarget(CtInvocation<T> invocation) {
                CtExpression<?> target = invocation.getTarget();
                if (!(target instanceof spoon.reflect.code.CtThisAccess))
                    return;

                spoon.reflect.code.CtThisAccess<?> thisAccess = (spoon.reflect.code.CtThisAccess<?>) target;
                CtTypeReference<?> targetType = thisAccess.getType();
                if (targetType == null)
                    return;

                String qn = targetType.getQualifiedName();
                String sn = targetType.getSimpleName();
                if (qn != null && sn != null && !qn.equals(sn)) {
                    Factory factory = invocation.getFactory();
                    spoon.reflect.code.CtThisAccess<?> simpleThisAccess = factory.createThisAccess();
                    CtTypeReference<?> simpleTypeRef = factory.createTypeReference();
                    simpleTypeRef.setSimpleName(sn);
                    // noinspection unchecked
                    simpleThisAccess.setType((CtTypeReference) simpleTypeRef);
                    invocation.setTarget(simpleThisAccess);
                }
            }

            @Override
            public <T> void visitCtTypeReference(CtTypeReference<T> typeRef) {
                if (typeRef != null) {
                    String qn = typeRef.getQualifiedName();
                    String sn = typeRef.getSimpleName();
                    // nested type 처리: qualifiedName에 '$'가 있고, 선언 타입이 있을 때만 단순화
                    if (qn != null && sn != null &&
                            !qn.equals(sn) &&
                            qn.contains("$") &&
                            typeRef.getDeclaringType() != null) {

                        typeRef.setSimpleName(sn);
                        typeRef.setPackage(null);
                    }
                }
                super.visitCtTypeReference(typeRef);
            }

            @Override
            public void scan(CtElement element) {
                // ★★ NPE 방지: Spoon은 종종 scan(null)을 호출합니다 ★★
                if (element == null)
                    return;

                // 선택적 디버그(문자열화 과정에서 SpoonException이 날 수 있으니 try-catch)
                if (DEBUG) {
                    try {
                        String s = element.toString();
                        if (s != null && s.contains(".this.")) {
                            // System.out.println("[DEBUG] Found .this.: " +
                            // element.getClass().getSimpleName());
                        }
                    } catch (spoon.SpoonException ignored) {
                    }
                }
                super.scan(element);
            }
        });
    }

    private static boolean isPrimitiveOrString(CtTypeReference<?> type) {
        if (type == null) {
            return false;
        }
        if (type.isPrimitive()) {
            return true;
        }
        return "java.lang.String".equals(type.getQualifiedName());
    }

    private static List<CtMethod<?>> getTestCases(CtModel ctModel) {
        List<CtMethod<?>> testcases = new ArrayList<>();
        List<CtType<?>> types = ctModel.getElements(new TypeFilter<>(CtType.class));
        int counter = 0;
        for (CtType<?> type : types) {
            if (!(type instanceof CtClass) || type.getDeclaringType() != null)
                continue;

            for (CtMethod<?> method : type.getMethods()) {
                counter++;

                if (isTestMethod(method)) {
                    removeTryCatchAndAssertion(method);
                    trimToLastMeaningfulStatement(method);
                    testcases.add((CtMethod) method);
                }
            }
        }
        return testcases;
    }

    private static void trimToLastMeaningfulStatement(CtMethod<?> method) {
        if (method == null || method.getBody() == null) {
            return;
        }

        List<CtStatement> statements = method.getBody().getStatements();
        if (statements.isEmpty()) {
            return;
        }

        int lastMeaningfulIndex = -1;
        for (int i = statements.size() - 1; i >= 0; i--) {
            CtStatement stmt = statements.get(i);
            if (isMeaningfulStatement(stmt)) {
                lastMeaningfulIndex = i;
                break;
            }
        }

        if (lastMeaningfulIndex >= 0 && lastMeaningfulIndex < statements.size() - 1) {
            int originalSize = statements.size();
            statements.subList(lastMeaningfulIndex + 1, statements.size()).clear();

            if (DEBUG) {
                System.out.println("[TRIM] Method " + method.getSimpleName() +
                        ": removed " + (originalSize - statements.size()) +
                        " trailing statements, kept " + statements.size() + " statements");
            }
        }
    }

    private static boolean isMeaningfulStatement(CtStatement stmt) {
        if (stmt == null) {
            return false;
        }

        List<CtInvocation<?>> invocations = stmt.getElements(new TypeFilter<>(CtInvocation.class));
        List<CtConstructorCall<?>> constructorCalls = stmt.getElements(new TypeFilter<>(CtConstructorCall.class));

        if (!invocations.isEmpty() || !constructorCalls.isEmpty()) {
            return true;
        }

        if (stmt instanceof CtLocalVariable) {
            CtLocalVariable<?> localVar = (CtLocalVariable<?>) stmt;
            CtExpression<?> defaultExpr = localVar.getDefaultExpression();
            if (defaultExpr != null && !(defaultExpr instanceof CtLiteral)
                    && !(defaultExpr instanceof CtVariableRead)) {
                return true;
            }
        }

        if (stmt instanceof CtAssignment) {
            CtAssignment<?, ?> assignment = (CtAssignment<?, ?>) stmt;
            CtExpression<?> rhs = assignment.getAssignment();

            if (rhs != null && !(rhs instanceof CtLiteral) && !(rhs instanceof CtVariableRead)) {
                return true;
            }

            String assignmentStr = assignment.toString().toLowerCase();
            if (assignmentStr.contains("success") &&
                    (assignmentStr.contains("false") || assignmentStr.contains("true"))) {
                return false;
            }
        }

        if (stmt instanceof CtIf || stmt instanceof CtLoop ||
                stmt instanceof CtSwitch || stmt instanceof CtTry) {
            return true;
        }

        if (stmt instanceof CtReturn) {
            return true;
        }

        if (stmt instanceof CtThrow) {
            return true;
        }

        return false;
    }

    private static void removeTryCatchAndAssertion(CtMethod<?> testcase) {
        if (testcase == null || testcase.getBody() == null) {
            return;
        }

        List<CtAnnotation<?>> annotations = testcase.getElements(new TypeFilter<>(CtAnnotation.class));
        for (int i = annotations.size() - 1; i >= 0; i--) {
            CtAnnotation<?> annotation = annotations.get(i);
            if (annotation.isParentInitialized()
                    && Override.class.getName().equals(annotation.getAnnotationType().getQualifiedName())) {
                annotation.delete();
            }
        }

        List<CtStatement> newStatements = processStatementList(testcase.getBody().getStatements());
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

    private static void removeTryCatchAndAssertionOnModel(CtModel ctModel) {
        List<CtMethod<?>> methods = ctModel.getElements(new TypeFilter<>(CtMethod.class));
        for (CtMethod method : methods) {
            removeTryCatchAndAssertion(method);
            removeEmptyBlocks(method);
        }

    }

    private static void removeEmptyBlocks(CtMethod<?> method) {
        List<CtBlock<?>> blocks = method.getElements(new TypeFilter<>(CtBlock.class));
        for (CtBlock<?> block : new ArrayList<>(blocks)) {
            if (block.getStatements().isEmpty()) {
                block.delete();
            }
        }
    }

    private static CtStatement processStatementForControl(CtStatement statement, CtElement parent) {
        if (statement instanceof CtBlock) {
            CtBlock<?> block = (CtBlock<?>) statement;
            List<CtStatement> newStmts = new ArrayList<>();
            for (CtStatement stmt : block.getStatements()) {
                newStmts.addAll(processStatement(stmt));
            }
            CtBlock<?> newBlock = statement.getFactory().createBlock();
            if (!newStmts.isEmpty()) {
                newBlock.setStatements(newStmts);
            }
            newBlock.setParent(parent);
            return newBlock;

        } else if (statement instanceof CtFor) {
            CtFor forLoop = (CtFor) statement;
            CtStatement body = forLoop.getBody();
            if (body != null) {
                CtStatement processedBody = processStatementForControl(body, forLoop);
                forLoop.setBody(processedBody);
            } else {
                CtBlock<?> emptyBlock = forLoop.getFactory().createBlock();
                emptyBlock.setParent(forLoop);
                forLoop.setBody(emptyBlock);
            }
            forLoop.setParent(parent);
            return forLoop;

        } else if (statement instanceof CtForEach) {
            CtForEach forEach = (CtForEach) statement;

            CtStatement body = forEach.getBody();
            if (body != null) {
                CtStatement processedBody = processStatementForControl(body, forEach);
                forEach.setBody(processedBody);
            } else {
                CtBlock<?> emptyBlock = forEach.getFactory().createBlock();
                emptyBlock.setParent(forEach);
                forEach.setBody(emptyBlock);
            }
            forEach.setParent(parent);
            return forEach;

        } else if (statement instanceof CtWhile) {
            CtWhile whileLoop = (CtWhile) statement;
            CtStatement body = whileLoop.getBody();
            if (body != null) {
                CtStatement processedBody = processStatementForControl(body, whileLoop);
                whileLoop.setBody(processedBody);
            } else {
                CtBlock<?> emptyBlock = whileLoop.getFactory().createBlock();
                emptyBlock.setParent(whileLoop);
                whileLoop.setBody(emptyBlock);
            }
            whileLoop.setParent(parent);
            return whileLoop;

        } else if (statement instanceof CtIf) {
            CtIf ctIf = (CtIf) statement;
            CtStatement thenStmt = ctIf.getThenStatement();
            if (thenStmt != null) {
                ctIf.setThenStatement(processStatementForControl(thenStmt, ctIf));
            }
            CtStatement elseStmt = ctIf.getElseStatement();
            if (elseStmt != null) {
                ctIf.setElseStatement(processStatementForControl(elseStmt, ctIf));
            }
            ctIf.setParent(parent);
            return ctIf;

        } else {
            List<CtStatement> processed = processStatement(statement);
            if (processed.size() == 1) {
                processed.get(0).setParent(parent);
                return processed.get(0);
            } else if (processed.isEmpty()) {
                CtBlock<?> emptyBlock = statement.getFactory().createBlock();
                emptyBlock.setParent(parent);
                return emptyBlock;
            } else {
                CtBlock<?> newBlock = statement.getFactory().createBlock();
                newBlock.setStatements(processed);
                newBlock.setParent(parent);
                return newBlock;
            }
        }
    }

    private static List<CtStatement> processStatement(CtStatement statement) {
        List<CtStatement> result = new ArrayList<>();

        if (isAssertion(statement)) {
            if (statement instanceof CtInvocation) {
                CtInvocation<?> assertionInvocation = (CtInvocation<?>) statement;
                for (CtExpression<?> arg : assertionInvocation.getArguments()) {
                    if (arg instanceof CtInvocation && !isAssertion((CtInvocation<?>) arg)) {
                        CtInvocation<?> innerInvocation = (CtInvocation<?>) arg;
                        result.add(innerInvocation.clone());
                    }
                }
            }
            return result;

        } else if (statement instanceof CtFor) {
            CtFor forLoop = (CtFor) statement;
            CtStatement body = forLoop.getBody();
            if (body != null) {
                CtStatement processedBody = processStatementForControl(body, forLoop);
                forLoop.setBody(processedBody);
            } else {
                CtBlock<?> emptyBlock = forLoop.getFactory().createBlock();
                emptyBlock.setParent(forLoop);
                forLoop.setBody(emptyBlock);
            }
            result.add(forLoop.clone());
            return result;

        } else if (statement instanceof CtForEach) {
            CtForEach forEach = (CtForEach) statement;
            CtStatement body = forEach.getBody();
            if (body != null) {
                CtStatement processedBody = processStatementForControl(body, forEach);
                forEach.setBody(processedBody);
            } else {
                CtBlock<?> emptyBlock = forEach.getFactory().createBlock();
                emptyBlock.setParent(forEach);
                forEach.setBody(emptyBlock);
            }
            result.add(forEach.clone());
            return result;

        } else if (statement instanceof CtWhile) {
            CtWhile whileLoop = (CtWhile) statement;
            CtStatement body = whileLoop.getBody();
            if (body != null) {
                CtStatement processedBody = processStatementForControl(body, whileLoop);
                whileLoop.setBody(processedBody);
            } else {
                CtBlock<?> emptyBlock = whileLoop.getFactory().createBlock();
                emptyBlock.setParent(whileLoop);
                whileLoop.setBody(emptyBlock);
            }
            result.add(whileLoop.clone());
            return result;

        } else if (statement instanceof CtIf) {
            CtIf ctIf = (CtIf) statement;
            CtStatement thenStmt = ctIf.getThenStatement();
            if (thenStmt != null) {
                CtStatement processedThen = processStatementForControl(thenStmt, ctIf);
                ctIf.setThenStatement(processedThen);
            }
            CtStatement elseStmt = ctIf.getElseStatement();
            if (elseStmt != null) {
                CtStatement processedElse = processStatementForControl(elseStmt, ctIf);
                ctIf.setElseStatement(processedElse);
            }
            result.add(ctIf.clone());
            return result;
        } else {
            result.add(statement.clone());
            return result;
        }
    }

    private static boolean isAssertion(CtStatement stmt) {
        if (stmt instanceof CtAssert<?>) {
            return true;
        }

        if (stmt instanceof CtExpression) {
            CtExpression<?> expr = ((CtExpression) stmt);
            if (expr instanceof CtInvocation<?>) {
                CtInvocation<?> invocation = (CtInvocation<?>) expr;
                return isAssertionInvocation(invocation);
            }
        }

        if (stmt instanceof CtInvocation<?>) {
            return isAssertionInvocation((CtInvocation<?>) stmt);
        }

        return false;
    }

    private static boolean isAssertionInvocation(CtInvocation<?> invocation) {
        CtExecutableReference<?> executable = invocation.getExecutable();
        if (executable == null) {
            return false;
        }

        String methodName = executable.getSimpleName();
        if ("fail".equalsIgnoreCase(methodName)) {
            return true;
        }

        CtTypeReference<?> declaringTypeRef = executable.getDeclaringType();
        if (declaringTypeRef == null) {
            return false;
        }

        String qualifiedName = declaringTypeRef.getQualifiedName();

        if ("junit.framework.TestCase".equals(qualifiedName)
                && (methodName.startsWith("assert") || methodName.equalsIgnoreCase("fail"))) {
            return true;
        }

        if (("org.junit.Assert".equals(qualifiedName) ||
                "org.junit.jupiter.api.Assertions".equals(qualifiedName))
                && (methodName.startsWith("assert") || methodName.equalsIgnoreCase("fail"))) {
            return true;
        }

        if ("org.testng.Assert".equals(qualifiedName)
                && (methodName.startsWith("assert") || methodName.equalsIgnoreCase("fail"))) {
            return true;
        }

        if (qualifiedName.toLowerCase().contains("assert")
                && (methodName.toLowerCase().startsWith("assert") || methodName.equalsIgnoreCase("fail"))) {
            return true;
        }

        if (invocation.getTarget() != null
                && invocation.getTarget().toString().toLowerCase().contains("assert")) {
            return true;
        }

        return false;
    }

    private static Pair<CtModel, Factory> initModel(String path, Launcher launcher) {

        File file = new File(path);

        launcher.getEnvironment().setNoClasspath(true);
        launcher.getEnvironment().setAutoImports(true);
        launcher.getEnvironment().setCommentEnabled(false);
        launcher.addInputResource(path);
        try {
            CtModel ctModel = launcher.buildModel();
        } catch (Exception e) {
            System.out.println("Error in building model for " + path + ": " + e.getMessage());
            return Pair.of(null, null);
        }

        return Pair.of(launcher.getModel(), launcher.getFactory());
    }

    private static boolean isTestMethod(CtMethod<?> method) {
        boolean j3 = method.getSimpleName().startsWith("test");
        boolean j4 = method.getAnnotations().stream()
                .anyMatch(a -> a.getAnnotationType().getSimpleName().equals("Test"));
        boolean isPublic = method.hasModifier(ModifierKind.PUBLIC);
        boolean noParams = method.getParameters().isEmpty();
        boolean hasBody = method.getBody() != null && !method.getBody().getStatements().isEmpty();

        return isPublic
                && (j3 || j4)
                && noParams
                && hasBody;
    }

    private static void processExpression(CtExpression<?> expr) {
        if (expr == null) {
            return;
        }
        if (expr instanceof CtConditionalImpl) {
            processConditional((CtConditionalImpl<?>) expr);
        } else if (expr instanceof CtBinaryOperatorImpl) {
            processBinaryOperator((CtBinaryOperatorImpl<?>) expr);
        } else if (expr.getType() != null && expr.getType().isPrimitive()) {
            insertPrimitiveTypeAndVal(expr.getType(), expr);
        }

    }

    private static void processConditional(CtConditionalImpl<?> conditional) {

        CtExpression<?> condition = conditional.getCondition();
        processExpression(condition);

        CtExpression<?> thenExpr = conditional.getThenExpression();
        processExpression(thenExpr);

        CtExpression<?> elseExpr = conditional.getElseExpression();
        processExpression(elseExpr);
    }

    private static void processBinaryOperator(CtBinaryOperatorImpl<?> binaryOp) {

        CtExpression<?> leftOperand = binaryOp.getLeftHandOperand();
        processExpression(leftOperand);

        CtExpression<?> rightOperand = binaryOp.getRightHandOperand();
        processExpression(rightOperand);

    }

    // =========================
    // ★ 신규 기능: CUT 공개 API 수집/매칭 + 베이스 테스트 선별
    // =========================

    /**
     * Extract public API method/ctor signatures from CUT files
     * 
     * @param cutFiles List of CUT file paths
     */
    private static Set<String> extractCutPublicApis(List<String> cutFiles) {
        Set<String> publicApiSignatures = new HashSet<>();

        if (cutFiles == null || cutFiles.isEmpty()) {
            return publicApiSignatures;
        }

        // System.out.println("[CUT_API] Analyzing " + cutFiles.size() + " CUT files for
        // public APIs");

        for (String cutFile : cutFiles) {
            try {
                Launcher launcher = new Launcher();
                launcher.getEnvironment().setNoClasspath(true);
                launcher.getEnvironment().setAutoImports(true);
                launcher.getEnvironment().setCommentEnabled(false);
                launcher.addInputResource(cutFile);

                CtModel ctModel = launcher.buildModel();

                List<CtClass<?>> classes = ctModel.getElements(new TypeFilter<>(CtClass.class));
                for (CtClass<?> clazz : classes) {
                    String className = clazz.getQualifiedName();

                    for (CtMethod<?> method : clazz.getMethods()) {
                        if (method.hasModifier(ModifierKind.PUBLIC)) {
                            String signature = buildMethodSignature(className, method);
                            publicApiSignatures.add(signature);
                            // System.out.println("[CUT_API] Found public API: " + signature);
                        }
                    }

                    for (CtConstructor<?> constructor : clazz.getConstructors()) {
                        if (constructor.hasModifier(ModifierKind.PUBLIC)) {
                            String signature = buildConstructorSignature(className, constructor);
                            publicApiSignatures.add(signature);
                            // System.out.println("[CUT_API] Found public constructor: " + signature);
                        }
                    }
                }

            } catch (Exception e) {
                // System.err.println("[CUT_API] Error analyzing CUT file: " + cutFile + " - " +
                // e.getMessage());
            }
        }

        // System.out.println("[CUT_API] Extracted " + publicApiSignatures.size() + "
        // public API signatures");
        return publicApiSignatures;
    }

    private static String buildMethodSignature(String className, CtMethod<?> method) {
        StringBuilder signature = new StringBuilder();
        signature.append(className).append(".").append(method.getSimpleName()).append("(");

        List<CtParameter<?>> parameters = method.getParameters();
        for (int i = 0; i < parameters.size(); i++) {
            if (i > 0) {
                signature.append(",");
            }
            signature.append(parameters.get(i).getType().getQualifiedName());
        }
        signature.append(")");

        return signature.toString();
    }

    private static String buildConstructorSignature(String className, CtConstructor<?> constructor) {
        StringBuilder signature = new StringBuilder();
        signature.append(className).append(".<init>(");

        List<CtParameter<?>> parameters = constructor.getParameters();
        for (int i = 0; i < parameters.size(); i++) {
            if (i > 0) {
                signature.append(",");
            }
            signature.append(parameters.get(i).getType().getQualifiedName());
        }
        signature.append(")");

        return signature.toString();
    }

    /**
     * Does the test method contain a call to any CUT public API?
     */
    private static boolean containsCutPublicApiInvocation(CtMethod<?> testMethod, Set<String> cutPublicApis) {
        if (cutPublicApis == null || cutPublicApis.isEmpty()) {
            return false;
        }

        List<CtInvocation<?>> invocations = testMethod.getElements(new TypeFilter<>(CtInvocation.class));
        List<CtConstructorCall<?>> constructorCalls = testMethod.getElements(new TypeFilter<>(CtConstructorCall.class));

        for (CtInvocation<?> invocation : invocations) {
            try {
                String invocationSignature = buildInvocationSignature(invocation);
                if (!invocationSignature.isEmpty() && cutPublicApis.contains(invocationSignature)) {
                    // System.out.println("[CUT_API_MATCH] Test method " +
                    // testMethod.getSimpleName() +
                    // " contains CUT API call: " + invocationSignature);
                    return true;
                }
            } catch (Exception e) {
                // ignore
            }
        }

        for (CtConstructorCall<?> constructorCall : constructorCalls) {
            try {
                String constructorSignature = buildConstructorCallSignature(constructorCall);
                if (!constructorSignature.isEmpty() && cutPublicApis.contains(constructorSignature)) {
                    // System.out.println("[CUT_API_MATCH] Test method " +
                    // testMethod.getSimpleName() +
                    // " contains CUT constructor call: " + constructorSignature);
                    return true;
                }
            } catch (Exception e) {
                // ignore
            }
        }

        return false;
    }

    private static String buildInvocationSignature(CtInvocation<?> invocation) {
        CtExecutableReference<?> executable = invocation.getExecutable();
        if (executable == null || executable.getDeclaringType() == null) {
            return "";
        }

        StringBuilder signature = new StringBuilder();
        signature.append(executable.getDeclaringType().getQualifiedName())
                .append(".").append(executable.getSimpleName()).append("(");

        List<CtTypeReference<?>> parameterTypes = executable.getParameters();
        for (int i = 0; i < parameterTypes.size(); i++) {
            if (i > 0) {
                signature.append(",");
            }
            signature.append(parameterTypes.get(i).getQualifiedName());
        }
        signature.append(")");

        return signature.toString();
    }

    private static String buildConstructorCallSignature(CtConstructorCall<?> constructorCall) {
        CtExecutableReference<?> executable = constructorCall.getExecutable();
        if (executable == null || executable.getDeclaringType() == null) {
            return "";
        }

        StringBuilder signature = new StringBuilder();
        signature.append(executable.getDeclaringType().getQualifiedName())
                .append(".<init>(");

        List<CtTypeReference<?>> parameterTypes = executable.getParameters();
        for (int i = 0; i < parameterTypes.size(); i++) {
            if (i > 0) {
                signature.append(",");
            }
            signature.append(parameterTypes.get(i).getQualifiedName());
        }
        signature.append(")");

        return signature.toString();
    }

    /**
     * Filter test methods for inclusion in baseTestMethodMap:
     * 1) include ALL tests from bug-triggering files
     * 2) include tests that call any CUT public API
     */
    private static List<CtMethod<?>> filterTestMethodsForBaseTest(List<CtMethod<?>> testMethods,
            String filePath,
            Set<String> bugTriggeringTestFilePaths,
            Set<String> cutPublicApis) {

        List<CtMethod<?>> filteredMethods = new ArrayList<>();
        boolean isBugTriggeringFile = bugTriggeringTestFilePaths != null
                && bugTriggeringTestFilePaths.contains(filePath);

        if (isBugTriggeringFile) {
            filteredMethods.addAll(testMethods);
            // System.out.println("[BASE_TEST_FILTER] Including ALL " + testMethods.size() +
            // " tests from bug triggering file: " + filePath);
        } else {
            for (CtMethod<?> testMethod : testMethods) {
                if (containsCutPublicApiInvocation(testMethod, cutPublicApis)) {
                    filteredMethods.add(testMethod);
                }
            }
            if (!filteredMethods.isEmpty()) {
                // System.out.println("[BASE_TEST_FILTER] Including " + filteredMethods.size() +
                // " CUT API invoking tests from file: " + filePath);
            } else {
                // System.out.println("[BASE_TEST_FILTER] No CUT API invoking tests in file: " +
                // filePath);
            }
        }

        return filteredMethods;
    }

    private static String sanitizeStringForJavaLiteral(String s) {
        if (s == null)
            return null;
        StringBuilder out = new StringBuilder(s.length() + 16);
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            switch (c) {
                case '\n':
                    out.append("\\n");
                    break;
                case '\r':
                    out.append("\\r");
                    break;
                case '\t':
                    out.append("\\t");
                    break;
                case '\"':
                    out.append("\\\"");
                    break;
                case '\\':
                    out.append("\\\\");
                    break;
                default:
                    if (c < 0x20) {
                        out.append(String.format("\\u%04x", (int) c)); // 기타 제어문자
                    } else {
                        out.append(c);
                    }
            }
        }
        return out.toString();
    }

    private static CtLiteral<String> createSafeStringLiteral(Factory factory, String raw) {
        return factory.createLiteral(sanitizeStringForJavaLiteral(raw));
    }
}