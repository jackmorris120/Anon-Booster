package Generater.MUTMutation.Inlining;

import spoon.Launcher;
import spoon.compiler.Environment;
import spoon.reflect.CtModel;
import spoon.reflect.visitor.filter.TypeFilter;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.io.File; // <--- 오류 해결: File 클래스 임포트
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import Generater.MUTMutation.Inlining.MegaClassBuilder;
import Generater.MUTMutation.Inlining.SpoonPacakge;
import utils.Config;
import spoon.reflect.code.*;
import spoon.reflect.declaration.*;
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.io.File;
import spoon.compiler.ModelBuildingException;
import Generater.MUTMutation.ASTParser;

public class TestTransformer {

    private Launcher launcher;
    private Map<String, List<CtType<?>>> fileTypeMap = new HashMap<>();
    private Set<String> targetClassFqns = new HashSet<>();
    private List<String> targetPkg = new ArrayList<>(); // 패키지 이름을 저장할 변수
    private boolean limitedScope = false;

    public void transformAndSave(List<String> sourceFilesToAnalyze) throws Exception {
        long startTime = System.currentTimeMillis();
        System.out.println("");
        System.out.println("=============================================");
        System.out.println("PHASE 1: Building and filtering model...");
        SpoonPacakge spoonPacakge = this.buildModel(sourceFilesToAnalyze);

        if (this.fileTypeMap.isEmpty()) {
            System.out.println("No target files found after filtering. Exiting.");
            return;
        }
        System.out.println("");
        System.out.println("=============================================");
        System.out.println("\nPHASE 2: Running helper inlining transformation...");
        HelperParser parser = new HelperParser(this.fileTypeMap, this.targetClassFqns);
        parser.run();
        Map<String, List<CtMethod<?>>> inLinedTests = parser.getInLinedTests();
        long endTime = System.currentTimeMillis();
        System.out.println("Helper inlining completed in " + (endTime - startTime) + " ms.");
        System.out.println("");
        System.out.println("=============================================");

        System.out.println("\nPHASE 3: Saving transformed files...");
        long saveStartTime = System.currentTimeMillis();
        MegaClassBuilder.run(spoonPacakge, inLinedTests);
        long saveEndTime = System.currentTimeMillis();
        System.out.println("Transformed files saved in " + (saveEndTime - saveStartTime) + " ms.");
        // this.saveResults();
        System.out.println("\n Process finished successfully.");

        System.out.println("=============================================");
        System.out.println("");
    }

    private List<String> filterInPkgFiles(List<String> relevantTestPaths, List<String> btTestList) {
        List<String> ret = new ArrayList<>();
        if (targetPkg == null || targetPkg.isEmpty()) {
            System.err.println("Target package is null or empty. Skipping filtering.");
            return ret;
        }

        for (String path : relevantTestPaths) {
            File file = new File(path);

            try (BufferedReader br = new BufferedReader(new FileReader(file))) {
                String line;
                while ((line = br.readLine()) != null) {
                    line = line.trim();

                    // 패키지 선언문만 탐색
                    if (line.startsWith("package ")) {
                        String pkgLine = line;
                        // 예: package com.example.test;
                        String parsedPkg = pkgLine.substring("package ".length()).trim();

                        // 세미콜론 포함 시 제거
                        if (parsedPkg.endsWith(";")) {
                            parsedPkg = parsedPkg.substring(0, parsedPkg.length() - 1).trim();
                        }

                        // Check if the parsed package matches any target package
                        if (targetPkg.contains(parsedPkg)) {
                            ret.add(path);
                        }
                        break; // 첫 번째 패키지 선언만 보면 되므로 break
                    }
                }
            } catch (IOException e) {
                System.err.println("Error reading file: " + path);
                // e.printStackTrace();
            }
        }

        return ret;
    }

    private List<String> filterTargetPkgs(List<String> CUT_FILES) {
        // 중복된 패키지 이름을 자동으로 제거하기 위해 Set을 사용합니다.
        Set<String> packageNames = new HashSet<>();

        // 제공된 모든 CUT 파일 경로를 순회합니다.
        for (String cutFile : CUT_FILES) {
            // try-with-resources 구문을 사용하여 파일을 안전하게 엽니다.
            // 이 구문은 블록이 끝나면 자동으로 파일을 닫아줍니다.
            try (BufferedReader reader = new BufferedReader(new FileReader(cutFile))) {
                String line;
                // 파일의 각 라인을 한 줄씩 읽어들입니다.
                while ((line = reader.readLine()) != null) {
                    String trimmedLine = line.trim(); // 라인 앞뒤의 공백을 제거합니다.

                    // 라인이 "package "로 시작하는지 확인합니다.
                    if (trimmedLine.startsWith("package ")) {
                        // "package " 키워드와 세미콜론(;) 사이의 문자열을 추출합니다.
                        int startIndex = "package ".length();
                        int endIndex = trimmedLine.indexOf(';');

                        if (endIndex != -1) {
                            String packageName = trimmedLine.substring(startIndex, endIndex).trim();
                            packageNames.add(packageName);
                            // 패키지 선언은 파일 당 하나이므로, 찾으면 더 이상 읽을 필요가 없습니다.
                            break;
                        }
                    }
                }
            } catch (IOException e) {
                // 파일을 읽는 도중 에러가 발생하면 콘솔에 에러 메시지를 출력합니다.
                System.err.println("Error reading file: " + cutFile);
                // e.printStackTrace();
            }
        }

        // 최종적으로 수집된 고유한 패키지 이름들을 List 형태로 변환하여 반환합니다.
        return new ArrayList<>(packageNames);
    }

    private List<String> filterTargetPkg(String joinedTestList) {
        Set<String> pkgSet = new HashSet<>();

        if (joinedTestList == null || joinedTestList.isEmpty()) {
            return null;
        }
        String[] entries = joinedTestList.split(";");

        for (String entry : entries) {
            if (!entry.contains("::"))
                continue;
            String classWithPkg = entry.split("::")[0].trim();
            int lastDot = classWithPkg.lastIndexOf(".");
            if (lastDot > 0) {
                String pkg = classWithPkg.substring(0, lastDot);
                pkgSet.add(pkg);
            }
        }
        if (!pkgSet.isEmpty()) {
            List<String> pkgList = new ArrayList<>(pkgSet);
            return pkgList;
        }

        return null;
    }

    /**
     * Filters test files to include only those that contain bug triggering tests
     * (file-level filtering)
     * 
     * @param relevantTestPaths  All test files to filter
     * @param bugTriggeringTests Bug triggering test string from config
     * @return List of file paths that contain bug triggering tests
     */
    private List<String> filterBugTriggeringTestFiles(List<String> relevantTestPaths, String bugTriggeringTests) {
        List<String> ret = new ArrayList<>();
        if (bugTriggeringTests == null || bugTriggeringTests.trim().isEmpty()) {
            return ret;
        }

        // Use ASTParser.convertClassToPath to get the actual file paths from bug
        // triggering test string
        List<String> bugTriggeringFilePaths = ASTParser.convertClassToPath(bugTriggeringTests);
        Set<String> bugTriggeringFileSet = new HashSet<>(bugTriggeringFilePaths);

        for (String testFilePath : relevantTestPaths) {
            if (bugTriggeringFileSet.contains(testFilePath)) {
                ret.add(testFilePath);
            }
        }

        return ret;
    }

    private SpoonPacakge buildModel(List<String> relevantTestPaths) {
        System.out.println("Total # of relevant test paths: " + relevantTestPaths.size());

        Set<String> bugTriggeringSet = ASTParser.extractPackageNamesFromBugTriggeringTests(Config.BUGTRIGGERRING_TESTS);
        List<String> bugTriggeringList = new ArrayList<>(bugTriggeringSet);
        targetPkg = bugTriggeringList;
        System.out.println("Target packages from BugTriggeringTests: " + targetPkg);

        List<String> sourceFilesToAnalyze = new ArrayList<>();

        // Two-switch filtering logic
        boolean enableFileFiltering = Config.LIMIT_TO_BUG_TRIGGERING_TESTS;
        boolean enablePackageFiltering = Config.LIMIT_TO_BUG_TRIGGERING_PACKAGES && !bugTriggeringList.isEmpty();

        // Apply filtering based on the two-switch logic
        if (enableFileFiltering && enablePackageFiltering) {
            // Most restrictive: Apply both file-level and package-level filtering
            System.out.println("BOTH FILTERS ENABLED: Applying file-level then package-level filtering...");
            List<String> fileFiltered = filterBugTriggeringTestFiles(relevantTestPaths, Config.BUGTRIGGERRING_TESTS);
            sourceFilesToAnalyze = filterInPkgFiles(fileFiltered, bugTriggeringList);
            System.out.println(
                    "File-level filter: " + relevantTestPaths.size() + " -> " + fileFiltered.size() + " files");
            System.out.println(
                    "Package-level filter: " + fileFiltered.size() + " -> " + sourceFilesToAnalyze.size() + " files");

        } else if (enableFileFiltering && !enablePackageFiltering) {
            // File-level filtering only
            System.out.println("FILE-LEVEL FILTERING ONLY: Filtering to bug triggering test files...");
            sourceFilesToAnalyze = filterBugTriggeringTestFiles(relevantTestPaths, Config.BUGTRIGGERRING_TESTS);
            System.out.println("Filtered " + relevantTestPaths.size() + " files down to " + sourceFilesToAnalyze.size()
                    + " bug triggering test files");

        } else if (!enableFileFiltering && enablePackageFiltering) {
            // Package-level filtering only
            System.out.println("PACKAGE-LEVEL FILTERING ONLY: Filtering to bug triggering packages...");
            sourceFilesToAnalyze = filterInPkgFiles(relevantTestPaths, bugTriggeringList);
            System.out.println("Filtered " + relevantTestPaths.size() + " files down to " + sourceFilesToAnalyze.size()
                    + " files in target packages: " + bugTriggeringList);

        } else {
            // No filtering
            sourceFilesToAnalyze = relevantTestPaths;
        }

        System.out.println("Final # of source files to analyze: " + sourceFilesToAnalyze.size());

        // ===================== [자동 필터링 로직 시작] =====================
        System.out.println("\nFiltering out files that cause build errors...");
        List<String> goodFiles = new ArrayList<>();
        String[] classpath = Arrays.stream(Config.CLASS_PATH.split(java.io.File.pathSeparator))
                .filter(path -> path != null && !path.trim().isEmpty()).distinct().toArray(String[]::new);

        for (String fileToTest : sourceFilesToAnalyze) {
            try {
                // 1. 각 파일을 테스트하기 위한 임시 Launcher를 생성합니다.
                Launcher tempLauncher = new Launcher();
                Environment tempEnv = tempLauncher.getEnvironment();
                tempEnv.setComplianceLevel(8);
                tempEnv.setNoClasspath(false);
                tempEnv.setAutoImports(false);
                tempEnv.setIgnoreSyntaxErrors(true); // Use same lenient settings as final build
                tempEnv.setCommentEnabled(false);
                tempEnv.setSourceClasspath(classpath);

                // 2. 단 하나의 파일만 추가하여 모델 빌드를 시도합니다.
                tempLauncher.addInputResource(fileToTest);
                tempLauncher.buildModel();

                // 3. 예외가 발생하지 않으면 '안전한 파일' 목록에 추가합니다.
                goodFiles.add(fileToTest);

            } catch (ModelBuildingException e) {
                String errorMsg = e.getMessage();

                // Check if it's a duplicate annotation error
                if (errorMsg != null && errorMsg.contains("Duplicate annotation")) {
                    try {
                        String cleanedFile = removeDuplicateAnnotations(fileToTest);

                        // Retry with cleaned file
                        Launcher retryLauncher = new Launcher();
                        Environment retryEnv = retryLauncher.getEnvironment();
                        retryEnv.setComplianceLevel(8);
                        retryEnv.setNoClasspath(false);
                        retryEnv.setAutoImports(false);
                        retryEnv.setIgnoreSyntaxErrors(true);
                        retryEnv.setCommentEnabled(false);
                        retryEnv.setSourceClasspath(classpath);

                        retryLauncher.addInputResource(cleanedFile);
                        retryLauncher.buildModel();

                        goodFiles.add(fileToTest);

                        // Clean up temp file
                        new File(cleanedFile).delete();

                    } catch (Exception retryEx) {
                        System.err.println("SKIPPING problematic file: " + fileToTest);
                    }
                } else {
                    // 4. ModelBuildingException이 발생하면 해당 파일은 건너뜁니다.
                    System.err.println("SKIPPING problematic file due to build error: " + fileToTest);
                    e.printStackTrace();
                }
            } catch (Exception e) {
                // 그 외 예외 처리
                System.err.println("SKIPPING problematic file due to unexpected error (" + e.getClass().getSimpleName()
                        + "): " + fileToTest);
            }
        }
        System.out.println("Filtering complete. " + goodFiles.size() + " of " + sourceFilesToAnalyze.size()
                + " files are safe to build.\n");
        // ===================== [자동 필터링 로직 끝] =====================

        // 이제 필터링된 'goodFiles' 목록을 사용하여 최종 모델을 빌드합니다.
        this.launcher = new Launcher();
        Environment env = launcher.getEnvironment();
        env.setComplianceLevel(8);
        env.setNoClasspath(false);
        env.setAutoImports(false);
        env.setIgnoreSyntaxErrors(true); // 최종 빌드에서는 다시 관대하게 설정
        env.setCommentEnabled(false);

        env.setSourceClasspath(classpath);
        // System.out.println("USED CLASSPATHS FOR BUILDING MODEL ");
        // for (String path : classpath) {
        // System.out.println(" - "+path);
        // }

        for (String inp : goodFiles) { // 필터링된 goodFiles를 사용
            if (inp != null && !inp.trim().isEmpty()) {
                launcher.addInputResource(inp);
            }
        }

        // Add EXTENDED_TESTS files (BaseMapTest, BaseTest, etc.) to the model
        if (Config.EXTENDED_TESTS != null && !Config.EXTENDED_TESTS.isEmpty()) {
            System.out.println("Adding " + Config.EXTENDED_TESTS.size() + " EXTENDED_TESTS files to model...");
            for (String extendedFqn : Config.EXTENDED_TESTS) {
                // Convert FQN to file path
                List<String> paths = ASTParser.convertClassToPath(extendedFqn);
                for (String path : paths) {
                    if (path != null && !path.trim().isEmpty()) {
                        // Check if file exists before adding
                        File file = new File(path);
                        if (file.exists() && file.isFile()) {
                            try {
                                launcher.addInputResource(path);
                                // System.out.println(" Added extended test: " + extendedFqn + " -> " + path);
                            } catch (Exception e) {
                                // System.err.println(" Failed to add extended test: " + extendedFqn + " -> " +
                                // path);
                            }
                        } else {
                            // System.out.println(" Skipping non-existent extended test: " + extendedFqn + "
                            // -> " + path);
                        }
                    }
                }
            }
        }

        System.out.println("Building a complete model from filtered source roots...");
        CtModel model = launcher.buildModel();
        System.out.println("Model build successful. Total types found: "
                + model.getElements(new TypeFilter<>(CtType.class)).size());

        Map<String, String> classNameToTargetPath = new HashMap<>();
        for (String targetFilePath : goodFiles) { // 필터링된 goodFiles를 사용
            String className = getClassNameFromPath(targetFilePath);
            if (className != null) {
                classNameToTargetPath.put(className, targetFilePath);
                this.targetClassFqns.add(className);
            }
        }

        // Also add EXTENDED_TESTS to classNameToTargetPath (so they can be used for
        // inlining)
        if (Config.EXTENDED_TESTS != null && !Config.EXTENDED_TESTS.isEmpty()) {
            System.out.println("Adding " + Config.EXTENDED_TESTS.size()
                    + " EXTENDED_TESTS to classNameToTargetPath for helper method lookup...");
            for (String extendedFqn : Config.EXTENDED_TESTS) {
                // Convert FQN to file path
                List<String> paths = ASTParser.convertClassToPath(extendedFqn);
                if (!paths.isEmpty()) {
                    String path = paths.get(0);
                    classNameToTargetPath.put(extendedFqn, path);
                    // System.out.println(" Added to classNameToTargetPath: " + extendedFqn + " -> "
                    // + path);
                }
            }
        }

        System.out.println("Filtering model to target "
                + (goodFiles.size() + (Config.EXTENDED_TESTS != null ? Config.EXTENDED_TESTS.size() : 0))
                + " files for transformation...");
        for (CtType<?> type : model.getElements(new TypeFilter<>(CtType.class))) {
            if (type.getPosition().isValidPosition() && !type.isShadow()) {
                String modelClassName = type.getQualifiedName();
                if (classNameToTargetPath.containsKey(modelClassName)) {
                    String targetPath = classNameToTargetPath.get(modelClassName);
                    this.fileTypeMap.computeIfAbsent(targetPath, k -> new ArrayList<>()).add(type);
                }
            }
        }

        System.out.println("Filtered down to " + this.fileTypeMap.size() + " files to be transformed.");
        SpoonPacakge spoonPackage = new SpoonPacakge(this.launcher, model, env, targetPkg);
        return spoonPackage;
    }

    /**
     * 변환된 파일 내용을 생성하여 사용자가 요청한 방식으로 덮어씁니다.
     */
    private void saveResults() {
        System.out.println("\n=============== [SAVING TRANSFORMED FILES] ===============");
        System.out.println("# of Files to save: " + this.fileTypeMap.size());
        if (this.fileTypeMap.isEmpty()) {
            System.out.println("No transformed classes to write. Skipping save.");
            return;
        }

        // PrettyPrinter를 준비합니다. 자동 임포트 관리를 위해 autoImports를 활성화합니다.
        launcher.getEnvironment().setAutoImports(false);

        // 변환된 파일 경로와 새로운 소스 코드 내용을 담을 맵
        Map<String, String> transformedSources = new HashMap<>();

        for (Map.Entry<String, List<CtType<?>>> entry : this.fileTypeMap.entrySet()) {
            String targetFilePath = entry.getKey();
            List<CtType<?>> typesInFile = entry.getValue();

            if (!typesInFile.isEmpty()) {
                // CtType에서 상위 객체인 CtCompilationUnit(파일 전체에 해당)을 가져옵니다.
                // 이렇게 하면 패키지 선언, 임포트 구문까지 포함된 전체 소스 코드를 얻을 수 있습니다.
                CtCompilationUnit cu = typesInFile.get(0).getPosition().getCompilationUnit();

                // 파일 전체를 예쁘게 출력하여 새로운 소스 코드 내용을 생성합니다.
                String newContent = cu.prettyprint();
                transformedSources.put(targetFilePath, newContent);
            }
        }

        // 사용자가 제공한 패턴으로 파일 쓰기 실행
        for (Map.Entry<String, String> entry : transformedSources.entrySet()) {
            String filePathString = entry.getKey();
            String newContent = entry.getValue();

            try {
                Path filePath = Paths.get(filePathString);
                // 혹시 디렉토리가 없을 경우를 대비해 생성합니다.
                Files.createDirectories(filePath.getParent());
                Files.write(filePath, newContent.getBytes(StandardCharsets.UTF_8));
                System.out.println("SUCCESS: Wrote file -> " + filePathString);
            } catch (IOException e) {
                System.err.println("ERROR: Failed to write file -> " + filePathString);
                // e.printStackTrace();
            }
        }
    }

    private String getClassNameFromPath(String fullPath) {
        String buildRoot = Paths.get(Config.BUILD_PATH).toString();
        String pathString = Paths.get(fullPath).toString();

        System.err.println("[DEBUG] buildRoot: " + buildRoot);

        // fullPath가 buildRoot로 시작하는지 확인
        if (pathString.startsWith(buildRoot)) {
            // 루트 경로와 구분자(/ 또는 \)를 제거하여 상대 경로를 만듭니다.
            String relativePath = pathString.substring(buildRoot.length() + 1);

            if (relativePath.endsWith(".java")) {
                // ".java" 확장자를 제거하고, 파일 구분자를 '.'으로 변경합니다.
                String result = relativePath.substring(0, relativePath.length() - 5).replace(File.separator, ".");
                System.err.println("[DEBUG] Successfully extracted class name from relative path: " + result);
                return result;
            }
        }

        // Fallback: 파일이 BUILD_PATH 아래에 없는 경우, 직접 패키지명을 추출
        System.err.println(
                "[DEBUG] Path does not start with buildRoot - using fallback method (reading package from file)");
        try {
            // 파일에서 package 선언을 읽어서 추출
            String fileContent = new String(Files.readAllBytes(Paths.get(fullPath)));
            java.util.regex.Pattern packagePattern = java.util.regex.Pattern
                    .compile("^\\s*package\\s+([a-zA-Z_][a-zA-Z0-9_.]*);");
            java.util.regex.Matcher matcher = packagePattern.matcher(fileContent);

            if (matcher.find()) {
                String packageName = matcher.group(1);
                String fileName = new File(fullPath).getName();
                String className = fileName.substring(0, fileName.length() - 5); // .java 제거
                String result = packageName + "." + className;
                System.err.println("[DEBUG] Successfully extracted class name from package declaration: " + result);
                return result;
            } else {
                System.err.println("[DEBUG] No package declaration found in file");
            }
        } catch (Exception e) {
            System.err.println("[DEBUG] Exception during fallback extraction: " + e.getMessage());
            // e.printStackTrace();
        }

        System.err.println("WARN: Could not determine class name for path: " + fullPath);
        return null;
    }

    /**
     * Remove duplicate annotations from a Java file and save to a temporary file
     * 
     * @param filePath Original file path
     * @return Path to cleaned temporary file
     */
    private String removeDuplicateAnnotations(String filePath) throws IOException {
        List<String> lines = Files.readAllLines(Paths.get(filePath), StandardCharsets.UTF_8);
        List<String> cleanedLines = new ArrayList<>();

        String previousLine = null;
        int duplicatesRemoved = 0;

        for (String line : lines) {
            String trimmed = line.trim();

            // Check if this line is the same annotation as previous line
            if (previousLine != null &&
                    trimmed.startsWith("@") &&
                    previousLine.trim().equals(trimmed)) {
                // Skip duplicate annotation
                duplicatesRemoved++;
                // System.out.println("[DEBUG] Removing duplicate: " + trimmed);
                continue;
            }

            cleanedLines.add(line);
            previousLine = line;
        }

        // System.out.println("[DEBUG] Total duplicates removed: " + duplicatesRemoved);

        // Create temporary file
        Path tempFile = Files.createTempFile("cleaned_", ".java");
        Files.write(tempFile, cleanedLines, StandardCharsets.UTF_8);

        return tempFile.toString();
    }
}