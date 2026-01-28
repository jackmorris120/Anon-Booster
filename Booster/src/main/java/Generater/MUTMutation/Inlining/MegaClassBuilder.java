package Generater.MUTMutation.Inlining;

import utils.Config;
import Compiler.Compiler;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import javax.tools.Diagnostic;
import javax.tools.JavaFileObject;
import java.lang.reflect.Modifier;
import java.util.concurrent.atomic.AtomicInteger;

import spoon.Launcher;
import spoon.SpoonException;
import spoon.reflect.CtModel;
import spoon.reflect.code.*;
import spoon.reflect.declaration.*;
import spoon.reflect.factory.Factory;
import spoon.reflect.reference.CtTypeReference;
import spoon.reflect.visitor.CtScanner;
import spoon.reflect.visitor.filter.TypeFilter;
import spoon.reflect.reference.CtParameterReference;
import spoon.reflect.reference.CtVariableReference;
import spoon.compiler.Environment;
import spoon.support.sniper.SniperJavaPrettyPrinter;
import spoon.reflect.visitor.PrettyPrinter;
import spoon.reflect.visitor.DefaultJavaPrettyPrinter;
import spoon.reflect.reference.CtExecutableReference;
import Generater.MUTMutation.Inlining.SpoonPacakge;

/**
 * 여러 테스트를 Round-Robin으로 합친 뒤,
 * 헬퍼 메서드를 호출 위치에 인라인한 MegaTestClass 생성기
 */
public class MegaClassBuilder {
    private static String megaPackageName;
    private static String megaClassName = "MegaTestClass";

    // helper 메서드 시그니처 → CtMethod 맵
    private static Set<String> importStmts = new LinkedHashSet<>();
    private static String targetPkg;

    public static void run(SpoonPacakge spoonPacakge, Map<String, List<CtMethod<?>>> inLinedTests) {
        createMegaClass(spoonPacakge, inLinedTests);
    }


    private static List<CtMethod> parseRoundRobin(Map<String, List<CtMethod<?>>> inLinedTests) {
        List<CtMethod> testMethods = new ArrayList<>();
        int maxRounds = 0;
        for (List<CtMethod<?>> methodList : inLinedTests.values()) {
            if (methodList.size() > maxRounds) {
                maxRounds = methodList.size();
            }
        }

        for (int i = 0; i < maxRounds; i++) {
            for (List<CtMethod<?>> methodList : inLinedTests.values()) {
                if (i < methodList.size()) {
                    testMethods.add(methodList.get(i));
                }
            }
        }
        Collections.shuffle(testMethods);
        return testMethods;
    }

    public static void createMegaClass(SpoonPacakge spoonPacakge, Map<String, List<CtMethod<?>>> inLinedTests) {
        long startTime = System.currentTimeMillis();
        List<CtMethod> testMethods = parseRoundRobin(inLinedTests);
        long endTime = System.currentTimeMillis();
        System.out.println("Done Parsing Round-Robin Test Methods: " + testMethods.size() + " methods found. " +
                "Time taken: " + (endTime - startTime) + " ms.");
        Config.MEGA_TEST_CASES = testMethods;
        Launcher launcher = spoonPacakge.getLauncher();
        Environment env = launcher.getEnvironment();
        Factory factory = launcher.getFactory();
        env.setAutoImports(false);

        importStmts = HelperParser.getImportStmts();
        targetPkg = spoonPacakge.getTargetPkg().get(0);
        
        // Extract CUT package from CUT_FILES since Config.PACKAGE is empty
        String cutPackage = extractPackageFromCUTFiles();
        
        // Debug logging to check package values
        System.out.println("[DEBUG] Test targetPkg: " + targetPkg);
        System.out.println("[DEBUG] Config.PACKAGE: " + Config.PACKAGE);
        System.out.println("[DEBUG] CUT files: " + Config.CUT_FILES);
        System.out.println("[DEBUG] Extracted CUT package: " + cutPackage);
        
        // Use CUT package for MegaTestClass generation
        if (cutPackage != null && !cutPackage.isEmpty()) {
            megaPackageName = cutPackage;
        } else {
            // Fallback to test package if CUT package extraction fails
            megaPackageName = targetPkg.replace("package ", "").replace(";", "").trim();
        }
        
        System.out.println("[DEBUG] Final megaPackageName for MegaTest: " + megaPackageName);
        
        // Original package setting (commented for future use - was using test package)
        // megaPackageName = targetPkg.replace("package ", "").replace(";", "").trim();

        CtPackage pkg = factory.Package().getOrCreate(megaPackageName);
        CtClass<?> megaClass = factory.Class().create(pkg, megaClassName);
        megaClass.setModifiers(Collections.singleton(ModifierKind.PUBLIC));
        long classStartTime = System.currentTimeMillis();

        for (CtMethod<?> m : testMethods) {
            CtMethod<?> cm = m.clone();
            String originalClassName = m.getDeclaringType().getSimpleName();

            String newUniqueName = cm.getSimpleName() + "_" + originalClassName;
            
            cm.setSimpleName(newUniqueName);
        

            if (!containsProblematicNestedClass(cm)) {
              
                megaClass.addMethod(cm);
            } 
        }
        long classEndTime = System.currentTimeMillis();
        
        int actualMethodCount = megaClass.getMethods().size();
        System.out.println("MegaClass created with " + actualMethodCount + " methods (out of " + testMethods.size() + " candidates) in "
                + (classEndTime - classStartTime) + " ms.");
        
         if (actualMethodCount == 0) {
             System.err.println("\n================================================================");
             System.err.println("ERROR: MegaClass has no methods!");
             System.err.println("================================================================");
             System.err.println("Possible reasons:");
             System.err.println("  1. All test methods contain problematic nested classes");
             System.err.println("  2. Input test methods list was empty or invalid");
             System.err.println("  3. All methods were filtered out during processing");
             System.err.println("================================================================");
             System.err.println("Total candidate methods: " + testMethods.size());
             System.err.println("Methods added to MegaClass: " + actualMethodCount);
             System.err.println("================================================================");
             System.exit(1);
         }
         
         // Add null initializations for undefined variables in each method
         addUndefinedVariableInitializations(megaClass, factory);
         
         generateFinalMegaClassSource(megaClass);
    }

    private static void addUndefinedVariableInitializations(CtClass<?> megaClass, Factory factory) {
        for (CtMethod<?> method : megaClass.getMethods()) {
            // Extract all undefined variables from method body
            java.util.Set<String> undefinedVars = extractUndefinedVariablesFromMethod(method);
            
            if (undefinedVars.isEmpty()) {
                continue;
            }
            
            System.out.println("[AST Fix] Method " + method.getSimpleName() + " has " + undefinedVars.size() + " undefined variables");
            
            // Get method body
            CtBlock<?> body = method.getBody();
            if (body == null || body.getStatements().isEmpty()) {
                continue;
            }
            
            // Add null initializations at the beginning of method body
            for (String var : undefinedVars) {
                try {
                    CtStatement nullInit = factory.createCodeSnippetStatement(
                        "java.lang.Object " + var + " = null"
                    );
                    body.insertBegin(nullInit);
                } catch (Exception e) {
                    System.err.println("[AST Fix] Failed to add null init for " + var + ": " + e.getMessage());
                }
            }
        }
    }
    
    private static java.util.Set<String> extractUndefinedVariablesFromMethod(CtMethod<?> method) {
        java.util.Set<String> undefinedVars = new java.util.LinkedHashSet<>();
        java.util.Set<String> declaredVars = new java.util.HashSet<>();
        
        // Get all statements in method
        List<CtStatement> allStmts = method.getBody().getStatements();
        
        for (CtStatement stmt : allStmts) {
            String stmtStr = stmt.toString();
            
            // Find all variable references like "lastCompiler_XXX"
            java.util.regex.Pattern pattern = java.util.regex.Pattern.compile(
                "(lastCompiler_\\d+|last\\w+_\\d+)"
            );
            java.util.regex.Matcher matcher = pattern.matcher(stmtStr);
            
            while (matcher.find()) {
                String var = matcher.group(1);
                if (!declaredVars.contains(var) && !isJavaKeyword(var)) {
                    undefinedVars.add(var);
                }
            }
            
            // Track declared variables
            if (stmt instanceof CtLocalVariable) {
                CtLocalVariable<?> localVar = (CtLocalVariable<?>) stmt;
                declaredVars.add(localVar.getSimpleName());
            }
        }
        
        return undefinedVars;
    }
    
    private static boolean isJavaKeyword(String word) {
        return word.equals("new") || word.equals("null") || word.equals("true") || 
               word.equals("false") || word.equals("this") || word.equals("super");
    }

    private static void generateFinalMegaClassSource(CtClass<?> megaClass) {
        long writeStartTime = System.currentTimeMillis();
        String src = buildFinalSourceCode(megaPackageName, importStmts, megaClass);
        long writeEndTime = System.currentTimeMillis();
        System.out.println("MegaClass Written with in " + (writeEndTime - writeStartTime) + " ms.");
        String pkgDir = megaPackageName.replace('.', '/');
        String dir = Config.BUILD_PATH + "/" + pkgDir + "/";
        String file = dir + megaClassName + ".java";
        System.out.println("[MegaClass Location] " + file);
        Config.MEGAFILE_PATH = file;
        Config.TEST_FILE = file;
        Config.FULL_CLASS_NAME = megaPackageName + "." + megaClassName;
        // PrimitiveMutateParser.setPackageName(Config.FULL_CLASS_NAME);

        String sep = System.getProperty("file.separator");
        Config.OUTPUT_PATH = file.substring(0, file.lastIndexOf(sep));
        // System.out.println("Compiling MegaClass : ");
        // List<Diagnostic<? extends JavaFileObject>> errs = Compiler.compileWholeClassFile(Config.TEST_FILE, src);
        // // System.out.println(errs);s
        // handleCompileErrors(errs, src);
        writeToFile(src);
    }

    private static void handleCompileErrors(List<Diagnostic<? extends JavaFileObject>> errs, String src) {
        List<String> del = parseErrorImports(errs);
        String cleaned = cleanImportStatements(src, del);
        writeToFile(cleaned);
    }

    private static List<String> parseErrorImports(List<Diagnostic<? extends JavaFileObject>> errs) {
        Set<String> importsToRemove = new LinkedHashSet<>(); // 중복 제거를 위해 Set 사용
        // System.out.println(errs);
        for (Diagnostic<? extends JavaFileObject> d : errs) {
            // 에러 메시지 전체를 문자열로 가져옵니다.
            String errorMessage = d.toString();

            // 에러 메시지를 한 줄씩 나눕니다.
            for (String line : errorMessage.split("\\r?\\n")) {
                // 각 줄의 앞뒤 공백을 제거합니다.
                String trimmedLine = line.trim();

                // 해당 줄이 'import'로 시작하고 ';'로 끝나면, 제거 목록에 추가합니다.
                if (trimmedLine.startsWith("import ") && trimmedLine.endsWith(";")) {
                    importsToRemove.add(trimmedLine);
                }else{
                    System.out.println(" - "+trimmedLine);
                }
            }
        }

        System.out.println("Error Imports : "+ importsToRemove);
        return new ArrayList<>(importsToRemove);
    }

    private static String cleanImportStatements(String src, List<String> del) {
        StringBuilder sb = new StringBuilder();
        for (String line : src.split("\\r?\\n")) {
            String t = line.trim();
            if (t.startsWith("import") && del.contains(t))
                continue;
            sb.append(line).append(System.lineSeparator());
        }
        return sb.toString();
    }

    private static void writeToFile(String content) {
        try {
            File out = new File(Config.TEST_FILE);
            File pd = out.getParentFile();
            if (!pd.exists())
                pd.mkdirs();
            try (FileWriter w = new FileWriter(out)) {
                w.write(content);
            }
        } catch (IOException e) {
            // e.printStackTrace();
        }
    }

    private static boolean containsProblematicNestedClass(CtMethod<?> m) {
        return m.getElements(new TypeFilter<CtTypeReference>(CtTypeReference.class)).stream()
                .map(CtTypeReference::getQualifiedName)
                .filter(q -> q != null)
                .anyMatch(q -> (q.contains("$") && !q.startsWith("java.")));
    }


    static class CustomPrettyPrinter extends spoon.reflect.visitor.DefaultJavaPrettyPrinter {
        public CustomPrettyPrinter(Environment env) {
            super(env);
        }

        @Override
        public <T> void visitCtTypeReference(spoon.reflect.reference.CtTypeReference<T> reference) {
            String qName = reference.getQualifiedName();
            if (qName != null && qName.contains("$") && !qName.matches(".*\\$\\d+$")) {
                getElementPrinterHelper().writeQualifiedName(qName.replace('$', '.'));
            } else {
                super.visitCtTypeReference(reference);
            }
        }

        @Override
        public <T> void visitCtFieldRead(spoon.reflect.code.CtFieldRead<T> fieldRead) {
            // Use default behavior - the issue might be in field reference creation, not printing
            super.visitCtFieldRead(fieldRead);
        }

        @Override
        public <T> void visitCtFieldWrite(spoon.reflect.code.CtFieldWrite<T> fieldWrite) {
            // Use default behavior
            super.visitCtFieldWrite(fieldWrite);
        }
    }

    private static String buildFinalSourceCode(String pkg, Set<String> imps, CtClass<?> megaClass) {
        Factory factory = megaClass.getFactory();
        Environment env = factory.getEnvironment();
        env.setAutoImports(false);

        StringBuilder sb = new StringBuilder();
        if (pkg != null && !pkg.isEmpty()) {
            sb.append("package ").append(pkg).append(";\n\n");
        }
        for (String imp : imps) {
            sb.append(imp).append("\n");
        }
        sb.append("\n");

        try {
            CustomPrettyPrinter printer = new CustomPrettyPrinter(env);
            sb.append(printer.prettyprint(megaClass));
        } catch (SpoonException e) {
            System.err.println("PrettyPrint 실패, fallback toString(): " + e.getMessage());
            sb.append(megaClass.toString());
        }

        return sb.toString();
    }

    /**
     * Extract package name from CUT files
     */
    private static String extractPackageFromCUTFiles() {
        if (Config.CUT_FILES == null || Config.CUT_FILES.isEmpty()) {
            return null;
        }
        
        try {
            // Get the first CUT file to extract package from
            String cutFilePath = Config.CUT_FILES.get(0);
            File cutFile = new File(cutFilePath);
            
            if (!cutFile.exists()) {
                System.err.println("[WARNING] CUT file does not exist: " + cutFilePath);
                return null;
            }
            
            // Read the file and look for package declaration
            try (BufferedReader reader = new BufferedReader(new FileReader(cutFile))) {
                String line;
                while ((line = reader.readLine()) != null) {
                    line = line.trim();
                    if (line.startsWith("package ") && line.endsWith(";")) {
                        // Extract package name: "package org.joda.time.chrono;" -> "org.joda.time.chrono"
                        return line.substring(8, line.length() - 1).trim();
                    }
                    // Stop looking after finding imports or class declaration
                    if (line.startsWith("import ") || line.startsWith("public class") || line.startsWith("class")) {
                        break;
                    }
                }
            }
        } catch (Exception e) {
            System.err.println("[ERROR] Failed to extract package from CUT files: " + e.getMessage());
        }
        
        return null;
    }

}