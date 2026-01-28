package Compiler;

import Generater.MUTMutation.ASTParser;
import Generater.MUTMutation.CandidatePool;
import Generater.MUTMutation.Input;
import Generater.MUTMutation.MUTInput;
import RegressionOracles.Analyzer;
import RegressionOracles.AssertionAdder;
import RegressionOracles.TryCatchFailAdder;
import RegressionOracles.RegressionUtil.Logger;

import org.junit.runner.JUnitCore;
import org.junit.runner.Result;
import org.junit.runner.notification.Failure;
import org.mdkt.compiler.InMemoryJavaCompiler;
import spoon.Launcher;
import spoon.SpoonException;
import spoon.reflect.code.CtAbstractInvocation;
import spoon.reflect.code.CtCodeSnippetStatement;
import spoon.reflect.code.CtLocalVariable;
import spoon.reflect.code.CtStatement;
import spoon.reflect.declaration.*;
import spoon.reflect.factory.Factory;
import spoon.reflect.reference.CtTypeReference;
import spoon.reflect.visitor.filter.TypeFilter;
import spoon.reflect.visitor.CtScanner;
import spoon.reflect.code.*;
import spoon.support.reflect.code.CtInvocationImpl;
import spoon.support.reflect.code.CtVariableReadImpl;
import spoon.support.reflect.code.CtConstructorCallImpl;
import sun.misc.URLClassPath;
import utils.Config;
import utils.Pair;
import utils.TestMinimizer;

import javax.tools.*;
import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.lang.annotation.Annotation;
import java.lang.reflect.Field;
import java.net.URI;
import java.net.URLClassLoader;
import java.util.*;
import java.util.concurrent.*;

public class Compiler {
    // Debug flag for oracle transformation
    private static final boolean DEBUG_ORACLE_TRANSFORM = false;
    
    // Shared compiler instances for performance optimization
    private static final JavaCompiler SHARED_COMPILER;
    
    // Initialize shared compiler instances once
    static {
        SHARED_COMPILER = ToolProvider.getSystemJavaCompiler();
        if (SHARED_COMPILER == null) {
            throw new RuntimeException("No Java compiler available. Make sure you're running on JDK, not JRE.");
        }
    }
    
    /**
     * Get compiler options with current classpath
     * Use Config.CLASS_PATH if available, otherwise fall back to system classpath
     */
    private static List<String> getCompilerOptions() {
        String classpath;
        try {
            // Try to use Config.CLASS_PATH if available
            classpath = utils.Config.CLASS_PATH;
            if (classpath == null || classpath.isEmpty()) {
                classpath = System.getProperty("java.class.path");
            }
        } catch (Exception e) {
            classpath = System.getProperty("java.class.path");
        }
        return Arrays.asList("-cp", classpath, "-encoding", "UTF-8");
    }
    
    /**
     * Get a reusable DiagnosticCollector for the current thread
     */
    private static DiagnosticCollector<JavaFileObject> getDiagnosticCollector() {
        // Create a new DiagnosticCollector each time to avoid clear() issues
        // The ThreadLocal approach with clearing has compatibility issues
        return new DiagnosticCollector<JavaFileObject>();
    }
    
    private List<CtClass<Object>> testcases;
    private String packageName;
    private String packageAndImport = "";
    public static List<String> options = new ArrayList<String>();
    private Map<String, CtMethod> nameToMethod = new HashMap<>();
    private List<List<CtMethod>> splitTestcases = new LinkedList<>();
    private Set<String> runningClassNames = new HashSet<>();
    private List<CtMethod> mutatedTestcases = new ArrayList<>();
    private List<CtMethod> usedBucketTestcases = new ArrayList<>();
    private List<CtMethod> runnableTestList = new LinkedList<>();
    private List<String> runnableTestStringList = new LinkedList<>();
    private Map<String, Failure> testNameToFailMap = new HashMap<>();
    private Set<String> timedOutTestNameSet = new HashSet<>();
    private static int numOfFailingTests = 0;
    private static int numOfPassingTests = 0;
    private static int mutVariableCounter = 0;
    private TestMinimizer testMinimizer;
     
    // [NEW] Bucketing용: 테스트명 → Exception 타입 매핑
    private Map<String, String> testNameToExceptionMap = new HashMap<>();
    // [NEW] Bucketing용: Exception별 테스트 메서드들
    private Map<String, List<String>> exceptionBuckets = new LinkedHashMap<>();
    // [NEW] Bucketing용: Pass 테스트 메서드들
    private List<String> passingTestStringList = new LinkedList<>();
    
    // [NEW] SeqP Bucketing용: 메서드 순서대로 저장된 메서드명 리스트
    private LinkedList<String> orderedMethodNames = new LinkedList<>();
    // [NEW] SeqP Bucketing용: 메서드명 → Signature 매핑
    private Map<String, String> methodToSignatureMapping = new HashMap<>();
    public static boolean isPassing = false;
    /**
     * init the test cases
     *
     * @param packageAndImport
     */
    public Compiler(String packageAndImport, String packageName, TestMinimizer minimizer) {
        this.packageAndImport = packageAndImport;
        this.packageName = packageName;
        this.testMinimizer = minimizer;
        // init compile options
        initCompileOptions();
        initOutputFolderForClassLoader();
    }

    /**
     * write to file
     *
     * @param fileName
     * @param clazz
     * @throws Exception
     */
    private static void writeFile(String fileName, String clazz) throws Exception {
        File sourceFile = new File(Config.OUTPUT_PATH + File.separator + fileName + ".java");
        sourceFile.createNewFile();
        FileWriter fileWriter = new FileWriter(sourceFile.getAbsoluteFile());
        PrintWriter printWriter = new PrintWriter(fileWriter);
        printWriter.print(clazz);
        printWriter.close();
    }

    /**
     * Apply bucketing to CtClass methods by organizing them by Signature
     * Modifies the CtClass in-place to reorder methods according to bucketing
     * 
     * 주의: 이 메서드는 SeqP 모드에서만 호출됨
     * SeqC는 testStringListToFile에서 bucketing을 처리함
     */
     public void applyBucketingToCtClass(CtClass<?> clazz) {
         if (!Config.ENABLE_TEST_BUCKETING || testMinimizer == null) {
             if (Config.DEBUG_TEST_BUCKETING) {
                 System.out.println("[Bucketing Debug] SKIP: ENABLE_TEST_BUCKETING=" + Config.ENABLE_TEST_BUCKETING + " testMinimizer=" + (testMinimizer != null));
             }
             return; // No bucketing needed
         }
         
         Map<String, List<String>> buckets = testMinimizer.getExceptionBuckets();
         if (buckets.isEmpty()) {
             if (Config.DEBUG_TEST_BUCKETING) {
                 System.out.println("[Bucketing Debug] SKIP: buckets is empty");
             }
             return; // No bucketing data
         }
         
         if (Config.DEBUG_TEST_BUCKETING) {
             System.out.println("[Bucketing Debug] Processing class: " + clazz.getSimpleName() + " with " + buckets.size() + " buckets");
         }
         
         // Get all methods from class
         List<CtMethod<?>> allMethods = new ArrayList<>(clazz.getMethods());
         
         // Create a map of method name to CtMethod
         Map<String, CtMethod<?>> methodMap = new HashMap<>();
         for (CtMethod<?> method : allMethods) {
             methodMap.put(method.getSimpleName(), method);
         }
         
         // Find which methods in this class exist in the bucketing buckets
         Set<String> classMethodsInBuckets = new HashSet<>();
         for (Map.Entry<String, List<String>> entry : buckets.entrySet()) {
             for (String testName : entry.getValue()) {
                 if (methodMap.containsKey(testName)) {
                     classMethodsInBuckets.add(testName);
                 }
             }
         }
         
         if (Config.DEBUG_TEST_BUCKETING) {
             System.out.println("[Bucketing Debug] " + clazz.getSimpleName() + ": Found " + classMethodsInBuckets.size() + " methods in buckets out of " + methodMap.size() + " total methods");
         }
         
         // If no methods from this class are in buckets, no bucketing needed
         if (classMethodsInBuckets.isEmpty()) {
             if (Config.DEBUG_TEST_BUCKETING) {
                 System.out.println("[Bucketing Debug] No methods found in buckets for " + clazz.getSimpleName());
             }
             return;
         }
         
         // Clear previous mappings
         orderedMethodNames.clear();
         methodToSignatureMapping.clear();
         
         // Remove all methods from class
         for (CtMethod<?> method : allMethods) {
             clazz.removeMethod(method);
         }
         
         // Re-add methods in bucketing order (only methods that exist in this class)
         // IMPORTANT: 이 순서가 나중에 소스 코드에서의 메서드 순서가 됨
         Set<String> addedMethods = new HashSet<>();
         for (Map.Entry<String, List<String>> entry : buckets.entrySet()) {
             String signature = entry.getKey();
             for (String testName : entry.getValue()) {
                 CtMethod<?> method = methodMap.get(testName);
                 if (method != null && !addedMethods.contains(testName)) {
                     clazz.addMethod(method);
                     addedMethods.add(testName);
                     // Store mapping: 메서드명 → Signature
                     orderedMethodNames.add(testName);
                     methodToSignatureMapping.put(testName, signature);
                 }
             }
         }
         
         // Add remaining methods (passing tests)
         for (Map.Entry<String, CtMethod<?>> entry : methodMap.entrySet()) {
             if (!addedMethods.contains(entry.getKey())) {
                 clazz.addMethod(entry.getValue());
                 orderedMethodNames.add(entry.getKey());
                 // Passing tests don't have a signature
             }
         }
         
         if (Config.DEBUG_TEST_BUCKETING) {
             System.out.println("[Bucketing Debug] Stored " + methodToSignatureMapping.size() + " method-to-signature mappings for " + clazz.getSimpleName());
         }
     }


    /**
     * Helper method to extract test method name from test string
     * Example input: "@Test\n    public void testMethod_1() throws..."
     * Output: "testMethod_1"
     */
      private String extractTestMethodName(String testString) {
        // Look for pattern: "public void METHOD_NAME(" or "public void METHOD_NAME "
        int publicIdx = testString.indexOf("public void ");
        if (publicIdx == -1) {
            return null;
        }
        
        int startIdx = publicIdx + 12; // "public void ".length() = 12
        int endIdx = startIdx;
        
        // Find the end of method name (next whitespace or parenthesis)
        while (endIdx < testString.length()) {
            char c = testString.charAt(endIdx);
            if (c == '(' || Character.isWhitespace(c)) {
                break;
            }
            endIdx++;
        }
        
        if (endIdx > startIdx) {
            return testString.substring(startIdx, endIdx);
        }
        
        return null;
    }
    


    public String testStringListToFile(List<String> testStringList, String fileName) {
         Factory facotry = new Launcher().getFactory();
         facotry.getEnvironment().disableConsistencyChecks(); // setSelfChecks(true);
         /**
          * Set up Class: new class name is original_MUT_MUTcount (e.g.,
          * XYSeries_ESTest_addOrUpdate_1)
          */
         CtClass<Object> clazz = facotry.Core().createClass();
         clazz.setSimpleName(fileName);
         Set<ModifierKind> modifiers = new HashSet<>();
         modifiers.add(ModifierKind.PUBLIC);
         clazz.setModifiers(modifiers);
         String emptyClassString = clazz.toString().replace("}", "\n");
         
           // [NEW] Bucketing 모드: Exception별로 정렬된 테스트 추가
           if (Config.ENABLE_TEST_BUCKETING && testMinimizer != null && testMinimizer.isBucketingEnabled()) {
               // Bucketing 활성화: Exception별 그룹으로 정렬
               Map<String, List<String>> buckets = testMinimizer.getExceptionBuckets();
               
                // 1단계: testName → testString 맵 생성 + 사용 가능한 테스트 이름 세트 (빠른 lookup)
                // [FIX] 중복된 테스트는 건너뛰고 첫 번째 것만 사용
                Map<String, String> testNameToStringMap = new HashMap<>();
                Set<String> availableTestNames = new HashSet<>();
                
                for (String testString : testStringList) {
                    String testName = extractTestMethodName(testString);
                    if (testName != null) {
                        // 이미 있으면 건너뛰기 (중복 방지)
                        if (!testNameToStringMap.containsKey(testName)) {
                            testNameToStringMap.put(testName, testString);
                            availableTestNames.add(testName);
                        }
                    }
                }
               
               // 2단계: 각 Exception 타입별로 필터링된 테스트만 추출
               Map<String, List<String>> filteredBuckets = new LinkedHashMap<>();
               for (Map.Entry<String, List<String>> entry : buckets.entrySet()) {
                   String exceptionType = entry.getKey();
                   List<String> filteredTests = new ArrayList<>();
                   
                   // 이 split에 실제로 포함된 테스트들만 필터링
                   for (String testName : entry.getValue()) {
                       if (availableTestNames.contains(testName)) {
                           filteredTests.add(testName);
                       }
                   }
                   
                   // 이 exception에 이 split에서 존재하는 테스트가 있으면 bucket에 추가
                   if (!filteredTests.isEmpty()) {
                       filteredBuckets.put(exceptionType, filteredTests);
                   }
               }
               
                 // 3단계: 필터링된 bucket으로 테스트 추가 + 사용된 테스트 추적
                 Set<String> usedTestNames = new HashSet<>();
                 for (Map.Entry<String, List<String>> entry : filteredBuckets.entrySet()) {
                     String signature = entry.getKey();
                     emptyClassString += "\n    // ============================================================\n";
                     emptyClassString += "    // SIGNATURE BUCKET: " + signature + "\n";
                     emptyClassString += "    // ============================================================\n\n";
                    
                    // 해당 Exception의 테스트들을 추가
                    for (String testName : entry.getValue()) {
                        String testString = testNameToStringMap.get(testName);
                        if (testString != null) {
                            emptyClassString += testString + "\n\n";
                            usedTestNames.add(testName);
                        }
                    }
                }
                // if (!Config.REMOVE_PASSING_TESTS) {
                    // 4단계: 이 split에 포함되었지만 bucket에 없는 테스트들은 Passing test (또는 컴파일 안 된 테스트)
                    List<String> passingTestsThisSplit = new ArrayList<>();
                    for (String testName : availableTestNames) {
                        if (!usedTestNames.contains(testName)) {
                            String testString = testNameToStringMap.get(testName);
                            if (testString != null) {
                                passingTestsThisSplit.add(testString);
                            }
                        }
                    }

                    if (!passingTestsThisSplit.isEmpty()) {
                        emptyClassString += "\n    // ============================================================\n";
                        emptyClassString += "    // PASSING TESTS\n";
                        emptyClassString += "    // ============================================================\n\n";
                        for (String testString : passingTestsThisSplit) {
                            emptyClassString += testString + "\n\n";
                        }
                    }
                // }
                
         } else {
             // 기본 모드: 원래대로
             for (String testString : testStringList) {
                 emptyClassString += testString + "\n\n";
             }
         }
         
         String testIncludingClassString = emptyClassString + "}";

         return this.packageAndImport + testIncludingClassString;
     }

    public boolean compileFile(String fileName, String content) {
        List<Diagnostic<? extends JavaFileObject>> errorMessage;
        if (Config.ASSEMBLE_MODE.equals("seqp")) {
            errorMessage = compileWholeClassFileForPrim(fileName, content);
        } else {
            errorMessage = compileWholeClassFile(fileName, content);
        }

        if (checkCompileError(errorMessage)) {
            return true;
        } else {
            System.out.println(errorMessage.toString());
            return false;
        }
    }

    public Pair<CtMethod, String> compileEach(Pair<CtClass, String> generatedTestAndStringPair) {
        CtMethod testMethod = handleTestcaseClass(generatedTestAndStringPair.getKey());
        String testMethodString = generatedTestAndStringPair.getValue();
        
        // Replace method name in string only if it's the default "test" name
        // RecursiveTestCaseGenerator already has the correct method name, so skip replacement
        if (!testMethod.getSimpleName().startsWith("test_")) {
            testMethodString = testMethodString.replace("public void test", "public void " + testMethod.getSimpleName());
        }
        
        generatedTestAndStringPair.setValue(testMethodString);

        nameToMethod.put(testMethod.getSimpleName(), testMethod);
        if (safe2Compile(generatedTestAndStringPair)) {
            // System.out.println("Is Safe to Compile : "+testMethod.getSimpleName());
            return new Pair<CtMethod, String>(testMethod, testMethodString);
        }
        Config.NUM_COMPILE_FAIL++;
        return null;
    }

    public Pair<CtMethod, String> compileEachForPrim(Pair<CtClass, String> generatedTestAndStringPair,
            String newMethodName) {
        // Apply AST-level normalization to the CtClass before processing
        normalizeThisAccessInClass(generatedTestAndStringPair.getKey());

        CtMethod testMethod = handleTestcaseClassForPrim(generatedTestAndStringPair.getKey(), newMethodName);
        String testMethodName = testMethod.getSimpleName();
        String testMethodString = generatedTestAndStringPair.getValue();

        testMethodString = testMethodString.replace("public void mockTest", "public void " + testMethodName);

        // Apply final this reference normalization to fix nested class qualified this references
        if (testMethodString.contains(".this.")) {
            java.util.regex.Pattern pattern = java.util.regex.Pattern.compile(
                "\\b[A-Za-z_][A-Za-z0-9_]*(?:\\.[A-Za-z_][A-Za-z0-9_]*)+\\.this\\."
            );
            testMethodString = pattern.matcher(testMethodString).replaceAll("this.");
        }

        generatedTestAndStringPair.setValue(testMethodString);

        nameToMethod.put(testMethod.getSimpleName(), testMethod);
        if (safe2Compile(generatedTestAndStringPair)) {
            // System.out.println("Is Safe to Compile : "+testMethod.getSimpleName());
            return new Pair<CtMethod, String>(testMethod, testMethodString);
        }
        Config.NUM_COMPILE_FAIL++;
        return null;
    }

    private boolean safe2Compile(Pair<CtClass, String> generatedTestAndStringPair) {
        List<Diagnostic<? extends JavaFileObject>> errorMessage = new ArrayList<>();
        boolean errorFree = false;
        // CtClass rawClass = generateClass(Collections.singletonList(testCase),
        // testCase.getSimpleName());

        String rawClassWithDependency = null;
        try {
            String classString = generatedTestAndStringPair.getValue();
            // Apply final normalization before compilation
            if (classString.contains(".this.")) {
                java.util.regex.Pattern pattern = java.util.regex.Pattern.compile(
                    "\\b[A-Za-z_][A-Za-z0-9_]*(?:\\.[A-Za-z_][A-Za-z0-9_]*)+\\.this\\."
                );
                classString = pattern.matcher(classString).replaceAll("this.");
            }
            rawClassWithDependency = this.packageAndImport + classString;
        } catch (SpoonException e) {
            return false;
        }

         // Choose compile method based on ASSEMBLE_MODE
         if (Config.ASSEMBLE_MODE.equals("seqp")) {
             // SeqP: Only compile once, no undefined variable fix needed
             errorMessage = compileWholeClassFileForPrim(generatedTestAndStringPair.getKey().getSimpleName(),
                     rawClassWithDependency);
             errorFree = checkCompileError(errorMessage);
         } else {
             // SeqC: Compile and attempt to fix undefined variables if needed
             errorMessage = compileWholeClassFile(generatedTestAndStringPair.getKey().getSimpleName(),
                     rawClassWithDependency);
             errorFree = checkCompileError(errorMessage);
             
             // If compile failed, try to fix undefined variable errors (SeqC only)
             if (!errorFree) {
                 String classString = generatedTestAndStringPair.getValue();
                 Map<String, String> varToType = extractUndefinedVariables(errorMessage, classString);
                 
                 if (!varToType.isEmpty()) {
                     // Add null initializations for undefined variables with correct types
                     String fixedClassString = addNullInitializations(classString, varToType);
                     generatedTestAndStringPair.setValue(fixedClassString);
                     rawClassWithDependency = this.packageAndImport + fixedClassString;
                     
                     // Retry compilation
                     errorMessage = compileWholeClassFile(generatedTestAndStringPair.getKey().getSimpleName(),
                             rawClassWithDependency);
                     errorFree = checkCompileError(errorMessage);
                 }
             }
         }
         
         // DEBUG: Check if Logger.observe is causing compile errors

         
         if (!errorFree) {
         List<String> badImports = parseErrorImports(errorMessage);
         if (!badImports.isEmpty()) {
             this.packageAndImport = cleanImportStatements(this.packageAndImport, badImports);
         }
         if(Config.DEBUG_COMPILE_FAIL_TESTS){
            System.out.println("------------------------------------");
            System.out.println("Test:");
            Set<CtMethod<?>> allMethods = generatedTestAndStringPair.getKey().getMethods();
            List<CtMethod<?>> methodList = new ArrayList<>(allMethods);
            CtMethod testMethod = methodList.get(0);
            // System.out.println(testMethod);
            // System.out.println(generatedTestAndStringPair.getValue());
            System.out.println(rawClassWithDependency);
            System.out.println();
            System.out.println("Error message:");
            for (Diagnostic<? extends JavaFileObject> diagnostic : errorMessage) {
            System.out.println(diagnostic.toString());
            }
            System.out.println("------------------------------------");
        }
        
        }

        return errorFree;
    }

    private Map<String, String> extractUndefinedVariables(List<Diagnostic<? extends JavaFileObject>> errors, String classString) {
         Map<String, String> varToType = new LinkedHashMap<>();
         
         for (Diagnostic<? extends JavaFileObject> d : errors) {
             String errorMsg = d.toString();
             
              // Pattern 1: Extract "cannot find symbol ... symbol: variable XXX"
              java.util.regex.Pattern cantFindPattern = java.util.regex.Pattern.compile(
                  "symbol:\\s*variable\\s+([a-zA-Z_][a-zA-Z0-9_.]*)"
              );
              java.util.regex.Matcher cantFindMatcher = cantFindPattern.matcher(errorMsg);
              if (cantFindMatcher.find()) {
                  String undefinedVar = cantFindMatcher.group(1);
                  
                  // [수정] _mut이 포함된 변수는 스킵 (MUT 결과 변수이므로 나중에 선언됨)
                  if (undefinedVar.contains("_mut")) {
                     //  System.out.println("[extractUndefinedVariables] Skipping _mut variable: " + undefinedVar);
                      continue;
                  }
                  
                  // [수정] FQN 형식(qualified name)이면 스킵 (예: java.lang.Double.NaN)
                  // FQN은 이미 사용 가능한 형태이므로 변수 선언할 필요 없음
                  if (undefinedVar.contains(".")) {
                      System.out.println("[extractUndefinedVariables] Skipping FQN variable: " + undefinedVar);
                      continue;
                  }
                  
                  // Try to infer type from classString
                  // Look for: "XXX varName = undefinedVar = "
                  java.util.regex.Pattern typePattern = java.util.regex.Pattern.compile(
                      "((?:[\\w.]+)(?:\\[\\])*?)\\s+\\w+\\s*=\\s*" + java.util.regex.Pattern.quote(undefinedVar) + "\\s*="
                  );
                  java.util.regex.Matcher typeMatcher = typePattern.matcher(classString);
                  if (typeMatcher.find()) {
                      String type = typeMatcher.group(1);
                      if (!type.equals("java.lang.Object")) {
                          varToType.put(undefinedVar, type);
                      } else {
                          // Type is Object, use generic Object
                          varToType.put(undefinedVar, "java.lang.Object");
                      }
                  } else {
                      // Default to Object if type cannot be inferred
                      varToType.put(undefinedVar, "java.lang.Object");
                  }
              }
            
              // Pattern 2: Extract "incompatible types" errors
              java.util.regex.Pattern incompatiblePattern = java.util.regex.Pattern.compile(
                  "incompatible types:\\s*java\\.lang\\.Object cannot be converted to\\s+([\\w.]+)"
              );
              java.util.regex.Matcher incompatibleMatcher = incompatiblePattern.matcher(errorMsg);
              if (incompatibleMatcher.find()) {
                  String requiredType = incompatibleMatcher.group(1);
                  
                  // Extract variable name from error context
                  java.util.regex.Pattern varNamePattern = java.util.regex.Pattern.compile(
                      "([a-zA-Z_][a-zA-Z0-9_]*)\\s*="
                  );
                  java.util.regex.Matcher varNameMatcher = varNamePattern.matcher(errorMsg);
                  if (varNameMatcher.find()) {
                      String var = varNameMatcher.group(1);
                      
                      // [수정] _mut이 포함된 변수는 스킵 (MUT 결과 변수이므로 나중에 선언됨)
                      if (var.contains("_mut")) {
                         //  System.out.println("[extractUndefinedVariables] Skipping _mut variable: " + var);
                          continue;
                      }
                      
                      varToType.put(var, requiredType);
                  }
              }
              
              // Pattern 3: Extract "possible lossy conversion" errors (배열 인덱스 타입 불일치)
              // 예: "possible lossy conversion from double to int"
              java.util.regex.Pattern lossyPattern = java.util.regex.Pattern.compile(
                  "possible lossy conversion from\\s+([\\w.]+)\\s+to\\s+([\\w.]+)"
              );
              java.util.regex.Matcher lossyMatcher = lossyPattern.matcher(errorMsg);
              if (lossyMatcher.find()) {
                  String fromType = lossyMatcher.group(1);
                  String toType = lossyMatcher.group(2);
                  // 배열 인덱스 오류는 캐스팅으로 해결 불가능하므로 
                  // 실제로는 테스트 생성 단계에서 인덱스 타입을 맞춰야 하는데,
                  // 여기서는 에러만 추적함 (로깅 용도)
                  // System.out.println("[Type Mismatch] Lossy conversion from " + fromType + " to " + toType);
              }
        }
        
        return varToType;
    }
    
      private String addNullInitializations(String classString, Map<String, String> varToType) {
           // Find the method body opening brace and add null initializations
           int methodBodyStart = classString.indexOf("throws Throwable {");
           if (methodBodyStart == -1) {
               methodBodyStart = classString.indexOf("throws Throwable{");
           }
           if (methodBodyStart == -1) {
               return classString; // Cannot find method body, return original
           }
           
           // ★ 먼저 배열 인덱스 타입 불일치 문제 수정
           classString = fixArrayIndexTypeMismatch(classString);
           
           int insertPos = methodBodyStart + (classString.contains("throws Throwable {") ? 
                                              "throws Throwable {".length() : 
                                              "throws Throwable{".length());
           
           StringBuilder nullInits = new StringBuilder();
           for (Map.Entry<String, String> entry : varToType.entrySet()) {
               String var = entry.getKey();
               String type = entry.getValue();
               
               // [수정] _mut이 포함된 변수는 스킵 (MUT 결과 변수이므로 선언하면 안됨)
               if (var.contains("_mut")) {
                   System.out.println("[addNullInitializations] Skipping _mut variable: " + var);
                   continue;
               }
               
               // [수정] FQN 형식(qualified name)이면 스킵 (예: java.lang.Double.NaN)
               // FQN은 이미 사용 가능한 형태이므로 변수 선언할 필요 없음
               if (var.contains(".")) {
                   System.out.println("[addNullInitializations] Skipping FQN variable: " + var);
                   continue;
               }
               
               nullInits.append("\n\t    ").append(type).append(" ").append(var).append(" = null;");
           }
           
           return classString.substring(0, insertPos) + 
                  nullInits.toString() + 
                  classString.substring(insertPos);
       }
      
      /**
       * ★ 배열 인덱스 타입 불일치 수정
       * 
       * 주의: 이것은 임시 방편입니다!
       * 근본 원인: Tway/Random 변환에서 배열 인덱스 위치에 
       * double/float 같은 non-int 값이 선택됨
       * 
       * 올바른 해결책: 테스트 생성 단계에서 배열 인덱스 타입을 
       * 미리 int로 강제해야 함
       * 
       * 예: stat[0.25] → stat[(int)0.25]
       * stat[1.7976...] → stat[(int)1.7976...]
       */
      private String fixArrayIndexTypeMismatch(String classString) {
          String result = classString;
          
          // 패턴: [소수점 리터럴] 형태 찾기
          java.util.regex.Pattern doubleIndexPattern = java.util.regex.Pattern.compile(
              "\\[([0-9]*\\.[0-9]+(?:[eE][\\-\\+]?[0-9]+)?)\\]"
          );
          
          java.util.regex.Matcher matcher = doubleIndexPattern.matcher(result);
          int count = 0;
          StringBuffer sb = new StringBuffer();
          
          while (matcher.find()) {
              count++;
              String doubleValue = matcher.group(1);
              // [(int)0.25] 형태로 변환
              String replacement = "[(int)" + doubleValue + "]";
              matcher.appendReplacement(sb, java.util.regex.Matcher.quoteReplacement(replacement));
          }
          matcher.appendTail(sb);
          
          if (count > 0) {
              // System.out.println("[WARNING] Fixed " + count + " array index type mismatches (double→int casting added)");
              // System.out.println("[WARNING] This is a workaround. Consider fixing array index types at generation time.");
          }
          
          return sb.toString();
      }

    private List<String> parseErrorImports(List<Diagnostic<? extends JavaFileObject>> errs) {
        Set<String> importsToRemove = new LinkedHashSet<>();
        // 정규표현식: "import"로 시작하고 ";"로 끝나는 모든 라인을 찾습니다.
        java.util.regex.Pattern importPattern = java.util.regex.Pattern.compile("^\\s*import\\s+.*;", java.util.regex.Pattern.MULTILINE);
    
        for (Diagnostic<? extends JavaFileObject> d : errs) {
            String errorMessage = d.toString();
            java.util.regex.Matcher matcher = importPattern.matcher(errorMessage);
            while (matcher.find()) {
                importsToRemove.add(matcher.group().trim());
            }
        }
        return new ArrayList<>(importsToRemove);
    }

    private String cleanImportStatements(String source, List<String> toRemove) {
        Set<String> toRemoveSet = new HashSet<>(toRemove);
        List<String> cleanedLines = new ArrayList<>();
        // 모든 종류의 개행 문자를 기준으로 분리합니다.
        for (String line : source.split("\\R")) { 
            if (!toRemoveSet.contains(line.trim())) {
                cleanedLines.add(line);
            }
        }
        return String.join(System.lineSeparator(), cleanedLines);
    }

    private boolean checkCompileError(List<Diagnostic<? extends JavaFileObject>> errorMessage) {
        for (Diagnostic e : errorMessage) {
            if (e.getKind() == Diagnostic.Kind.ERROR) { // Nov. 2021: added due to ambiguity error
                return false;
            }
        }
        return true;
    }

    private CtMethod handleTestcaseClass(CtClass<Object> testcase) {
        List<CtMethod> methods = testcase.getElements(new TypeFilter<>(CtMethod.class));
        CtMethod method = methods.get(0);
        
        // Only rename if method name is "test" (default name)
        // Otherwise keep the existing name (e.g., from RecursiveTestCaseGenerator)
        if ("test".equals(method.getSimpleName())) {
            String methodName = testcase.getSimpleName();
            method.setSimpleName(methodName);
        }
        
        return method;
    }

    private CtMethod handleTestcaseClassForPrim(CtClass<Object> testcase, String newMethodName) {
        String methodName = testcase.getSimpleName();
        List<CtMethod> methods = testcase.getElements(new TypeFilter<>(CtMethod.class));
        CtMethod method = methods.stream()
                .filter(m -> "mockTest".equals(m.getSimpleName()))
                .findFirst()
                .orElse(methods.get(0));
        method.setSimpleName(newMethodName);

        return method;
    }

    /**
     * Compile and create .class file
     *
     * @param fileName
     * @param content
     * @return
     */
    public static List<Diagnostic<? extends JavaFileObject>> compileWholeClassFile(String fileName, String content) {
        // init source code file
        JavaFileObject file = new Source(fileName, JavaFileObject.Kind.SOURCE, content);
        
        // Use shared compiler instance and reusable diagnostics collector
        DiagnosticCollector<JavaFileObject> diagnostics = getDiagnosticCollector();
        
        // Use shared compiler and options for better performance
        JavaCompiler.CompilationTask task = SHARED_COMPILER.getTask(null, null, diagnostics, 
                options.isEmpty() ? getCompilerOptions() : options, null, Arrays.asList(file));
        task.call();
        
        return new ArrayList<>(diagnostics.getDiagnostics()); // Return copy to avoid issues with reuse
    }

    public static List<Diagnostic<? extends JavaFileObject>> compileWholeClassFileForPrim(String fileName,
            String content) {
        // 1) in-memory JavaFileObject
        JavaFileObject file = new Source(fileName, JavaFileObject.Kind.SOURCE, content);

        // 2) Use shared compiler instance and reusable diagnostics collector
        DiagnosticCollector<JavaFileObject> diagnostics = getDiagnosticCollector();

        // 3) Create standard file manager - we'll use it directly without wrapping
        // because custom FileManager filtering doesn't work reliably in Java 8
        StandardJavaFileManager fileManager = SHARED_COMPILER.getStandardFileManager(diagnostics, null, null);

        // 4) Build compile options and modify classpath to exclude source directories
        boolean hasD = false;
        boolean hasCp = false;
        List<String> compileOptions = new java.util.ArrayList<>();

        for (int i = 0; i < options.size(); i++) {
            String opt = options.get(i);
            if ("-d".equals(opt)) {
                hasD = true;
                compileOptions.add(opt);
                if (i + 1 < options.size()) {
                    compileOptions.add(options.get(++i));
                }
            } else if ("-cp".equals(opt) || "-classpath".equals(opt)) {
                hasCp = true;
                compileOptions.add(opt);
                if (i + 1 < options.size()) {
                    String classpath = options.get(++i);
                    // Keep the original classpath - we'll rely on -implicit:none and -sourcepath
                    compileOptions.add(classpath);
                }
            } else {
                compileOptions.add(opt);
            }
        }

        // Keep the original output directory
        if (!hasD) {
            compileOptions.addAll(Arrays.asList("-d", System.getProperty("user.dir")));
        }

        // Add -implicit:none to prevent compiler from compiling implicitly referenced source files
        // This ensures only the explicitly provided in-memory file is compiled
        compileOptions.add("-implicit:none");

        // Set sourcepath to a non-existent directory to prevent searching for sources
        compileOptions.add("-sourcepath");
        compileOptions.add("/nonexistent_sourcepath_to_prevent_source_discovery");

        // 5) 컴파일 태스크 생성 & 실행 (use shared compiler)
        JavaCompiler.CompilationTask task = SHARED_COMPILER.getTask(null, fileManager, diagnostics, compileOptions, null,
                Arrays.asList(file));
        task.call();

        // 6) 출력 위치 로깅 (디버깅용, 필요시 주석 해제)
        // Iterable<? extends File> outs = fileManager.getLocation(StandardLocation.CLASS_OUTPUT);
        // if (outs != null) {
        //     for (File outDir : outs) {
        //         System.out.println(">> .class FILE DIR: " + outDir.getAbsolutePath());
        //     }
        // } else {
        //     System.out.println(">>Class OUTPUT Dir Undefined, user.dir: " + System.getProperty("user.dir"));
        // }

        // 7) 리소스 정리
        try {
            fileManager.close();
        } catch (Exception e) {
            // 무시하거나 로그로 남기기
        }

        return new ArrayList<>(diagnostics.getDiagnostics()); // Return copy to avoid issues with reuse
    }

    /**
     * init compile options
     */
    private void initCompileOptions() {
        // add class path
        options.add("-cp");
        options.add(Config.CLASS_PATH);
        // class output path
        options.add("-d");
        options.add(Config.BUILD_PATH + File.separator);
        // add encoding option to handle special characters
        options.add("-encoding");
        options.add("UTF-8");
    }

    public Result runCompiledTestCase(Pair<CtMethod, String> compiledTestAndStringPair) throws Exception {
        CtMethod testCase = compiledTestAndStringPair.getKey();
        String testCaseString = compiledTestAndStringPair.getValue();
        Class<?> clazz = null;
        try {
            String temp = packageNamePlusFileName(testCase.getSimpleName());
            clazz = ClassLoader.getSystemClassLoader().loadClass(packageNamePlusFileName(testCase.getSimpleName()));
        } catch (Exception e) {
            System.out.println(String.format("Load running class : %s failed.",
                    packageNamePlusFileName(testCase.getSimpleName())));
            // System.out.println(testCase.toString());
            // // e.printStackTrace();
        }
        // Runs Test Class without ParallelComputer to allow @Test(timeout) annotation to work
        // System.out.println("Running Test : \n"+clazz)

        // Run test with forced 1-second timeout wrapper to ensure termination
        // even if @Test(timeout=1000) annotation fails to work properly
        Result result = null;
        final Class<?> finalClazz = clazz;
        String testClassName = testCase.getSimpleName();
        java.util.concurrent.ExecutorService executor = java.util.concurrent.Executors.newSingleThreadExecutor();
        java.util.concurrent.Future<Result> future = executor.submit(() -> JUnitCore.runClasses(finalClazz));

        if(DEBUG_ORACLE_TRANSFORM){
            System.out.println("============================================");
            System.out.println("[ORACLE DEBUG] TEST : \n"+ testCase);
        }
        
        long testStartTime = System.currentTimeMillis();
        try {
            result = future.get(1050, java.util.concurrent.TimeUnit.MILLISECONDS);
            long testDuration = System.currentTimeMillis() - testStartTime;
            
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[OracleTransform] TEST EXECUTION COMPLETED - Duration: " + testDuration + "ms");
            }
            
            // DEBUG: Check Logger.observations immediately after test execution
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[OracleTransform] AFTER TEST EXECUTION - Logger.observations keys: " + 
                    RegressionOracles.RegressionUtil.Logger.observations.keySet());
                System.out.println("[OracleTransform] AFTER TEST EXECUTION - Logger.observations size: " + 
                    RegressionOracles.RegressionUtil.Logger.observations.size());
            }
        } catch (java.util.concurrent.TimeoutException e) {
            long testDuration = System.currentTimeMillis() - testStartTime;
            future.cancel(true);
            executor.shutdownNow();
            timedOutTestNameSet.add(testClassName);
            System.out.println("[TIMEOUT-WRAPPER] Test timed out after " + testDuration + "ms (1050ms wrapper limit): "
                    + testClassName);
            
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TIMEOUT-WRAPPER] Logger.observations at timeout - keys: " + 
                    RegressionOracles.RegressionUtil.Logger.observations.keySet());
                System.out.println("[TIMEOUT-WRAPPER] Logger.observations size: " + 
                    RegressionOracles.RegressionUtil.Logger.observations.size());
            }
            
            return new Result(); // Return empty result for timeout
        } catch (Exception e) {
            long testDuration = System.currentTimeMillis() - testStartTime;
            future.cancel(true);
            executor.shutdownNow();
            System.out.println("[EXECUTION-ERROR] Exception during test execution after " + testDuration + "ms: "
                    + e.getClass().getName());
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[EXECUTION-ERROR] Message: " + e.getMessage());
                e.printStackTrace();
            }
            return new Result(); // Return empty result for exception
        } finally {
             executor.shutdownNow();
             try {
                 if (!executor.awaitTermination(100, java.util.concurrent.TimeUnit.MILLISECONDS)) {
                     executor.shutdownNow();
                 }
              } catch (InterruptedException ie) {
                  executor.shutdownNow();
              }
              // [FIX] REGRESSION_MODE 또는 BUCKETING이 활성화된 경우 아직 지우면 안됨
              if (!Config.REGRESSION_MODE && !Config.ENABLE_TEST_BUCKETING) {
                  RegressionOracles.RegressionUtil.Logger.clearObservations();
              }
          }
          // [FIX] Minimization이 활성화된 경우에만 TestMinimizer 실행
          if (Config.ENABLE_TEST_MINIMIZATION || Config.ENABLE_TEST_BUCKETING) {
              if (this.testMinimizer == null) {
                  this.testMinimizer = new utils.TestMinimizer();
                  // [NEW] MUT 추출 설정 적용
                  this.testMinimizer.setEnableMUTExtraction(Config.ENABLE_MUT_EXTRACTION_IN_SIGNATURE);
              }

             if (!result.getFailures().isEmpty()) {
                 Failure firstFailure = result.getFailures().get(0);

                 // [FIX] Minimization이 활성화된 경우에만 중복 필터링
                 if (Config.ENABLE_TEST_MINIMIZATION && !testMinimizer.isUnique(firstFailure)) {
                     if (utils.Config.DEBUG_TEST_MINIMIZATION) {
                         System.out.println("\n[TestMinimizer] Duplicate Filtered (SeqC)");
                         System.out.println("Test Name: " + firstFailure.getTestHeader());

                         if (firstFailure.getException() != null) {
                             System.out.println("Exception: " + firstFailure.getException().getClass().getName());
                             System.out.println("Message:   " + firstFailure.getMessage());
                             System.out.println("--- Stack Trace (Filtered) ---");
                             for (StackTraceElement elem : firstFailure.getException().getStackTrace()) {
                                 System.out.println("  at " + elem.toString());
                             }
                         }
                         System.out.println("--------------------------------------------------\n");
                     }
                     return result;
                 } else if (Config.ENABLE_TEST_BUCKETING && !testMinimizer.isUnique(firstFailure)) {
                     // Bucketing 모드에서는 항상 true를 반환하므로 여기 도달 안 함
                     // 하지만 bucketing 정보는 수집됨
                 }
             }
         }
        
        for (Failure failure : result.getFailures()) {
             // System.out.println("Found Failure: " + failure.getTestHeader());
             String testName = failure.getTestHeader().split("\\(")[0];

             testNameToFailMap.put(testName, failure);
             if (Config.DEBUG_TEST_MINIMIZATION) {
                 System.out.println("\n========== [DEBUG: Failure StackTrace Analysis] ==========");
                 System.out.println("Test Name: " + failure.getTestHeader());
                 if (failure.getException() != null) {
                     System.out.println("Exception: " + failure.getException().getClass().getName());
                     System.out.println("Message:   " + failure.getMessage());
                     System.out.println("--- Stack Trace Elements ---");
                     for (StackTraceElement elem : failure.getException().getStackTrace()) {
                         System.out.println("  at " + elem.getClassName() + "." + elem.getMethodName()
                                 + "(" + elem.getFileName() + ":" + elem.getLineNumber() + ")");
                     }
                 }
                 System.out.println("==========================================================\n");
             }

             if (DEBUG_ORACLE_TRANSFORM && failure.getException() != null) {
                 System.out.println("[TEST_FAILURE] Test: " + testName);
                 System.out.println("[TEST_FAILURE] Exception: " + failure.getException().getClass().getName());
                 System.out.println("[TEST_FAILURE] Message: " + failure.getException().getMessage());
             }
             
             if (failure.getException() != null
                     && failure.getException().getMessage() != null
                     && failure.getException().getMessage().contains("test timed out after")) {
                 timedOutTestNameSet.add(testName);
                 System.out.println("[JUnit-TIMEOUT] " + failure.getException() + " | " + testCase.getSimpleName());

             }
         }
         // If NOT TimeOUT Exception
         if (!timedOutTestNameSet.contains(testCase.getSimpleName())) {
             if (DEBUG_ORACLE_TRANSFORM) System.out.println("[OracleTransform] Test NOT timed out: " + testCase.getSimpleName());
            Factory factory = new Launcher().getFactory();
            // Create Annotation
            CtAnnotationType testRefer = factory.createAnnotationType("Test");
            CtAnnotation<Annotation> testAnno = factory.createAnnotation();
            testAnno.setAnnotationType(testRefer.getReference());
            testAnno.addValue("timeout", 4000);
            List<CtAnnotation<? extends Annotation>> annotation = new LinkedList<>();
            annotation.add(testAnno);
            testCase.setAnnotations(annotation);
            testCaseString = testCaseString.replace("@org.junit.Test(timeout = 1000)",
                    "@org.junit.Test(timeout = 4000)");

   
            if (Config.REGRESSION_MODE) {
                    // if (DEBUG_ORACLE_TRANSFORM) System.out.println("[OracleTransform] Entering REGRESSION_MODE block");
                final Analyzer analyzer = new Analyzer();
                final CtClass testClass = testCase.getParent(CtClass.class);
                Map<CtMethod, List<CtLocalVariable>> localVariablesPerTestMethod = analyzer.analyze(testClass, false);
                Map<CtMethod, List<CtLocalVariable>> localVariablesPrimitive = analyzer.analyze(testClass, true);

                Launcher launcher = new Launcher();
                List<CtStatement> origStmts = new ArrayList<>();
                List<CtStatement> stmts = testCase.getBody().getStatements();

                for (CtStatement stmt : stmts) {
                    if (!stmt.clone().toString().contains("RegressionOracles.RegressionUtil.Logger.observe")) {
                        origStmts.add(stmt.clone());
                    }
                }
                testCase.getBody().setStatements(origStmts);

                List<String> oracleRemovedTestStringList = new ArrayList<>();

                for (String line : testCaseString.split("\n")) {
                    if (!line.contains("RegressionOracles.RegressionUtil.Logger.observe")) {
                        if (line.contains("// if statement for MUT null check"))
                            continue;
                        else {
                            // System.out.println(line);
                            oracleRemovedTestStringList.add(line);
                        }
                    }
                }
                String oracleRemovedTestString = String.join("\n", oracleRemovedTestStringList);
                
                
                // If This Test has failed before
                if (testNameToFailMap.containsKey(testCase.getSimpleName())) { // add try catch fail
                    // System.out.println("========================");
                    // System.out.println("Adding Try Catch for : "+testCase.getSimpleName());
                    
                    // Config 옵션에 따른 Oracle 생성 전략
                    if (Config.ENABLE_MULTIPLE_ORACLE_GEN) {
                        // [전략 1] 반복 실행 및 Oracle 재생성
                        Pair<CtMethod, String> multipleOracleResult = addTryCatchFailWithMultipleAttempts(
                            testCase, launcher, testClass
                        );
                        
                        if (multipleOracleResult != null) {
                            runnableTestStringList.add(fixSpecialConstants(multipleOracleResult.getValue()));
                            runnableTestList.add(multipleOracleResult.getKey());
                            numOfFailingTests++;
                        } else {
                            runnableTestList.add(testCase);
                            runnableTestStringList.add(fixSpecialConstants(testCase.toString()));
                        }
                    } else {
                        // [전략 2, 3] 기본 또는 전체 wrap (TryCatchFailAdder에서 처리)
                        // 실행 파일 전체 내용을 TryCatchFailAdder에 전달 (정확한 라인 매칭을 위해)
                        String executedFileContent = this.packageAndImport + testClass;
                        Pair<CtMethod, String> failAddedMethodAndStringPair = TryCatchFailAdder.addTryCatchFail(testCase,
                                testNameToFailMap.get(testCase.getSimpleName()), launcher, executedFileContent);
                        // Add Try Catch for the cause of failure
                        if (failAddedMethodAndStringPair != null) {
                            // try-catch가 추가된 최종 CtMethod 객체를 가져옵니다.
                            CtMethod failAdded = failAddedMethodAndStringPair.getKey();

                            // Spoon의 Pretty Printer를 사용해 최종 코드를 한 번에 생성합니다.
                            String outputMethodString = failAdded.toString();           
                            // System.out.println("outputMethodString: \n" + outputMethodString);

                            // 수정된 메서드를 리스트에 추가합니다.
                            runnableTestStringList.add(fixSpecialConstants(outputMethodString));
                            runnableTestList.add(failAdded);
                            numOfFailingTests++;

                        } else {
                            runnableTestList.add(testCase);
                            runnableTestStringList.add(fixSpecialConstants(testCase.toString()));
                            // System.out.println("WARNING: no try catch fail is added for " +
                            // testCase.getSimpleName());
                            // System.out.println("==================================");
                        }
                    }
                } 
                else { // add regression assertions
                    if (DEBUG_ORACLE_TRANSFORM) {
                        System.out.println("[Oracle] === ADDING ASSERTIONS ===");
                        System.out.println("[Oracle] localVariablesPerTestMethod keys: " + localVariablesPerTestMethod.keySet());
                        System.out.println("[Oracle] localVariablesPrimitive keys: " + localVariablesPrimitive.keySet());
                    }
                    
                    // Config 옵션에 따른 Assertion 생성 전략
                    if (Config.ENABLE_MULTIPLE_ORACLE_GEN) {
                        // [전략 1] 반복 실행 및 Assertion 검증
                        Pair<CtMethod, String> assertionResult = addAssertionsWithMultipleAttempts(
                            testCase, launcher, testClass, localVariablesPerTestMethod, localVariablesPrimitive
                        );
                        
                        if (assertionResult != null && assertionResult.getKey() != null) {
                            numOfPassingTests++;
                            runnableTestList.add(assertionResult.getKey());
                            runnableTestStringList.add(assertionResult.getValue());
                            if (DEBUG_ORACLE_TRANSFORM) System.out.println("[Oracle] Assertions VERIFIED successfully");
                        } else {
                            runnableTestList.add(testCase);
                            runnableTestStringList.add(fixSpecialConstants(testCase.toString()));
                            if (DEBUG_ORACLE_TRANSFORM) System.out.println("[Oracle] WARNING: assertion verification failed for " + testCase.getSimpleName());
                        }
                    } else {
                        final AssertionAdder assertionAdder = new AssertionAdder(launcher.getFactory());
                        CtMethod assertionAdded = assertionAdder.addAssertion(testCase, localVariablesPerTestMethod,
                                localVariablesPrimitive);
                        
                        if (DEBUG_ORACLE_TRANSFORM) {
                            System.out.println("[Oracle] AssertionAdder.addAssertion returned: " + (assertionAdded != null ? "non-null" : "null"));
                        }
                        
                        if (assertionAdded != null) {

                            // Spoon의 pretty printer를 사용해 전체 메서드 코드를 한번에 생성합니다.
                            // 이 방법이 훨씬 안정적이고 정확합니다.
                            String outputMethodString = assertionAdded.toString();
                            // System.out.println("outputMethodString: \n" + outputMethodString);
                            // 나머지 로직
                            numOfPassingTests++;
                            runnableTestList.add(assertionAdded);
                            runnableTestStringList.add(fixSpecialConstants(outputMethodString));
                            if (DEBUG_ORACLE_TRANSFORM) System.out.println("[Oracle] Assertions ADDED successfully");
                        } else {
                            runnableTestList.add(testCase);
                            runnableTestStringList.add(fixSpecialConstants(testCase.toString()));
                            if (DEBUG_ORACLE_TRANSFORM) System.out.println("[Oracle] WARNING: no assertion is added for " + testCase.getSimpleName());
                        }
                    }
                }
                
                RegressionOracles.RegressionUtil.Logger.clearObservations();
            } else {
                if(Config.REMOVE_PASSING_TESTS){
                    if (testNameToFailMap.containsKey(testCase.getSimpleName())) {
                        runnableTestStringList.add(fixSpecialConstants(testCase.toString()));
                    }
                }else{
                    runnableTestStringList.add(fixSpecialConstants(testCase.toString()));
                }
                
                
            }
        }
        return result;
    }

    public CtMethod runCompiledTestCaseForPrim(Pair<CtMethod, String> compiledTestAndStringPair) throws Exception {
        CtMethod testCase = compiledTestAndStringPair.getKey();
        String testCaseString = compiledTestAndStringPair.getValue();

        // Get class name from the test method's parent class
        String className = testCase.getParent(CtClass.class).getSimpleName();

        Class<?> clazz = null;
        try {
            clazz = ClassLoader.getSystemClassLoader().loadClass(packageNamePlusFileName(className));
        } catch (Exception e) {
            System.out.println(String.format("Load running class : %s failed.",
                    packageNamePlusFileName(className)));
        }
        // Runs Test Class without ParallelComputer to allow @Test(timeout) annotation to work
        CtClass<?> ctClass = testCase.getParent(CtClass.class);
        // System.out.println("Running Test : \n" + clazz);
        // System.out.println(this.packageAndImport+ctClass);

        // Run test with forced 1050ms timeout wrapper to ensure termination
        // even if @Test(timeout=1000) annotation fails to work properly
        Result result = null;
        final Class<?> finalClazz = clazz;
        java.util.concurrent.ExecutorService executor = java.util.concurrent.Executors.newSingleThreadExecutor();
         java.util.concurrent.Future<Result> future = executor.submit(() -> JUnitCore.runClasses(finalClazz));

         if(DEBUG_ORACLE_TRANSFORM){
             System.out.println("============================================");
             System.out.println("[ORACLE DEBUG-Prim] TEST : \n"+ this.packageAndImport + ctClass);
             System.out.println("============================================");
         }
        

         long testStartTime = System.currentTimeMillis();
        try {
            result = future.get(1050, java.util.concurrent.TimeUnit.MILLISECONDS);
            long testDuration = System.currentTimeMillis() - testStartTime;
            
            
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[OracleTransform-Prim] TEST EXECUTION COMPLETED - Duration: " + testDuration + "ms");
            }
            
            // DEBUG: Check Logger.observations immediately after test execution
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[OracleTransform-Prim] AFTER TEST EXECUTION - Logger.observations keys: " + 
                    RegressionOracles.RegressionUtil.Logger.observations.keySet());
                System.out.println("[OracleTransform-Prim] AFTER TEST EXECUTION - Logger.observations size: " + 
                    RegressionOracles.RegressionUtil.Logger.observations.size());
            }
            // DEBUG: Check Logger.observations immediately after test execution
        } catch (java.util.concurrent.TimeoutException e) {
            long testDuration = System.currentTimeMillis() - testStartTime;
            future.cancel(true);
            executor.shutdownNow();
            timedOutTestNameSet.add(className);
            System.out.println("[TIMEOUT-WRAPPER-Prim] Test timed out after " + testDuration + "ms (1050ms wrapper limit): " + className);
            System.out.println("[TIMEOUT-WRAPPER-Prim] This likely means the test exceeded 1000ms AND wrapper couldn't get result in 1050ms");
            System.out.println("[TIMEOUT-WRAPPER-Prim] Possible causes: Logger.observe() operations, object toString() calls, or infinite loops");
            
            
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TIMEOUT-WRAPPER-Prim] Logger.observations at timeout - keys: " + 
                    RegressionOracles.RegressionUtil.Logger.observations.keySet());
                System.out.println("[TIMEOUT-WRAPPER-Prim] Logger.observations size: " + 
                    RegressionOracles.RegressionUtil.Logger.observations.size());
            }
            
            return null;
        } catch (Exception e) {
            long testDuration = System.currentTimeMillis() - testStartTime;
            future.cancel(true);
            executor.shutdownNow();
            System.out.println("[EXECUTION-ERROR-Prim] Exception during test execution after " + testDuration + "ms: "
                    + e.getClass().getName());
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[EXECUTION-ERROR-Prim] Message: " + e.getMessage());
                e.printStackTrace();
            }
            return null;
        } finally {
             executor.shutdownNow();
             try {
                 if (!executor.awaitTermination(100, java.util.concurrent.TimeUnit.MILLISECONDS)) {
                     executor.shutdownNow();
                 }
              } catch (InterruptedException ie) {
                  executor.shutdownNow();
              }
              // [FIX] REGRESSION_MODE 또는 BUCKETING이 활성화된 경우 아직 지우면 안됨
              if (!Config.REGRESSION_MODE && !Config.ENABLE_TEST_BUCKETING) {
                  RegressionOracles.RegressionUtil.Logger.clearObservations();
              }
          }

           // [FIX] Minimization이 활성화된 경우에만 TestMinimizer 실행
        if (Config.ENABLE_TEST_MINIMIZATION || Config.ENABLE_TEST_BUCKETING) {
            if (this.testMinimizer == null) {
                this.testMinimizer = new utils.TestMinimizer();
                // [NEW] MUT 추출 설정 적용
                this.testMinimizer.setEnableMUTExtraction(Config.ENABLE_MUT_EXTRACTION_IN_SIGNATURE);
            }

            if (!result.getFailures().isEmpty()) {
                Failure firstFailure = result.getFailures().get(0);

                // [FIX] Minimization이 활성화된 경우에만 중복 필터링
                if (Config.ENABLE_TEST_MINIMIZATION && !testMinimizer.isUnique(firstFailure)) {
                    if (utils.Config.DEBUG_TEST_MINIMIZATION) {
                        System.out.println("\n[TestMinimizer] Duplicate Filtered (SeqP)");
                        System.out.println("Test Name: " + firstFailure.getTestHeader());

                        if (firstFailure.getException() != null) {
                            System.out.println("Exception: " + firstFailure.getException().getClass().getName());
                            System.out.println("Message:   " + firstFailure.getMessage());
                            System.out.println("--- Stack Trace (Filtered) ---");
                            for (StackTraceElement elem : firstFailure.getException().getStackTrace()) {
                                System.out.println("  at " + elem.toString());
                            }
                        }
                        System.out.println("--------------------------------------------------\n");
                    }
                    return null;
                } else if (Config.ENABLE_TEST_BUCKETING && !testMinimizer.isUnique(firstFailure)) {
                    // Bucketing 모드에서는 항상 true를 반환하므로 여기 도달 안 함
                    // 하지만 bucketing 정보는 수집됨
                }
            }
        }
        


        for (Failure failure : result.getFailures()) {
            String testName = failure.getTestHeader().split("\\(")[0];
            testNameToFailMap.put(testName, failure);
            
            // DEBUG: Print all test failures to see if Logger.observe is causing issues

            if (Config.DEBUG_TEST_MINIMIZATION) {
                System.out.println("\n========== [DEBUG: Failure StackTrace Analysis] ==========");
                System.out.println("Test Name: " + failure.getTestHeader());
                if (failure.getException() != null) {
                    System.out.println("Exception: " + failure.getException().getClass().getName());
                    System.out.println("Message:   " + failure.getMessage());
                    System.out.println("--- Stack Trace Elements ---");
                    for (StackTraceElement elem : failure.getException().getStackTrace()) {
                        System.out.println("  at " + elem.getClassName() + "." + elem.getMethodName()
                                + "(" + elem.getFileName() + ":" + elem.getLineNumber() + ")");
                    }
                }
                System.out.println("==========================================================\n");
            }

            if (DEBUG_ORACLE_TRANSFORM && failure.getException() != null) {
                System.out.println("[TEST_FAILURE-Prim] Test: " + testName);
                System.out.println("[TEST_FAILURE-Prim] Exception: " + failure.getException().getClass().getName());
                System.out.println("[TEST_FAILURE-Prim] Message: " + failure.getException().getMessage());
            }
            
            if (failure.getException() != null
                    && failure.getException().getMessage() != null
                    && failure.getException().getMessage().contains("test timed out after")) {
                timedOutTestNameSet.add(className);
                System.out.println("[JUnit-TIMEOUT-Prim] " + failure.getException() + " | " + className);
            }
        }
        if (timedOutTestNameSet.contains(className)) {
             return null; // 타임아웃된 테스트는 null 반환
        }
         
         // Timeout을 항상 4000으로 설정 (dynamic execution과는 별개)
        if (!timedOutTestNameSet.contains(className)) {
             Factory factory = new Launcher().getFactory();
             // Create Annotation
             CtAnnotationType testRefer = factory.createAnnotationType("Test");
             CtAnnotation<Annotation> testAnno = factory.createAnnotation();
             testAnno.setAnnotationType(testRefer.getReference());
             testAnno.addValue("timeout", 4000);
             List<CtAnnotation<? extends Annotation>> annotation = new LinkedList<>();
             annotation.add(testAnno);
             testCase.setAnnotations(annotation);
             testCaseString = testCaseString.replace("@org.junit.Test(timeout = 1000)",
                     "@org.junit.Test(timeout = 4000)");
        }
         
        if (!Config.REGRESSION_MODE) {
            if(Config.REMOVE_PASSING_TESTS){
                if(testNameToFailMap.containsKey(testCase.getSimpleName())){
                    runnableTestList.add(testCase);
                    return testCase; 
                }else{
                    isPassing = true;
                    return null;
                }
            }else{
                runnableTestList.add(testCase);
                return testCase; 
            }
        }
         // If NOT TimeOUT Exception
        if (!timedOutTestNameSet.contains(className)) {

            if (DEBUG_ORACLE_TRANSFORM) System.out.println("[OracleTransform] Config.REGRESSION_MODE = " + Config.REGRESSION_MODE);
            if (Config.REGRESSION_MODE) {
                    // if (DEBUG_ORACLE_TRANSFORM) System.out.println("[OracleTransform] Entering REGRESSION_MODE block");
                final Analyzer analyzer = new Analyzer();
                final CtClass testClass = testCase.getParent(CtClass.class);
                Map<CtMethod, List<CtLocalVariable>> localVariablesPerTestMethod = analyzer.analyze(testClass, false);
                Map<CtMethod, List<CtLocalVariable>> localVariablesPrimitive = analyzer.analyze(testClass, true);

                Launcher launcher = new Launcher();
                List<CtStatement> origStmts = new ArrayList<>();
                List<CtStatement> stmts = testCase.getBody().getStatements();

                for (CtStatement stmt : stmts) {
                    if (!stmt.clone().toString().contains("RegressionOracles.RegressionUtil.Logger.observe")) {
                        origStmts.add(stmt.clone());
                    }
                }
                testCase.getBody().setStatements(origStmts);


                if (testNameToFailMap.containsKey(testCase.getSimpleName())) { // add try catch fail
                    // Config 옵션에 따른 Oracle 생성 전략
                    if (Config.ENABLE_MULTIPLE_ORACLE_GEN) {
                        // [전략 1] 반복 실행 및 Oracle 재생성
                        CtMethod multipleOracleMethod = addTryCatchFailWithMultipleAttemptsForPrim(
                            testCase, launcher, ctClass
                        );
                        
                        if (multipleOracleMethod != null) {
                            runnableTestList.add(multipleOracleMethod);
                            return multipleOracleMethod;
                        }
                    } else {
                        // [전략 2, 3] 기본 또는 전체 wrap (TryCatchFailAdder에서 처리)
                        // 실행 파일 전체 내용을 TryCatchFailAdder에 전달 (정확한 라인 매칭을 위해)
                        String executedFileContent = this.packageAndImport + ctClass;
                        Pair<CtMethod, String> failAddedPair = TryCatchFailAdder.addTryCatchFail(testCase,
                                testNameToFailMap.get(testCase.getSimpleName()), launcher, executedFileContent);
                        if (failAddedPair != null) {
                            CtMethod failAddedMethod = failAddedPair.getKey();
                            runnableTestList.add(failAddedMethod);
                            return failAddedMethod;
                        }
                    }
                }
                else { // add regression assertions
                    // Config 옵션에 따른 Assertion 생성 전략
                    if (Config.ENABLE_MULTIPLE_ORACLE_GEN) {
                        // [전략 1] 반복 실행 및 Assertion 검증
                        CtMethod assertionResult = addAssertionsWithMultipleAttemptsForPrim(
                            testCase, launcher, ctClass, localVariablesPerTestMethod, localVariablesPrimitive
                        );
                        
                        if (assertionResult != null) {
                            return assertionResult;
                        } else {
                            runnableTestList.add(testCase);
                            return testCase;
                        }
                    } else {
                        // [기본 전략] 기존 로직 - 한번만 추가하고 검증 안함
                        final AssertionAdder assertionAdder = new AssertionAdder(launcher.getFactory());
                        CtMethod assertionAdded = assertionAdder.addAssertion(testCase, localVariablesPerTestMethod,
                                localVariablesPrimitive);
                        
                        if (assertionAdded != null) {
                            runnableTestList.add(assertionAdded);
                            return assertionAdded;
                        } else {
                            runnableTestList.add(testCase);
                            return testCase;
                        }
                    }
                }
                
                // [FIX] REGRESSION_MODE 블록이 완료된 후에 Logger.observations 지우기
                RegressionOracles.RegressionUtil.Logger.clearObservations();
            }
        }

        runnableTestList.add(testCase);
        return testCase;
    }

    /**
     * [전략 1] runCompiledTestCase용 반복 실행 및 Oracle 재생성
     * 테스트가 성공할 때까지 반복 실행하면서 각 실패마다 Oracle 추가
     */
    private Pair<CtMethod, String> addTryCatchFailWithMultipleAttempts(
            CtMethod testCase, Launcher launcher, CtClass<?> testClass) {
        
        final boolean DEBUG = DEBUG_ORACLE_TRANSFORM;
        
        int maxAttempts = Config.MULTIPLE_ORACLE_MAX_ITERATIONS != null ? 
                          Config.MULTIPLE_ORACLE_MAX_ITERATIONS : 5;  // 기본값 5회
        int attemptCount = 0;
        CtMethod currentTestMethod = testCase.clone();
        
        // [NEW] 같은 에러가 반복되는지 감지
        String previousErrorSignature = null;
        int sameErrorCount = 0;
        
        if (DEBUG) {
            System.out.println("\n╔════════════════════════════════════════════════════════════╗");
            System.out.println("║   [MultipleOracleGen-seqc] Starting Repeat Compilation     ║");
            System.out.println("╚════════════════════════════════════════════════════════════╝");
            System.out.println("[MultipleOracleGen] Test method: " + testCase.getSimpleName());
            System.out.println("[MultipleOracleGen] Max attempts: " + maxAttempts);
            System.out.println("[MultipleOracleGen] Config.ENABLE_MULTIPLE_ORACLE_GEN: " + Config.ENABLE_MULTIPLE_ORACLE_GEN);
            System.out.println("[MultipleOracleGen] Config.MULTIPLE_ORACLE_MAX_ITERATIONS: " + Config.MULTIPLE_ORACLE_MAX_ITERATIONS);
        }
        System.out.println("[Compiler-MultipleOracleGen] Starting multiple oracle generation for: " + testCase.getSimpleName());
        System.out.println("[Compiler-MultipleOracleGen] Max attempts: " + maxAttempts);
        
        while (attemptCount < maxAttempts) {
            attemptCount++;
            
            if (DEBUG) {
                System.out.println("\n┌──────────────────────────────────────────────────────────┐");
                System.out.println("│ [Attempt " + attemptCount + "/" + maxAttempts + "]");
                System.out.println("└──────────────────────────────────────────────────────────┘");
            }
            
            // [1] 테스트 실행 - 클래스 로드
            Class<?> clazz = null;
            String className = packageNamePlusFileName(currentTestMethod.getSimpleName());
            
            try {
                if (DEBUG) {
                    System.out.println("[MultipleOracleGen] ├─ [Step 1] Loading compiled class");
                    System.out.println("[MultipleOracleGen] │  Class name: " + className);
                }
                
                // [CRITICAL FIX] SystemClassLoader는 캐시하므로 업데이트된 .class를 로드하지 못함!
                // Child-First ClassLoader를 사용하여 BUILD_PATH를 먼저 검색
                
                final String targetClassName = className;
                java.net.URL buildPathURL = new java.io.File(Config.BUILD_PATH).toURI().toURL();
                
                // Child-First URLClassLoader
                java.net.URLClassLoader newClassLoader = new java.net.URLClassLoader(
                    new java.net.URL[]{buildPathURL}, 
                    ClassLoader.getSystemClassLoader()
                ) {
                    @Override
                    public Class<?> loadClass(String name) throws ClassNotFoundException {
                        // 테스트 클래스는 child-first (BUILD_PATH 우선)
                        if (name.equals(targetClassName)) {
                            try {
                                // 먼저 이 ClassLoader에서 찾기 시도
                                return findClass(name);
                            } catch (ClassNotFoundException e) {
                                // 못 찾으면 parent에게 위임
                                return super.loadClass(name);
                            }
                        }
                        // 다른 클래스들(JUnit, Jsoup 등)은 parent-first (기본 동작)
                        return super.loadClass(name);
                    }
                };
                
                clazz = newClassLoader.loadClass(targetClassName);
                
                if (DEBUG) {
                    System.out.println("[MultipleOracleGen] │  ✓ Class loaded successfully with Child-First ClassLoader");
                    System.out.println("[MultipleOracleGen] │    ClassLoader: " + newClassLoader.toString());
                }
            } catch (Exception e) {
                if (DEBUG) {
                    System.out.println("[MultipleOracleGen] │  ✗ ClassLoadError: " + e.getClass().getSimpleName());
                    System.out.println("[MultipleOracleGen] │  Message: " + e.getMessage());
                }
                System.out.println("[Compiler-MultipleOracleGen] Failed to load class: " + e.getMessage());
                break;
            }
            
            // [2] JUnit 실행
            Result result = null;
            final Class<?> finalClazz = clazz;
            
            if (DEBUG) {
                System.out.println("[MultipleOracleGen] ├─ [Step 2] Executing JUnit test");
            }
            
            long testStartTime = System.currentTimeMillis();
            java.util.concurrent.ExecutorService executor = java.util.concurrent.Executors.newSingleThreadExecutor();
            java.util.concurrent.Future<Result> future = executor.submit(() -> JUnitCore.runClasses(finalClazz));
            
            try {
                result = future.get(1050, java.util.concurrent.TimeUnit.MILLISECONDS);
                long testDuration = System.currentTimeMillis() - testStartTime;
                
                if (DEBUG) {
                    System.out.println("[MultipleOracleGen] │  ✓ Test execution completed");
                    System.out.println("[MultipleOracleGen] │  Duration: " + testDuration + "ms");
                }
            } catch (java.util.concurrent.TimeoutException e) {
                if (DEBUG) {
                    System.out.println("[MultipleOracleGen] │  ✗ TimeoutException: Test exceeded 1050ms");
                }
                System.out.println("[Compiler-MultipleOracleGen] Test execution timed out");
                executor.shutdownNow();
                break;
            } catch (Exception e) {
                if (DEBUG) {
                    System.out.println("[MultipleOracleGen] │  ✗ Exception: " + e.getClass().getSimpleName());
                    System.out.println("[MultipleOracleGen] │  Message: " + e.getMessage());
                }
                System.out.println("[Compiler-MultipleOracleGen] Test execution failed: " + e.getMessage());
                executor.shutdownNow();
                break;
            } finally {
                 executor.shutdownNow();
                 try {
                     if (!executor.awaitTermination(100, java.util.concurrent.TimeUnit.MILLISECONDS)) {
                         executor.shutdownNow();
                     }
                 } catch (InterruptedException ie) {
                     executor.shutdownNow();
                 }
                 // Clear observations to prevent memory leak
                 RegressionOracles.RegressionUtil.Logger.clearObservations();
             }
            
            // [3] 결과 확인
            if (DEBUG) {
                System.out.println("[MultipleOracleGen] ├─ [Step 3] Analyzing test result");
                System.out.println("[MultipleOracleGen] │  Total run: " + result.getRunCount());
                System.out.println("[MultipleOracleGen] │  Failures: " + result.getFailures().size());
                System.out.println("[MultipleOracleGen] │  Ignores: " + result.getIgnoreCount());
            }
            
            if (result.getFailures().isEmpty()) {
                if (DEBUG) {
                    System.out.println("[MultipleOracleGen] └─ ✓✓✓ Test PASSED ✓✓✓");
                    System.out.println("[MultipleOracleGen]");
                    System.out.println("[MultipleOracleGen] SUCCESS! Oracles generated successfully in " + attemptCount + " attempt(s)");
                    System.out.println("[MultipleOracleGen] Final test method is ready");
                }
                System.out.println("[Compiler-MultipleOracleGen] ✓ Test PASSED on attempt " + attemptCount);
                System.out.println("[Compiler-MultipleOracleGen] Successfully generated oracles in " + attemptCount + " attempt(s)");
                return new Pair<>(currentTestMethod, currentTestMethod.toString());
            }
            
             // [4] 실패 시 Oracle 추가
             Failure failure = result.getFailures().get(0);
             String failureException = failure.getException() != null ? 
                     failure.getException().getClass().getName() : "Unknown";
             String failureMsg = failure.getException() != null && failure.getException().getMessage() != null ?
                     failure.getException().getMessage() : "No message";
             
             // [NEW] 같은 에러 반복 감지
             String currentErrorSignature = failureException + "::" + failureMsg;
             if (currentErrorSignature.equals(previousErrorSignature)) {
                 sameErrorCount++;
                 if (DEBUG) {
                     System.out.println("[MultipleOracleGen] └─ ✗ Test FAILED (Same error as before #" + sameErrorCount + ")");
                 }
                 // 같은 에러가 2회 반복되면 더 이상 진행 불가
                 if (sameErrorCount >= 2) {
                     if (DEBUG) {
                         System.out.println("[MultipleOracleGen] ✗✗✗ Same error repeated - Cannot find more crash points");
                         System.out.println("[MultipleOracleGen] Breaking loop to prevent infinite retry");
                     }
                     System.out.println("[Compiler-MultipleOracleGen] Same error repeated, breaking loop");
                     break;
                 }
             } else {
                 previousErrorSignature = currentErrorSignature;
                 sameErrorCount = 0;
             }
             
             if (DEBUG) {
                 System.out.println("[MultipleOracleGen] └─ ✗ Test FAILED");
                 System.out.println("[MultipleOracleGen]");
                 System.out.println("[MultipleOracleGen] ├─ [Step 4] Adding Oracle");
                 System.out.println("[MultipleOracleGen] │  Exception: " + failureException);
                 if (failureMsg.length() > 80) {
                     System.out.println("[MultipleOracleGen] │  Message: " + failureMsg.substring(0, 80) + "...");
                 } else {
                     System.out.println("[MultipleOracleGen] │  Message: " + failureMsg);
                 }
                 
                 // 상세한 StackTrace 출력
                 if (failure.getException() != null && failure.getException().getStackTrace() != null) {
                     System.out.println("[MultipleOracleGen] │  Stack trace details:");
                     StackTraceElement[] stackTrace = failure.getException().getStackTrace();
                     for (int i = 0; i < Math.min(stackTrace.length, 10); i++) {
                         StackTraceElement elem = stackTrace[i];
                         System.out.println("[MultipleOracleGen] │    [" + i + "] " + elem.getClassName() + "." + 
                             elem.getMethodName() + ":" + elem.getLineNumber());
                     }
                     if (stackTrace.length > 10) {
                         System.out.println("[MultipleOracleGen] │    ... (" + (stackTrace.length - 10) + " more frames)");
                     }
                 }
             }
            
            String executedContent = this.packageAndImport + testClass;
            
            if (DEBUG) {
                System.out.println("[MultipleOracleGen] │  Calling TryCatchFailAdder.addTryCatchFail()...");
            }
            
            Pair<CtMethod, String> oracleResult = TryCatchFailAdder.addTryCatchFail(
                currentTestMethod, failure, launcher, executedContent
            );
            
            if (oracleResult != null) {
                currentTestMethod = oracleResult.getKey().clone();
                if (DEBUG) {
                    System.out.println("[MultipleOracleGen] │  ✓ Oracle added successfully");
                    System.out.println("[MultipleOracleGen] │  Total oracles added so far: " + attemptCount);
                }
                
                // [CRITICAL] Oracle 추가 후 Skeletal class(메가 클래스) 업데이트 및 재컴파일!
                if (DEBUG) {
                    System.out.println("[MultipleOracleGen] │  ═══════════════════════════════════════════════════════");
                    System.out.println("[MultipleOracleGen] │  Updating Skeletal class and recompiling...");
                    System.out.println("[MultipleOracleGen] │  ═══════════════════════════════════════════════════════");
                }
                
                try {
                    // Step 1: Skeletal class에서 기존 메서드 제거 및 새 메서드 추가
                    if (DEBUG) {
                        System.out.println("[MultipleOracleGen] │  [STEP 1] Cloning and updating Skeletal class");
                        System.out.println("[MultipleOracleGen] │  Original class: " + testClass.getQualifiedName());
                    }
                    
                    CtClass<?> skeletalClass = testClass.clone();
                    if (DEBUG) {
                        System.out.println("[MultipleOracleGen] │  ✓ Skeletal class cloned");
                    }
                    
                    // 기존 메서드 제거
                    int methodCountBefore = skeletalClass.getMethods().size();
                    try {
                        CtMethod oldMethod = skeletalClass.getMethod(currentTestMethod.getSimpleName());
                        if (DEBUG) {
                            System.out.println("[MultipleOracleGen] │  Found existing method: " + currentTestMethod.getSimpleName());
                            System.out.println("[MultipleOracleGen] │  Method signature (before): " + oldMethod.getSignature());
                        }
                        skeletalClass.removeMethod(oldMethod);
                        if (DEBUG) {
                            System.out.println("[MultipleOracleGen] │  ✓ Old method removed");
                        }
                    } catch (Exception e) {
                        if (DEBUG) {
                            System.out.println("[MultipleOracleGen] │  ⚠ No existing method found (first time): " + e.getMessage());
                        }
                    }
                    
                    // 새 메서드 추가 (oracle이 포함된)
                    skeletalClass.addMethod(currentTestMethod);
                    int methodCountAfter = skeletalClass.getMethods().size();
                    
                    if (DEBUG) {
                        System.out.println("[MultipleOracleGen] │  ✓ New method added");
                        System.out.println("[MultipleOracleGen] │  Method count: " + methodCountBefore + " → " + methodCountAfter);
                        System.out.println("[MultipleOracleGen] │  New method signature: " + currentTestMethod.getSignature());
                        
                        // 메서드 본문 길이 확인
                        String methodBody = currentTestMethod.getBody().toString();
                        int lineCount = methodBody.split("\n").length;
                        System.out.println("[MultipleOracleGen] │  New method body lines: " + lineCount);
                        System.out.println("[MultipleOracleGen] │  Contains try-catch: " + methodBody.contains("try {"));
                    }
                    
                    // [CRITICAL] testClass도 업데이트 (다음 iteration을 위해)
                    try {
                        CtMethod oldMethodInTestClass = testClass.getMethod(currentTestMethod.getSimpleName());
                        testClass.removeMethod(oldMethodInTestClass);
                    } catch (Exception e) {
                        // 메서드 없으면 무시
                    }
                    testClass.addMethod(currentTestMethod.clone());
                    
                    if (DEBUG) {
                        System.out.println("[MultipleOracleGen] │  ✓ Original testClass also updated for next iteration");
                        
                        // 메서드 본문 미리보기
                        String methodBody = currentTestMethod.toString();
                        String[] methodLines = methodBody.split("\n");
                        System.out.println("[MultipleOracleGen] │  ─── Method Preview (first 20 lines) ───");
                        for (int i = 0; i < Math.min(20, methodLines.length); i++) {
                            System.out.println("[MultipleOracleGen] │    " + methodLines[i]);
                        }
                        if (methodLines.length > 20) {
                            System.out.println("[MultipleOracleGen] │    ... (" + (methodLines.length - 20) + " more lines)");
                        }
                        System.out.println("[MultipleOracleGen] │  ─────────────────────────");
                    }
                    
                    // Step 2: 메모리에서 컴파일 (파일 저장하지 않음!)
                    if (DEBUG) {
                        System.out.println("[MultipleOracleGen] │  ───────────────────────────────────────────────────────");
                        System.out.println("[MultipleOracleGen] │  [STEP 2] Compiling in-memory (no file I/O)");
                    }
                    
                    // [CRITICAL FIX] skeletalClass.toString()은 package/import를 포함하지 않음!
                    // packageAndImport를 앞에 추가해야 함
                    String classContent = this.packageAndImport + skeletalClass.toString();
                    
                    if (DEBUG) {
                        System.out.println("[MultipleOracleGen] │  ═══════════════════════════════════════════════════════");
                        System.out.println("[MultipleOracleGen] │  [DEBUG] Full class content to be compiled:");
                        System.out.println("[MultipleOracleGen] │  ═══════════════════════════════════════════════════════");
                        String[] lines = classContent.split("\n");
                        for (int i = 0; i < Math.min(30, lines.length); i++) {
                            System.out.println(String.format("[MultipleOracleGen] │  %3d: %s", i + 1, lines[i]));
                        }
                        if (lines.length > 30) {
                            System.out.println("[MultipleOracleGen] │  ... (" + (lines.length - 30) + " more lines)");
                        }
                        System.out.println("[MultipleOracleGen] │  ═══════════════════════════════════════════════════════");
                        System.out.println("[MultipleOracleGen] │  Total lines: " + lines.length);
                    }
                    
                    // Step 3: In-memory 컴파일 (compileWholeClassFile 사용)
                    if (DEBUG) {
                        System.out.println("[MultipleOracleGen] │  ───────────────────────────────────────────────────────");
                        System.out.println("[MultipleOracleGen] │  [STEP 3] In-memory compilation");
                    }
                    
                    String compileClassName = skeletalClass.getSimpleName();
                    List<Diagnostic<? extends JavaFileObject>> diagnostics = 
                        compileWholeClassFile(compileClassName, classContent);
                    
                    boolean compilationSuccess = checkCompileError(diagnostics);
                    
                    if (DEBUG) {
                        if (compilationSuccess) {
                            System.out.println("[MultipleOracleGen] │  ✓ Compilation successful");
                            
                            // [DEBUG] .class 파일이 실제로 생성되었는지 확인
                            String classQualifiedName = skeletalClass.getQualifiedName();
                            String packagePath = classQualifiedName.replace('.', File.separatorChar);
                            String expectedClassPath = Config.BUILD_PATH + File.separator + packagePath + ".class";
                            File classFile = new File(expectedClassPath);
                            
                            System.out.println("[MultipleOracleGen] │  [DEBUG] Checking .class file:");
                            System.out.println("[MultipleOracleGen] │    Expected path: " + expectedClassPath);
                            System.out.println("[MultipleOracleGen] │    File exists: " + classFile.exists());
                            if (classFile.exists()) {
                                System.out.println("[MultipleOracleGen] │    File size: " + classFile.length() + " bytes");
                                System.out.println("[MultipleOracleGen] │    Last modified: " + new java.util.Date(classFile.lastModified()));
                            } else {
                                System.out.println("[MultipleOracleGen] │    ⚠ WARNING: .class file NOT FOUND!");
                                System.out.println("[MultipleOracleGen] │    Compile options used:");
                                for (String opt : options) {
                                    System.out.println("[MultipleOracleGen] │      " + opt);
                                }
                            }
                        } else {
                            System.out.println("[MultipleOracleGen] │  ⚠ Compilation failed");
                            System.out.println("[MultipleOracleGen] │  ─── Compilation Errors ───");
                            for (Diagnostic<? extends JavaFileObject> d : diagnostics) {
                                System.out.println("[MultipleOracleGen] │  " + d.toString());
                            }
                            System.out.println("[MultipleOracleGen] │  ─────────────────────────");
                        }
                    }
                    
                    // Step 4: ClassLoader 캐시 무효화 (다음 로드에서 새 .class를 읽도록)
                    if (DEBUG) {
                        System.out.println("[MultipleOracleGen] │  ───────────────────────────────────────────────────────");
                        System.out.println("[MultipleOracleGen] │  [STEP 4] ClassLoader cache status");
                    }
                    
                    try {
                        ClassLoader cl = ClassLoader.getSystemClassLoader();
                        if (DEBUG) {
                            System.out.println("[MultipleOracleGen] │  ClassLoader: " + cl.getClass().getName());
                            System.out.println("[MultipleOracleGen] │  ClassLoader is URLClassLoader: " + (cl instanceof java.net.URLClassLoader));
                        }
                        
                        if (cl instanceof java.net.URLClassLoader) {
                            java.net.URLClassLoader urlCL = (java.net.URLClassLoader) cl;
                            if (DEBUG) {
                                System.out.println("[MultipleOracleGen] │  URLClassLoader URLs:");
                                for (java.net.URL url : urlCL.getURLs()) {
                                    System.out.println("[MultipleOracleGen] │    - " + url);
                                }
                            }
                        }
                        
                        if (DEBUG) {
                            System.out.println("[MultipleOracleGen] │  ✓ Next attempt will load updated .class from: " + Config.BUILD_PATH);
                        }
                    } catch (Exception e) {
                        if (DEBUG) {
                            System.out.println("[MultipleOracleGen] │  ⚠ ClassLoader warning: " + e.getMessage());
                        }
                    }
                    
                    if (DEBUG) {
                        System.out.println("[MultipleOracleGen] │  ═══════════════════════════════════════════════════════");
                        System.out.println("[MultipleOracleGen] └─ Skeletal class update COMPLETE - Proceeding to next attempt...");
                    }
                    System.out.println("[Compiler-MultipleOracleGen] ✓ Oracle added and Skeletal class recompiled successfully");
                    
                } catch (Exception e) {
                    if (DEBUG) {
                        System.out.println("[MultipleOracleGen] │  ✗✗✗ FAILED to update/recompile Skeletal class ✗✗✗");
                        System.out.println("[MultipleOracleGen] │  Exception type: " + e.getClass().getName());
                        System.out.println("[MultipleOracleGen] │  Exception message: " + e.getMessage());
                        System.out.println("[MultipleOracleGen] │  Stack trace:");
                        e.printStackTrace(System.out);
                    }
                    System.out.println("[Compiler-MultipleOracleGen] ✗ Failed to recompile Skeletal class - breaking loop");
                    break;
                }
                
            } else {
                if (DEBUG) {
                    System.out.println("[MultipleOracleGen] │  ✗ Oracle addition failed (returned null)");
                    System.out.println("[MultipleOracleGen] │  Reason: Already wrapped in try-catch or cannot find target statement");
                    System.out.println("[MultipleOracleGen] └─ Breaking due to oracle failure");
                }
                System.out.println("[Compiler-MultipleOracleGen] Failed to add oracle - breaking loop");
                break;
            }
        }
        
        // 루프 종료 (최대 시도 또는 에러)
        if (DEBUG) {
            System.out.println("\n╔════════════════════════════════════════════════════════════╗");
            System.out.println("║ [MultipleOracleGen] Loop Ended");
            System.out.println("╚════════════════════════════════════════════════════════════╝");
            System.out.println("[MultipleOracleGen] Total attempts executed: " + attemptCount + "/" + maxAttempts);
            System.out.println("[MultipleOracleGen] Returning method with " + attemptCount + " oracle addition(s)");
            System.out.println();
        }
        System.out.println("[Compiler-MultipleOracleGen] Max attempts (" + maxAttempts + ") reached");
        System.out.println("[Compiler-MultipleOracleGen] Returning last attempted method with oracles");
        return new Pair<>(currentTestMethod, currentTestMethod.toString());
    }
    
    /**
     * [전략 1] runCompiledTestCaseForPrim용 반복 실행 및 Oracle 재생성
     */
    private CtMethod addTryCatchFailWithMultipleAttemptsForPrim(
            CtMethod testCase, Launcher launcher, CtClass<?> ctClass) {
        
        final boolean DEBUG = DEBUG_ORACLE_TRANSFORM;
        
        int maxAttempts = Config.MULTIPLE_ORACLE_MAX_ITERATIONS != null ? 
                          Config.MULTIPLE_ORACLE_MAX_ITERATIONS : 5;  // 기본값 5회
        int attemptCount = 0;
        CtMethod currentTestMethod = testCase.clone();
        
        // [NEW] 같은 에러가 반복되는지 감지
        String previousErrorSignature = null;
        int sameErrorCount = 0;
        
        if (DEBUG) {
            System.out.println("\n╔════════════════════════════════════════════════════════════╗");
            System.out.println("║   [MultipleOracleGen-seqp] Starting Repeat Compilation     ║");
            System.out.println("╚════════════════════════════════════════════════════════════╝");
            System.out.println("[MultipleOracleGenPrim] Test method: " + testCase.getSimpleName());
            System.out.println("[MultipleOracleGenPrim] Max attempts: " + maxAttempts);
            System.out.println("[MultipleOracleGenPrim] Config.ENABLE_MULTIPLE_ORACLE_GEN: " + Config.ENABLE_MULTIPLE_ORACLE_GEN);
            System.out.println("[MultipleOracleGenPrim] Config.MULTIPLE_ORACLE_MAX_ITERATIONS: " + Config.MULTIPLE_ORACLE_MAX_ITERATIONS);
        }
        System.out.println("[Compiler-MultipleOracleGenPrim] Starting multiple oracle generation for: " + testCase.getSimpleName());
        System.out.println("[Compiler-MultipleOracleGenPrim] Max attempts: " + maxAttempts);
        
        while (attemptCount < maxAttempts) {
            attemptCount++;
            
            if (DEBUG) {
                System.out.println("\n┌──────────────────────────────────────────────────────────┐");
                System.out.println("│ [Attempt " + attemptCount + "/" + maxAttempts + "]");
                System.out.println("└──────────────────────────────────────────────────────────┘");
            }
            
            // [1] 테스트 실행 - 클래스 로드
            // [FIX] currentTestMethod의 parent가 null일 수 있으므로, ctClass 사용
            String className = ctClass.getSimpleName();
            Class<?> clazz = null;
            
            try {
                if (DEBUG) {
                    System.out.println("[MultipleOracleGenPrim] ├─ [Step 1] Loading compiled class");
                    System.out.println("[MultipleOracleGenPrim] │  Class name: " + packageNamePlusFileName(className));
                }
                
                // [CRITICAL FIX] SystemClassLoader는 캐시하므로 업데이트된 .class를 로드하지 못함!
                // Child-First ClassLoader를 사용하여 BUILD_PATH를 먼저 검색
                
                final String targetClassName = packageNamePlusFileName(className);
                java.net.URL buildPathURL = new java.io.File(Config.BUILD_PATH).toURI().toURL();
                
                // Child-First URLClassLoader
                java.net.URLClassLoader newClassLoader = new java.net.URLClassLoader(
                    new java.net.URL[]{buildPathURL}, 
                    ClassLoader.getSystemClassLoader()
                ) {
                    @Override
                    public Class<?> loadClass(String name) throws ClassNotFoundException {
                        // 테스트 클래스는 child-first (BUILD_PATH 우선)
                        if (name.equals(targetClassName)) {
                            try {
                                // 먼저 이 ClassLoader에서 찾기 시도
                                return findClass(name);
                            } catch (ClassNotFoundException e) {
                                // 못 찾으면 parent에게 위임
                                return super.loadClass(name);
                            }
                        }
                        // 다른 클래스들(JUnit, Jsoup 등)은 parent-first (기본 동작)
                        return super.loadClass(name);
                    }
                };
                
                clazz = newClassLoader.loadClass(targetClassName);
                
                if (DEBUG) {
                    System.out.println("[MultipleOracleGenPrim] │  ✓ Class loaded successfully with Child-First ClassLoader");
                    System.out.println("[MultipleOracleGenPrim] │    ClassLoader: " + newClassLoader.toString());
                }
            } catch (Exception e) {
                if (DEBUG) {
                    System.out.println("[MultipleOracleGenPrim] │  ✗ ClassLoadError: " + e.getClass().getSimpleName());
                    System.out.println("[MultipleOracleGenPrim] │  Message: " + e.getMessage());
                }
                System.out.println("[Compiler-MultipleOracleGenPrim] Failed to load class: " + e.getMessage());
                break;
            }
            
            // [2] JUnit 실행
            Result result = null;
            final Class<?> finalClazz = clazz;
            
            if (DEBUG) {
                System.out.println("[MultipleOracleGenPrim] ├─ [Step 2] Executing JUnit test");
            }
            
            long testStartTime = System.currentTimeMillis();
            java.util.concurrent.ExecutorService executor = java.util.concurrent.Executors.newSingleThreadExecutor();
            java.util.concurrent.Future<Result> future = executor.submit(() -> JUnitCore.runClasses(finalClazz));
            
            try {
                result = future.get(1050, java.util.concurrent.TimeUnit.MILLISECONDS);
                long testDuration = System.currentTimeMillis() - testStartTime;
                
                if (DEBUG) {
                    System.out.println("[MultipleOracleGenPrim] │  ✓ Test execution completed");
                    System.out.println("[MultipleOracleGenPrim] │  Duration: " + testDuration + "ms");
                }
            } catch (java.util.concurrent.TimeoutException e) {
                if (DEBUG) {
                    System.out.println("[MultipleOracleGenPrim] │  ✗ TimeoutException: Test exceeded 1050ms");
                }
                System.out.println("[Compiler-MultipleOracleGenPrim] Test execution timed out");
                executor.shutdownNow();
                break;
            } catch (Exception e) {
                if (DEBUG) {
                    System.out.println("[MultipleOracleGenPrim] │  ✗ Exception: " + e.getClass().getSimpleName());
                    System.out.println("[MultipleOracleGenPrim] │  Message: " + e.getMessage());
                }
                System.out.println("[Compiler-MultipleOracleGenPrim] Test execution failed: " + e.getMessage());
                executor.shutdownNow();
                break;
            } finally {
                 executor.shutdownNow();
                 try {
                     if (!executor.awaitTermination(100, java.util.concurrent.TimeUnit.MILLISECONDS)) {
                         executor.shutdownNow();
                     }
                 } catch (InterruptedException ie) {
                     executor.shutdownNow();
                 }
                 // Clear observations to prevent memory leak
                 RegressionOracles.RegressionUtil.Logger.clearObservations();
             }
            
            // [3] 결과 확인
            if (DEBUG) {
                System.out.println("[MultipleOracleGenPrim] ├─ [Step 3] Analyzing test result");
                System.out.println("[MultipleOracleGenPrim] │  Total run: " + result.getRunCount());
                System.out.println("[MultipleOracleGenPrim] │  Failures: " + result.getFailures().size());
                System.out.println("[MultipleOracleGenPrim] │  Ignores: " + result.getIgnoreCount());
            }
            
            if (result.getFailures().isEmpty()) {
                if (DEBUG) {
                    System.out.println("[MultipleOracleGenPrim] └─ ✓✓✓ Test PASSED ✓✓✓");
                    System.out.println("[MultipleOracleGenPrim]");
                    System.out.println("[MultipleOracleGenPrim] SUCCESS! Oracles generated successfully in " + attemptCount + " attempt(s)");
                    System.out.println("[MultipleOracleGenPrim] Final test method is ready");
                }
                System.out.println("[Compiler-MultipleOracleGenPrim] ✓ Test PASSED on attempt " + attemptCount);
                System.out.println("[Compiler-MultipleOracleGenPrim] Successfully generated oracles in " + attemptCount + " attempt(s)");
                runnableTestList.add(currentTestMethod);
                return currentTestMethod;
            }
            
             // [4] 실패 시 Oracle 추가
             Failure failure = result.getFailures().get(0);
             String failureException = failure.getException() != null ? 
                     failure.getException().getClass().getName() : "Unknown";
             String failureMsg = failure.getException() != null && failure.getException().getMessage() != null ?
                     failure.getException().getMessage() : "No message";
             
             // [NEW] 같은 에러 반복 감지
             String currentErrorSignature = failureException + "::" + failureMsg;
             if (currentErrorSignature.equals(previousErrorSignature)) {
                 sameErrorCount++;
                 if (DEBUG) {
                     System.out.println("[MultipleOracleGenPrim] └─ ✗ Test FAILED (Same error as before #" + sameErrorCount + ")");
                 }
                 // 같은 에러가 2회 반복되면 더 이상 진행 불가
                 if (sameErrorCount >= 2) {
                     if (DEBUG) {
                         System.out.println("[MultipleOracleGenPrim] ✗✗✗ Same error repeated - Cannot find more crash points");
                         System.out.println("[MultipleOracleGenPrim] Breaking loop to prevent infinite retry");
                     }
                     System.out.println("[Compiler-MultipleOracleGenPrim] Same error repeated, breaking loop");
                     break;
                 }
             } else {
                 previousErrorSignature = currentErrorSignature;
                 sameErrorCount = 0;
             }
             
              if (DEBUG) {
                  System.out.println("[MultipleOracleGenPrim] └─ ✗ Test FAILED");
                  System.out.println("[MultipleOracleGenPrim]");
                  System.out.println("[MultipleOracleGenPrim] ├─ [Step 4] Adding Oracle");
                  System.out.println("[MultipleOracleGenPrim] │  Exception: " + failureException);
                  if (failureMsg.length() > 80) {
                      System.out.println("[MultipleOracleGenPrim] │  Message: " + failureMsg.substring(0, 80) + "...");
                  } else {
                      System.out.println("[MultipleOracleGenPrim] │  Message: " + failureMsg);
                  }
                  
                  // 상세한 StackTrace 출력
                  if (failure.getException() != null && failure.getException().getStackTrace() != null) {
                      System.out.println("[MultipleOracleGenPrim] │  Stack trace details:");
                      StackTraceElement[] stackTrace = failure.getException().getStackTrace();
                      for (int i = 0; i < Math.min(stackTrace.length, 10); i++) {
                          StackTraceElement elem = stackTrace[i];
                          System.out.println("[MultipleOracleGenPrim] │    [" + i + "] " + elem.getClassName() + "." + 
                              elem.getMethodName() + ":" + elem.getLineNumber());
                      }
                      if (stackTrace.length > 10) {
                          System.out.println("[MultipleOracleGenPrim] │    ... (" + (stackTrace.length - 10) + " more frames)");
                      }
                  }
              }
             
              String executedContent = this.packageAndImport + ctClass;
              
              if (DEBUG) {
                  System.out.println("[MultipleOracleGenPrim] │  Calling TryCatchFailAdder.addTryCatchFail()...");
              }
              
              Pair<CtMethod, String> oracleResult = TryCatchFailAdder.addTryCatchFail(
                  currentTestMethod, failure, launcher, executedContent
              );
             
             if (oracleResult != null) {
                 currentTestMethod = oracleResult.getKey().clone();
                 if (DEBUG) {
                     System.out.println("[MultipleOracleGenPrim] │  ✓ Oracle added successfully");
                     System.out.println("[MultipleOracleGenPrim] │  Total oracles added so far: " + attemptCount);
                 }
                 
                 // [CRITICAL] Skeletal class(ctClass) 업데이트 및 재컴파일!
                 if (DEBUG) {
                     System.out.println("[MultipleOracleGenPrim] │  ═══════════════════════════════════════════════════════");
                     System.out.println("[MultipleOracleGenPrim] │  Updating Skeletal class and recompiling...");
                     System.out.println("[MultipleOracleGenPrim] │  ═══════════════════════════════════════════════════════");
                 }
                 
                 try {
                     // Step 1: ctClass에서 기존 메서드 제거 및 새 메서드 추가
                     if (DEBUG) {
                         System.out.println("[MultipleOracleGenPrim] │  [STEP 1] Updating Skeletal class");
                     }
                     
                     int methodCountBefore = ctClass.getMethods().size();
                     try {
                         CtMethod oldMethod = ctClass.getMethod(currentTestMethod.getSimpleName());
                         ctClass.removeMethod(oldMethod);
                         if (DEBUG) {
                             System.out.println("[MultipleOracleGenPrim] │  ✓ Old method removed");
                         }
                     } catch (Exception e) {
                         if (DEBUG) {
                             System.out.println("[MultipleOracleGenPrim] │  ⚠ No existing method found (first time)");
                         }
                     }
                     
                    ctClass.addMethod(currentTestMethod.clone());
                    int methodCountAfter = ctClass.getMethods().size();
                    
                    if (DEBUG) {
                        System.out.println("[MultipleOracleGenPrim] │  ✓ New method added");
                        System.out.println("[MultipleOracleGenPrim] │  Method count: " + methodCountBefore + " → " + methodCountAfter);
                        
                        // 메서드 본문 미리보기
                        String methodBody = currentTestMethod.toString();
                        String[] methodLines = methodBody.split("\n");
                        System.out.println("[MultipleOracleGenPrim] │  ─── Method Preview (first 20 lines) ───");
                        for (int i = 0; i < Math.min(20, methodLines.length); i++) {
                            System.out.println("[MultipleOracleGenPrim] │    " + methodLines[i]);
                        }
                        if (methodLines.length > 20) {
                            System.out.println("[MultipleOracleGenPrim] │    ... (" + (methodLines.length - 20) + " more lines)");
                        }
                        System.out.println("[MultipleOracleGenPrim] │  ─────────────────────────");
                    }
                     
                     // Step 2: 메모리에서 컴파일 (파일 저장하지 않음!)
                     if (DEBUG) {
                         System.out.println("[MultipleOracleGenPrim] │  ───────────────────────────────────────────────────────");
                         System.out.println("[MultipleOracleGenPrim] │  [STEP 2] Compiling in-memory (no file I/O)");
                     }
                     
                     // [CRITICAL FIX] ctClass.toString()은 package/import를 포함하지 않음!
                     // packageAndImport를 앞에 추가해야 함
                     String classContent = this.packageAndImport + ctClass.toString();
                     
                     if (DEBUG) {
                         System.out.println("[MultipleOracleGenPrim] │  ═══════════════════════════════════════════════════════");
                         System.out.println("[MultipleOracleGenPrim] │  [DEBUG] Full class content to be compiled:");
                         System.out.println("[MultipleOracleGenPrim] │  ═══════════════════════════════════════════════════════");
                         String[] lines = classContent.split("\n");
                         for (int i = 0; i < Math.min(30, lines.length); i++) {
                             System.out.println(String.format("[MultipleOracleGenPrim] │  %3d: %s", i + 1, lines[i]));
                         }
                         if (lines.length > 30) {
                             System.out.println("[MultipleOracleGenPrim] │  ... (" + (lines.length - 30) + " more lines)");
                         }
                         System.out.println("[MultipleOracleGenPrim] │  ═══════════════════════════════════════════════════════");
                         System.out.println("[MultipleOracleGenPrim] │  Total lines: " + lines.length);
                     }
                     
                     // Step 3: In-memory 컴파일 (compileWholeClassFileForPrim 사용)
                     if (DEBUG) {
                         System.out.println("[MultipleOracleGenPrim] │  ───────────────────────────────────────────────────────");
                         System.out.println("[MultipleOracleGenPrim] │  [STEP 3] In-memory compilation");
                     }
                     
                    String compileClassName = ctClass.getSimpleName();
                    List<Diagnostic<? extends JavaFileObject>> diagnostics = 
                        compileWholeClassFileForPrim(compileClassName, classContent);
                     
                    boolean compilationSuccess = checkCompileError(diagnostics);
                    
                    if (DEBUG) {
                        if (compilationSuccess) {
                            System.out.println("[MultipleOracleGenPrim] │  ✓ Compilation successful");
                            
                            // [DEBUG] .class 파일이 실제로 생성되었는지 확인
                            String classQualifiedName = ctClass.getQualifiedName();
                            String packagePath = classQualifiedName.replace('.', File.separatorChar);
                            String expectedClassPath = Config.BUILD_PATH + File.separator + packagePath + ".class";
                            File classFile = new File(expectedClassPath);
                            
                            System.out.println("[MultipleOracleGenPrim] │  [DEBUG] Checking .class file:");
                            System.out.println("[MultipleOracleGenPrim] │    Expected path: " + expectedClassPath);
                            System.out.println("[MultipleOracleGenPrim] │    File exists: " + classFile.exists());
                            if (classFile.exists()) {
                                System.out.println("[MultipleOracleGenPrim] │    File size: " + classFile.length() + " bytes");
                                System.out.println("[MultipleOracleGenPrim] │    Last modified: " + new java.util.Date(classFile.lastModified()));
                            } else {
                                System.out.println("[MultipleOracleGenPrim] │    ⚠ WARNING: .class file NOT FOUND!");
                                System.out.println("[MultipleOracleGenPrim] │    Compile options used:");
                                for (String opt : options) {
                                    System.out.println("[MultipleOracleGenPrim] │      " + opt);
                                }
                            }
                        } else {
                            System.out.println("[MultipleOracleGenPrim] │  ⚠ Compilation failed");
                            System.out.println("[MultipleOracleGenPrim] │  ─── Compilation Errors ───");
                            for (Diagnostic<? extends JavaFileObject> d : diagnostics) {
                                System.out.println("[MultipleOracleGenPrim] │  " + d.toString());
                            }
                            System.out.println("[MultipleOracleGenPrim] │  ─────────────────────────");
                        }
                    }
                     
                     if (DEBUG) {
                         System.out.println("[MultipleOracleGenPrim] │  ═══════════════════════════════════════════════════════");
                         System.out.println("[MultipleOracleGenPrim] └─ Skeletal class update COMPLETE - Proceeding to next attempt...");
                     }
                     System.out.println("[Compiler-MultipleOracleGenPrim] ✓ Oracle added and Skeletal class recompiled successfully");
                     
                 } catch (Exception e) {
                     if (DEBUG) {
                         System.out.println("[MultipleOracleGenPrim] │  ✗✗✗ FAILED to update/recompile Skeletal class ✗✗✗");
                         System.out.println("[MultipleOracleGenPrim] │  Exception: " + e.getMessage());
                         e.printStackTrace(System.out);
                     }
                     System.out.println("[Compiler-MultipleOracleGenPrim] ✗ Failed to recompile - breaking loop");
                     break;
                 }
                 
             } else {
                 if (DEBUG) {
                     System.out.println("[MultipleOracleGenPrim] │  ✗ Oracle addition failed (returned null)");
                     System.out.println("[MultipleOracleGenPrim] │  Reason: Already wrapped in try-catch or cannot find target statement");
                     System.out.println("[MultipleOracleGenPrim] └─ Breaking due to oracle failure");
                 }
                 System.out.println("[Compiler-MultipleOracleGenPrim] Failed to add oracle - breaking loop");
                 break;
             }
        }
        
        // 루프 종료 (최대 시도 또는 에러)
        if (DEBUG) {
            System.out.println("\n╔════════════════════════════════════════════════════════════╗");
            System.out.println("║ [MultipleOracleGenPrim] Loop Ended");
            System.out.println("╚════════════════════════════════════════════════════════════╝");
            System.out.println("[MultipleOracleGenPrim] Total attempts executed: " + attemptCount + "/" + maxAttempts);
            System.out.println("[MultipleOracleGenPrim] Returning method with " + attemptCount + " oracle addition(s)");
            System.out.println();
        }
        System.out.println("[Compiler-MultipleOracleGenPrim] Max attempts (" + maxAttempts + ") reached");
        System.out.println("[Compiler-MultipleOracleGenPrim] Returning last attempted method with oracles");
        runnableTestList.add(currentTestMethod);
        return currentTestMethod;
    }
    
    /**
     * [전략 1 - PASSED tests] runCompiledTestCase용 반복 실행 및 Assertion 재생성
     * PASSED 테스트에 assertion을 추가한 후, 테스트를 재실행하여 assertion이 올바른지 검증합니다.
     * Assertion이 실패하면 다시 추가하고 재실행하는 과정을 반복합니다.
     */
    private Pair<CtMethod, String> addAssertionsWithMultipleAttempts(
            CtMethod testCase, Launcher launcher, CtClass<?> testClass,
            Map<CtMethod, List<CtLocalVariable>> localVariablesPerTestMethod,
            Map<CtMethod, List<CtLocalVariable>> localVariablesPrimitive) {
        
        final boolean DEBUG = DEBUG_ORACLE_TRANSFORM;
        
        int maxAttempts = Config.MULTIPLE_ORACLE_MAX_ITERATIONS != null ? 
                          Config.MULTIPLE_ORACLE_MAX_ITERATIONS : 5;
        int attemptCount = 0;
        CtMethod currentTestMethod = testCase.clone();
        
        if (DEBUG) {
            System.out.println("\n╔════════════════════════════════════════════════════════════╗");
            System.out.println("║   [AssertionVerify-seqc] Starting Assertion Verification   ║");
            System.out.println("╚════════════════════════════════════════════════════════════╝");
            System.out.println("[AssertionVerify] Test method: " + testCase.getSimpleName());
            System.out.println("[AssertionVerify] Max attempts: " + maxAttempts);
        }
        System.out.println("[Compiler-AssertionVerify] Starting assertion verification for: " + testCase.getSimpleName());
        
        while (attemptCount < maxAttempts) {
            attemptCount++;
            
            if (DEBUG) {
                System.out.println("\n┌──────────────────────────────────────────────────────────┐");
                System.out.println("│ [Attempt " + attemptCount + "/" + maxAttempts + "]");
                System.out.println("└──────────────────────────────────────────────────────────┘");
            }
            
            // [1] Assertion 추가
            if (DEBUG) {
                System.out.println("[AssertionVerify] ├─ [Step 1] Adding assertions");
            }
            
            // [FIX] currentTestMethod가 clone된 메서드라서 parent가 없음
            // AssertionAdder가 parent가 필요하므로, 임시로 testClass에 메서드 추가
            CtClass<?> workingClass = testClass.clone();
            try {
                CtMethod oldMethod = workingClass.getMethod(currentTestMethod.getSimpleName());
                workingClass.removeMethod(oldMethod);
            } catch (Exception e) {
                // 메서드가 없는 경우는 무시
            }
            workingClass.addMethod(currentTestMethod);
            
            if (DEBUG) {
                System.out.println("[AssertionVerify] │  currentTestMethod added to working class for AssertionAdder");
            }
            
            final AssertionAdder assertionAdder = new AssertionAdder(launcher.getFactory());
            CtMethod assertionAdded = assertionAdder.addAssertion(
                currentTestMethod, localVariablesPerTestMethod, localVariablesPrimitive);
            
            if (assertionAdded == null) {
                if (DEBUG) {
                    System.out.println("[AssertionVerify] │  ✗ AssertionAdder returned null");
                }
                System.out.println("[Compiler-AssertionVerify] Failed to add assertions");
                break;
            }
            
            currentTestMethod = assertionAdded;
            
            if (DEBUG) {
                System.out.println("[AssertionVerify] │  ✓ Assertions added");
            }
            
            // [2] 테스트 실행 - 클래스 로드
            Class<?> clazz = null;
            String className = packageNamePlusFileName(currentTestMethod.getSimpleName());
            
            try {
                if (DEBUG) {
                    System.out.println("[AssertionVerify] ├─ [Step 2] Loading compiled class");
                    System.out.println("[AssertionVerify] │  Class name: " + className);
                }
                clazz = ClassLoader.getSystemClassLoader().loadClass(className);
                if (DEBUG) {
                    System.out.println("[AssertionVerify] │  ✓ Class loaded successfully");
                }
            } catch (Exception e) {
                if (DEBUG) {
                    System.out.println("[AssertionVerify] │  ✗ ClassLoadError: " + e.getClass().getSimpleName());
                }
                System.out.println("[Compiler-AssertionVerify] Failed to load class: " + e.getMessage());
                break;
            }
            
            // [3] JUnit 실행
            Result result = null;
            final Class<?> finalClazz = clazz;
            
            if (DEBUG) {
                System.out.println("[AssertionVerify] ├─ [Step 3] Executing JUnit test");
            }
            
            long testStartTime = System.currentTimeMillis();
            java.util.concurrent.ExecutorService executor = java.util.concurrent.Executors.newSingleThreadExecutor();
            java.util.concurrent.Future<Result> future = executor.submit(() -> JUnitCore.runClasses(finalClazz));
            
            try {
                result = future.get(1050, java.util.concurrent.TimeUnit.MILLISECONDS);
                long testDuration = System.currentTimeMillis() - testStartTime;
                
                if (DEBUG) {
                    System.out.println("[AssertionVerify] │  ✓ Test execution completed");
                    System.out.println("[AssertionVerify] │  Duration: " + testDuration + "ms");
                }
            } catch (java.util.concurrent.TimeoutException e) {
                if (DEBUG) {
                    System.out.println("[AssertionVerify] │  ✗ TimeoutException: Test exceeded 1050ms");
                }
                System.out.println("[Compiler-AssertionVerify] Test execution timed out");
                executor.shutdownNow();
                break;
            } catch (Exception e) {
                if (DEBUG) {
                    System.out.println("[AssertionVerify] │  ✗ Exception: " + e.getClass().getSimpleName());
                }
                System.out.println("[Compiler-AssertionVerify] Test execution failed: " + e.getMessage());
                executor.shutdownNow();
                break;
            } finally {
                 executor.shutdownNow();
                 try {
                     if (!executor.awaitTermination(100, java.util.concurrent.TimeUnit.MILLISECONDS)) {
                         executor.shutdownNow();
                     }
                 } catch (InterruptedException ie) {
                     executor.shutdownNow();
                 }
                 // Clear observations to prevent memory leak
                 RegressionOracles.RegressionUtil.Logger.clearObservations();
             }
            
            // [4] 결과 확인
            if (DEBUG) {
                System.out.println("[AssertionVerify] ├─ [Step 4] Analyzing test result");
                System.out.println("[AssertionVerify] │  Total run: " + result.getRunCount());
                System.out.println("[AssertionVerify] │  Failures: " + result.getFailures().size());
            }
            
            if (result.getFailures().isEmpty()) {
                if (DEBUG) {
                    System.out.println("[AssertionVerify] └─ ✓✓✓ Test PASSED with assertions ✓✓✓");
                    System.out.println("[AssertionVerify]");
                    System.out.println("[AssertionVerify] SUCCESS! Assertions verified in " + attemptCount + " attempt(s)");
                }
                System.out.println("[Compiler-AssertionVerify] ✓ Test PASSED with assertions on attempt " + attemptCount);
                return new Pair<>(currentTestMethod, fixSpecialConstants(currentTestMethod.toString()));
            }
            
            // [5] 실패 시 다시 시도 (assertion이 잘못되었을 수 있음)
            Failure failure = result.getFailures().get(0);
            String failureException = failure.getException() != null ? 
                    failure.getException().getClass().getName() : "Unknown";
            
            if (DEBUG) {
                System.out.println("[AssertionVerify] └─ ✗ Test FAILED with assertions");
                System.out.println("[AssertionVerify] │  Exception: " + failureException);
                System.out.println("[AssertionVerify] │  Retrying assertion generation...");
            }
            System.out.println("[Compiler-AssertionVerify] Assertion failed, retrying...");
            
            // 다음 시도를 위해 assertion을 제거하고 원본 메서드로 복원
            currentTestMethod = testCase.clone();
        }
        
        // 루프 종료 (최대 시도 또는 에러)
        if (DEBUG) {
            System.out.println("\n╔════════════════════════════════════════════════════════════╗");
            System.out.println("║ [AssertionVerify] Loop Ended");
            System.out.println("╚════════════════════════════════════════════════════════════╝");
            System.out.println("[AssertionVerify] Total attempts executed: " + attemptCount + "/" + maxAttempts);
        }
        System.out.println("[Compiler-AssertionVerify] Max attempts reached, using last version");
        return new Pair<>(currentTestMethod, fixSpecialConstants(currentTestMethod.toString()));
    }
    
    /**
     * [전략 1 - PASSED tests] runCompiledTestCaseForPrim용 반복 실행 및 Assertion 재생성
     */
    private CtMethod addAssertionsWithMultipleAttemptsForPrim(
            CtMethod testCase, Launcher launcher, CtClass<?> ctClass,
            Map<CtMethod, List<CtLocalVariable>> localVariablesPerTestMethod,
            Map<CtMethod, List<CtLocalVariable>> localVariablesPrimitive) {
        
        final boolean DEBUG = DEBUG_ORACLE_TRANSFORM;
        
        int maxAttempts = Config.MULTIPLE_ORACLE_MAX_ITERATIONS != null ? 
                          Config.MULTIPLE_ORACLE_MAX_ITERATIONS : 5;
        int attemptCount = 0;
        CtMethod currentTestMethod = testCase.clone();
        
        if (DEBUG) {
            System.out.println("\n╔════════════════════════════════════════════════════════════╗");
            System.out.println("║   [AssertionVerifyPrim] Starting Assertion Verification    ║");
            System.out.println("╚════════════════════════════════════════════════════════════╝");
            System.out.println("[AssertionVerifyPrim] Test method: " + testCase.getSimpleName());
            System.out.println("[AssertionVerifyPrim] Max attempts: " + maxAttempts);
        }
        System.out.println("[Compiler-AssertionVerifyPrim] Starting assertion verification for: " + testCase.getSimpleName());
        
        while (attemptCount < maxAttempts) {
            attemptCount++;
            
            if (DEBUG) {
                System.out.println("\n┌──────────────────────────────────────────────────────────┐");
                System.out.println("│ [Attempt " + attemptCount + "/" + maxAttempts + "]");
                System.out.println("└──────────────────────────────────────────────────────────┘");
            }
            
            // [1] Assertion 추가
            if (DEBUG) {
                System.out.println("[AssertionVerifyPrim] ├─ [Step 1] Adding assertions");
            }
            
            // [FIX] currentTestMethod가 clone된 메서드라서 parent가 없음
            // AssertionAdder가 parent가 필요하므로, 임시로 ctClass에 메서드 추가
            CtClass<?> workingClass = ctClass.clone();
            try {
                CtMethod oldMethod = workingClass.getMethod(currentTestMethod.getSimpleName());
                workingClass.removeMethod(oldMethod);
            } catch (Exception e) {
                // 메서드가 없는 경우는 무시
            }
            workingClass.addMethod(currentTestMethod);
            
            if (DEBUG) {
                System.out.println("[AssertionVerifyPrim] │  currentTestMethod added to working class for AssertionAdder");
            }
            
            final AssertionAdder assertionAdder = new AssertionAdder(launcher.getFactory());
            CtMethod assertionAdded = assertionAdder.addAssertion(
                currentTestMethod, localVariablesPerTestMethod, localVariablesPrimitive);
            
            if (assertionAdded == null) {
                if (DEBUG) {
                    System.out.println("[AssertionVerifyPrim] │  ✗ AssertionAdder returned null");
                }
                System.out.println("[Compiler-AssertionVerifyPrim] Failed to add assertions");
                break;
            }
            
            currentTestMethod = assertionAdded;
            
            if (DEBUG) {
                System.out.println("[AssertionVerifyPrim] │  ✓ Assertions added");
            }
            
            // [2] 테스트 실행 - 클래스 로드
            String className = currentTestMethod.getParent(CtClass.class).getSimpleName();
            Class<?> clazz = null;
            
            try {
                if (DEBUG) {
                    System.out.println("[AssertionVerifyPrim] ├─ [Step 2] Loading compiled class");
                    System.out.println("[AssertionVerifyPrim] │  Class name: " + packageNamePlusFileName(className));
                }
                clazz = ClassLoader.getSystemClassLoader().loadClass(packageNamePlusFileName(className));
                if (DEBUG) {
                    System.out.println("[AssertionVerifyPrim] │  ✓ Class loaded successfully");
                }
            } catch (Exception e) {
                if (DEBUG) {
                    System.out.println("[AssertionVerifyPrim] │  ✗ ClassLoadError: " + e.getClass().getSimpleName());
                }
                System.out.println("[Compiler-AssertionVerifyPrim] Failed to load class: " + e.getMessage());
                break;
            }
            
            // [3] JUnit 실행
            Result result = null;
            final Class<?> finalClazz = clazz;
            
            if (DEBUG) {
                System.out.println("[AssertionVerifyPrim] ├─ [Step 3] Executing JUnit test");
            }
            
            long testStartTime = System.currentTimeMillis();
            java.util.concurrent.ExecutorService executor = java.util.concurrent.Executors.newSingleThreadExecutor();
            java.util.concurrent.Future<Result> future = executor.submit(() -> JUnitCore.runClasses(finalClazz));
            
            try {
                result = future.get(1050, java.util.concurrent.TimeUnit.MILLISECONDS);
                long testDuration = System.currentTimeMillis() - testStartTime;
                
                if (DEBUG) {
                    System.out.println("[AssertionVerifyPrim] │  ✓ Test execution completed");
                    System.out.println("[AssertionVerifyPrim] │  Duration: " + testDuration + "ms");
                }
            } catch (java.util.concurrent.TimeoutException e) {
                if (DEBUG) {
                    System.out.println("[AssertionVerifyPrim] │  ✗ TimeoutException: Test exceeded 1050ms");
                }
                System.out.println("[Compiler-AssertionVerifyPrim] Test execution timed out");
                executor.shutdownNow();
                break;
            } catch (Exception e) {
                if (DEBUG) {
                    System.out.println("[AssertionVerifyPrim] │  ✗ Exception: " + e.getClass().getSimpleName());
                }
                System.out.println("[Compiler-AssertionVerifyPrim] Test execution failed: " + e.getMessage());
                executor.shutdownNow();
                break;
            } finally {
                 executor.shutdownNow();
                 try {
                     if (!executor.awaitTermination(100, java.util.concurrent.TimeUnit.MILLISECONDS)) {
                         executor.shutdownNow();
                     }
                 } catch (InterruptedException ie) {
                     executor.shutdownNow();
                 }
                 // Clear observations to prevent memory leak
                 RegressionOracles.RegressionUtil.Logger.clearObservations();
             }
            
            // [4] 결과 확인
            if (DEBUG) {
                System.out.println("[AssertionVerifyPrim] ├─ [Step 4] Analyzing test result");
                System.out.println("[AssertionVerifyPrim] │  Total run: " + result.getRunCount());
                System.out.println("[AssertionVerifyPrim] │  Failures: " + result.getFailures().size());
            }
            
            if (result.getFailures().isEmpty()) {
                if (DEBUG) {
                    System.out.println("[AssertionVerifyPrim] └─ ✓✓✓ Test PASSED with assertions ✓✓✓");
                    System.out.println("[AssertionVerifyPrim]");
                    System.out.println("[AssertionVerifyPrim] SUCCESS! Assertions verified in " + attemptCount + " attempt(s)");
                }
                System.out.println("[Compiler-AssertionVerifyPrim] ✓ Test PASSED with assertions on attempt " + attemptCount);
                runnableTestList.add(currentTestMethod);
                return currentTestMethod;
            }
            
            // [5] 실패 시 다시 시도 (assertion이 잘못되었을 수 있음)
            Failure failure = result.getFailures().get(0);
            String failureException = failure.getException() != null ? 
                    failure.getException().getClass().getName() : "Unknown";
            
            if (DEBUG) {
                System.out.println("[AssertionVerifyPrim] └─ ✗ Test FAILED with assertions");
                System.out.println("[AssertionVerifyPrim] │  Exception: " + failureException);
                System.out.println("[AssertionVerifyPrim] │  Retrying assertion generation...");
            }
            System.out.println("[Compiler-AssertionVerifyPrim] Assertion failed, retrying...");
            
            // 다음 시도를 위해 assertion을 제거하고 원본 메서드로 복원
            currentTestMethod = testCase.clone();
        }
        
        // 루프 종료 (최대 시도 또는 에러)
        if (DEBUG) {
            System.out.println("\n╔════════════════════════════════════════════════════════════╗");
            System.out.println("║ [AssertionVerifyPrim] Loop Ended");
            System.out.println("╚════════════════════════════════════════════════════════════╝");
            System.out.println("[AssertionVerifyPrim] Total attempts executed: " + attemptCount + "/" + maxAttempts);
        }
        System.out.println("[Compiler-AssertionVerifyPrim] Max attempts reached, using last version");
        runnableTestList.add(currentTestMethod);
        return currentTestMethod;
    }

    /**
     * Fix special float/double constants that cannot be used as bare identifiers
     */
    private String fixSpecialConstants(String code) {
        if (code == null) return null;
        
        code = code.replaceAll("(?<!\\.)\\bNaNF\\b", "java.lang.Float.NaN");
        code = code.replaceAll("(?<!\\.)\\bNaN\\b(?!F)", "java.lang.Double.NaN");
        code = code.replaceAll("(?<!\\.)\\bPOSITIVE_INFINITYF\\b", "java.lang.Float.POSITIVE_INFINITY");
        code = code.replaceAll("(?<!\\.)\\bNEGATIVE_INFINITYF\\b", "java.lang.Float.NEGATIVE_INFINITY");
        code = code.replaceAll("(?<!\\.)\\bPOSITIVE_INFINITY\\b(?!F)", "java.lang.Double.POSITIVE_INFINITY");
        code = code.replaceAll("(?<!\\.)\\bNEGATIVE_INFINITY\\b(?!F)", "java.lang.Double.NEGATIVE_INFINITY");
        code = code.replaceAll("(?<!\\.)\\bInfinity\\b", "java.lang.Double.POSITIVE_INFINITY");
        
        return code;
    }
    
    /**
     * init output folder for loaded classes
     */
    private void initOutputFolderForClassLoader() {
        try {
            File output = new File(Config.BUILD_PATH);
            URLClassLoader urlClassLoader = (URLClassLoader) ClassLoader.getSystemClassLoader();
            Field ucp = URLClassLoader.class.getDeclaredField("ucp");
            ucp.setAccessible(true);
            URLClassPath urlClassPath = (URLClassPath) ucp.get(urlClassLoader);
            urlClassPath.addURL(output.toURI().toURL());
        } catch (Exception e) {
            System.out.println("Loading output folder for class failed!");
        }
    }

    private String packageNamePlusFileName(String fileName) {
        if (packageName.equals(""))
            return fileName;
        else
            return packageName + "." + fileName;
    }

    public List<CtClass<Object>> getTestcases() {
        return testcases;
    }

    public void setTestcases(List<CtClass<Object>> testcases) {
        this.testcases = testcases;
    }

    public String getPackageName() {
        return packageName;
    }

    public void setPackageName(String packageName) {
        this.packageName = packageName;
    }

    public String getPackageAndImport() {
        return packageAndImport;
    }

    public void setPackageAndImport(String packageAndImport) {
        this.packageAndImport = packageAndImport;
    }

    public List<String> getOptions() {
        return options;
    }

    public void setOptions(List<String> options) {
        this.options = options;
    }

    public Map<String, CtMethod> getNameToMethod() {
        return nameToMethod;
    }

    public void setNameToMethod(Map<String, CtMethod> nameToMethod) {
        this.nameToMethod = nameToMethod;
    }

    public List<CtMethod> getRunnableTestList() {
        return runnableTestList;
    }

    public List<String> getRunnableTestStringList() {
        return runnableTestStringList;
    }

    public void setRunnableTestStringListEmpty() {
        runnableTestStringList.clear();
    }
    
    // [NEW] Bucketing 관련 메서드들
    
    /**
     * TestMinimizer와 협력하여 Exception Bucket 정보 구성
     * Bucketing 모드일 때 호출됨
     */
    public void organizeBucketsFromMinimizer() {
        if (!Config.ENABLE_TEST_BUCKETING || testMinimizer == null) {
            return;
        }
        
        // TestMinimizer에서 Exception별 테스트 그룹 획득
        Map<String, List<String>> buckets = testMinimizer.getExceptionBuckets();
        exceptionBuckets.putAll(buckets);
        
        if (Config.DEBUG_TEST_BUCKETING) {
            System.out.println("[Bucketing] Organized " + buckets.size() + " exception buckets");
            for (Map.Entry<String, List<String>> entry : buckets.entrySet()) {
                System.out.println("  - " + entry.getKey() + ": " + entry.getValue().size() + " tests");
            }
        }
    }
    
    /**
     * 테스트명과 Exception 타입을 매핑
     */
    public void mapTestNameToException(String testName, String exceptionType) {
        testNameToExceptionMap.put(testName, exceptionType);
    }
    
    
    /**
     * Exception Bucket 정보 반환
     */
    public Map<String, List<String>> getExceptionBuckets() {
        return new LinkedHashMap<>(exceptionBuckets);
    }


    class CompileTask implements Callable<Pair> {
        private final String packageName;
        private String fileName;
        private String content;

        /**
         * init task
         *
         * @param fileName
         * @param content
         */
        public CompileTask(String fileName, String content, String packageName) {
            this.fileName = fileName;
            this.content = content;
            this.packageName = packageName;
        }

        public Pair<Boolean, Class<?>> call() throws Exception {
            /**
             * first argument indicates compile success or not
             * second argument contains the compiled class
             */
            Pair<Boolean, Class<?>> result = new Pair<>(false, null);
            InMemoryJavaCompiler compiler = InMemoryJavaCompiler.newInstance();
            compiler.useOptions("-cp", Config.CLASS_PATH, "-encoding", "UTF-8");
            compiler.ignoreWarnings();
            Class<?> clazz = null;
            /**
             * check compile
             */
            try {
                clazz = compiler.compile(packageName + "." + fileName, content);
            } catch (Exception e) {
                return result;
            }

            // compile success
            result.setKey(true);
            result.setValue(clazz);
            return result;
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
                        Factory factory = thisAccess.getFactory();
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
                            Factory factory = fieldWrite.getFactory();
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
                            Factory factory = fieldRead.getFactory();
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
                            Factory factory = invocation.getFactory();
                            CtThisAccess<?> simpleThisAccess = factory.createThisAccess();
                            invocation.setTarget(simpleThisAccess);
                        }
                    }
                }
            }
        });
    }

    /**
     * wrapper class for source code
     */
    public static class Source extends SimpleJavaFileObject {
        private final String content;

        public Source(String name, Kind kind, String content) {
            super(URI.create("memo:///" + name.replace('.', '/') + kind.extension), kind);
            this.content = content;
        }

        @Override
        public CharSequence getCharContent(boolean ignore) {
            return this.content;
        }
    }
}