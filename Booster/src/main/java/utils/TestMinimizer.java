package utils;

import java.util.*;
import java.util.regex.Pattern;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;

import org.junit.runner.Result;
import org.junit.runner.Description;
import org.junit.runner.notification.Failure;

public class TestMinimizer {

    // [최적화 1] Lock-free 구조: 여러 Compiler 스레드가 동시에 접근해도 멈추지 않음 (SeqP 모드 대응)
    // [FIXED] Instance-level 변수로 변경 (각 TestMinimizer가 독립적 데이터 유지)
    private Set<String> uniqueSignatures = ConcurrentHashMap.newKeySet();

     // [NEW] Exception별 고유 테스트 추적 (Exception Type → Test name)
     // [FIXED] Instance-level 변수로 변경
     private Map<String, String> exceptionToTestMap = new ConcurrentHashMap<>();
     
      // [NEW] Bucketing용: Signature별 모든 테스트 추적 (Signature → Set of Test names)
      // Signature = Exception Type + StackTrace의 고유 조합 (Minimization 목적)
      private Map<String, Set<String>> signatureToTestsMapBucketing = new ConcurrentHashMap<>();
      
      // [NEW] Bucketing 그룹화용: Exception Type + StackTrace (Message, MUT 제외)
      // 더 넓은 범위로 그룹화하기 위한 별도 Signature
      private Map<String, Set<String>> signatureToTestsMapBucketingForGrouping = new ConcurrentHashMap<>();

     // 통계용 Atomic 변수 (Thread-safe)
    private AtomicInteger totalTests = new AtomicInteger(0);
    private AtomicInteger uniqueTests = new AtomicInteger(0);
    private AtomicInteger duplicateTests = new AtomicInteger(0);

    // [최적화 2] Prefix 검사 최적화를 위한 단순화 (배열 순회 비용 절감)
    // 필요한 경우 추가 가능하지만, 아래 isIgnoredFast 메서드에서 하드코딩으로 처리하여 속도 향상
    private static final Pattern GENERATED_CLASS_PATTERN = Pattern.compile(".*(_P_|_M_|_C_|MegaTestClass|TestClass_).*");
    
     // Mode for TestMinimizer: "seqc" or "seqp"
     private String mode = "seqp"; // default mode
     
     // MUT Extraction switch: whether to include MUT info in signature
     private boolean enableMUTExtraction = false; // default: disabled
     
     /**
      * Constructor to specify minimizer mode
      * @param mode "seqc" for sequential compilation with MUT inclusion, "seqp" for primitive mutation
      */
     public TestMinimizer(String mode) {
         this.mode = mode != null ? mode.toLowerCase() : "seqp";
     }
     
     // Default constructor for backward compatibility
     public TestMinimizer() {
         this("seqp");
     }
     
     /**
      * Set whether to enable MUT extraction in signature
      * @param enable true to include MUT info, false for pure signature only
      */
     public void setEnableMUTExtraction(boolean enable) {
         this.enableMUTExtraction = enable;
     }
     
     /**
      * Get whether MUT extraction is enabled
      * @return true if MUT extraction is enabled, false otherwise
      */
     public boolean isEnableMUTExtraction() {
         return enableMUTExtraction;
     }

     public boolean isUnique(Failure failure) {
          if (failure == null) return true; // Pass는 저장

          totalTests.incrementAndGet();
          String signature = extractSignature(failure, mode);

          if (Config.DEBUG_TEST_MINIMIZATION) {
               System.out.println("[TestMinimizer] Signature (" + mode + "): " + signature);
           }

          // putIfAbsent와 유사한 동작 (Set.add는 없으면 넣고 true, 있으면 false 반환)
          // ConcurrentHashMap에 최적화되어 있어 별도 synchronized 불필요
          boolean isNew = uniqueSignatures.add(signature);
          
            // Bucketing용: Signature 기반 테스트 추적
            String testName = extractTestName(failure);
            
            // Signature별 모든 테스트 추적 (Set으로 중복 자동 제거)
            signatureToTestsMapBucketing.computeIfAbsent(signature, k -> 
                ConcurrentHashMap.newKeySet()
            ).add(testName);
            
             // [NEW] Bucketing 그룹화용: 더 넓은 범위의 Signature 생성 (Message, MUT 제외)
             String signatureForGrouping = extractSignatureForBucketing(failure, mode);
             
             // Bucketing 그룹화용 Signature별 테스트 추적
             signatureToTestsMapBucketingForGrouping.computeIfAbsent(signatureForGrouping, k -> 
                 ConcurrentHashMap.newKeySet()
             ).add(testName);

          if (isNew) {
               uniqueTests.incrementAndGet();
               
               return true; // Unique
           } else {
               duplicateTests.incrementAndGet();
               if(Config.ENABLE_TEST_MINIMIZATION){
                return false;
               }
               return true; 
           }
      }

     /**
      * Extract MUT information from SeqP test method name
      * Format: nodeTest_P_handlesAbsPrefix_43
      * Returns: "handlesAbsPrefix" from "_P_..._" pattern
      */
     private String extractMUTFromTestMethodName(String methodName) {
         if (methodName == null || methodName.isEmpty()) {
             return "";
         }
         
         // Look for pattern: _P_ followed by MUT name and then _number
         int patternIndex = methodName.indexOf("_P_");
         if (patternIndex == -1) {
             return "";
         }
         
         int startIndex = patternIndex + 3; // "_P_".length() = 3
         int endIndex = startIndex;
         
         // Find the next underscore followed by a digit (the version number)
         for (int i = startIndex; i < methodName.length(); i++) {
             if (methodName.charAt(i) == '_' && i + 1 < methodName.length() 
                 && Character.isDigit(methodName.charAt(i + 1))) {
                 endIndex = i;
                 break;
             }
         }
         
         if (startIndex < endIndex) {
             return methodName.substring(startIndex, endIndex);
         }
         
         return "";
     }

     /**
      * Extract MUT information from test class name
      * Format: MegaTestClass_M_addEntity_1 or similar
      * Returns: "addEntity" from "_M_addEntity_" pattern
      */
     private String extractMUTFromClassName(String className) {
        if (className == null || className.isEmpty()) {
            return "";
        }
        
        // Look for pattern: _M_ or _P_ or _C_ followed by MUT name and then _number
        // Example: MegaTestClass_M_addEntity_1 -> extract "addEntity"
        String[] patterns = {"_M_", "_P_", "_C_"};
        
        for (String pattern : patterns) {
            int patternIndex = className.indexOf(pattern);
            if (patternIndex != -1) {
                int startIndex = patternIndex + pattern.length();
                // Find the next underscore followed by a digit (the version number)
                int endIndex = className.length();
                for (int i = startIndex; i < className.length(); i++) {
                    if (className.charAt(i) == '_' && i + 1 < className.length() 
                        && Character.isDigit(className.charAt(i + 1))) {
                        endIndex = i;
                        break;
                    }
                }
                if (startIndex < endIndex) {
                    return className.substring(startIndex, endIndex);
                }
            }
        }
        return "";
    }

    private String extractSignature(Failure failure, String mode) {
        Throwable exception = failure.getException();

        // 예외가 없는 경우(AssertionError 등)는 헤더 사용 -> 빠른 리턴
        if(exception == null){
            return failure.getTestHeader();
        }

        // [최적화 3] StringBuilder 용량 미리 지정 (재할당 방지)
         StringBuilder sb = new StringBuilder(256);
         sb.append(exception.getClass().getName());
         
         // [NEW] Exception message 추가
         if(Config.ENABLE_ERROR_MSG_EXTRACTION_IN_SIGNATURE){
            String message = exception.getMessage();
            if (message != null && !message.isEmpty()) {
                sb.append(": ").append(message);
            }
            sb.append("::");
         }
         Description description = failure.getDescription();
         String currentTestClassName = (description != null) ? description.getClassName() : "";
         
          // [SWITCHABLE] Extract MUT information from test class name
          // enableMUTExtraction 스위치로 MUT 정보 포함 여부 결정
          if (enableMUTExtraction) {
              String mutInfo = "";
              if ("seqc".equals(mode)) {
                  mutInfo = extractMUTFromClassName(currentTestClassName);
                  if (!mutInfo.isEmpty()) {
                      sb.append("[MUT:").append(mutInfo).append("]|");
                  }
              } else if ("seqp".equals(mode)) {
                  // SeqP: Extract MUT from test method name (e.g., "nodeTest_P_handlesAbsPrefix_43" → "handlesAbsPrefix")
                  mutInfo = extractMUTFromTestMethodName(description != null ? description.getMethodName() : "");
                  if (!mutInfo.isEmpty()) {
                      sb.append("[MUT:").append(mutInfo).append("]|");
                  }
              }
          }
        
        // Inner Class 처리를 위한 Prefix 미리 계산 (반복문 내부 연산 제거)
        String innerClassPrefix = (currentTestClassName != null && !currentTestClassName.isEmpty()) 
                                  ? currentTestClassName + "$" 
                                  : null;

        StackTraceElement[] stackTrace = exception.getStackTrace();
        
        for(StackTraceElement elem : stackTrace){
            String className = elem.getClassName();

            // [최적화 4] Fast Ignore Check: 배열 순회 대신 단순 조건문으로 변경 (JIT 최적화 유리)
            if(isIgnoredFast(className)){
                continue;
            }

            // Generated Test Class 식별 로직
            boolean isGenTest = false;
            if (currentTestClassName != null && !currentTestClassName.isEmpty()) {
                if (className.equals(currentTestClassName)) {
                    isGenTest = true;
                } else if (innerClassPrefix != null && className.startsWith(innerClassPrefix)) {
                    isGenTest = true;
                }
            }

            if(isGenTest){
                sb.append("<GEN_TEST>|");
                break; 
            } else {
                // MUT (라이브러리) 코드는 라인 번호까지 상세 기록
                sb.append(className)
                  .append(".")
                  .append(elem.getMethodName())
                  .append(":")
                  .append(elem.getLineNumber())
                  .append("|");
            }
        }
        
        return sb.toString();
    }
     
     /**
      * [NEW] Bucketing 그룹화용 Signature 추출
      * Exception Type + StackTrace (Message, MUT 정보 제외)
      * 더 넓은 범위로 동일한 버그들을 그룹화하기 위함
      */
     private String extractSignatureForBucketing(Failure failure, String mode) {
         Throwable exception = failure.getException();
         
         // 예외가 없는 경우(AssertionError 등)는 헤더 사용 -> 빠른 리턴
         if(exception == null){
             return failure.getTestHeader();
         }
         
         // [최적화] StringBuilder 용량 미리 지정 (재할당 방지)
         StringBuilder sb = new StringBuilder(256);
         // Exception 클래스명만 추가 (Message 제외)
         sb.append(exception.getClass().getName()).append("::");
         
         Description description = failure.getDescription();
         String currentTestClassName = (description != null) ? description.getClassName() : "";
         
         // Inner Class 처리를 위한 Prefix 미리 계산 (반복문 내부 연산 제거)
         String innerClassPrefix = (currentTestClassName != null && !currentTestClassName.isEmpty()) 
                                   ? currentTestClassName + "$" 
                                   : null;
         
         StackTraceElement[] stackTrace = exception.getStackTrace();
         
         for(StackTraceElement elem : stackTrace){
             String className = elem.getClassName();
             
             // [최적화] Fast Ignore Check
             if(isIgnoredFast(className)){
                 continue;
             }
             
             // Generated Test Class 식별 로직
             boolean isGenTest = false;
             if (currentTestClassName != null && !currentTestClassName.isEmpty()) {
                 if (className.equals(currentTestClassName)) {
                     isGenTest = true;
                 } else if (innerClassPrefix != null && className.startsWith(innerClassPrefix)) {
                     isGenTest = true;
                 }
             }
             
             if(isGenTest){
                 sb.append("<GEN_TEST>|");
                 // [최적화] Loop Truncation
                 break; 
             } else {
                 // MUT (라이브러리) 코드는 라인 번호까지 상세 기록
                 sb.append(className)
                   .append(".")
                   .append(elem.getMethodName())
                   .append(":")
                   .append(elem.getLineNumber())
                   .append("|");
             }
         }
         
         return sb.toString();
     }
 

     // 배열 순회 대신 단순 조건문 나열 (CPU 분기 예측 및 인라인화 유리)
     private boolean isIgnoredFast(String className) {
         if (className.startsWith("org.junit.")) return true;
         if (className.startsWith("sun.reflect.")) return true;
         if (className.startsWith("java.lang.reflect.")) return true;
         if (className.startsWith("java.util.concurrent.")) return true;
         if (className.equals("java.lang.Thread")) return true;
         return false;
     }
     
     /**
      * [NEW] Exception 타입 추출 (e.g., "IndexOutOfBoundsException")
      */
     private String extractExceptionType(Failure failure) {
         Throwable exception = failure.getException();
         if (exception == null) {
             return "AssertionError";
         }
         String fullName = exception.getClass().getName();
         int lastDot = fullName.lastIndexOf('.');
         return lastDot >= 0 ? fullName.substring(lastDot + 1) : fullName;
     }
     
     /**
      * [NEW] 테스트 메서드 이름 추출
      */
     private String extractTestName(Failure failure) {
         Description description = failure.getDescription();
         if (description == null) return "unknown";
         
         String methodName = description.getMethodName();
         if (methodName != null && !methodName.isEmpty()) {
             return methodName;
         }
         
         // Fallback to test header
         String header = failure.getTestHeader();
         if (header != null && !header.isEmpty()) {
             // Extract method name from header like "methodName(ClassName)"
             int parenIdx = header.indexOf('(');
             if (parenIdx > 0) {
                 return header.substring(0, parenIdx);
             }
             return header;
         }
         
         return "unknown";
     }

    public void printStats(){
        System.out.println("=== Test Minimization Stats ===");
        System.out.println("Total Failures Checked: " + totalTests.get());
        System.out.println("Unique Failures Kept:   " + uniqueTests.get());
        System.out.println("Duplicates Filtered:    " + duplicateTests.get());
        System.out.println("===============================");
    }
    
    /**
      * 상세한 통계 출력 (각 생성 방식 종료 시점)
      */
     public void printDetailedStats(String mode) {
         String separator = repeat("═", 70);
         System.out.println("\n" + separator);
         System.out.println("  TEST MINIMIZATION STATISTICS - " + mode.toUpperCase());
         System.out.println(separator);
         
         int total = totalTests.get();
         int unique = uniqueTests.get();
         int duplicate = duplicateTests.get();

         // 기본 통계
         double reductionRate = total == 0 ? 0.0 : 
             (double) duplicate / total * 100.0;
         
         System.out.println(String.format("  %-35s %d", "Total Failing Tests Processed:", total));
         System.out.println(String.format("  %-35s %d", "Unique Tests (Kept):", unique));
         System.out.println(String.format("  %-35s %d", "Duplicate Tests (Filtered):", duplicate));
         System.out.println(String.format("  %-35s %.2f%%", "Reduction Rate:", reductionRate));
         System.out.println(String.format("  %-35s %d", "Unique StackTrace Signatures:", uniqueSignatures.size()));
         
         System.out.println(separator);
         
         // 효율성 메시지
         if (duplicate > 0) {
             System.out.println(String.format("  ✓ Successfully reduced test suite by %d tests (%.1f%% reduction)", 
                 duplicate, reductionRate));
         } else {
             System.out.println("  ℹ No duplicate tests found (all tests are unique)");
         }
         
         System.out.println(separator);
         
         // [NEW] Exception별 그룹화된 리포트
         if (!exceptionToTestMap.isEmpty()) {
             System.out.println("\n  UNIQUE EXCEPTIONS & REPRESENTATIVE TESTS:");
             System.out.println("  " + repeat("─", 66));
             
             // Exception 타입별로 정렬
             List<Map.Entry<String, String>> sortedEntries = 
                 new ArrayList<>(exceptionToTestMap.entrySet());
             sortedEntries.sort((e1, e2) -> e1.getKey().compareTo(e2.getKey()));
             
             int index = 1;
             for (Map.Entry<String, String> entry : sortedEntries) {
                 String exceptionType = entry.getKey();
                 String testName = entry.getValue();
                 
                 // 테스트 이름이 길면 생략 부호 추가
                 String displayTestName = testName;
                 if (displayTestName.length() > 35) {
                     displayTestName = displayTestName.substring(0, 32) + "...";
                 }
                 
                 System.out.println(String.format("  [%2d] %-25s → %s", 
                     index, exceptionType, displayTestName));
                 index++;
             }
             System.out.println("  " + repeat("─", 66));
         }
         
         System.out.println(separator + "\n");
     }
    
    /**
     * Java 8 호환 repeat 함수
     */
    private String repeat(String s, int count) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < count; i++) {
            sb.append(s);
        }
        return sb.toString();
    }

    public int getTotalTests() {
        return totalTests.get();
    }

    public int getUniqueTests() {
        return uniqueTests.get();
    }

    public int getDuplicateTests() {
        return duplicateTests.get();
    }

    public Set<String> getUniqueSignatures() {
         return new HashSet<>(uniqueSignatures);
     }
    
    /**
     * [NEW] Bucketing용 메서드들
     */
    
    /**
     * Exception 타입별로 정렬된 예외 목록 반환
     * Bucketing 모드에서 Exception별 그룹을 만들 때 사용
     */
    public List<String> getSortedExceptionTypes() {
        List<String> types = new ArrayList<>(exceptionToTestMap.keySet());
        Collections.sort(types);
        return types;
    }
    
    /**
     * 특정 Exception 타입의 설명 메시지 생성 (코멘트용)
     */
    public String getExceptionBucketComment(String exceptionType) {
        return String.format("// Exception Bucket: %s", exceptionType);
    }
    
    /**
     * Bucketing 모드인지 확인
     */
    public boolean isBucketingEnabled() {
        return Config.ENABLE_TEST_BUCKETING;
    }
    
    /**
     * [NEW] Bucketing용: Exception별 모든 테스트 반환
     */
     public List<String> getTestsForSignature(String signature) {
         Set<String> tests = signatureToTestsMapBucketing.get(signature);
         return tests != null ? new ArrayList<>(tests) : new ArrayList<>();
     }
     
      /**
       * [NEW] Bucketing용: 정렬된 Signature별로 테스트들을 조직화
       * Map<Signature, List<TestNames>>
       * Signature는 Exception Type + StackTrace의 고유 조합 (Minimization 목적)
       */
      public Map<String, List<String>> getExceptionBuckets() {
          Map<String, List<String>> buckets = new LinkedHashMap<>();
          List<String> sortedSignatures = new ArrayList<>(uniqueSignatures);
          Collections.sort(sortedSignatures);
          
          for (String signature : sortedSignatures) {
              List<String> tests = getTestsForSignature(signature);
              if (!tests.isEmpty()) {
                  buckets.put(signature, tests);
              }
          }
          return buckets;
      }
      
      /**
       * [NEW] Bucketing 그룹화용: Exception Type + StackTrace만으로 테스트 그룹화
       * Message, MUT 정보 제외로 더 넓은 범위 그룹화
       * Map<BucketingSignature, List<TestNames>>
       */
        public Map<String, List<String>> getExceptionBucketsForGrouping() {
            Map<String, List<String>> buckets = new LinkedHashMap<>();
            List<String> sortedSignatures = new ArrayList<>(signatureToTestsMapBucketingForGrouping.keySet());
            Collections.sort(sortedSignatures);
            
            for (String signature : sortedSignatures) {
                Set<String> tests = signatureToTestsMapBucketingForGrouping.get(signature);
                if (tests != null && !tests.isEmpty()) {
                    buckets.put(signature, new ArrayList<>(tests));
                }
            }
            return buckets;
        }
}