package Generater.PrimitiveMutation;

import spoon.reflect.code.*;
import Generater.PrimitiveMutation.TriplePairs;
import spoon.Launcher;
import spoon.SpoonException;
import spoon.reflect.code.*;
import spoon.reflect.declaration.*;
import spoon.reflect.factory.Factory;
import spoon.reflect.reference.CtTypeReference;
import spoon.reflect.visitor.filter.TypeFilter;
import spoon.reflect.visitor.CtScanner;
import spoon.support.compiler.VirtualFile;
import spoon.support.reflect.code.*;
import utils.Config;
import utils.Pair;
import Generater.MUTMutation.TestCaseGenerator;
import RegressionOracles.Analyzer;
import RegressionOracles.ObserverInstrumenter;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.lang.annotation.Annotation;
import java.util.*;
import java.util.stream.Collectors;
import spoon.reflect.reference.*;

import Generater.PrimitiveMutation.CombinationIterator;

public class PrimitiveTwayTestGenerator {

    // --- 변경점: static 제거 ---
    private String testClassName;
    private Launcher launcher;
    private Analyzer analyzer;
    private ObserverInstrumenter collector;

    /**
     * 안전한 toString() 호출 - NPE 및 Spoon 예외 방지
     */
    private static String safeToString(Object obj) {
        try {
            return obj.toString();
        } catch (spoon.SpoonException e) {
            // Spoon의 nested class 해결 문제나 NPE 처리
            if (e.getMessage() != null && (e.getMessage().contains("Cannot compute access path to type") ||
                e.getCause() instanceof NullPointerException)) {
                return obj.getClass().getSimpleName() + "@" + Integer.toHexString(obj.hashCode());
            }
            throw e;
        } catch (NullPointerException e) {
            // toString() 중 NPE 발생 시
            return obj.getClass().getSimpleName() + "@" + Integer.toHexString(obj.hashCode());
        } catch (Exception e) {
            // 다른 일반적인 toString() 실패 시
            return obj.getClass().getSimpleName() + "@" + Integer.toHexString(obj.hashCode());
        }
    }

    /**
     * CtThisAccess 요소의 null 타겟 문제를 수정
     */
    private static void fixNullThisAccessElements(CtElement element) {
        element.accept(new CtScanner() {
            @Override
            public <T> void visitCtThisAccess(spoon.reflect.code.CtThisAccess<T> thisAccess) {
                // ❌ thisAccess.setImplicit(true);  // 지우기!
                // explicit/implicit은 그대로 두고, 타입만 정리
                try {
                    CtTypeReference<T> t = thisAccess.getType();
                    if (t != null) {
                        String qn = t.getQualifiedName();
                        if (qn != null && qn.contains("$")) {
                            // "Outer$Inner.this" 같은 경우 프린터가 NPE → 타입 제거
                            thisAccess.setType(null);
                        }
                    }
                } catch (Exception ignore) {
                    // 방어적으로 타입만 제거
                    thisAccess.setType(null);
                }
                super.visitCtThisAccess(thisAccess);
            }

            @Override
            public <T> void visitCtFieldWrite(spoon.reflect.code.CtFieldWrite<T> fw) {
                super.visitCtFieldWrite(fw);
                CtExpression<?> target = fw.getTarget();
                if (target instanceof spoon.reflect.code.CtThisAccess) {
                    spoon.reflect.code.CtThisAccess<?> ta = (spoon.reflect.code.CtThisAccess<?>) target;
                    // implicit/explicit 그대로, 타입만 정리
                    try {
                        if (ta.getType() != null) {
                            String qn = ta.getType().getQualifiedName();
                            if (qn != null && qn.contains("$")) {
                                ta.setType(null);
                            }
                        }
                    } catch (Exception ignore) {
                        ta.setType(null);
                    }
                }
            }

            @Override
            public <T> void visitCtFieldRead(spoon.reflect.code.CtFieldRead<T> fr) {
                super.visitCtFieldRead(fr);
                CtExpression<?> target = fr.getTarget();
                if (target instanceof spoon.reflect.code.CtThisAccess) {
                    spoon.reflect.code.CtThisAccess<?> ta = (spoon.reflect.code.CtThisAccess<?>) target;
                    try {
                        if (ta.getType() != null) {
                            String qn = ta.getType().getQualifiedName();
                            if (qn != null && qn.contains("$")) {
                                ta.setType(null);
                            }
                        }
                    } catch (Exception ignore) {
                        ta.setType(null);
                    }
                }
            }

            @Override
            public <T> void visitCtInvocation(CtInvocation<T> inv) {
                super.visitCtInvocation(inv);
                CtExpression<?> target = inv.getTarget();
                if (target instanceof spoon.reflect.code.CtThisAccess) {
                    spoon.reflect.code.CtThisAccess<?> ta = (spoon.reflect.code.CtThisAccess<?>) target;
                    try {
                        if (ta.getType() != null) {
                            String qn = ta.getType().getQualifiedName();
                            if (qn != null && qn.contains("$")) {
                                ta.setType(null);
                            }
                        }
                    } catch (Exception ignore) {
                        ta.setType(null);
                    }
                }
            }
        });
    }



    /**
     * _mut 변수의 타입을 FQN으로 변환
     */
    private static String convertMutVariablesToFQN(String sourceCode, CtClass<?> clazz) {
        if (sourceCode == null || clazz == null) return sourceCode;
        
        // _mut로 끝나는 변수 선언을 찾아서 타입을 FQN으로 변경
        java.util.regex.Pattern pattern = java.util.regex.Pattern.compile(
                "\\b([A-Za-z_][A-Za-z0-9_]*(?:\\.[A-Za-z_][A-Za-z0-9_]*)*(?:\\$[A-Za-z_][A-Za-z0-9_]*)*(?:\\[\\])?)\\s+(\\w+_mut)\\s*=");
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
     * 클래스에서 simple type name에 해당하는 FQN을 찾기
     */
    private static String findFQNForType(CtClass<?> clazz, String simpleTypeName) {
        try {
            // 클래스 내의 모든 로컬 변수를 스캔하여 타입 정보 수집
            final java.util.Map<String, String> typeMap = new java.util.HashMap<>();
            
            clazz.accept(new CtScanner() {
                @Override
                public <T> void visitCtLocalVariable(CtLocalVariable<T> localVar) {
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


    
    


    private static String safeToStringForSourceCode(Object obj) throws Exception {
        try {
            if (obj instanceof CtElement) {
                CtElement el = (CtElement) obj;
                // 1) 타입만 먼저 정리 (Type.this → this)
                fixNullThisAccessElements(el);
                // 2) 섀도잉 고려해 this. 붙이기
                canonicalizeThisAccesses(el);
            }

            String result;
            if (obj instanceof CtClass) {
                CtClass<?> clazz = (CtClass<?>) obj;
                try {
                    result = clazz.toString();
                    // System.err.println("[DEBUG] Standard toString() succeeded");
                } catch (spoon.SpoonException e) {
                    String msg = e.getMessage() == null ? "" : e.getMessage();
                    if (msg.contains("Cannot compute access path to type")) {
                        // System.err.println("[INFO] Using FQN conversion due to nested class issue: " + msg);

                        // FQN 변환
                        result = generateSourceCodeWithSmartFQN(clazz);

                        // 변환 후에도 동일하게: 타입 정리 → this. 복구
                        fixNullThisAccessElements(clazz);
                        canonicalizeThisAccesses(clazz);

                        try {
                            result = clazz.toString();
                            // System.err.println("[DEBUG] Fallback toString() after FQN succeeded");
                        } catch (Exception ignore) {
                            // System.err.println("[WARN] Using generated source string from FQN conversion");
                        }
                    } else {
                        throw e;
                    }
                } catch (NullPointerException npe) {
                    // NullPointerException 발생 시 - CtThisAccess 문제일 가능성 높음
                    // System.out.println("[INFO] NullPointerException in toString() - attempting FQN conversion");
                    
                    // ★ CtThisAccess 요소들을 모두 제거하거나 안전하게 처리
                    removeProblematicThisAccess(clazz);
                    
                    try {
                        result = clazz.toString();
                        // System.out.println("[INFO] Successfully generated source code after removing CtThisAccess issues");
                    } catch (Exception e2) {
                        // 마지막 수단: FQN 변환
                        // System.out.println("[INFO] Fallback to FQN conversion");
                        // System.out.println("[INFO] Re-applying CtThisAccess fix before FQN conversion");
                        
                        // FQN 변환 전에도 한 번 더 처리
                        removeProblematicThisAccess(clazz);
                        
                        try {
                            result = generateSourceCodeWithSmartFQN(clazz);
                        } catch (Exception e3) {
                            // System.out.println("[ERROR] FQN conversion also failed: " + e3.getMessage());
                            // 최후의 수단: 매우 단순한 문자열 기반 처리
                            throw e3;
                        }
                    }
                }

                // 마지막에 또 fixNull()를 호출해서 explicit를 implicit로 만들지 말 것!
                result = convertMutVariablesToFQN(result, clazz);
                return result;
            } else {
                return obj.toString();
            }
        } catch (spoon.SpoonException e) {
            // System.out.println("[WARN] SpoonException in safeToStringForSourceCode: " + e.getMessage());
            // e.printStackTrace();
            throw new RuntimeException("SpoonException: " + e.getMessage(), e);
        } catch (NullPointerException e) {
            // System.out.println("[WARN] NullPointerException in safeToStringForSourceCode");
            // e.printStackTrace();
            throw new RuntimeException("NullPointerException during source code generation", e);
        }
    }
    
    /**
     * CtThisAccess 요소들의 null 타입을 수정
     * 
     * 전략: this를 제거하는 것이 아니라, null 타입을 올바른 타입으로 설정
     * 목적: 원본 코드를 최대한 보존하면서 Spoon pretty printer의 NPE 방지
     * 
     * Public으로 변경하여 Main.java에서도 사용 가능
     */
    public static void removeProblematicThisAccess(CtClass<?> clazz) {
        try {
            // 모든 CtFieldAccess 찾기 (CtFieldRead와 CtFieldWrite 포함)
            List<CtFieldAccess> fieldAccesses = clazz.getElements(new TypeFilter<CtFieldAccess>(CtFieldAccess.class));
            // System.out.println("[DEBUG] Found " + fieldAccesses.size() + " CtFieldAccess elements");
            
            int removedCount = 0;
            
            for (CtFieldAccess fieldAccess : fieldAccesses) {
                try {
                    // Target이 CtThisAccess인지 확인
                    CtExpression<?> target = fieldAccess.getTarget();
                    if (target instanceof CtThisAccess) {
                        CtThisAccess thisAccess = (CtThisAccess) target;
                        
                        // CtThisAccess의 타입이 null인지 확인
                        if (thisAccess.getType() == null) {
                            // System.out.println("[DEBUG] Found CtFieldAccess with null-type CtThisAccess: " + fieldAccess.getVariable().getSimpleName());
                            
                            // Target을 null로 설정하여 implicit 접근으로 변환
                            // this.field → field
                            try {
                                fieldAccess.setTarget(null);
                                // System.out.println("[DEBUG] Successfully converted to implicit access: " + fieldAccess.getVariable().getSimpleName());
                                removedCount++;
                            } catch (Exception e) {
                                // System.out.println("[DEBUG] Could not set target to null: " + e.getMessage());
                                
                                // 대안: 필드 이름으로 새로운 CtVariableAccess 생성
                                try {
                                    // 단순히 target을 제거하는 대신 부모 컨텍스트에서 교체
                                    // System.out.println("[DEBUG] Attempting alternative fix...");
                                } catch (Exception e2) {
                                    // System.out.println("[DEBUG] Alternative fix failed: " + e2.getMessage());
                                }
                            }
                        }
                    }
                } catch (Exception e) {
                    // System.out.println("[DEBUG] Error processing CtFieldAccess: " + e.getMessage());
                }
            }
            
            // System.out.println("[INFO] CtThisAccess removed from field access: " + removedCount);
            
             // 추가: 남아있는 모든 CtThisAccess 강제 처리
             List<CtThisAccess> remainingThisAccesses = clazz.getElements(new TypeFilter<CtThisAccess>(CtThisAccess.class));
             // System.out.println("[DEBUG] Remaining standalone CtThisAccess: " + remainingThisAccesses.size());
             
             int deletedCount = 0;
             int fixedByParentCount = 0;
             
             // 역순으로 처리하여 삭제 시 인덱스 문제 방지
             // ★ 중요: 조건 없이 모든 남은 CtThisAccess를 처리
             // getType()이 non-null이어도 내부가 broken일 수 있음
             for (int i = remainingThisAccesses.size() - 1; i >= 0; i--) {
                 CtThisAccess thisAccess = remainingThisAccesses.get(i);
                 try {
                     // ★ 중요: 제거하면 안 되는 경우들:
                     // 1. 메서드 호출의 인자: typeSer.writeTypePrefixForObject(this, jgen)
                     // 2. return 문의 값: return this;
                     CtElement parent = thisAccess.getParent();
                     
                     // 메서드 호출의 인자 위치 체크
                     boolean isMethodArgument = parent instanceof CtInvocation;
                     
                     // return 문의 반환 값 체크
                     boolean isReturnValue = parent instanceof CtReturn;
                     
                     if (isMethodArgument || isReturnValue) {
                         // 메서드 호출 인자 또는 return 값이면 건너뛰기 (제거 금지)
                         // System.out.println("[DEBUG] Skipping CtThisAccess used as method argument or return value");
                         continue;
                     }
                     
                     // getType() 확인 (디버그용)
                     CtTypeReference<?> type = null;
                     boolean hasNullType = false;
                     try {
                         type = thisAccess.getType();
                         hasNullType = (type == null);
                     } catch (Exception e) {
                         hasNullType = true;
                         // System.out.println("[DEBUG] getType() threw exception for #" + i + ": " + e.getMessage());
                     }
                     
                     // System.out.println("[DEBUG] Processing remaining CtThisAccess #" + i + 
                     //     ", parent: " + (parent != null ? parent.getClass().getSimpleName() : "null") +
                     //     ", hasNullType: " + hasNullType);
                     
                     // 전략 1: 부모가 CtFieldAccess인 경우 target 제거
                     if (parent instanceof CtFieldAccess) {
                         CtFieldAccess fieldAccess = (CtFieldAccess) parent;
                         try {
                             fieldAccess.setTarget(null);
                            // System.out.println("[DEBUG] Successfully removed from CtFieldAccess");
                            fixedByParentCount++;
                            continue;
                        } catch (Exception e) {
                            // System.out.println("[DEBUG] setTarget(null) failed: " + e.getMessage());
                            // 실패 시 아래 delete() 시도
                        }
                    }
                    
                    // 전략 2: 직접 삭제 시도
                    try {
                        thisAccess.delete();
                        // System.out.println("[DEBUG] Successfully deleted CtThisAccess #" + i);
                        deletedCount++;
                    } catch (Exception e) {
                        // System.out.println("[WARN] delete() failed for CtThisAccess #" + i + ": " + e.getMessage());
                        // 최후의 수단: 타입을 강제로 설정 시도
                        try {
                            CtTypeReference<?> classType = clazz.getReference();
                            if (classType != null) {
                                thisAccess.setType(classType);
                                // System.out.println("[DEBUG] Last resort: set type to class reference");
                                fixedByParentCount++;
                            }
                        } catch (Exception e3) {
                            // System.out.println("[ERROR] Even last resort failed: " + e3.getMessage());
                        }
                    }
                } catch (Exception e) {
                    // System.out.println("[WARN] Error processing CtThisAccess #" + i + ": " + e.getMessage());
                    // e.printStackTrace();
                }
            }
            
            // System.out.println("[INFO] Remaining CtThisAccess processing: fixedByParent=" + fixedByParentCount + ", deleted=" + deletedCount);
            
            // 최종 확인 및 강제 처리
            List<CtThisAccess> finalCheck = clazz.getElements(new TypeFilter<CtThisAccess>(CtThisAccess.class));
            int nullTypeCount = 0;
            int forcedFixCount = 0;
            
            // System.out.println("[INFO] Final check: total CtThisAccess=" + finalCheck.size());
            
            // 모든 남은 CtThisAccess를 다시 검사하고 null type이면 강제 수정
            for (int i = finalCheck.size() - 1; i >= 0; i--) {
                CtThisAccess ta = finalCheck.get(i);
                try {
                    CtTypeReference<?> type = ta.getType();
                    if (type == null) {
                        nullTypeCount++;
                        // System.out.println("[WARN] Found null type CtThisAccess in final check #" + i);
                        
                        // 강제로 클래스 타입 설정
                        try {
                            CtTypeReference<?> classType = clazz.getReference();
                            ta.setType(classType);
                            // System.out.println("[INFO] Forced type setting for CtThisAccess #" + i);
                            forcedFixCount++;
                        } catch (Exception e) {
                            // System.out.println("[ERROR] Could not force type setting: " + e.getMessage());
                            
                            // 최후의 수단: CtFieldAccess parent에서 제거
                            CtElement parent = ta.getParent();
                            if (parent instanceof CtFieldAccess) {
                                try {
                                    ((CtFieldAccess) parent).setTarget(null);
                                    // System.out.println("[INFO] Removed as last resort from parent");
                                    forcedFixCount++;
                                } catch (Exception e2) {
                                    // System.out.println("[ERROR] Last resort also failed: " + e2.getMessage());
                                }
                            }
                        }
                    }
                } catch (Exception e) {
                    // System.out.println("[WARN] Error checking CtThisAccess #" + i + ": " + e.getMessage());
                }
            }
            
            // System.out.println("[INFO] Final check result: nullType=" + nullTypeCount + ", forcedFix=" + forcedFixCount);
            
            // if (nullTypeCount > forcedFixCount) {
                // System.out.println("[ERROR] Still have " + (nullTypeCount - forcedFixCount) + " unfixed CtThisAccess - toString() will likely fail!");
            // }
            
        } catch (Exception e) {
            // System.out.println("[WARN] Error in removeProblematicThisAccess: " + e.getMessage());
            // e.printStackTrace();
        }
    }



    public static int dupTests = 0;
    public static long overheadTime = 0;

    private final Map<String, CachedData> cache = new HashMap<>();
    private final HashMap<CtMethod, Set<Integer>> generatedTests = new HashMap<>();
    // --- 변경점 끝 ---

    public enum TwayStatus {
        SUCCESS, // 성공적으로 새 테스트 생성
        DUPLICATE, // 중복 테스트 생성됨
        NO_POSITIONS_TO_MUTATE, // 변환할 위치 없음
        ALL_COMBINATIONS_EXHAUSTED_FOR_T, // 현재 T-way 조합 모두 소진
        ERROR // 기타 오류
    }

    // ========== GETTERS AND SETTERS ===========
    public Launcher getLauncher() {
        return launcher;
    }

    public String getTestClassName() {
        return testClassName;
    }

    // ========== INNER CLASSES ===========

    public static class TwayGenerationResult {
        public final TwayStatus status;
        public final Pair<CtClass, String> testPair;

        public TwayGenerationResult(TwayStatus status, Pair<CtClass, String> testPair) {
            this.status = status;
            this.testPair = testPair;
        }
    }

    static class CachedData {
         List<TriplePairs> maskedPositions;
         Iterator<Map<String, Object>> combIter;
         List<Map<String, Object>> generatedCombinationsCache;

         int currentTway = 2;
         int maxTway = 0;
         boolean isRandomMode = false;
     }

    // ========== CONSTRUCTORS ===========

    public PrimitiveTwayTestGenerator(String testFile) {
        // --- 변경점: this 키워드 사용하여 인스턴스 변수 초기화 ---
        this.testClassName = extractFileName(testFile, ".java");
        Config.TEST_FILE = testFile;
        this.launcher = new Launcher();
        this.launcher.getEnvironment().setAutoImports(false);
        this.analyzer = new Analyzer();
        this.collector = new ObserverInstrumenter(this.launcher.getFactory());
        // --- 변경점 끝 ---
    }

    // ========== SERVICE METHODS ===========

    // --- 변경점: static 제거 ---
    // PrimitiveTwayTestGenerator.java

    public TwayGenerationResult generateTwayTestCases(CtMethod<?> testMethod,
            int count,
            String originalfileName,
            CtClass<?> skeletalTestClass,
            int attemptNumber) {

        String methodName = testMethod.getSimpleName();
        String key = skeletalTestClass.getQualifiedName() + "_" + methodName;

        CachedData cachedData = this.cache.get(key);

        // 1. 캐시 초기화 (메서드 첫 방문 시)
        if (cachedData == null) {
            cachedData = new CachedData();
            cachedData.maskedPositions = findMaskedPositions(testMethod);
            cachedData.maxTway = cachedData.maskedPositions.size();
            cachedData.generatedCombinationsCache = new ArrayList<>(); // 캐시 리스트 초기화

            if (cachedData.maskedPositions.size() == 0) {
                cache.put(key, cachedData);
                return new TwayGenerationResult(TwayStatus.NO_POSITIONS_TO_MUTATE, null);
            }

            if (cachedData.maskedPositions.size() <= 1) {
                cachedData.isRandomMode = true;
            } else {
                cachedData.isRandomMode = false;
                cachedData.currentTway = 2;
                // Create combination iterator without pre-generating all combinations
                List<TriplePairs> topTPositions = findTopTPositions(cachedData.maskedPositions, cachedData.currentTway);
                cachedData.combIter = generateTwayCombinationsForTopPositions(topTPositions);
            }
            cache.put(key, cachedData);
        }

        // Return immediately if no positions to mutate
        if (cachedData.maskedPositions.isEmpty()) {
            return new TwayGenerationResult(TwayStatus.NO_POSITIONS_TO_MUTATE, null);
        }

        CtMethod<?> testMethodClone = testMethod.clone();

        // Handle random mode
        if (cachedData.isRandomMode) {
            applyRandomMutation(testMethodClone, cachedData.maskedPositions);
        }
        else {
             // [복구] 이전 방식: pos1, pos2가 겹치지만 다음 pos가 추가되는 방식
             // T=2: [pos1, pos2]
             // T=3: [pos1, pos2, pos3]  ← pos1, pos2는 겹침, pos3 추가
             // T=4: [pos1, pos2, pos3, pos4]  ← 기존 포함, pos4 추가
             
             while (attemptNumber >= cachedData.generatedCombinationsCache.size()) {

                 if (cachedData.combIter.hasNext()) {
                     cachedData.generatedCombinationsCache.add(cachedData.combIter.next());
                 } else {
                
                     if (cachedData.currentTway >= cachedData.maxTway) {
                         return new TwayGenerationResult(TwayStatus.ALL_COMBINATIONS_EXHAUSTED_FOR_T, null);
                     }

                     cachedData.currentTway++;
                     List<TriplePairs> topTPositions = findTopTPositions(cachedData.maskedPositions,
                             cachedData.currentTway);
                     cachedData.combIter = generateTwayCombinationsForTopPositions(topTPositions);
                     if (!cachedData.combIter.hasNext()) {
                         return new TwayGenerationResult(TwayStatus.ALL_COMBINATIONS_EXHAUSTED_FOR_T, null);
                     }
                 }
             }
             Map<String, Object> combination = cachedData.generatedCombinationsCache.get(attemptNumber);
             applyAllMasks(testMethodClone, cachedData.maskedPositions, combination);
         }

        List<CtStatement> mutatedStmts = extractBodyStatements(testMethodClone);
        if (checkDuplication(testMethod, mutatedStmts) || mutatedStmts.isEmpty()) {
            return new TwayGenerationResult(TwayStatus.DUPLICATE, null);
        }
        
        if (Config.REGRESSION_MODE && mutatedStmts.size() > 0) {
            CtStatement lastStmt = mutatedStmts.get(mutatedStmts.size() - 1);
            CtAbstractInvocation mut = TestCaseGenerator.getMUT(lastStmt);

            if (lastStmt.getElements(new TypeFilter<>(CtLocalVariable.class)).size() <= 0 &&
                    mut != null && mut instanceof CtInvocationImpl) {

                CtLocalVariable mutant_assign = null;
                CtTypeReference returnType = ((CtInvocationImpl) mut).getType();

                if (returnType != null && !returnType.getSimpleName().equals("void")
                        && !mut.getExecutable().getSimpleName().equals("hashCode")) {

                    // Check for wildcard types or type variables that cannot be used as concrete types
                    String qualifiedName = returnType.getQualifiedName();
                    String simpleName = returnType.getSimpleName();

                    // Skip if type is wildcard (?), type variable (T, E, etc.), or unknown
                    if (qualifiedName == null || qualifiedName.equals("?") ||
                        simpleName.equals("?") || simpleName.length() == 1 ||
                        qualifiedName.equals("java.lang.reflect.Type")) {
                        // Cannot create variable with wildcard or type variable - skip
                    } else {
                        Launcher launcher = new Launcher();
                        Factory factory = launcher.getFactory();
                        String name = simpleName.toLowerCase();
                        name = name.replace("[", "");
                        name = name.replace("]", "");

                        // FQN을 사용하여 새로운 타입 참조 생성
                        CtTypeReference<?> fqnTypeRef = factory.createReference(qualifiedName);

                        mutant_assign = factory.createLocalVariable(
                                fqnTypeRef,
                                name + "_mut",
                                ((CtInvocationImpl) mut)
                        );
                    }
                }

                if (mutant_assign != null) {
                    mutatedStmts.remove(lastStmt);
                    mutatedStmts.add(mutant_assign);
                }
            }
        }

        String newClassName = skeletalTestClass.getSimpleName() + "_P_" + methodName + "_" + count;

        if (Config.REGRESSION_MODE) {
            // Generate basic test class and method without code snippets
            Pair<CtClass, List<String>> classAndMethodStringPair = generateMethodsWithoutCodeSnippet(mutatedStmts, newClassName, skeletalTestClass);
            if(classAndMethodStringPair==null){
                // System.out.println("[ERROR] Failed to generate methods without code snippet for: " + newClassName);
                return new TwayGenerationResult(TwayStatus.ERROR, null);
            }
            CtClass<Object> generatedClass = classAndMethodStringPair.getKey();

            // Add regression oracle to the generated test
            Pair<CtClass, List<String>> observerAddedTestAndStringPair = addRegressionOracleToTest(generatedClass, newClassName);

            if (observerAddedTestAndStringPair == null) {
                // System.out.println("[ERROR] Failed to add regression oracle for: " + newClassName);
                return new TwayGenerationResult(TwayStatus.ERROR, null);
            } 
            
            // Get final instrumented class
            CtClass<?> finalInstrumentedClass = observerAddedTestAndStringPair.getKey();

            canonicalizeThisAccesses(finalInstrumentedClass);
            this.launcher.getEnvironment().setPreserveLineNumbers(false);
            // Generate source code using safe toString() for source code
            String rawSourceCode;
            try {
                rawSourceCode = safeToStringForSourceCode(finalInstrumentedClass);
            } catch (Exception e) {
                // System.out.println("[ERROR] Failed to generate source code for: " + newClassName);
                // System.out.println("[ERROR] Cause: " + e.getMessage());
                // System.out.println("[ERROR] Exception type: " + e.getClass().getName());
                // e.printStackTrace();
                return new TwayGenerationResult(TwayStatus.ERROR, null);
            }
            
            // Apply final this reference normalization to override pretty printer
            String normalizedSourceCode = rawSourceCode;
            if (rawSourceCode.contains(".this")) {
                // Pattern to match qualified this references like "OuterClass.InnerClass.this"
                // This handles both ".this." and ".this;" or ".this)" cases
                java.util.regex.Pattern pattern = java.util.regex.Pattern.compile(
                    "\\b[A-Za-z_][A-Za-z0-9_]*(?:\\.[A-Za-z_][A-Za-z0-9_]*)+\\.this\\b"
                );
                normalizedSourceCode = pattern.matcher(rawSourceCode).replaceAll("this");
            }

            // Fix Spoon bug: nested class constructors incorrectly output super() instead of this()
            // Spoon's toString() converts "this(args)" to "super(args)" in nested class no-arg constructors
            normalizedSourceCode = fixConstructorCalls(normalizedSourceCode, skeletalTestClass);
            
            // Also fix qualified class references like "MocksSerializationTest.AlreadySerializable.class"
            if (normalizedSourceCode.contains(".class")) {
                // Pattern to match qualified class references in method calls
                java.util.regex.Pattern classPattern = java.util.regex.Pattern.compile(
                    "\\b[A-Za-z_][A-Za-z0-9_]*(?:\\.[A-Za-z_][A-Za-z0-9_]*)+\\.([A-Za-z_][A-Za-z0-9_]*)\\.class\\b"
                );
                normalizedSourceCode = classPattern.matcher(normalizedSourceCode).replaceAll("$1.class");
            }

            // Fix references to original class name in helper methods to use new generated class name
            String originalClassName = skeletalTestClass.getSimpleName();
            String generatedClassName = finalInstrumentedClass.getSimpleName();
            if (!originalClassName.equals(generatedClassName) && originalClassName != null && generatedClassName != null) {
                // Replace constructor calls: "new OriginalClass(" -> "new NewClass("
                java.util.regex.Pattern constructorPattern = java.util.regex.Pattern.compile(
                    "\\bnew\\s+" + java.util.regex.Pattern.quote(originalClassName) + "\\s*\\("
                );
                normalizedSourceCode = constructorPattern.matcher(normalizedSourceCode).replaceAll("new " + generatedClassName + "(");

                // Replace variable declarations: "OriginalClass var = " -> "NewClass var = "
                java.util.regex.Pattern variablePattern = java.util.regex.Pattern.compile(
                    "\\b" + java.util.regex.Pattern.quote(originalClassName) + "\\s+([a-zA-Z_][a-zA-Z0-9_]*)\\s*="
                );
                normalizedSourceCode = variablePattern.matcher(normalizedSourceCode).replaceAll(generatedClassName + " $1 =");

                // Replace class references in nested class access: "OriginalClass.NestedClass" -> "NewClass.NestedClass"
                java.util.regex.Pattern nestedClassPattern = java.util.regex.Pattern.compile(
                    "\\b" + java.util.regex.Pattern.quote(originalClassName) + "\\.([A-Z][a-zA-Z0-9_]*)"
                );
                normalizedSourceCode = nestedClassPattern.matcher(normalizedSourceCode).replaceAll(generatedClassName + ".$1");
            }

            // Generate final code with FQN replacement
            String finalStr = normalizedSourceCode.replace("Logger.observe", "RegressionOracles.RegressionUtil.Logger.observe");

            // Preserve FQN from original source file
            finalStr = preserveFQNFromOriginal(finalStr, skeletalTestClass);

            // Collect missing imports from skeletal class
            Set<String> missingImports = collectMissingImportsFromSkeletal(skeletalTestClass);

            // Insert imports into the source code
            if (missingImports != null && !missingImports.isEmpty()) {
                finalStr = insertImportsIntoSource(finalStr, missingImports);
            }

            // Return final result
            Pair<CtClass, String> finalPair = new Pair<>(finalInstrumentedClass, finalStr);

            return new TwayGenerationResult(TwayStatus.SUCCESS, finalPair);
        }
        else{
            CtClass<?> mutatedTest = generateMethods(mutatedStmts, newClassName, skeletalTestClass);

            // Apply same canonicalization as regression mode
            canonicalizeThisAccesses(mutatedTest);
            this.launcher.getEnvironment().setPreserveLineNumbers(false);

            String mutatedTestString = null;
            try {
                mutatedTestString = safeToStringForSourceCode(mutatedTest);
            } catch (Exception e) {
                // System.out.println("[ERROR] Failed to generate mutated test source code for: " + newClassName);
                // System.out.println("[ERROR] Cause: " + e.getMessage());
                // System.out.println("[ERROR] Exception type: " + e.getClass().getName());
                // e.printStackTrace();
                return new TwayGenerationResult(TwayStatus.ERROR, null);
            }

            // Apply final this reference normalization to override pretty printer
            String normalizedSourceCode = mutatedTestString;
            if (mutatedTestString.contains(".this")) {
                // Pattern to match qualified this references like "OuterClass.InnerClass.this"
                // This handles both ".this." and ".this;" or ".this)" cases
                java.util.regex.Pattern pattern = java.util.regex.Pattern.compile(
                    "\\b[A-Za-z_][A-Za-z0-9_]*(?:\\.[A-Za-z_][A-Za-z0-9_]*)+\\.this\\b"
                );
                normalizedSourceCode = pattern.matcher(mutatedTestString).replaceAll("this");
            }

            // Also fix qualified class references like "MocksSerializationTest.AlreadySerializable.class"
            if (normalizedSourceCode.contains(".class")) {
                // Pattern to match qualified class references in method calls
                java.util.regex.Pattern classPattern = java.util.regex.Pattern.compile(
                    "\\b[A-Za-z_][A-Za-z0-9_]*(?:\\.[A-Za-z_][A-Za-z0-9_]*)+\\.([A-Za-z_][A-Za-z0-9_]*)\\.class\\b"
                );
                normalizedSourceCode = classPattern.matcher(normalizedSourceCode).replaceAll("$1.class");
            }

            // Fix Spoon bug: nested class constructors incorrectly output super() instead of this()
            normalizedSourceCode = fixConstructorCalls(normalizedSourceCode, skeletalTestClass);

            // Fix type inference issues - restore original parameter types
            if (normalizedSourceCode.contains("TemplateType")) {
                // Fix method parameters that were incorrectly inferred as TemplateType -> String
                java.util.regex.Pattern templateTypeParamPattern = java.util.regex.Pattern.compile(
                    "\\bTemplateType\\s+([a-zA-Z_][a-zA-Z0-9_]*)\\s*,"
                );
                normalizedSourceCode = templateTypeParamPattern.matcher(normalizedSourceCode).replaceAll("String $1,");

                // Also handle last parameter case
                java.util.regex.Pattern templateTypeLastParamPattern = java.util.regex.Pattern.compile(
                    "\\bTemplateType\\s+([a-zA-Z_][a-zA-Z0-9_]*)\\s*\\)"
                );
                normalizedSourceCode = templateTypeLastParamPattern.matcher(normalizedSourceCode).replaceAll("String $1)");
            }

            // Fix references to original class name in helper methods to use new generated class name
            String originalClassName = skeletalTestClass.getSimpleName();
            String generatedClassName = mutatedTest.getSimpleName();
            if (!originalClassName.equals(generatedClassName) && originalClassName != null && generatedClassName != null) {
                // Replace constructor calls: "new OriginalClass(" -> "new NewClass("
                java.util.regex.Pattern constructorPattern = java.util.regex.Pattern.compile(
                    "\\bnew\\s+" + java.util.regex.Pattern.quote(originalClassName) + "\\s*\\("
                );
                normalizedSourceCode = constructorPattern.matcher(normalizedSourceCode).replaceAll("new " + generatedClassName + "(");

                // Replace variable declarations: "OriginalClass var = " -> "NewClass var = "
                java.util.regex.Pattern variablePattern = java.util.regex.Pattern.compile(
                    "\\b" + java.util.regex.Pattern.quote(originalClassName) + "\\s+([a-zA-Z_][a-zA-Z0-9_]*)\\s*="
                );
                normalizedSourceCode = variablePattern.matcher(normalizedSourceCode).replaceAll(generatedClassName + " $1 =");

                // Replace class references in nested class access: "OriginalClass.NestedClass" -> "NewClass.NestedClass"
                java.util.regex.Pattern nestedClassPattern = java.util.regex.Pattern.compile(
                    "\\b" + java.util.regex.Pattern.quote(originalClassName) + "\\.([A-Z][a-zA-Z0-9_]*)"
                );
                normalizedSourceCode = nestedClassPattern.matcher(normalizedSourceCode).replaceAll(generatedClassName + ".$1");
            }

            // Preserve FQN from original source file
            normalizedSourceCode = preserveFQNFromOriginal(normalizedSourceCode, skeletalTestClass);

            // Collect missing imports from skeletal class
            Set<String> missingImports = collectMissingImportsFromSkeletal(skeletalTestClass);

            // Insert imports into the source code
            if (missingImports != null && !missingImports.isEmpty()) {
                normalizedSourceCode = insertImportsIntoSource(normalizedSourceCode, missingImports);
            }

            return new TwayGenerationResult(TwayStatus.SUCCESS, new Pair<>(mutatedTest, normalizedSourceCode));
        }
        
    }
    // --- 변경점 끝 ---

    private void applyRandomMutation(CtMethod<?> testMethodClone, List<TriplePairs> maskedPositions) {
        for (TriplePairs position : maskedPositions) {
            Object oldValue = position.getLiteral().getValue();
            Object candidate = generateRandomValue(oldValue, position.getDetectedType());
            if (candidate == null) continue;

            // ★ 항상 캐스팅
            Object newValue = attemptTypeCastingWithDetectedType(oldValue, candidate, position.getDetectedType());
            if (newValue == null) continue;

            CtLiteral<?> literalInClone = findLiteralByPath(testMethodClone, position.getStmtPath());
            if (literalInClone == null) continue;

            CtLiteral<Object> replacement = (CtLiteral<Object>) literalInClone.clone();
            replacement.setValue(newValue);
            replaceLiteralSafely(literalInClone, replacement);
        }
    }

    // PrimitiveTwayTestGenerator.java

    public static CtClass<?> generateMethods(List<CtStatement> stmts, String newClassName,
            CtClass<?> skeletalTestClass) {

        Factory factory = skeletalTestClass.getFactory();
        factory.getEnvironment().disableConsistencyChecks();

        CtClass<?> clazz = skeletalTestClass.clone();
        clazz.setSimpleName(newClassName);
        
        // Apply normalization to fix nested class this references after cloning
        // normalizeThisAccessInClass(clazz);

        // 3) 테스트 메서드 생성
        CtMethod<Object> testMethod = factory.Core().createMethod();
        CtBlock<Object> body = factory.Core().createBlock();

        // Use statements directly instead of code snippets to preserve type information
        body.setStatements(stmts);
        testMethod.setBody(body);
        testMethod.setSimpleName("mockTest");
        testMethod.setType((CtTypeReference) factory.Type().createReference(void.class));
        testMethod.setModifiers(Collections.singleton(ModifierKind.PUBLIC));
        testMethod.setThrownTypes(Collections.singleton(
                factory.Type().createReference(Throwable.class)));

        // @Test(timeout=1000)
        CtAnnotationType at = factory.createAnnotationType("org.junit.Test");
        CtAnnotation<Annotation> anno = factory.createAnnotation();
        anno.setAnnotationType(at.getReference());
        anno.addValue("timeout", 1000);
        testMethod.addAnnotation(anno);

        clazz.addMethod(testMethod);
        return clazz;
    }

    private static Pair<CtClass, List<String>> generateMethodsWithoutCodeSnippet(List<CtStatement> stmts,
                                                                                String newClassName, CtClass<?> skeletalTestClass) {

        Factory factory = skeletalTestClass.getFactory();
        factory.getEnvironment().disableConsistencyChecks();

   
        CtClass<?> clazz = skeletalTestClass.clone();
        clazz.setSimpleName(newClassName);
        
        // Apply normalization to fix nested class this references after cloning
        // normalizeThisAccessInClass(clazz);

        CtMethod<Object> newTestMethod = factory.Core().createMethod();
        CtBlock<Object> methodBody = factory.Core().createBlock();

        methodBody.setStatements(stmts);
        newTestMethod.setBody(methodBody);

        newTestMethod.setSimpleName("mockTest");
        newTestMethod.setType((CtTypeReference) factory.Type().createReference(void.class));
        newTestMethod.setModifiers(Collections.singleton(ModifierKind.PUBLIC));
        newTestMethod.setThrownTypes(Collections.singleton(factory.Type().createReference(Throwable.class)));

   
        CtAnnotationType at = factory.createAnnotationType("org.junit.Test");
        CtAnnotation<Annotation> anno = factory.createAnnotation();
        anno.setAnnotationType(at.getReference());
        anno.addValue("timeout", 1000);
        newTestMethod.addAnnotation(anno);


        clazz.addMethod(newTestMethod);


        List<String> classAndMethodStringPair = new ArrayList<>();
        try{
            classAndMethodStringPair.add(safeToString(clazz));
            classAndMethodStringPair.add(safeToString(newTestMethod));
        }catch(Exception e){
            // System.out.println("[WARN] Exception in generateMethodsWithoutCodeSnippet while converting to string");
            // System.out.println("[WARN] Exception type: " + e.getClass().getName());
            // System.out.println("[WARN] Message: " + e.getMessage());
            // e.printStackTrace();
            return null;
        }
        

        return new Pair<>(clazz, classAndMethodStringPair);
    }

    private Pair<CtClass, List<String>> addRegressionOracleToTest(CtClass<Object> generatedTest, String testName) {
        try {
            Map<CtMethod, List<CtLocalVariable>> localVariablesPerTestMethod = this.analyzer.analyze(generatedTest, false);
            Map<CtMethod, List<CtLocalVariable>> localVariablesPrimitive = this.analyzer.analyze(generatedTest, true);

            Set<CtMethod<?>> methods = generatedTest.getMethods();
            CtMethod<?> targetTestMethod = null;

            for (CtMethod<?> method : methods) {
                if ("mockTest".equals(method.getSimpleName())) {
                    targetTestMethod = method;
                    break;
                }
            }
            if (targetTestMethod == null) {
                // System.out.println("[WARN] Method 'mockTest' not found in generated class: " + generatedTest.getSimpleName());
                return null;
            }
            Pair<CtClass, List<String>> observerAddedClassAndStringPair = this.collector.instrumentObserver(targetTestMethod, localVariablesPerTestMethod, localVariablesPrimitive, testName);

            return observerAddedClassAndStringPair;
        } catch (Exception e) {
            // System.out.println("[WARN] Exception in addRegressionOracleToTest: " + e.getMessage());
            // System.out.println("[WARN] Exception type: " + e.getClass().getName());
            // e.printStackTrace();
            return null;
        }
    }


    private static List<TriplePairs> findTopTPositions(List<TriplePairs> maskedPositions, int t) {
        List<TriplePairs> topPositions = new ArrayList<>();
        Map<String, Set<CtElement>> primitiveTypeAndVal = PrimitiveParser.getPrimitiveTypeAndVal();
        if (Config.Tway_TOPT) {
            Map<TriplePairs, Integer> positionPoolSizeMap = new HashMap<>();
            for (TriplePairs triple : maskedPositions) {
                String castedType = triple.getDetectedType(); // 예: "double"
                int poolSize = 0;
                if (primitiveTypeAndVal.containsKey(castedType)) {
                    poolSize = primitiveTypeAndVal.get(castedType).size();
                }
                positionPoolSizeMap.put(triple, poolSize);
            }

            // 내림차순 정렬
            List<Map.Entry<TriplePairs, Integer>> sorted = new ArrayList<>(positionPoolSizeMap.entrySet());
            sorted.sort((e1, e2) -> e2.getValue().compareTo(e1.getValue()));

            for (int i = 0; i < Math.min(t, sorted.size()); i++) {
                topPositions.add(sorted.get(i).getKey());
            }
        } else {
            List<TriplePairs> randomPositions = new ArrayList<>(maskedPositions);
            Collections.shuffle(randomPositions);
            for (int i = 0; i < Math.min(t, randomPositions.size()); i++) {
                topPositions.add(randomPositions.get(i));
            }
        }
        return topPositions;
    }

    private static Iterator<Map<String, Object>> generateTwayCombinationsForTopPositions(
            List<TriplePairs> topPositions) {

        Map<TriplePairs, List<Object>> mapping = generateCombinationMappingForTopPositions(topPositions);
        final int LIMIT = 1000000;
        mapping.replaceAll((k, v) -> v.size() > LIMIT ? v.subList(0, LIMIT) : v);

        return new CombinationIterator(mapping);
    }

    // ... (이하 다른 static 메서드들은 변경 없음) ...

    // PrimitiveTwayTestGenerator.java에 이 코드로 교체하십시오.

    private static Map<TriplePairs, List<Object>> generateCombinationMappingForTopPositions(
        List<TriplePairs> topPositions) {

        Map<String, Set<CtElement>> primitiveTypeAndVal = PrimitiveParser.getPrimitiveTypeAndVal();
        Map<TriplePairs, List<Object>> combinationMapping = new HashMap<>();

        for (TriplePairs triple : topPositions) {
            String key = normalizeTypeKey(triple.getDetectedType());
            if ("unknown".equals(key)) {
                combinationMapping.put(triple, Collections.emptyList());
                continue;
            }

            Set<CtElement> candidates = primitiveTypeAndVal.getOrDefault(key, Collections.emptySet());
            List<Object> values = new ArrayList<>(candidates.size());

            for (CtElement c : candidates) {
                Object typed = valueFromPoolElementForType(c, key);
                if (typed != null) values.add(typed);
            }

            combinationMapping.put(triple, values);
        }
        return combinationMapping;
    }


    private static void generateCombinationsRecursive(Map<TriplePairs, List<Object>> mapping,
            List<TriplePairs> keys,
            int index,
            Map<String, Object> current,
            List<Map<String, Object>> results) {

        if (index == keys.size()) {
            results.add(new HashMap<>(current));
            return;
        }

        TriplePairs keyTriple = keys.get(index);
        String keyString = safeToString(keyTriple.getStmtPath());
        List<Object> values = mapping.get(keyTriple);

        if (values == null || values.isEmpty()) {
            current.put(keyString, null);
            generateCombinationsRecursive(mapping, keys, index + 1, current, results);
            current.remove(keyString); // 백트래킹
        } else {
            for (Object value : values) {
                current.put(keyString, value);
                generateCombinationsRecursive(mapping, keys, index + 1, current, results);
                current.remove(keyString); // 백트래킹
            }
        }
    }

    private static List<TriplePairs> findMaskedPositions(CtMethod<?> method) {
        List<TriplePairs> result = new ArrayList<>();
        if (method.getBody() != null) {
            extractLiteralsRecursively(
                    method.getBody().getStatements(),
                    new ArrayList<>(),
                    result);
        }
        return result;
    }

    private static void extractLiteralsRecursively(
            List<CtStatement> statements,
            List<Integer> path,
            List<TriplePairs> result) {

        for (int i = 0; i < statements.size(); i++) {
            CtStatement stmt = statements.get(i);
            List<Integer> currentPath = new ArrayList<>(path);
            currentPath.add(i);

            // Recursive search within blocks
            if (stmt instanceof CtBlock) {
                extractLiteralsRecursively(
                        ((CtBlock<?>) stmt).getStatements(),
                        currentPath,
                        result);

                // Recursive search within if-then/if-else
            } else if (stmt instanceof CtIf) {
                CtIf ctIf = (CtIf) stmt;
                if (ctIf.getThenStatement() != null) {
                    extractLiteralsRecursively(
                            Collections.singletonList(ctIf.getThenStatement()),
                            currentPath,
                            result);
                }
                if (ctIf.getElseStatement() != null) {
                    extractLiteralsRecursively(
                            Collections.singletonList(ctIf.getElseStatement()),
                            currentPath,
                            result);
                }

                // Recursive search within loop body
            } else if (stmt instanceof CtLoop) {
                CtLoop loop = (CtLoop) stmt;
                if (loop.getBody() != null) {
                    extractLiteralsRecursively(
                            Collections.singletonList(loop.getBody()),
                            currentPath,
                            result);
                }

                // Regular statements: extract and record literals only
            } else {
                List<CtLiteral<?>> literals = stmt.getElements(new TypeFilter<>(CtLiteral.class));
                int literalIndex = 0;
                for (CtLiteral<?> literal : literals) {
                    if (!isLiteral(literal.getType()))
                        continue;
                    if (literal.getValue() == null)
                        continue;

                    String type = detectFinalCastType(literal);
                    if ("unknown".equals(type))
                        continue;

                    List<Integer> literalPath = new ArrayList<>(currentPath);
                    literalPath.add(literalIndex++);
                    result.add(new TriplePairs(literalPath, literal, type));
                }
            }
        }
    }

    private static boolean isLiteral(CtTypeReference<?> type) {
            if (type.isPrimitive() || type.getQualifiedName().equals("java.lang.String"))
                return true;
            return false;
        }

    private static String detectFinalCastType(CtLiteral<?> literal) {
        // ★ 0-1) 배열 인덱스 문맥 체크 (최우선!)
        // 배열 접근 표현식 안에 있는 리터럴은 무조건 int 타입이어야 함
        // 예: array[0.25] (X) → array[0] (O)
        CtElement parent = literal.getParent();
        while (parent != null) {
            if (parent instanceof spoon.reflect.code.CtArrayRead 
                || parent instanceof spoon.reflect.code.CtArrayWrite) {
                // 배열 인덱스는 항상 int 타입
                return "int";
            }
            // 배열 접근 표현식이 아니면 더 위로 올라가지 않음
            // (너무 멀리 올라가면 다른 컨텍스트와 혼동됨)
            if (parent instanceof CtAbstractInvocation 
                || parent instanceof CtVariable 
                || parent instanceof CtStatement) {
                break;
            }
            parent = parent.getParent();
        }
        
        // ★ 0-2) 배열 생성 크기 문맥 체크 (최우선!)
        // 배열 생성 시 크기를 지정하는 리터럴은 무조건 int 타입이어야 함
        // 예: new double[50.0] (X) → new double[50] (O)
        CtNewArray<?> newArrayParent = literal.getParent(CtNewArray.class);
        if (newArrayParent != null) {
            // dimensionExpressions: 배열 크기를 나타내는 표현식들
            // 예: new int[5][10] → dimensionExpressions = [5, 10]
            List<CtExpression<Integer>> dimExprs = newArrayParent.getDimensionExpressions();
            if (dimExprs != null) {
                for (CtExpression<Integer> dimExpr : dimExprs) {
                    // 현재 리터럴이 dimension expression에 포함되어 있으면 int 타입
                    if (dimExpr == literal || containsLiteral(dimExpr, literal)) {
                        return "int";
                    }
                }
            }
        }
        
        // 1) 배열 초기화 리터럴 문맥: new T[] { ... } -> 컴포넌트 타입 우선
        CtNewArray<?> newArray = literal.getParent(CtNewArray.class);
        if (newArray != null && newArray.getType() instanceof CtArrayTypeReference) {
            CtArrayTypeReference<?> arr = (CtArrayTypeReference<?>) newArray.getType();
            if (arr.getComponentType() != null) {
                return arr.getComponentType().getQualifiedName(); // byte, short, char, ...
            }
        }

        // 2) 가장 가까운 호출/생성자 호출까지 "위로" 올라가서 인자 타입을 본다
        CtElement cur = literal;
        CtAbstractInvocation<?> owningCall = null;
        while (cur != null) {
            if (cur instanceof CtInvocation<?> || cur instanceof CtConstructorCall<?>) {
                owningCall = (CtAbstractInvocation<?>) cur;
                break;
            }
            cur = cur.getParent();
        }
        if (owningCall != null) {
            // literal을 포함하는 실제 인자 위치를 찾는다 (중첩 표현식 고려)
            List<CtExpression<?>> args = owningCall.getArguments();
            int argIndex = -1;
            for (int i = 0; i < args.size(); i++) {
                CtExpression<?> a = args.get(i);
                if (a == literal || containsLiteral(a, literal)) {
                    argIndex = i;
                    break;
                }
            }
            if (argIndex >= 0 && owningCall.getExecutable() != null) {
                List<CtTypeReference<?>> paramTypes = owningCall.getExecutable().getParameters();
                if (argIndex < paramTypes.size()) {
                    CtTypeReference<?> paramType = paramTypes.get(argIndex);
                    if (paramType != null && !"java.lang.reflect.Type".equals(paramType.getQualifiedName())) {
                        return paramType.getQualifiedName(); // ★ 호출 인자 타입을 최우선으로 사용
                    }
                }
            }
        }

        // 3) 기존 캐스트가 있으면 그 타입 사용
        List<CtTypeReference<?>> casts = literal.getTypeCasts();
        if (casts != null && !casts.isEmpty()) {
            return casts.get(0).getQualifiedName();
        }

        // 4) 변수/필드 선언 타입 (메서드 파라미터는 건너뜀)
        cur = literal;
        while (cur != null && !(cur instanceof CtVariable<?>)) cur = cur.getParent();
        if (cur instanceof CtVariable<?>) {
            CtVariable<?> var = (CtVariable<?>) cur;
            if (!(var instanceof CtParameter<?>)) {
                CtTypeReference<?> varTypeRef = var.getType();
                if (varTypeRef != null && !"java.lang.reflect.Type".equals(varTypeRef.getQualifiedName())) {
                    return varTypeRef.getQualifiedName();
                }
            }
        }

        // 5) 부모 표현식 타입
        cur = literal;
        while (cur.getParent() instanceof CtExpression<?>) {
            CtExpression<?> expr = (CtExpression<?>) cur.getParent();
            CtTypeReference<?> exprType = expr.getType();
            if (exprType != null && !"java.lang.reflect.Type".equals(exprType.getQualifiedName())) {
                return exprType.getQualifiedName();
            }
            cur = expr;
        }

        // 6) 리터럴 자체 타입
        CtTypeReference<?> litType = literal.getType();
        if (litType != null && !"java.lang.reflect.Type".equals(litType.getQualifiedName())) {
            return litType.getQualifiedName();
        }

        return "unknown";
    }




    // Helper method to check if an expression contains a specific literal
    private static boolean containsLiteral(CtExpression<?> expr, CtLiteral<?> target) {
        if (expr == target) {
            return true;
        }
        List<CtLiteral<?>> literals = expr.getElements(new TypeFilter<>(CtLiteral.class));
        return literals.contains(target);
    }


    private static void applyCombination(CtMethod<?> testMethodClone, List<TriplePairs> topPositions,
            Map<String, Object> combination) {
        for (TriplePairs triple : topPositions) {
            String key = safeToString(triple.getStmtPath());
            Object candidateValue = combination.get(key);
            if (candidateValue == null)
                continue;

            // 복사본에서 리터럴을 동적으로 찾음
            CtLiteral<?> literalInClone = findLiteralByPath(testMethodClone, triple.getStmtPath());
            if (literalInClone == null)
                continue;

            Object oldValue = literalInClone.getValue();
            Object castedVal = attemptTypeCastingWithDetectedType(oldValue, candidateValue, triple.getDetectedType());
            if (castedVal == null)
                continue;

            CtLiteral<Object> clonedLiteral = (CtLiteral<Object>) literalInClone.clone();
            clonedLiteral.setValue(castedVal);
            replaceLiteralSafely(literalInClone, clonedLiteral);
        }
    }

    private static Object generateRandomValue(Object currentValue, String detectedType) {
        Map<String, Set<CtElement>> pools = PrimitiveParser.getPrimitiveTypeAndVal();
        String key = normalizeTypeKey(detectedType);
        List<CtElement> candidates = new ArrayList<>(pools.getOrDefault(key, Collections.emptySet()));
        if (candidates.isEmpty()) return null;

        CtElement pick = candidates.get(new Random().nextInt(candidates.size()));
        return valueFromPoolElementForType(pick, key);
    }


    private static void applyAllMasks(CtMethod<?> testClone, List<TriplePairs> maskedPositions, Map<String, Object> combination) {
        for (TriplePairs tp : maskedPositions) {
            CtLiteral<?> orig = findLiteralByPath(testClone, tp.getStmtPath());
            if (orig == null) continue;

            String key = safeToString(tp.getStmtPath());
            Object base = combination.containsKey(key) ? combination.get(key) : generateRandomValue(orig.getValue(), tp.getDetectedType());

            // ★ 항상 캐스팅
            Object newVal = attemptTypeCastingWithDetectedType(orig.getValue(), base, tp.getDetectedType());
            if (newVal == null) newVal = orig.getValue();

            CtLiteral<Object> replacement = (CtLiteral<Object>) orig.clone();
            replacement.setValue(newVal);
            replaceLiteralSafely(orig, replacement);
        }
    }



    private static CtLiteral<?> findLiteralByPath(
            CtMethod<?> method, List<Integer> path) {

        // Traverse statements/blocks/if/loop structures
        CtElement cur = method.getBody();
        for (int depth = 0; depth < path.size() - 1; depth++) {
            int idx = path.get(depth);
            if (cur instanceof CtBlock<?>) {
                List<CtStatement> stmts = ((CtBlock<?>) cur).getStatements();
                if (idx >= stmts.size())
                    return null; // Index out of bounds check
                cur = stmts.get(idx);
            } else if (cur instanceof CtIf && idx == 0) {
                cur = ((CtIf) cur).getThenStatement();
            } else if (cur instanceof CtIf && idx == 1) {
                cur = ((CtIf) cur).getElseStatement();
            } else if (cur instanceof CtLoop) {
                cur = ((CtLoop) cur).getBody();
            } else {
                return null;
            }
            if (cur == null)
                return null; // Check for null after traversal
        }

        // Select literal using last index
        int litIdx = path.get(path.size() - 1);
        if (!(cur instanceof CtStatement))
            return null; // Ensure current element is a statement
        CtStatement stmt = (CtStatement) cur;

        List<CtLiteral<?>> lits = new ArrayList<>();
        for (CtLiteral<?> lit : stmt.getElements(new TypeFilter<>(CtLiteral.class))) {
            if (lit.getValue() != null && isLiteral(lit.getType())) {
                lits.add(lit);
            }
        }

        if (litIdx < 0 || litIdx >= lits.size()) {
            return null;
        }
        return lits.get(litIdx);
    }

    private static void replaceLiteralSafely(CtLiteral<?> originalLiteral, CtLiteral<?> newLiteral) {
        // 위치/주석 유지
        newLiteral.setPosition(originalLiteral.getPosition());
        originalLiteral.getComments().forEach(c -> newLiteral.addComment(c.clone()));

        CtElement parent = originalLiteral.getParent();

        // 부모가 단항 연산자(+/-)면, 연산자 자체를 없애고 newLiteral로 통째 교체
        // -> newLiteral 값이 음수면 '-'가 그대로 출력되고, 양수면 그대로 양수로 출력됨
        if (parent instanceof CtUnaryOperator<?>) {
            CtUnaryOperator<?> uop = (CtUnaryOperator<?>) parent;
            UnaryOperatorKind kind = uop.getKind();
            if (kind == UnaryOperatorKind.NEG || kind == UnaryOperatorKind.POS) {
                uop.replace(newLiteral); // 부호 조작 없이 그대로 교체
                return;
            }
        }

        // 그 외에는 원래 리터럴만 교체
        originalLiteral.replace(newLiteral);
    }


    private static Object attemptTypeCastingWithDetectedType(Object oldValue,
        Object newValue,
        String detectedType) {
        if (newValue == null) return null;

        // 이미 같은 런타임 타입이면 그대로
        if (oldValue != null && oldValue.getClass().isAssignableFrom(newValue.getClass())) {
            return newValue;
        }

        String key = normalizeTypeKey(detectedType);
        Object coerced = coerceToType(newValue, key);
        return coerced; // 실패하면 null
    }


    // ========= UTILITY METHODS ===========

    private static boolean isAnonymousOrLocalNested(String qn) {
        return qn != null && qn.matches(".*\\$\\d+(\\$.*)?");
    }

    private static boolean isJavaSdkNested(String qn) {
        return qn != null && (qn.startsWith("java.") || qn.startsWith("javax."));
    }

    private static String generateSourceCodeWithSmartFQN(CtClass<?> clazz) {
        // System.err.println("\n[DEBUG] Using smart FQN conversion for " + clazz.getSimpleName());
        try {
            CtClass<?> workingClazz = clazz.clone();

            workingClazz.accept(new CtScanner() {
                @Override
                public <T> void visitCtTypeReference(CtTypeReference<T> reference) {
                    try {
                        String qn = reference.getQualifiedName();
                        if (qn != null && qn.contains("$")) {
                            // 1) 익명/로컬, 2) 자바 SDK 타입(java.*, javax.*)은 건드리지 않음
                            if (!(isAnonymousOrLocalNested(qn) || isJavaSdkNested(qn))) {
                                // 문제 가능성이 있는 중첩 타입만 FQN 점 표기로 교체
                            }
                        }
                    } catch (Exception e) {
                        // System.err.println("  Exception in FQN convert: " + e.getMessage());
                    }
                    super.visitCtTypeReference(reference);
                }
            });

            String result = workingClazz.toString();
            // System.err.println("  Successfully generated source code with smart FQN");
            return result;
        } catch (Exception e) {
            // System.err.println("  Failed smart FQN approach: " + e.getMessage());
            throw e;
        }
    }



    private static void canonicalizeThisAccesses(CtElement root) {
        root.accept(new CtScanner() {

            private <X> spoon.reflect.code.CtThisAccess<X> explicitThis(Factory f) {
                spoon.reflect.code.CtThisAccess<X> t = f.Core().createThisAccess();
                t.setImplicit(false); // "this" 출력
                t.setType(null);
                return t;
            }

            private <X> spoon.reflect.code.CtThisAccess<X> implicitThis(Factory f) {
                spoon.reflect.code.CtThisAccess<X> t = f.Core().createThisAccess();
                t.setImplicit(true); // "this" 생략
                t.setType(null);
                return t;
            }

            private boolean isShadowedByLocalOrParam(CtElement where, String name) {
                if (name == null) return false;
                CtExecutable<?> exec = where.getParent(CtExecutable.class);
                if (exec != null) {
                    for (Object p : exec.getParameters()) {
                        CtParameter<?> cp = (CtParameter<?>) p;
                        if (name.equals(cp.getSimpleName())) return true;
                    }
                    CtBlock<?> blk = where.getParent(CtBlock.class);
                    if (blk != null) {
                        List<CtLocalVariable<?>> locals =
                            blk.getElements(new TypeFilter<>(CtLocalVariable.class));
                        for (CtLocalVariable<?> lv : locals) {
                            if (name.equals(lv.getSimpleName())) return true;
                        }
                    }
                }
                return false;
            }

            private CtField<?> findEnclosingFieldByName(CtElement where, String name) {
                CtClass<?> owner = where.getParent(CtClass.class);
                if (owner == null || name == null) return null;
                for (CtField<?> f : owner.getFields()) {
                    if (name.equals(f.getSimpleName())) return f;
                }
                return null;
            }

            @Override
            public <T> void visitCtThisAccess(spoon.reflect.code.CtThisAccess<T> thisAccess) {
                // Check if this is used as a standalone expression (not as target of field/method access)
                CtElement parent = thisAccess.getParent();

                boolean needsExplicit = false;

                // Case 1: Method/constructor argument
                if (parent instanceof CtAbstractInvocation<?>) {
                    CtAbstractInvocation<?> inv = (CtAbstractInvocation<?>) parent;
                    for (CtExpression<?> arg : inv.getArguments()) {
                        if (arg == thisAccess) {
                            needsExplicit = true;
                            break;
                        }
                    }
                }

                // Case 2: Return statement
                if (parent instanceof CtReturn<?>) {
                    needsExplicit = true;
                }

                if (needsExplicit) {
                    // Keep explicit for method arguments and return statements
                    thisAccess.setImplicit(false);
                } else {
                    // Default: implicit for field/method access targets
                    thisAccess.setImplicit(true);
                }

                thisAccess.setType(null); // Always remove type to avoid NPE
                super.visitCtThisAccess(thisAccess);
            }

            @Override
            public <T> void visitCtFieldWrite(spoon.reflect.code.CtFieldWrite<T> fw) {
                super.visitCtFieldWrite(fw);
                String fieldName = (fw.getVariable() != null) ? fw.getVariable().getSimpleName() : null;
                boolean shadow = isShadowedByLocalOrParam(fw, fieldName);

                CtExpression<?> tgt = fw.getTarget();
                if (tgt == null) {
                    // ★ implicit target(null)도 처리
                    fw.setTarget(shadow ? explicitThis(fw.getFactory()) : implicitThis(fw.getFactory()));
                } else if (tgt instanceof spoon.reflect.code.CtThisAccess) {
                    fw.setTarget(shadow ? explicitThis(fw.getFactory()) : implicitThis(fw.getFactory()));
                }
            }

            @Override
            public <T> void visitCtFieldRead(spoon.reflect.code.CtFieldRead<T> fr) {
                super.visitCtFieldRead(fr);
                String fieldName = (fr.getVariable() != null) ? fr.getVariable().getSimpleName() : null;
                boolean shadow = isShadowedByLocalOrParam(fr, fieldName);

                CtExpression<?> tgt = fr.getTarget();
                if (tgt == null) {
                    fr.setTarget(shadow ? explicitThis(fr.getFactory()) : implicitThis(fr.getFactory()));
                } else if (tgt instanceof spoon.reflect.code.CtThisAccess) {
                    fr.setTarget(shadow ? explicitThis(fr.getFactory()) : implicitThis(fr.getFactory()));
                }
            }

            @Override
            public <T> void visitCtInvocation(CtInvocation<T> inv) {
                super.visitCtInvocation(inv);
                CtExpression<?> tgt = inv.getTarget();
                String callName = (inv.getExecutable() != null) ? inv.getExecutable().getSimpleName() : null;
                boolean shadow = isShadowedByLocalOrParam(inv, callName);

                if (tgt == null) {
                    inv.setTarget(shadow ? explicitThis(inv.getFactory()) : implicitThis(inv.getFactory()));
                } else if (tgt instanceof spoon.reflect.code.CtThisAccess) {
                    inv.setTarget(shadow ? explicitThis(inv.getFactory()) : implicitThis(inv.getFactory()));
                }
            }

            @Override
            public <T, A extends T> void visitCtAssignment(CtAssignment<T, A> assign) {
                super.visitCtAssignment(assign);

                // ★ 좌변이 VariableWrite(필드가 아닌 변수로 잡힌 경우)라도
                // 같은 이름의 필드가 있고 섀도잉이면 FieldWrite(this.field)로 교체
                CtExpression<T> lhs = assign.getAssigned();
                if (lhs instanceof CtVariableWrite) {
                    @SuppressWarnings("rawtypes")
                    CtVariableWrite vw = (CtVariableWrite) lhs;
                    String name = (vw.getVariable() != null) ? vw.getVariable().getSimpleName() : null;

                    if (isShadowedByLocalOrParam(assign, name)) {
                        CtField<?> fld = findEnclosingFieldByName(assign, name);
                        if (fld != null) {
                            Factory f = assign.getFactory();

                            @SuppressWarnings({ "rawtypes", "unchecked" })
                            CtFieldWrite fw = f.Core().createFieldWrite();
                            @SuppressWarnings({ "rawtypes", "unchecked" })
                            CtFieldReference fr = fld.getReference();

                            fw.setVariable(fr);
                            fw.setTarget(explicitThis(f)); // this.field 로 강제
                            // 타입 제네릭 미스 경고 억제
                            @SuppressWarnings({ "rawtypes", "unchecked" })
                            CtExpression casted = (CtExpression) fw;
                            assign.setAssigned(casted);
                        }
                    }
                }
            }
        });
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

    // --- 변경점: static 제거하고 인스턴스 변수 사용 ---
    private boolean checkDuplication(CtMethod testMethod, List<CtStatement> generatedStmts) {
        if (generatedStmts == null || generatedStmts.size() == 0) {
            return false;
        }
        long startTime = System.currentTimeMillis();
        StringBuilder stmtString;
        try {
            stmtString = appendStmts(generatedStmts);
        } catch (Exception e) {
            return false;
        }

        int hashVal = safeToString(stmtString).hashCode();

        Set<Integer> genTests = this.generatedTests.computeIfAbsent(testMethod, k -> new HashSet<>());
        if (genTests.contains(hashVal)) {
            dupTests++;
            long endTime = System.currentTimeMillis();
            overheadTime += (endTime - startTime);
            return true;
        } else {
            genTests.add(hashVal);
            long endTime = System.currentTimeMillis();
            overheadTime += (endTime - startTime);
            return false;
        }
    }
    // --- 변경점 끝 ---

    private static StringBuilder appendStmts(List<CtStatement> generatedStmts) throws Exception {
        StringBuilder stmtString = new StringBuilder();
        for (CtStatement stmt : generatedStmts) {
            stmtString.append(safeToString(stmt));
        }
        return stmtString;
    }

    public static List<CtStatement> extractBodyStatements(CtMethod<?> testMethod) {
        if (testMethod == null || testMethod.getBody() == null) {
            return Collections.emptyList();
        }
        return testMethod.getBody().getStatements();
    }


    private static Boolean toBoolean(Object candidateValue) {
        if (candidateValue instanceof Number) {
            Number num = (Number) candidateValue;
            return (num.doubleValue() != 0.0);
        }
        if (candidateValue instanceof Boolean) {
            return (Boolean) candidateValue;
        }
        if (candidateValue instanceof String) {
            return Boolean.parseBoolean((String) candidateValue);
        }
        return false;
    }

    private static Byte toByte(Object val) {
        if (val instanceof Number) {
            return ((Number) val).byteValue();
        } else if (val instanceof Character) {
            return (byte) ((Character) val).charValue();
        }
        return null;
    }

    private static Short toShort(Object val) {
        if (val instanceof Number) {
            return ((Number) val).shortValue();
        } else if (val instanceof Character) {
            return (short) ((Character) val).charValue();
        }
        return null;
    }

    private static Character toChar(Object val) {
        if (val instanceof Character) {
            return (Character) val;
        } else if (val instanceof Number) {
            return (char) ((Number) val).intValue();
        } else if (val instanceof String) {
            String str = (String) val;
            if (str.length() == 1) {
                return str.charAt(0);
            }
        }
        return null;
    }

    private static Double toDouble(Object val) {
        if (val instanceof Number) {
            return ((Number) val).doubleValue();
        } else if (val instanceof Character) {
            return (double) ((Character) val);
        }
        return null;
    }

    private static Float toFloat(Object val) {
        if (val instanceof Number) {
            return ((Number) val).floatValue();
        } else if (val instanceof Character) {
            return (float) ((Character) val);
        }
        return null;
    }

    private static Integer toInt(Object val) {
        if (val instanceof Number) {
            return ((Number) val).intValue();
        } else if (val instanceof Character) {
            return (int) ((Character) val);
        }
        return null;
    }

    private static Long toLong(Object val) {
        if (val instanceof Number) {
            return ((Number) val).longValue();
        } else if (val instanceof Character) {
            return (long) ((Character) val);
        }
        return null;
    }

    @SuppressWarnings("unchecked")
    private static <T> void setOperandSafely(CtUnaryOperator<T> unaryOp, CtExpression<?> operand) {
        unaryOp.setOperand((CtExpression<T>) operand);
    }
    
    /**
     * Normalizes CtThisAccess references in a class to use simple names
     * instead of fully qualified names for nested classes.
     * This fixes the issue where "this.field" becomes "OuterClass.InnerClass.this.field"
     */
    private static void normalizeThisAccessInClass(CtClass<?> ctClass) {
        if (ctClass == null) return;

        ctClass.accept(new CtScanner() {
            private <X> spoon.reflect.code.CtThisAccess<X> simpleThis(Factory f) {
                spoon.reflect.code.CtThisAccess<X> t = f.createThisAccess();
                t.setImplicit(true);
                t.setType(null); // 타입 제거 (implicit this에는 불필요)
                return t;
            }

            @Override
            public <T> void visitCtThisAccess(spoon.reflect.code.CtThisAccess<T> thisAccess) {
                // 어떤 경우든 implicit + type 제거
                thisAccess.setImplicit(true);
                thisAccess.setType(null);
                super.visitCtThisAccess(thisAccess);
            }

            @Override
            public <T> void visitCtFieldWrite(spoon.reflect.code.CtFieldWrite<T> fw) {
                super.visitCtFieldWrite(fw);
                if (fw.getTarget() instanceof spoon.reflect.code.CtThisAccess) {
                    fw.setTarget(simpleThis(fw.getFactory()));
                }
            }

            @Override
            public <T> void visitCtFieldRead(spoon.reflect.code.CtFieldRead<T> fr) {
                super.visitCtFieldRead(fr);
                if (fr.getTarget() instanceof spoon.reflect.code.CtThisAccess) {
                    fr.setTarget(simpleThis(fr.getFactory()));
                }
            }

            @Override
            public <T> void visitCtInvocation(CtInvocation<T> inv) {
                super.visitCtInvocation(inv);
                if (inv.getTarget() instanceof spoon.reflect.code.CtThisAccess) {
                    inv.setTarget(simpleThis(inv.getFactory()));
                }
            }
        });
    }

    /**
     * Inserts imports into source code after package declaration
     */
    private static String insertImportsIntoSource(String sourceCode, Set<String> imports) {
        if (imports == null || imports.isEmpty() || sourceCode == null) {
            return sourceCode;
        }

        // Find the position to insert imports (after package declaration)
        int insertPosition = 0;
        String[] lines = sourceCode.split("\n");
        StringBuilder result = new StringBuilder();

        boolean packageFound = false;
        boolean importsInserted = false;

        for (int i = 0; i < lines.length; i++) {
            String line = lines[i].trim();

            // Add current line
            result.append(lines[i]).append("\n");

            // Insert imports after package declaration
            if (!importsInserted && line.startsWith("package ") && line.endsWith(";")) {
                packageFound = true;
                result.append("\n");
                for (String imp : imports) {
                    result.append(imp).append("\n");
                }
                importsInserted = true;
            }
            // If no package found and we see the first import or class declaration, insert before it
            else if (!packageFound && !importsInserted &&
                     (line.startsWith("import ") || line.startsWith("public class ") || line.startsWith("class "))) {
                // We need to insert before this line, so remove it from result and insert imports first
                result.setLength(result.length() - lines[i].length() - 1); // Remove the line we just added
                for (String imp : imports) {
                    result.append(imp).append("\n");
                }
                result.append("\n");
                result.append(lines[i]).append("\n"); // Re-add the current line
                importsInserted = true;
            }
        }

        return result.toString();
    }

    /**
     * Collects missing imports from skeletal class by scanning all type references
     */
    private static Set<String> collectMissingImportsFromSkeletal(CtClass<?> skeletal) {
        Set<String> imports = new LinkedHashSet<>();

        if (skeletal == null) {
            return imports;
        }

        String skeletalPackage = skeletal.getPackage() != null ?
            skeletal.getPackage().getQualifiedName() : "";

        String skeletalQualifiedName = skeletal.getQualifiedName();

        skeletal.accept(new CtScanner() {
            @Override
            public <T> void visitCtTypeReference(CtTypeReference<T> reference) {
                try {
                    String qualifiedName = reference.getQualifiedName();

                    if (qualifiedName == null || qualifiedName.isEmpty()) {
                        super.visitCtTypeReference(reference);
                        return;
                    }

                    // Skip primitives
                    if (reference.isPrimitive()) {
                        super.visitCtTypeReference(reference);
                        return;
                    }

                    // Skip arrays - we'll handle component type
                    if (reference instanceof CtArrayTypeReference) {
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

                    // Skip java.lang package
                    if (qualifiedName.startsWith("java.lang.")) {
                        String afterLang = qualifiedName.substring("java.lang.".length());
                        if (!afterLang.contains(".")) {
                            super.visitCtTypeReference(reference);
                            return;
                        }
                    }

                    // Skip same package
                    String typePackage = "";
                    int lastDot = qualifiedName.lastIndexOf('.');
                    if (lastDot > 0) {
                        typePackage = qualifiedName.substring(0, lastDot);
                    }

                    if (typePackage.equals(skeletalPackage)) {
                        super.visitCtTypeReference(reference);
                        return;
                    }

                    // For FQN types like java.io.Serializable, add import
                    if (qualifiedName.contains(".")) {
                        // Replace comma with dot (Spoon may use comma for inner types)
                        String importType = qualifiedName.replace(',', '.');
                        // Remove array brackets
                        importType = importType.replace("[]", "");
                        imports.add("import " + importType + ";");
                    }

                } catch (Exception e) {
                    // Ignore exceptions during type reference scanning
                }
                super.visitCtTypeReference(reference);
            }
        });

        return imports;
    }

    /**
     * Count oracle statements in source code
     */
    private static int countOracles(String sourceCode) {
        int count = 0;
        for (String line : sourceCode.split("\n")) {
            if (line.contains("Logger.observe") || line.contains("RegressionUtil")) {
                count++;
            }
        }
        return count;
    }

    /**
     * Preserves fully qualified names (FQN) from the original source file
     * Spoon's pretty printer may shorten FQNs, so we restore them from the original source
     */
    private static String preserveFQNFromOriginal(String sourceCode, CtClass<?> skeletalClass) {
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
            // System.err.println("[ERROR] Error reading source file in preserveFQNFromOriginal: " + e.getMessage());
        }

        return sourceCode;
    }

    /**
     * Fixes Spoon bug where nested class constructors with this() calls are output as super()
     * Since Spoon already converts this() to super() in the AST, we need to check the original source file
     */
    private static String fixConstructorCalls(String sourceCode, CtClass<?> skeletalClass) {
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
            // System.err.println("[ERROR] Error reading source file in fixConstructorCalls: " + e.getMessage());
        }

        return sourceCode;
    }

    // wrapper → primitive 로 통일하고 우리가 쓰는 키로 맞춥니다.
    private static String normalizeTypeKey(String detectedType) {
        if (detectedType == null) return "unknown";
        switch (detectedType) {
            case "java.lang.Byte":      return "byte";
            case "java.lang.Short":     return "short";
            case "java.lang.Integer":   return "int";
            case "java.lang.Long":      return "long";
            case "java.lang.Float":     return "float";
            case "java.lang.Double":    return "double";
            case "java.lang.Character": return "char";
            case "java.lang.Boolean":   return "boolean";
            case "byte":
            case "short":
            case "int":
            case "long":
            case "float":
            case "double":
            case "char":
            case "boolean":
            case "java.lang.String":
                return detectedType;
            default:
                return detectedType;
        }
    }

    private static Object coerceToType(Object v, String normalizedKey) {
        switch (normalizedKey) {
            case "byte":
                if (v instanceof Number)   return ((Number) v).byteValue();
                if (v instanceof Character) return (byte) ((Character) v).charValue();
                return null;
            case "short":
                if (v instanceof Number)   return ((Number) v).shortValue();
                if (v instanceof Character) return (short) ((Character) v).charValue();
                return null;
            case "char":
                if (v instanceof Character) return v;
                if (v instanceof Number)     return (char) ((Number) v).intValue();
                if (v instanceof String) {
                    String s = (String) v;
                    return s.length() == 1 ? s.charAt(0) : null;
                }
                return null;
            case "int":
                if (v instanceof Number)   return ((Number) v).intValue();
                if (v instanceof Character) return (int) ((Character) v).charValue();
                return null;
            case "long":
                if (v instanceof Number)   return ((Number) v).longValue();
                if (v instanceof Character) return (long) ((Character) v).charValue();
                return null;
            case "float":
                if (v instanceof Number)   return ((Number) v).floatValue();
                if (v instanceof Character) return (float) ((Character) v).charValue();
                return null;
            case "double":
                if (v instanceof Number)   return ((Number) v).doubleValue();
                if (v instanceof Character) return (double) ((Character) v).charValue();
                return null;
            case "boolean":
                if (v instanceof Boolean) return v;
                if (v instanceof Number)  return ((Number) v).doubleValue() != 0.0;
                if (v instanceof String)  return Boolean.parseBoolean((String) v);
                return null;
            case "java.lang.String":
                return String.valueOf(v);
            default:
                return null;
        }
    }

    private static Object valueFromPoolElementForType(CtElement e, String normalizedKey) {
        if (e instanceof CtLiteral<?>) {
            Object v = ((CtLiteral<?>) e).getValue();
            if (v == null) return null;
            return coerceToType(v, normalizedKey);
        } else if (e instanceof CtUnaryOperatorImpl<?>) {
            CtUnaryOperatorImpl<?> u = (CtUnaryOperatorImpl<?>) e;
            if (u.getKind() == UnaryOperatorKind.NEG && u.getOperand() instanceof CtLiteral<?>) {
                Object op = ((CtLiteral<?>) u.getOperand()).getValue();
                if (op instanceof Number) {
                    // 부호는 그대로 보존해서, 요청 타입으로 강제 변환
                    double neg = -((Number) op).doubleValue();
                    return coerceToType(neg, normalizedKey);
                }
            }
        }
        return null;
    }




    
}