package Generater.MUTMutation;

import spoon.reflect.CtModel;
import spoon.reflect.code.*;
import spoon.reflect.declaration.*;
import spoon.reflect.factory.Factory;
import spoon.reflect.reference.CtTypeReference;
import spoon.reflect.visitor.filter.TypeFilter;
import spoon.support.reflect.code.CtConstructorCallImpl;
import utils.Pair;
import utils.Config;
import spoon.reflect.code.CtLiteral;

import java.util.*;

public class CandidatePool {

    /**
     * this pool is for local variable like org.jfree.data.time.TimeSeries timeSeries0 = new org.jfree.data.time.TimeSeries(quarter1);
     * note that this might cause problem when wrong sequence order
     * do not use it easily
     */
    // private static HashMap<CtTypeReference, Set<CtExpression>> definitionPool = new HashMap();
    /**
     * this pool is used to generate the method to arguments map
     * Key is either CtInvocationImpl or CtConstructorImpl
     */
    /**
     * Key: variable type such as XYSeries
     * Value: set of variable names such as xYSeries0
     */
    private static HashMap<CtTypeReference, Set<CtLocalVariable>> vartypeTovarnames = new HashMap<>();

    /**
     * Key: type of direct values
     * Value: direct values
     */
    private static HashMap<CtTypeReference, Set<CtElement>> directToValues = new HashMap<>();

    /**
     * To access vartypeToInputPool easily
     * Key: CtTypeReference
     * Value: Set of pairs
     */
    private static HashMap<CtTypeReference, Set<Pair<CtTypeReference, CtElement>>> varTypeNamePool = new HashMap<>();

        /**
     * Key: Pair of (variable type, variable name)
     * Value: Set of argument inputs
     */
    private static HashMap<Pair<CtTypeReference, CtElement>, Set<List<CtElement>>> vartypeToInputPool = new HashMap<>();

    /**
     * method of each test case
     */
    private static Set<CtMethod> testcases = new HashSet<>();

    /**
     * Key is either CtInvocationImpl or CtConstructorImpl
     * Value: list of arguments where index 0 is receiver object followed by parameter arguments afterwards
     */
    private static HashMap<CtAbstractInvocation, Set<List<CtTypeReference>>> MUTnameToArgtypes = new HashMap<>();

    private static Map<CtTypeReference, Set<String>> processedNormalizedDeclarations = new HashMap<>();
    
    // Statistics for tracking sequence limitations
    private static int sequencesSkippedDueToLimit = 0;
    
    // Track sequence count per type (across all variables of that type)
    private static Map<CtTypeReference, Integer> sequenceCountPerType = new HashMap<>();
    
    /**
     * ★ Lazy Evaluation 캐시 - 런타임에 조회된 타입에 대한 호환 객체를 캐시
     * Key: 필요한 타입 (qualified name 문자열)
     * Value: 캐싱된 호환 가능한 객체 Set
     * 
     * 예시:
     * "java.util.List" → {
     *   Pair(ArrayList, list0),
     *   Pair(LinkedList, list1),
     *   Pair(Vector, list2),
     *   Pair(ArrayList, null_arraylist_...)
     * }
     * 
     * 동작 원리 (Lazy Evaluation):
     * 1. 처음 조회: varTypeNamePool + abstractToImplsMap에서 동적 생성 → 캐시 저장
     * 2. 이후 조회: 캐시에서 즉시 반환 (O(1))
     * 
     * 장점:
     * - 미리 모든 타입을 빌드하지 않아 초기화 빠름
     * - 실제 사용되는 타입만 캐싱되어 메모리 효율적
     * - 반복 조회 시 매우 빠름 (캐시 히트)
     */
    private static HashMap<String, Set<Pair<CtTypeReference, CtElement>>> compatibleCandidatesCache = new HashMap<>();


    public static HashMap<CtTypeReference, Set<CtLocalVariable>> getVartypeTovarnames() {
        return vartypeTovarnames;
    }

    public static HashMap<CtTypeReference, Set<Pair<CtTypeReference, CtElement>>> getVarTypeNamePool() {
        return varTypeNamePool;
    }

    public static HashMap<Pair<CtTypeReference, CtElement>, Set<List<CtElement>>> getVartypeToInputPool() {
        return vartypeToInputPool;
    }


    public static HashMap<CtAbstractInvocation, Set<List<CtTypeReference>>> getMUTnameToArgtypes() {
         return MUTnameToArgtypes;
     }

    public static boolean insertVartypeTovarnames(CtTypeReference type, CtLocalVariable var) {
        if (!vartypeTovarnames.containsKey(type))
            vartypeTovarnames.put(type, new HashSet<>());
        return vartypeTovarnames.get(type).add(var);
    }

    public static boolean isDeclarationProcessed(CtTypeReference type, String normalizedString) {
        if (!processedNormalizedDeclarations.containsKey(type)) {
            return false;
        }
        
        Set<String> existingDeclarations = processedNormalizedDeclarations.get(type);
        boolean found = existingDeclarations.contains(normalizedString);
        
        return found;
    }

    public static void addProcessedDeclaration(CtTypeReference type, String normalizedString) {
         processedNormalizedDeclarations.computeIfAbsent(type, k -> new HashSet<>()).add(normalizedString);
     }
     
     /**
      * ★ (제거됨) 미리 빌드하지 않고 lazy evaluation 방식 사용
      * 대신 getCompatibleCandidates()가 필요할 때마다 동적으로 생성하고 캐싱
      */
     
     /**
      * ★ Lazy Evaluation + 캐싱 방식의 호환 가능 객체 조회 메소드
      * 
      * 동작 방식:
      * 1순위: 캐시에 있으면 즉시 반환 (O(1)) ← 가장 빠름
      * 2순위: 캐시에 없으면 동적으로 생성하고 캐시에 저장
      *   2-1. varTypeNamePool에서 정확한 타입 찾기
      *   2-2. varTypeNamePool에서 qualified name 일치하는 타입 찾기
      *   2-3. abstractToImplsMap에서 구현체들 찾기
      * 
      * 장점:
      * - 미리 모든 타입을 빌드하지 않아 초기화 시간 절약
      * - 실제 사용되는 타입만 캐싱되므로 메모리 효율적
      * - 반복 조회 시 캐시 히트로 매우 빠름
      * 
      * @param typeQName 찾고자 하는 타입의 qualified name
      * @return 호환 가능한 객체 Set (없으면 빈 Set)
      */
     public static Set<Pair<CtTypeReference, CtElement>> getCompatibleCandidates(String typeQName) {
         if (typeQName == null) {
             return new HashSet<>();
         }
         
         // === 1순위: 캐시 조회 (이미 한 번 조회된 타입) ===
         if (compatibleCandidatesCache.containsKey(typeQName)) {
             // System.out.println("[CandidatePool] Cache HIT for type: " + typeQName);
             return new HashSet<>(compatibleCandidatesCache.get(typeQName));  // 복사본 반환
         }
         
         // === 2순위: 동적 생성 (처음 조회되는 타입) ===
         // System.out.println("[CandidatePool] Cache MISS for type: " + typeQName + ", building candidates...");
         Set<Pair<CtTypeReference, CtElement>> candidates = new HashSet<>();
         
         // 2-1. varTypeNamePool에서 정확한 타입으로 찾기 (참조 기반)
         boolean foundExactMatch = false;
         for (Map.Entry<CtTypeReference, Set<Pair<CtTypeReference, CtElement>>> entry : 
              varTypeNamePool.entrySet()) {
             CtTypeReference typeRef = entry.getKey();
             
             // 먼저 qualified name으로 비교
             if (typeRef.getQualifiedName().equals(typeQName)) {
                 candidates.addAll(entry.getValue());
                 foundExactMatch = true;
                 // break 하지 않고 계속 - 같은 qualified name의 다른 CtTypeReference가 있을 수 있음
             }
         }
         
         if (foundExactMatch) {
             // System.out.println("[CandidatePool]   - Found " + candidates.size() + " exact matches");
         }
         
         // 2-2. abstractToImplsMap에서 구현체 찾기
         List<CtTypeReference<?>> implementations = ASTParser.abstractToImplsMap.get(typeQName);
         if (implementations != null && !implementations.isEmpty()) {
             // System.out.println("[CandidatePool]   - Found " + implementations.size() + " implementations");
             int implCount = 0;
             for (CtTypeReference<?> implType : implementations) {
                 Set<Pair<CtTypeReference, CtElement>> implCandidates = varTypeNamePool.get(implType);
                 if (implCandidates != null && !implCandidates.isEmpty()) {
                     candidates.addAll(implCandidates);
                     implCount += implCandidates.size();
                 }
             }
             // System.out.println("[CandidatePool]   - Added " + implCount + " implementation candidates");
         }
         
         // === 캐시에 저장 (다음 조회 시 빠르게) ===
         compatibleCandidatesCache.put(typeQName, new HashSet<>(candidates));
         // System.out.println("[CandidatePool]   - Cached " + candidates.size() + " candidates for: " + typeQName);
         
         return candidates;
     }
     
     /**
      * ★ CtTypeReference 객체로 호환 가능 객체 조회 (오버로드)
      */
     public static Set<Pair<CtTypeReference, CtElement>> getCompatibleCandidates(CtTypeReference<?> type) {
         if (type == null) {
             return new HashSet<>();
         }
         return getCompatibleCandidates(type.getQualifiedName());
     }
     
     /**
      * 캐시 통계 출력 (디버깅용)
      */
     public static void printCacheStats() {
         System.out.println("\n========================================");
         System.out.println("   Compatible Candidates Cache Stats");
         System.out.println("========================================");
         System.out.println("Total cached types: " + compatibleCandidatesCache.size());
         
         if (compatibleCandidatesCache.isEmpty()) {
             System.out.println("(No types have been queried yet)");
             System.out.println("========================================\n");
             return;
         }
         
         System.out.println("\nCached type details:");
         int totalCandidates = 0;
         for (Map.Entry<String, Set<Pair<CtTypeReference, CtElement>>> entry : 
              compatibleCandidatesCache.entrySet()) {
             String typeQName = entry.getKey();
             int candidateCount = entry.getValue().size();
             totalCandidates += candidateCount;
             
             // 간단한 타입명만 표시
             String simpleTypeName = typeQName.substring(typeQName.lastIndexOf('.') + 1);
             System.out.println("  - " + simpleTypeName + ": " + candidateCount + " candidates");
         }
         
         System.out.println("\nTotal candidates across all types: " + totalCandidates);
         double avgCandidates = (double) totalCandidates / compatibleCandidatesCache.size();
         System.out.printf("Average candidates per type: %.2f%n", avgCandidates);
         System.out.println("========================================\n");
     }


    public static boolean insertVarTypeToInputPool(Pair<CtTypeReference, CtElement> typeAndName, List<CtElement> stmts) {
        if (typeAndName == null || typeAndName.getKey() == null || typeAndName.getValue() == null) {
            System.err.println("insertVarTypeToInputPool: typeAndName or key/value is Null SKIPPING");
            return false;
        }
        
        insertVarTypeNamePair(typeAndName);
        if (!vartypeToInputPool.containsKey(typeAndName))
            vartypeToInputPool.put(typeAndName, new HashSet<>());
        
        // Check if adding this sequence would exceed the maximum limit per type (across all variables of this type)
        CtTypeReference type = typeAndName.getKey();
        int currentSequenceCount = sequenceCountPerType.getOrDefault(type, 0);
        if (currentSequenceCount >= Config.MAX_SEQUENCES_PER_TYPE) {
            sequencesSkippedDueToLimit++;
            // System.out.println("[DEBUG-LIMIT] Skipping sequence - maximum limit (" + Config.MAX_SEQUENCES_PER_TYPE + ") reached for type: " + type.getSimpleName());
            return false; // Don't add more sequences if limit is reached
        }
        // System.out.println("[DEBUG-INSERT] Inserting unique sequence for key: " + typeAndName.getValue() +
        // " | Stmts size: " + stmts.size());
        for (CtElement e : stmts) {
            List<CtConstructorCallImpl> cons = e.getElements(new TypeFilter<>(CtConstructorCallImpl.class));
            if (cons.size() == 1) {
                CtConstructorCallImpl call = cons.get(0);
                CtExpression receiverObj = call.getTarget();
                if (receiverObj != null) { //To handle strBuilder0_111.new org.apache.commons.lang.text.StrBuilderWriter(), this statement causes compile error
                    String simpleName = call.getType().getSimpleName();
                    Factory factory = call.getFactory();
                    CtTypeReference<Object> newType = factory.createTypeReference();
                    newType.setPackage(null);
                    newType.setSimpleName(simpleName);
                    call.setType(newType); //set org.apache.commons.lang.text.StrBuilderWriter() to StrBuilderWriter()
                }
            }
        }
        
        boolean added = vartypeToInputPool.get(typeAndName).add(stmts);
        if (added) {
            // Update the sequence count for this type
            sequenceCountPerType.put(type, currentSequenceCount + 1);
        }
        return added;
    }

    private static boolean insertVarTypeNamePair(Pair<CtTypeReference, CtElement> typeAndName) {
        if (!varTypeNamePool.containsKey(typeAndName.getKey()))
            varTypeNamePool.put(typeAndName.getKey(), new HashSet<>());
        return varTypeNamePool.get(typeAndName.getKey()).add(typeAndName);
    }

    public static boolean insertMUTnameToArgtypes(CtAbstractInvocation method, List<CtTypeReference> types) {
        if (!MUTnameToArgtypes.containsKey(method))
            MUTnameToArgtypes.put(method, new HashSet<>());
        return MUTnameToArgtypes.get(method).add(types);
    }

    public static HashMap<CtTypeReference, Set<CtElement>> getDirectToValues() {
        return directToValues;
    }

    // public static void insertDirectToValues(CtTypeReference type, CtElement value) {
    //     if (!CandidatePool.directToValues.containsKey(type))
    //         CandidatePool.directToValues.put(type, new HashSet<>());
    //     CandidatePool.directToValues.get(type).add(value);
    //     // if(type.toString().contains("double")){
    //     //     System.out.println("Double Added : "+value);
    //     // }
    // }

    public static void insertDirectToValues(CtTypeReference type, CtElement value) {
        if (type == null || value == null) return; // null 체크 추가

        // CtLiteral인 경우 실제 값으로 정규화
        if (value instanceof CtLiteral<?>) {
            CtLiteral<?> literal = (CtLiteral<?>) value;
            Object literalValue = literal.getValue();
            if (literalValue != null) {
                // 타입별로 값을 정규화하여 중복 제거
                if (!CandidatePool.directToValues.containsKey(type)) {
                    CandidatePool.directToValues.put(type, new HashSet<>());
                }
                Set<CtElement> values = CandidatePool.directToValues.get(type);
                
                // 값 기반으로 중복 체크
                boolean isDuplicate = values.stream()
                    .filter(e -> e instanceof CtLiteral<?>)
                    .map(e -> ((CtLiteral<?>) e).getValue())
                    .anyMatch(val -> Objects.equals(val, literalValue));
                
                if (!isDuplicate) {
                    values.add(value); // 중복이 아니면 추가
                }
            }
        } else {
            // 리터럴이 아닌 경우 (예: 변수 참조 등) 그대로 추가
            if (!CandidatePool.directToValues.containsKey(type)) {
                CandidatePool.directToValues.put(type, new HashSet<>());
            }
            CandidatePool.directToValues.get(type).add(value);
        }

        // 디버깅용 출력 (필요 시 주석 해제)
        // if (type.toString().contains("int")) {
        //     System.out.println("Int Added: " + value + " | Value: " + (value instanceof CtLiteral<?> ? ((CtLiteral<?>) value).getValue() : value));
        // }
}

    public static Set<CtMethod> getTestcases() {
        return testcases;
    }

    public static void setTestcases(Set<CtMethod> testcases) {
        CandidatePool.testcases = testcases;
    }
    public static void insertTestCases(Set<CtMethod> testcases) {
        for(CtMethod tc : testcases){
            CandidatePool.testcases.add(tc);
        }
    }

    public static boolean hasVarTypeToInputPoolKey(Pair<CtTypeReference, CtElement> typeAndName) {
        if (typeAndName == null) {
            return false;
        }
        return vartypeToInputPool.containsKey(typeAndName);
    }

    public static void printPoolSummary() {
        System.out.println("\n========================================");
        System.out.println("      Candidate Pool Summary");
        System.out.println("========================================");

        // 1. vartypeToInputPool (변수 풀) 요약
        System.out.println("\n--- Variable Input Pool (vartypeToInputPool) ---");
        System.out.println("Total Unique Variables (Type, Name pairs): " + vartypeToInputPool.size());
        Map<CtTypeReference, List<Pair<CtElement, Integer>>> groupedByType = new HashMap<>();
        for (Map.Entry<Pair<CtTypeReference, CtElement>, Set<List<CtElement>>> entry : vartypeToInputPool.entrySet()) {
            Pair<CtTypeReference, CtElement> typeAndNameKey = entry.getKey();
            if (typeAndNameKey.getKey() == null || typeAndNameKey.getValue() == null)
                continue;
            CtTypeReference type = typeAndNameKey.getKey();
            CtElement varName = typeAndNameKey.getValue();
            int sequenceCount = entry.getValue().size();
            Pair<CtElement, Integer> varInfo = new Pair<>(varName, sequenceCount);
            groupedByType.computeIfAbsent(type, k -> new ArrayList<>()).add(varInfo);
        }
        for (Map.Entry<CtTypeReference, List<Pair<CtElement, Integer>>> groupEntry : groupedByType.entrySet()) {
            System.out.println("  - Type: " + groupEntry.getKey().getSimpleName());
            for (Pair<CtElement, Integer> varInfo : groupEntry.getValue()) {
                System.out.println("    - Var: " + varInfo.getKey().toString() +
                        " | Unique Declaration Sequences: " + varInfo.getValue());
            }
        }

        // 2. directToValues (리터럴 풀) 요약
        System.out.println("\n--- Literal Value Pool (directToValues) ---");
        System.out.println("Total Types with Literals: " + directToValues.size());
        directToValues.forEach((type, values) -> {
            System.out.println("  - Type: " + type.getSimpleName() +
                    " | Unique Literals Collected: " + values.size());
        });

        // --- 3. MUTnameToArgtypes (MUT 풀) 요약 ---
        System.out.println("\n--- MUT Pool (MUTnameToArgtypes) ---");
        System.out.println("Total Unique MUTs Identified: " + MUTnameToArgtypes.size());

        // [추가] 맵의 각 항목을 순회하며 내용 출력
        int mutIndex = 1;
        for (Map.Entry<CtAbstractInvocation, Set<List<CtTypeReference>>> entry : MUTnameToArgtypes.entrySet()) {
            System.out.println("  - MUT #" + mutIndex++ + ": " + entry.getKey().toString());

            // 해당 MUT에 대해 수집된 모든 인자 타입 리스트들을 출력
            for (List<CtTypeReference> argTypeList : entry.getValue()) {
                System.out.println("    - Arg Types: " + argTypeList.toString());
            }
        }

        System.out.println("\n========================================\n");
    }

    /**
     * Analysis helper class for object types with input counts
     */
    public static class ObjectInputCount {
        public String typeName;
        public String qualifiedTypeName;
        public int inputCount;
        public int variableCount;
        public int sequenceCount;
        
        public ObjectInputCount(String typeName, String qualifiedTypeName, int inputCount, int variableCount, int sequenceCount) {
            this.typeName = typeName;
            this.qualifiedTypeName = qualifiedTypeName;
            this.inputCount = inputCount;
            this.variableCount = variableCount;
            this.sequenceCount = sequenceCount;
        }
        
        @Override
        public String toString() {
            return String.format("%-25s | Inputs: %,5d | Variables: %,3d | Sequences: %,4d", 
                    typeName, inputCount, variableCount, sequenceCount);
        }
    }

    /**
     * Analyzes and returns the top objects with the most inputs for combination explosion analysis
     * @param limit Maximum number of top objects to return (typically 10)
     * @return List of ObjectInputCount sorted by input count descending
     */
    public static List<ObjectInputCount> getTopObjectsByInputCount(int limit) {
        Map<CtTypeReference, ObjectInputCount> typeStats = new HashMap<>();
        
        // Analyze vartypeToInputPool to count inputs per type
        for (Map.Entry<Pair<CtTypeReference, CtElement>, Set<List<CtElement>>> entry : vartypeToInputPool.entrySet()) {
            Pair<CtTypeReference, CtElement> typeAndNameKey = entry.getKey();
            if (typeAndNameKey.getKey() == null || typeAndNameKey.getValue() == null) {
                continue;
            }
            
            CtTypeReference type = typeAndNameKey.getKey();
            Set<List<CtElement>> sequences = entry.getValue();
            
            // Count total inputs for this type
            int totalInputs = 0;
            for (List<CtElement> sequence : sequences) {
                totalInputs += sequence.size();
            }
            
            // Update or create type statistics
            ObjectInputCount currentStats = typeStats.get(type);
            if (currentStats == null) {
                String typeName = type.getSimpleName();
                String qualifiedTypeName = type.getQualifiedName();
                typeStats.put(type, new ObjectInputCount(typeName, qualifiedTypeName, totalInputs, 1, sequences.size()));
            } else {
                // Accumulate stats for this type
                currentStats.inputCount += totalInputs;
                currentStats.variableCount += 1;
                currentStats.sequenceCount += sequences.size();
            }
        }
        
        // Also analyze directToValues (literal values) to add to input counts
        for (Map.Entry<CtTypeReference, Set<CtElement>> entry : directToValues.entrySet()) {
            CtTypeReference type = entry.getKey();
            Set<CtElement> literals = entry.getValue();
            
            ObjectInputCount currentStats = typeStats.get(type);
            if (currentStats == null) {
                String typeName = type.getSimpleName();
                String qualifiedTypeName = type.getQualifiedName();
                typeStats.put(type, new ObjectInputCount(typeName, qualifiedTypeName, literals.size(), 0, 0));
            } else {
                // Add literal count to existing input count
                currentStats.inputCount += literals.size();
            }
        }
        
        // Sort by input count descending and return top objects
        return typeStats.values().stream()
                .sorted((a, b) -> Integer.compare(b.inputCount, a.inputCount))
                .limit(limit)
                .collect(java.util.stream.Collectors.toList());
    }

    /**
     * Prints a formatted report of the top objects with the most inputs
     * @param limit Maximum number of objects to show (typically 10)
     */
    public static void printTopObjectsWithMostInputs(int limit) {
        System.out.println("\nTOP " + limit + " OBJECTS WITH MOST INPUTS:");
        String separator = "================================================================================";
        System.out.println(separator);
        
        List<ObjectInputCount> topObjects = getTopObjectsByInputCount(limit);
        
        if (topObjects.isEmpty()) {
            System.out.println("   No objects found in candidate pools.");
            System.out.println(separator);
            return;
        }
        
        System.out.printf("%-4s %-25s | %-12s | %-12s | %-12s%n", 
                "Rank", "Object Type", "Total Inputs", "Variables", "Sequences");
        System.out.println("---- ------------------------- | ------------ | ------------ | ------------");
        
        int rank = 1;
        for (ObjectInputCount obj : topObjects) {
            System.out.printf("%-4d %s%n", rank++, obj.toString());
        }
        
        // Calculate and show summary statistics
        int totalInputsInTop = topObjects.stream().mapToInt(o -> o.inputCount).sum();
        int totalVariablesInTop = topObjects.stream().mapToInt(o -> o.variableCount).sum();
        int totalSequencesInTop = topObjects.stream().mapToInt(o -> o.sequenceCount).sum();
        
        System.out.println("---- ------------------------- | ------------ | ------------ | ------------");
        System.out.printf("%-4s %-25s | %,10d | %,10d | %,10d%n", 
                "SUM", "TOP " + limit + " OBJECTS TOTAL", 
                totalInputsInTop, totalVariablesInTop, totalSequencesInTop);
        
        // Show percentage of total pool
        int grandTotalInputs = 0;
        for (Map.Entry<Pair<CtTypeReference, CtElement>, Set<List<CtElement>>> entry : vartypeToInputPool.entrySet()) {
            for (List<CtElement> sequence : entry.getValue()) {
                grandTotalInputs += sequence.size();
            }
        }
        for (Set<CtElement> literals : directToValues.values()) {
            grandTotalInputs += literals.size();
        }
        
        if (grandTotalInputs > 0) {
            double percentage = (totalInputsInTop * 100.0) / grandTotalInputs;
            System.out.printf("%nTop %d objects represent %.1f%% of all inputs (%,d total)%n", 
                    limit, percentage, grandTotalInputs);
        }
        
        System.out.println(separator);
    }
    
    /**
     * Prints statistics about sequence limitation enforcement
     */
    public static void printSequenceLimitationStats() {
        System.out.println("\n========================================");
        System.out.println("      SEQUENCE LIMITATION STATS");
        System.out.println("========================================");
        
        System.out.printf("Maximum sequences per type: %,d%n", Config.MAX_SEQUENCES_PER_TYPE);
        System.out.printf("Sequences skipped due to limit: %,d%n", sequencesSkippedDueToLimit);
        
        // Count types that reached the limit
        int typesAtLimit = 0;
        int totalTypes = sequenceCountPerType.size();
        
        System.out.println("\nSequence count per type:");
        for (Map.Entry<CtTypeReference, Integer> entry : sequenceCountPerType.entrySet()) {
            String typeName = entry.getKey().getSimpleName();
            int count = entry.getValue();
            if (count >= Config.MAX_SEQUENCES_PER_TYPE) {
                typesAtLimit++;
                System.out.printf("  %s: %,d [AT LIMIT]%n", typeName, count);
            } else {
                System.out.printf("  %s: %,d%n", typeName, count);
            }
        }
        
        System.out.printf("%nTypes that reached the limit: %,d / %,d%n", typesAtLimit, totalTypes);
        if (totalTypes > 0) {
            double limitReachedPercentage = (typesAtLimit * 100.0) / totalTypes;
            System.out.printf("Percentage of types at limit: %.1f%%%n", limitReachedPercentage);
        }
        
        System.out.println("========================================\n");
    }
    
    /**
     * Adds extreme values for primitive types to enhance test coverage
     * This method should be called after all base test inputs have been collected
     */
    public static void addExtremeValuesForPrimitiveTypes() {
        if (!Config.ENABLE_PRIMITIVE_EXTREME_VALUES) {
            return;
        }
        
        int extremeValuesAdded = 0;
        
        // Create a factory for creating literals
        Factory factory = null;
        for (Map.Entry<CtTypeReference, Set<CtElement>> entry : directToValues.entrySet()) {
            if (!entry.getValue().isEmpty()) {
                CtElement firstElement = entry.getValue().iterator().next();
                factory = firstElement.getFactory();
                break;
            }
        }
        
        if (factory == null) {
            return;
        }
        
        // Add extreme values for each primitive type
        extremeValuesAdded += addExtremeValuesForType(factory, "int", Integer.class);
        extremeValuesAdded += addExtremeValuesForType(factory, "long", Long.class);
        extremeValuesAdded += addExtremeValuesForType(factory, "short", Short.class);
        extremeValuesAdded += addExtremeValuesForType(factory, "byte", Byte.class);
        extremeValuesAdded += addExtremeValuesForType(factory, "float", Float.class);
        extremeValuesAdded += addExtremeValuesForType(factory, "double", Double.class);
        extremeValuesAdded += addExtremeValuesForType(factory, "char", Character.class);
        extremeValuesAdded += addExtremeValuesForType(factory, "boolean", Boolean.class);
        
        // Also handle wrapper types
        extremeValuesAdded += addExtremeValuesForType(factory, "Integer", Integer.class);
        extremeValuesAdded += addExtremeValuesForType(factory, "Long", Long.class);
        extremeValuesAdded += addExtremeValuesForType(factory, "Short", Short.class);
        extremeValuesAdded += addExtremeValuesForType(factory, "Byte", Byte.class);
        extremeValuesAdded += addExtremeValuesForType(factory, "Float", Float.class);
        extremeValuesAdded += addExtremeValuesForType(factory, "Double", Double.class);
        extremeValuesAdded += addExtremeValuesForType(factory, "Character", Character.class);
        extremeValuesAdded += addExtremeValuesForType(factory, "Boolean", Boolean.class);
    }
    
    /**
     * Adds extreme values for a specific primitive type
     */
    private static int addExtremeValuesForType(Factory factory, String typeName, Class<?> typeClass) {
        CtTypeReference<?> typeRef = null;
        
        // Find existing type reference in directToValues
        for (CtTypeReference type : directToValues.keySet()) {
            if (type.getSimpleName().equals(typeName)) {
                typeRef = type;
                break;
            }
        }
        
        // If type doesn't exist in pool, create it
        if (typeRef == null) {
            typeRef = factory.createTypeReference();
            typeRef.setSimpleName(typeName);
        }
        
        int valuesAdded = 0;
         Set<Object> extremeValues = getExtremeValuesForType(typeClass);
         
         for (Object value : extremeValues) {
             CtExpression<?> expr = null;
             
             if (value instanceof Float) {
                 float fval = (Float) value;
                 if (Float.isNaN(fval)) {
                     expr = factory.createCodeSnippetExpression("Float.NaN");
                 } else if (Float.isInfinite(fval)) {
                     if (fval > 0) {
                         expr = factory.createCodeSnippetExpression("Float.POSITIVE_INFINITY");
                     } else {
                         expr = factory.createCodeSnippetExpression("Float.NEGATIVE_INFINITY");
                     }
                 } else {
                     expr = factory.createLiteral(value);
                 }
             } else if (value instanceof Double) {
                 double dval = (Double) value;
                 if (Double.isNaN(dval)) {
                     expr = factory.createCodeSnippetExpression("Double.NaN");
                 } else if (Double.isInfinite(dval)) {
                     if (dval > 0) {
                         expr = factory.createCodeSnippetExpression("Double.POSITIVE_INFINITY");
                     } else {
                         expr = factory.createCodeSnippetExpression("Double.NEGATIVE_INFINITY");
                     }
                 } else {
                     expr = factory.createLiteral(value);
                 }
             } else {
                 expr = factory.createLiteral(value);
             }
             
             insertDirectToValues(typeRef, expr);
             valuesAdded++;
         }
         
         return valuesAdded;
    }
    
    /**
     * Returns a set of extreme values for the given primitive type
     */
    private static Set<Object> getExtremeValuesForType(Class<?> typeClass) {
        Set<Object> extremeValues = new HashSet<>();
        
        if (typeClass == Integer.class) {
            extremeValues.add(Integer.MIN_VALUE);
            extremeValues.add(Integer.MAX_VALUE);
            extremeValues.add(0);
            extremeValues.add(-1);
            extremeValues.add(1);
            
        } else if (typeClass == Long.class) {
            extremeValues.add(Long.MIN_VALUE);
            extremeValues.add(Long.MAX_VALUE);
            extremeValues.add(0L);
            extremeValues.add(-1L);
            extremeValues.add(1L);
            
        } else if (typeClass == Short.class) {
            extremeValues.add(Short.MIN_VALUE);
            extremeValues.add(Short.MAX_VALUE);
            extremeValues.add((short) 0);
            extremeValues.add((short) -1);
            extremeValues.add((short) 1);
            
        } else if (typeClass == Byte.class) {
            extremeValues.add(Byte.MIN_VALUE);
            extremeValues.add(Byte.MAX_VALUE);
            extremeValues.add((byte) 0);
            extremeValues.add((byte) -1);
            extremeValues.add((byte) 1);
            
        } else if (typeClass == Float.class) {
            extremeValues.add(Float.MIN_VALUE);
            extremeValues.add(Float.MAX_VALUE);
            extremeValues.add(-Float.MAX_VALUE);
            extremeValues.add(Float.POSITIVE_INFINITY);
            extremeValues.add(Float.NEGATIVE_INFINITY);
            extremeValues.add(Float.NaN);
            extremeValues.add(0.0f);
            extremeValues.add(-0.0f);
            extremeValues.add(1.0f);
            extremeValues.add(-1.0f);
            
        } else if (typeClass == Double.class) {
            extremeValues.add(Double.MIN_VALUE);
            extremeValues.add(Double.MAX_VALUE);
            extremeValues.add(-Double.MAX_VALUE);
            extremeValues.add(Double.POSITIVE_INFINITY);
            extremeValues.add(Double.NEGATIVE_INFINITY);
            extremeValues.add(Double.NaN);
            extremeValues.add(0.0);
            extremeValues.add(-0.0);
            extremeValues.add(1.0);
            extremeValues.add(-1.0);
            
        } else if (typeClass == Character.class) {
            extremeValues.add(Character.MIN_VALUE);
            extremeValues.add(Character.MAX_VALUE);
            extremeValues.add('\0');
            extremeValues.add(' ');
            extremeValues.add('\n');
            extremeValues.add('\t');
            extremeValues.add('\r');
            
        } else if (typeClass == Boolean.class) {
            extremeValues.add(true);
            extremeValues.add(false);
        }
        
        return extremeValues;
    }

}
