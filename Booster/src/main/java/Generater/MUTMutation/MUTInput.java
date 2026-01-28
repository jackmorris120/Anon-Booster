package Generater.MUTMutation;

import spoon.reflect.code.CtAbstractInvocation;
import spoon.reflect.reference.CtTypeReference;
import spoon.reflect.declaration.CtElement;
import utils.Config;
import java.util.*;

public class MUTInput {
    private CtAbstractInvocation mutInvocation;
    private List<CtTypeReference> argTypes;
    private Map<String, Input> receiverInputMap = null;
    /**
     * Key: arg position of argTypes
     * Value: sets of existing inputs
     */
    private LinkedHashMap<Integer, List<Input>> inputs;

    private int upperBound;

    private List<Map.Entry<Integer, List<Input>>> sortedInputPools; 
    private boolean isSorted = false;
    private boolean isFull = false;
    private boolean isStacked = false;
    private List<Integer> currentPositions = new ArrayList<>();
    private List<Integer> usedPairs = new ArrayList<>();
    private List<List<Integer>> tWayCandidates = new ArrayList<>();
    private int currentCandidateIndex = 0;
    private int tWay = 0; 
    private String methodSignature;
    private boolean topT = Config.Tway_TOPT;
    private boolean isStatic = false;

    public MUTInput(CtAbstractInvocation mutInvocation, List<CtTypeReference> argTypes, LinkedHashMap<Integer, List<Input>> inputs, String methodSignature) {
        this.mutInvocation = mutInvocation;
        this.argTypes = argTypes;
        this.inputs = inputs;
        this.methodSignature = methodSignature;
        
        // Log argTypes for debugging
        StringBuilder argTypesStr = new StringBuilder();
        for (int i = 0; i < argTypes.size(); i++) {
            CtTypeReference t = argTypes.get(i);
            if (t != null) {
                argTypesStr.append(t.getQualifiedName());
            } else {
                argTypesStr.append("null");
            }
            if (i < argTypes.size() - 1) argTypesStr.append(", ");
        }
        // System.out.println("[MUT-CREATE] " + methodSignature + " | argTypes: [" + argTypesStr.toString() + "]");
        
        if (mutInvocation instanceof spoon.reflect.code.CtInvocation) {
            spoon.reflect.code.CtInvocation<?> inv = (spoon.reflect.code.CtInvocation<?>) mutInvocation;
            if (inv.getTarget() instanceof spoon.support.reflect.code.CtTypeAccessImpl) {
                this.isStatic = true;
            }
        } else if (mutInvocation instanceof spoon.reflect.code.CtConstructorCall) {
            this.isStatic = false;
        }
        
        int upperBound = 1;
        for (Integer pos : this.inputs.keySet()) {
            upperBound = upperBound * this.inputs.get(pos).size();
        }
        this.upperBound = upperBound;
        this.tWay = Math.max(1, Math.min(inputs.size(), 2));
    }

    public String getMethodSignature(){
        return methodSignature;
    }

    public CtAbstractInvocation getMUTInvocation() {
        return mutInvocation;
    }

    public List<CtTypeReference> getArgTypes() {
        return argTypes;
    }
    
    public boolean isStatic() {
        return isStatic;
    }
    public void initAllThePairs(List<Map.Entry<Integer, List<Input>>> sortedInputPools){

    }
    public LinkedHashMap<Integer, List<Input>> getInputs() {
        return inputs;
    }
    public boolean getIsStacked(){
        return this.isStacked;
    }
    public void setIsStacked(boolean val){
        this.isStacked = val;
    }
    public int getTWay(){
        return this.tWay;
    }

    public void setTWay(int num){
        this.tWay = num;
    }
    public void setUsedPairs(List<Integer> largestPositions){
        for (Integer idx : largestPositions){
            this.usedPairs.add(idx);
        }
    }
    
    public List<Integer> getUsedPairs(){
        return this.usedPairs;
    }

    public List<List<Integer>> getTwayCandidates(){
        return this.tWayCandidates;
    }

    public void setCurrentPositions(int idx){
        if (idx >= 0 && idx < tWayCandidates.size()) {
            currentPositions = tWayCandidates.get(idx);
        }
    }
    public List<Integer> getCurrentPositions(){
        return this.currentPositions;
    }

    public int getCurrentCandidateIndex(){
        return this.currentCandidateIndex;
    }

    public void setCurrentCandidateIndex(int num){
        this.currentCandidateIndex = num;
    }
    
    public void setIsFull(boolean isFull){
        this.isFull = isFull;
    }

    public boolean getIsFull(){
        return this.isFull;
    }

    public Map<String, Input> getReceiverInputMap() {
        if (this.receiverInputMap == null) {
            buildReceiverInputMap();
        }
        return this.receiverInputMap;
    }

    private void buildReceiverInputMap() {
        this.receiverInputMap = new HashMap<>();
        // position 0은 호출 객체를 의미합니다.
        List<Input> receiverCandidates = this.inputs.get(0); 
        
        if (receiverCandidates != null) {
            for (Input candidate : receiverCandidates) {
                if (candidate.isVar()) {
                    String varName = candidate.getVarName().toString();
                    // putIfAbsent를 사용해 동일한 이름의 키가 있을 경우 기존 값을 유지합니다.
                    this.receiverInputMap.putIfAbsent(varName, candidate);
                }
            }
        }
    }

    public void initSortedInputPools(LinkedHashMap<Integer, List<Input>> inputPools){
        if(topT){
            if(!isSorted){
                sortedInputPools = new ArrayList<>();
                for (Map.Entry<Integer, List<Input>> entry : inputPools.entrySet()) {
                    if (isStatic && entry.getKey() == 0) {
                        continue;
                    }
                    sortedInputPools.add(entry);
                }
                sortedInputPools.sort((e1, e2) -> Integer.compare(e2.getValue().size(), e1.getValue().size()));
                isSorted = true;
            }
        }else{
            if(!isSorted){
                sortedInputPools = new ArrayList<>();
                for (Map.Entry<Integer, List<Input>> entry : inputPools.entrySet()) {
                    if (isStatic && entry.getKey() == 0) {
                        continue;
                    }
                    sortedInputPools.add(entry);
                }
                Collections.shuffle(sortedInputPools);
                isSorted = true;
            }
        }
        
    }
  
    public void initTwayCandidates() {
        if (sortedInputPools == null) return;
        tWayCandidates.clear();
        currentCandidateIndex = 0;
        int size = sortedInputPools.size();
        setIsFull(false);
        
        if (tWay > size) return;
        if (size == 1 && tWay == 1) {
            List<Integer> single = new ArrayList<>();
            single.add(sortedInputPools.get(0).getKey());
            tWayCandidates.add(single);
            setIsStacked(true);
            return;
        }
        
        if (!isStatic) {
            // For non-static methods, also include position 0 (receiver) in t-way combinations
            // This allows testing with different receiver objects
            List<Integer> partial = new ArrayList<>();
            generateCombinationsRecursive(0, tWay, partial, size);
        } else {
            List<Integer> partial = new ArrayList<>();
            generateCombinationsRecursive(0, tWay, partial, size);
        }

        if (tWayCandidates.size() <= 1) {
            setIsFull(true);
        }
    }

    /**
     * 재귀 함수를 이용해 T개의 조합을 "중첩 for문과 같은 사전식 순서"로 생성한다.
     *
     * @param start     다음에 선택할 Pool의 시작 인덱스
     * @param picksLeft 앞으로 더 선택해야 하는 개수
     * @param partial   현재까지 선택해온 key 목록
     * @param size      전체 Pool 개수 (sortedInputPools.size())
     */
    private void generateCombinationsRecursive(int start,
                                            int picksLeft,
                                            List<Integer> partial,
                                            int size) {
        // base condition: 더 뽑을 게 없으면 partial을 하나의 조합으로 추가
        if (picksLeft == 0) {
            tWayCandidates.add(new ArrayList<>(partial));
            return;
        }
        for (int i = start; i <= size - picksLeft; i++) {
            // i번째 pool의 key를 partial에 추가
            partial.add(sortedInputPools.get(i).getKey());
            
            // 재귀 호출: i+1부터 picksLeft-1개 뽑기
            generateCombinationsRecursive(i + 1, picksLeft - 1, partial, size);

            // 재귀 복귀 후, 방금 넣은 i번째 key 제거하고 다음 i로 진행
            partial.remove(partial.size() - 1);
        }
    }
    
    private void generateCombinationsRecursiveExcludingPosition0(int start,
                                            int picksLeft,
                                            List<Integer> partial,
                                            int size) {
        if (picksLeft == 0) {
            tWayCandidates.add(new ArrayList<>(partial));
            return;
        }
        for (int i = start; i < size; i++) {
            int poolKey = sortedInputPools.get(i).getKey();
            if (poolKey == 0) {
                continue;
            }
            partial.add(poolKey);
            generateCombinationsRecursiveExcludingPosition0(i + 1, picksLeft - 1, partial, size);
            partial.remove(partial.size() - 1);
        }
    }



    public boolean setNextTWayCombination() {
        if(currentCandidateIndex >= tWayCandidates.size()-1) {
            return false; // 더 이상 pair 없음
        }
        currentCandidateIndex++;
        this.currentPositions= tWayCandidates.get(currentCandidateIndex);
        this.isFull = false;
        return true;
    }
    public int getTotalTWayCandidates() {
        return tWayCandidates.size();
    }

   

    public List<Map.Entry<Integer, List<Input>>> getSortedInputPools(){
        return sortedInputPools;
    }

    public boolean equals(List<CtTypeReference> args) {
        if (args.size() != argTypes.size() - 1)
            return false;
        List<CtTypeReference> trueArgs = argTypes.subList(1, argTypes.size());
        for (int i = 0; i < trueArgs.size(); i++) {
            CtTypeReference arg = args.get(i);
            if (!arg.getSimpleName().equals(trueArgs.get(i).getSimpleName()))
                return false;
        }
        return true;
    }

    public int getUpperBound() {
        return upperBound;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("MUTInput {\n");
        sb.append("  Method Siganture: ").append(methodSignature).append(",\n");
        sb.append("  mutInvocation: ").append(mutInvocation).append(",\n");
        sb.append("  argTypes: ").append(argTypes).append(",\n");
        sb.append("  inputs: {\n");
        
        for (Integer pos : inputs.keySet()) {
            List<Input> inputList = inputs.get(pos);
            if(pos.equals(0)){
                sb.append("    Position ").append(pos).append(" (return type): Size : ")
            .append(inputList.size()).append(" ").append(inputList).append("\n");
            }else{
                sb.append("    Position ").append(pos).append(": Size : ")
            .append(inputList.size()).append(" ").append(inputList).append("\n");
            }
            
            
            // 각 Input 객체 내부의 input 필드 사이즈를 출력
            int i = 1;
            for (Input input : inputList) {
                List<CtElement> internalElements = input.getInput();
                if (internalElements != null) {
                    sb.append("      Input #").append(i).append(" Type : "+input.getType())
                    .append(" internal input size: ")
                    .append(internalElements.size())
                    .append(" -> ").append(internalElements).append("\n");
                } else {
                    sb.append("      Input #").append(i)
                    .append(" internal input is null or empty.\n");
                }
                i++;
            }
        }

        sb.append("  },\n");
        sb.append("}");
        return sb.toString();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
    
        MUTInput mutInput = (MUTInput) o;
        return Objects.equals(mutInvocation.toString(), mutInput.mutInvocation.toString()) &&
            Objects.equals(argTypes, mutInput.argTypes) &&
            Objects.equals(inputs, mutInput.inputs);
    }

    @Override
    public int hashCode() {
        // equals()에서 사용한 필드들을 기반으로 해시 코드를 생성합니다.
        return Objects.hash(mutInvocation.toString(), argTypes, inputs);
    }



}
