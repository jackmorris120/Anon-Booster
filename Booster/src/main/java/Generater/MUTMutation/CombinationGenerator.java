package Generater.MUTMutation;

import RegressionOracles.Analyzer;
import RegressionOracles.ObserverInstrumenter;
import spoon.Launcher;
import spoon.reflect.code.*;
import spoon.reflect.declaration.*;
import spoon.reflect.factory.Factory;
import spoon.reflect.reference.CtExecutableReference;
import spoon.reflect.reference.CtTypeReference;
import spoon.reflect.reference.CtVariableReference;
import java.util.concurrent.TimeoutException;
import spoon.reflect.visitor.filter.TypeFilter;
import spoon.support.reflect.code.*;
import utils.Config;
import utils.Pair;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.lang.annotation.Annotation;
import java.util.*;


public class CombinationGenerator {
    private List<Integer> positions;
    private List<List<Integer>> inputIndices;
    private int[] currentIndices;
    private int currentIndex = 0;
    private long totalCombinations = 0;
    private boolean hasMore = true;
    private boolean DEBUG = false;

    public CombinationGenerator(LinkedHashMap<Integer, List<Input>> largestInputPools, int tWay) {
         if (tWay < 1 || tWay > largestInputPools.size()) {
             throw new IllegalArgumentException("Invalid tWay value. It must be between 1 and the number of input pools.");
         }
         
         // [수정] Position 0을 가장 우선적으로 변경하도록 정렬
         // Position 0 (Receiver Object)을 첫번째로 고정, 나머지는 pool size로 정렬
         List<Map.Entry<Integer, List<Input>>> sortedEntries = new ArrayList<>(largestInputPools.entrySet());
         
         // Position 0을 찾고 맨 앞으로 이동
         Map.Entry<Integer, List<Input>> pos0Entry = null;
         for (Map.Entry<Integer, List<Input>> entry : sortedEntries) {
             if (entry.getKey() == 0) {
                 pos0Entry = entry;
                 break;
             }
         }
         
         if (pos0Entry != null) {
             sortedEntries.remove(pos0Entry);
             sortedEntries.add(0, pos0Entry);  // Position 0을 맨 앞에 추가
         }
         
         // 나머지 positions은 pool size로 정렬 (작은 것 먼저)
         List<Map.Entry<Integer, List<Input>>> restEntries = new ArrayList<>(sortedEntries.subList(pos0Entry != null ? 1 : 0, sortedEntries.size()));
         restEntries.sort(Comparator.comparingInt(e -> e.getValue().size()));
         
         if (pos0Entry != null) {
             sortedEntries.clear();
             sortedEntries.add(pos0Entry);
             sortedEntries.addAll(restEntries);
         } else {
             sortedEntries = restEntries;
         }
         
         this.positions = new ArrayList<>();
         this.inputIndices = new ArrayList<>();
         
         for (Map.Entry<Integer, List<Input>> entry : sortedEntries) {
             Integer pos = entry.getKey();
             List<Input> inputs = entry.getValue();
             
             positions.add(pos);
             
             List<Integer> indices = new ArrayList<>();
             for (int i = 0; i < inputs.size(); i++) {
                 indices.add(i);
             }
             inputIndices.add(indices);
         }
         
         this.currentIndices = new int[inputIndices.size()];
         this.totalCombinations = calculateTotalCombinations();
         
         if(totalCombinations > 1000000) {
             // System.out.println("[WARNING] Large combination space detected: " + totalCombinations + " combinations");
         }
         if(DEBUG) {
             System.out.println("[DEBUG] CombinationGenerator created with a total of " + this.totalCombinations + " combinations.");
             System.out.println("[DEBUG] Position order (Priority on Receiver Position 0): " + this.positions);
         }
     }
    
    private long calculateTotalCombinations() {
        long total = 1;
        for (List<Integer> indices : inputIndices) {
            total *= indices.size();
            if (total > 100000000) {
                return 100000000;
            }
        }
        return total;
    }
    
    public int getCurrentIndex(){
        return this.currentIndex;
    }

    public int getTotalCombinations(){
        return (int) Math.min(totalCombinations, Integer.MAX_VALUE);
    }

    public boolean hasNext() {
        return hasMore;
    }

    public Map<Integer, Integer> nextCombination() {
         if (!hasMore) {
             return null;
         }
         
         Map<Integer, Integer> result = new LinkedHashMap<>();  // LinkedHashMap으로 순서 보장
         for (int i = 0; i < positions.size(); i++) {
             result.put(positions.get(i), inputIndices.get(i).get(currentIndices[i]));
         }
         
         if (DEBUG) {
             System.out.println("[DEBUG] Combination #" + currentIndex + ": " + result);
         }
         
         incrementIndices();
         currentIndex++;
         
         return result;
     }
    
     private void incrementIndices() {
         // [수정] Position 0 (Receiver)을 가장 우선적으로 변경하도록 수정
         // positions[0]이 0이면 (Position 0이 첫번째), 그것을 먼저 증가시킴
         // 예: 0,0 -> 1,0 -> 2,0 -> 0,1 -> 1,1 -> ...
         
         // Position 0이 currentIndices[0]에 해당하므로, 항상 첫번째 증가
         int pos = 0;
         
         while (pos < currentIndices.length) {
             currentIndices[pos]++;
             if (currentIndices[pos] < inputIndices.get(pos).size()) {
                 return;
             }
             currentIndices[pos] = 0;
             pos++;
         }
         
         hasMore = false;
     }
}