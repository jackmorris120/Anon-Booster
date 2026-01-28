package Generater.PrimitiveMutation;

import java.util.*;

public class CombinationIterator implements Iterator<Map<String, Object>> {

    private TriplePairs[] keys;
    private List<Object>[] pools;
    private int[] cursor;
    private boolean hasNext = true;
    private Map<String, Object> reusable = new HashMap<>();

    @SuppressWarnings("unchecked")
    public CombinationIterator(Map<TriplePairs, List<Object>> mapping) {
        keys = mapping.keySet().toArray(new TriplePairs[0]);
        pools = new List[keys.length];
        for (int i = 0; i < keys.length; i++) {
            List<Object> pool = mapping.get(keys[i]);
            pools[i] = (pool == null || pool.isEmpty())
                    ? Collections.singletonList(null)
                    : pool;
        }
        cursor = new int[keys.length]; // 모두 0
        buildMap();
    }

    private void buildMap() {
        reusable.clear();
        for (int i = 0; i < keys.length; i++) {
            reusable.put(keys[i].getStmtPath().toString(),
                    pools[i].get(cursor[i]));
        }
    }

    @Override
    public boolean hasNext() {
        return hasNext;
    }

    @Override
    public Map<String, Object> next() {
        if (!hasNext)
            throw new NoSuchElementException();
        Map<String, Object> snapshot = new HashMap<>(reusable);

        /* 진법 올림 */
        for (int pos = keys.length - 1; pos >= 0; pos--) {
            if (++cursor[pos] < pools[pos].size()) {
                buildMap();
                return snapshot;
            }
            cursor[pos] = 0;
        }
        hasNext = false; // 마지막 조합 방금 반환
        return snapshot;
    }
}