package utils;
import java.util.Objects;

public class Pair<K, V> {
    private K key;
    private V value;

    public Pair(K key, V value) {
        this.key = key;
        this.value = value;
    }

    public K getKey() {
        return key;
    }

    public void setKey(K key) {
        this.key = key;
    }

    public V getValue() {
        return value;
    }

    public void setValue(V value) {
        this.value = value;
    }

    @Override
    public String toString() {
        return "Pair{" + "key=" + key + ", value=" + value + '}';
    }
    
    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;
        Pair<?, ?> pair = (Pair<?, ?>) o;

        // key와 value의 문자열 표현을 비교합니다.
        String thisKeyStr = (this.key != null) ? this.key.toString() : null;
        String thatKeyStr = (pair.key != null) ? pair.key.toString() : null;

        String thisValueStr = (this.value != null) ? this.value.toString() : null;
        String thatValueStr = (pair.value != null) ? pair.value.toString() : null;

        return java.util.Objects.equals(thisKeyStr, thatKeyStr) &&
                java.util.Objects.equals(thisValueStr, thatValueStr);
    }

    @Override
    public int hashCode() {
        // equals에서 사용한 것과 동일한 toString() 결과를 기반으로 해시코드를 생성합니다.
        String keyStr = (key != null) ? key.toString() : null;
        String valueStr = (value != null) ? value.toString() : null;
        return java.util.Objects.hash(keyStr, valueStr);
    }
}
