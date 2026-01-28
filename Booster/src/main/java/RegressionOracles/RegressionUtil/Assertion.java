package RegressionOracles.RegressionUtil;

import utils.Config;

public class Assertion {
    private String key; //Flat3Map#isEmpty
    private Object getters; //flat3Map0_257.isEmpty()

    public Assertion(String key, Object getters) {
        this.key = key;
        this.getters = getters;
    }

    public String getKey() {
        return key;
    }

    public Object getGetters() {
        if (getters == null)
            return "null";
        if (getters instanceof String)
            return Config.STRING_IDENTIFIER + getters;
        if (getters instanceof Character)
            return getters; // Character 객체를 그대로 반환 (AssertionAdder에서 처리)
        if (getters.equals(Double.NaN))
            return "Double.NaN";
        else if (getters.equals(Double.POSITIVE_INFINITY))
            return "Double.POSITIVE_INFINITY";
        else if (getters.equals(Double.NEGATIVE_INFINITY))
            return "Double.NEGATIVE_INFINITY";
        if (getters.equals(Float.NaN))
            return "Float.NaN";
        else if (getters.equals(Float.POSITIVE_INFINITY))
            return "Float.POSITIVE_INFINITY";
        else if (getters.equals(Float.NEGATIVE_INFINITY))
            return "Float.NEGATIVE_INFINITY";
        else {
            if (key.startsWith("long") && !getters.toString().endsWith("L")) // when primitive type is long
                return getters.toString() + "L";
            else if (key.startsWith("float") && !getters.toString().endsWith("F")) // when primitive type is long
                return getters.toString() + "F";
            return getters;
        }
    }
}
