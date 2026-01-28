package Generater.PrimitiveMutation;

import spoon.reflect.code.CtLiteral;
import java.util.List;
import java.util.Objects;

public class TriplePairs {
    private final List<Integer> stmtPath;
    private final CtLiteral<?> literal;  // CtLiteral 객체
    private final String detectedType;   // 최종 캐스팅 타입 정보 (예: "double")

    public TriplePairs(List<Integer> stmtPath, CtLiteral<?> literal, String detectedType) {
        this.stmtPath = stmtPath;
        this.literal = literal;
        this.detectedType = detectedType;
    }

    public List<Integer> getStmtPath() {
        return stmtPath;
    }

    public CtLiteral<?> getLiteral() {
        return literal;
    }

    public String getDetectedType() {
        return detectedType;
    }

    @Override
    public String toString() {
        return String.format(
            "TriplePairs{stmtPath=%s, literal=%s, detectedType=%s}",
            Objects.toString(stmtPath),
            literal,
            detectedType
        );
    }
}
