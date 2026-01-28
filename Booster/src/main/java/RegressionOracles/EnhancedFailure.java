package RegressionOracles;

import org.junit.runner.notification.Failure;
import spoon.reflect.code.CtStatement;

/**
 * JUnit Failure를 확장하여 실패한 Statement 객체를 직접 저장
 * 라인 번호에 의존하지 않고 Statement 객체 자체로 매칭
 */
public class EnhancedFailure {
    private final Failure failure;
    private CtStatement mutStatement;  // 실패 원인이 된 MUT statement
    private String statementSignature; // Statement의 시그니처 (디버깅용)
    
    public EnhancedFailure(Failure failure) {
        this.failure = failure;
    }
    
    public EnhancedFailure(Failure failure, CtStatement mutStatement) {
        this.failure = failure;
        this.mutStatement = mutStatement;
        this.statementSignature = generateSignature(mutStatement);
    }
    
    /**
     * Statement의 고유한 시그니처 생성
     * 예: "doc.child(3)" -> "doc.child(3)"
     */
    private static String generateSignature(CtStatement stmt) {
        if (stmt == null) return null;
        String signature = stmt.toString().trim();
        // 공백 정규화
        signature = signature.replaceAll("\\s+", " ");
        return signature;
    }
    
    // Getters
    public Failure getFailure() {
        return failure;
    }
    
    public CtStatement getMutStatement() {
        return mutStatement;
    }
    
    public void setMutStatement(CtStatement mutStatement) {
        this.mutStatement = mutStatement;
        this.statementSignature = generateSignature(mutStatement);
    }
    
    public String getStatementSignature() {
        return statementSignature;
    }
    
    /**
     * 주어진 Statement가 실패한 MUT statement와 동일한지 확인
     */
    public boolean isMatchingStatement(CtStatement stmt) {
        if (mutStatement == null || stmt == null) {
            return false;
        }
        
        // Method 1: 객체 직접 비교 (가장 정확함)
        if (mutStatement.equals(stmt)) {
            return true;
        }
        
        // Method 2: 시그니처 비교 (객체가 다르지만 내용이 같은 경우)
        String stmtSignature = generateSignature(stmt);
        if (statementSignature != null && statementSignature.equals(stmtSignature)) {
            return true;
        }
        
        return false;
    }
    
    @Override
    public String toString() {
        return "EnhancedFailure{" +
                "exception=" + failure.getException().getClass().getSimpleName() +
                ", signature='" + statementSignature + '\'' +
                ", hasMutStatement=" + (mutStatement != null) +
                '}';
    }
}
