package Generater.MUTMutation;

import spoon.reflect.code.CtAbstractInvocation;
import spoon.reflect.code.CtExpression;
import spoon.reflect.declaration.CtMethod;
import spoon.reflect.code.CtLocalVariable;
import spoon.support.reflect.code.CtInvocationImpl;

import java.util.ArrayList;
import java.util.List;

/**
 * Raw test case data
 */
public class RawTestCase {
    private CtMethod originalTestCase;
    private List<Input> insertStmts;
    private List<CtExpression> arguments;
    private CtAbstractInvocation mut;

    // ────────── [추가] 로컬 변수 저장용 필드 ──────────
    private List<CtLocalVariable<?>> localVariables;
    // ──────────────────────────────────────────────

    // 기존 생성자
    public RawTestCase(CtMethod originalTestCase, List<Input> insertStmts, List<CtExpression> arguments, CtAbstractInvocation mut) {
        this.originalTestCase = originalTestCase;
        this.insertStmts = insertStmts;
        this.arguments = arguments;
        this.mut = mut;
        this.localVariables = new ArrayList<>();  // 초기화
    }

    // 기존 생성자
    public RawTestCase(List<Input> insertStmts, List<CtExpression> arguments, CtAbstractInvocation mut) {
        this.originalTestCase = null;
        this.insertStmts = insertStmts;
        this.arguments = arguments;
        this.mut = mut;
        this.localVariables = new ArrayList<>();  // 초기화
    }

    public CtMethod getOriginalTestCase() {
        return originalTestCase;
    }

    public void setOriginalTestCase(CtMethod originalTestCase) {
        this.originalTestCase = originalTestCase;
    }

    public List<Input> getInsertStmts() {
        return insertStmts;
    }

    public void setInsertStmts(List<Input> insertStmts) {
        this.insertStmts = insertStmts;
    }

    public List<CtExpression> getArguments() {
        if (arguments == null || arguments.isEmpty()) {
            return new ArrayList<>();
        }
        return arguments.subList(Math.min(1, arguments.size()), arguments.size());
    }

    public void setArguments(List<CtExpression> arguments) {
        this.arguments = arguments;
    }

    public CtAbstractInvocation getMut() {
        return mut;
    }

    public void setMut(CtInvocationImpl mut) {
        this.mut = mut;
    }

    // ────────── [추가] 로컬 변수 리스트의 Getter/Setter ──────────
    public List<CtLocalVariable<?>> getLocalVariables() {
        return localVariables;
    }

    public void addLocalVariable(CtLocalVariable<?> localVar) {
        this.localVariables.add(localVar);
    }
    // ──────────────────────────────────────────────────────────

    @Override
    public String toString() {
        return this.mut.getExecutable().getSignature() + "\n\t"
                + "Arguments : " + this.arguments + "\n\t"
                + "Insert STMTS : " + this.insertStmts;
    }
}
