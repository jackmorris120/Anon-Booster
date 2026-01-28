package Generater.MUTMutation;

import spoon.reflect.declaration.CtElement;
import spoon.reflect.reference.CtTypeReference;

import java.util.List;

public class Input {
    private boolean isMUTStatic; //this includes both static invocation and constructor call
    private CtTypeReference type;
    private boolean isVar;
    private CtElement varName;
    private List<CtElement> input;

    public Input(CtTypeReference type, boolean isVar, CtElement varName, List<CtElement> input) {
        this.type = type;
        this.isVar = isVar;
        this.varName = varName;
        this.input = input;
        this.isMUTStatic = false;
    }

    public Input(boolean isMUTStatic) {
        this.isMUTStatic = isMUTStatic;
        this.type = null;
        this.isVar = false;
        this.varName = null;
        this.input = null;
    }

    public CtTypeReference getType() {
        return type;
    }

    public boolean isVar() {
        return isVar;
    }

    public CtElement getDirectValue() {
        if (!isVar) {
            return varName;
        }
        return null; // 또는 예외 처리
    }

    public boolean isMUTStatic() {
        return isMUTStatic;
    }

    public CtElement getVarName() {
        return varName;
    }

    public List<CtElement> getInput() {
        return input;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("Input{");
        sb.append("Type=").append(type);
        sb.append(", isVar=").append(isVar);

        if (isVar) {
            sb.append(", Variable=").append(varName);
            if (input != null) {
                sb.append(", SetupStatements=").append(input.size());
            }
        } else {
            sb.append(", Value=").append(varName);
        }

        sb.append(", isStatic=").append(isMUTStatic);
        sb.append("}");

        return sb.toString();
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof Input))
            return false;
        Input other = (Input) o;

        if (this.isMUTStatic != other.isMUTStatic)
            return false;
        if (this.type != null) {
            if (other.type == null)
                return false;
            if (!this.type.toString().equals(other.type.toString()))
                return false;
        } else {
            if (other.type != null)
                return false;
        }
        if (this.isVar != other.isVar)
            return false;
        if (this.varName != null) {
            if (other.varName == null)
                return false;
//            if (!this.varName.toString().equals(other.varName.toString()))
//                return false;
        } else {
            if (other.varName != null)
                return false;
        }
        if (this.input != null) {
            if (other.input != null) {
                if (this.input.size() != other.input.size())
                    return false;
                for (int i = 0; i < this.input.size(); i++) {
                    CtElement ele = this.input.get(i);
//                    System.out.println(ele.toString());
                    if (!ele.toString().equals(other.input.get(i).toString()))
                        return false;
                }
            } else {
                return false;
            }
        } else {
            return other.input == null;
        }
        return true;

    }
}
