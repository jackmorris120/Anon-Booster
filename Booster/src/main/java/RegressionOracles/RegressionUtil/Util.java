package RegressionOracles.RegressionUtil;

import spoon.reflect.code.CtExpression;
import spoon.reflect.code.CtInvocation;
import spoon.reflect.code.CtLocalVariable;
import spoon.reflect.code.CtVariableAccess;
import spoon.reflect.declaration.CtClass;
import spoon.reflect.declaration.CtMethod;
import spoon.reflect.declaration.CtInterface;
import spoon.reflect.declaration.ModifierKind;
import spoon.reflect.factory.Factory;
import spoon.reflect.reference.CtExecutableReference;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Created by Benjamin DANGLOT
 * benjamin.danglot@inria.fr
 * on 26/06/17
 */
public class Util {
    public static String getKey(CtMethod method, CtLocalVariable localVariable) {
        // getter 메서드의 키도 로컬 변수 프리픽스 사용
        String localVarKey = "local$" + localVariable.getSimpleName();
        if (method.getParent(CtClass.class)==null){
            return method.getParent(CtInterface.class).getSimpleName() + "#" + method.getSimpleName() + "#" + localVarKey;
        } else {
            return method.getParent(CtClass.class).getSimpleName() + "#" + method.getSimpleName() + "#" + localVarKey;
        }
        
    }

    public static CtInvocation invok(CtMethod method, CtLocalVariable localVariable) {
        final CtExecutableReference reference = method.getReference();
        final CtVariableAccess variableRead = method.getFactory().createVariableRead(localVariable.getReference(), false);
        return method.getFactory().createInvocation(variableRead, reference);
    }

    public static List<CtMethod> getGetters(CtLocalVariable localVariable) {
        if (localVariable.getType().getTypeDeclaration() != null) {
            Set<CtMethod<?>> allMethods = (Set<CtMethod<?>>) localVariable.getType().getTypeDeclaration().getMethods();

            return allMethods.stream()
                    .filter(method -> {
                        boolean noParams = method.getParameters().isEmpty();
                        boolean isPublic = method.getModifiers().contains(ModifierKind.PUBLIC);
                        boolean notVoid = method.getType() != localVariable.getFactory().Type().VOID_PRIMITIVE;
                        boolean isPrimitiveOrString = method.getType().isPrimitive() || method.getType().getSimpleName().equals("String");
                        boolean hasGetterName = method.getSimpleName().startsWith("get") ||
                                method.getSimpleName().startsWith("is") ||
                                method.getSimpleName().equals("size");

                        return noParams && isPublic && notVoid && isPrimitiveOrString && hasGetterName;
                    })
                    .collect(Collectors.toList());
        } else {
            return new ArrayList<>();
        }
    }

    public static String getKey(CtLocalVariable localVariable) {
        // 로컬 변수는 "local$변수명" 형식으로 키 생성하여 필드 참조와 구분
        return "local$" + localVariable.getSimpleName();
    }

    public static CtExpression assignment(Factory factory, CtLocalVariable localVariable) {
        return factory.Code().createVariableAssignment(
                localVariable.getReference(), false, localVariable.getDefaultExpression()).getAssigned();
    }
}
