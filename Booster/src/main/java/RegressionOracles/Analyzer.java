package RegressionOracles;

import Generater.MUTMutation.ASTParser;
import Generater.MUTMutation.TestCaseGenerator;
import org.junit.Test;
import spoon.reflect.code.CtInvocation;
import spoon.reflect.code.CtLocalVariable;
import spoon.reflect.code.CtStatement;
import spoon.reflect.code.CtVariableRead;
import spoon.reflect.code.CtBlock;
import spoon.reflect.code.CtLoop;
import spoon.reflect.code.CtIf;
import spoon.reflect.code.CtTry;
import spoon.reflect.code.CtSwitch;
import spoon.reflect.declaration.CtAnnotation;
import spoon.reflect.declaration.CtElement;
import spoon.reflect.declaration.CtMethod;
import spoon.reflect.declaration.CtType;
import spoon.reflect.declaration.CtVariable;
import spoon.reflect.reference.CtTypeReference;
import spoon.reflect.visitor.filter.TypeFilter;
import spoon.support.reflect.code.CtConstructorCallImpl;
import spoon.support.reflect.code.CtInvocationImpl;
import spoon.support.reflect.code.CtVariableReadImpl;
import spoon.reflect.code.*;
import spoon.support.reflect.code.*;
import utils.Config;

import java.util.*;

public class Analyzer {

    /**
     * 안전한 toString() 호출 - 중첩 클래스 문제 해결
     */
    private static String safeToString(Object obj) {
        try {
            return obj.toString();
        } catch (spoon.SpoonException e) {
            // Spoon의 nested class 해결 문제 처리
            if (e.getMessage() != null && e.getMessage().contains("Cannot compute access path to type")) {
                return obj.getClass().getSimpleName() + "@" + Integer.toHexString(obj.hashCode());
            }
            throw e; // 다른 SpoonException은 재발생
        } catch (Exception e) {
            // 다른 일반적인 toString() 실패 시 클래스 이름과 해시코드 반환
            return obj.getClass().getSimpleName() + "@" + Integer.toHexString(obj.hashCode());
        }
    }
    /**
     * collects local variables that are NOT primitive and the type is CUT
     * (Config.FULL_CLASS_NAME)
     *
     * @param testMethod
     * @return
     */
    // List<CtLocalVariable> analyze(CtMethod testMethod) {
    //     List<CtLocalVariable> result = new ArrayList<>();
    //     List<CtStatement> stmts = testMethod.getBody().getStatements();
    //     for (CtStatement stmt : stmts) {
    //         if (isLastStmt(stmt, stmts)) { // check if stmt is MUT
    //             if (ASTParser.isInvocation(stmt)) {
    //                 if (ASTParser.isLocalVariable(stmt)) {
    //                     List<CtLocalVariable> localVars = stmt.getElements(new TypeFilter<>(CtLocalVariable.class));
    //                     CtLocalVariable localVar = localVars.get(0); // we have only one element in localVars because we
    //                                                                  // collected from a single statement
    //                     if (!localVar.getType().isPrimitive()) {
    //                         //Collects Object Types
    //                         result.add(localVar);
    //                         break;
    //                     }
    //                 } else {
    //                     List<CtInvocation> invokes = stmt.getElements(new TypeFilter<>(CtInvocation.class));
    //                     CtInvocation invoke = invokes.get(0);
    //                     if (!invoke.getExecutable().isStatic()) {
    //                         CtVariableReadImpl target = (CtVariableReadImpl) invoke.getTarget();
    //                         CtLocalVariable localVar = (CtLocalVariable) target.getVariable().getDeclaration();
    //                         if (localVar != null) {
    //                             if (!localVar.getType().isPrimitive()) {
    //                                 result.add(localVar);
    //                                 break;
    //                             }
    //                         }
    //                     } else { // MUT is static!
    //                         break;
    //                     }
    //                 }
    //             }
    //         }
    //     }
    //     return result;
    // }

    /**
     * collects ALL local variables that are NOT primitive
     * This allows assertion generation for all object variables in the test method
     * 
     * @param testMethod
     * @return
     */
     List<CtLocalVariable> analyze(CtMethod<?> testMethod) {
          List<CtLocalVariable> result = new ArrayList<>();
          
          // 메서드의 모든 로컬 변수를 수집
          List<CtLocalVariable> allLocalVars = testMethod.getBody().getElements(new TypeFilter<>(CtLocalVariable.class));
          
          // 메서드 스코프에만 속한 non-primitive 변수들을 필터링
          for (CtLocalVariable var : allLocalVars) {
              // 메서드 스코프에만 속한 변수인지 확인 (nested block 제외)
              if (isVariableInMethodScope(var, testMethod)) {
                  // non-primitive 타입인지 확인
                  if (var.getType() != null && !var.getType().isPrimitive()) {
                      // ★ 수정: 변수명에 stringVal이 포함되면 수집하지 않음
                      // 이것은 기본형을 String으로 변환하는 변수들이므로 제외
                      String varName = var.getSimpleName();
                      if (varName != null && varName.contains("stringVal")) {
                          // 기본형→String 변환 변수 제외
                          continue;
                      }
                      result.add(var);
                  }
              }
          }
          
          return result;
     }

    public Map<CtMethod, List<CtLocalVariable>> analyze(CtType<?> ctClass, boolean forPrimitive) {
        Map<CtMethod, List<CtLocalVariable>> result = new HashMap<>();
        CtTypeReference<Test> reference = ctClass.getFactory().Type().createReference(Test.class);
        Set<CtMethod<?>> methods = ctClass.getMethods();
        for (CtMethod<?> ctMethod : methods) {
            for (CtAnnotation a : ctMethod.getAnnotations()) {
                if (a.getAnnotationType().getSimpleName().equals(reference.getSimpleName())) {
                    if (forPrimitive) {
                        result.put(ctMethod, analyzePrimitive(ctMethod));
                    } else {
                        result.put(ctMethod, analyze(ctMethod));
                    }
                    break;
                }
            }
        }
        return result;
    }

     /**
      * collects ALL local variables that are primitive type (including MUT return value)
      * This allows assertion generation for all primitive variables in the test method
      *
      * @param testMethod
      * @return
      */
     List<CtLocalVariable> analyzePrimitive(CtMethod testMethod) {
         List<CtLocalVariable> result = new ArrayList<>();
         
         // 메서드의 모든 로컬 변수를 수집
         List<CtLocalVariable> allLocalVars = testMethod.getBody().getElements(new TypeFilter<>(CtLocalVariable.class));
         
         // 메서드 스코프에만 속한 primitive 변수들을 필터링
         for (CtLocalVariable var : allLocalVars) {
             // 메서드 스코프에만 속한 변수인지 확인 (nested block 제외)
             if (isVariableInMethodScope(var, testMethod)) {
                 // primitive 타입인지 확인
                 if (var.getType() != null && var.getType().isPrimitive()) {
                     result.add(var);
                 }
             }
         }
         
         return result;
     }
     
      /**
       * Check if a local variable is declared at method level scope (not inside blocks like loops/conditions)
       * 
       * 주의: 변수가 for/while/if 등의 제어문에서 직접 선언된 경우도 제외
       * 예: for (int i = 0; ...) → i는 루프 제어 변수이므로 관찰 불가
       *     if (condition) { int x = 1; } → x는 if 블록 내 변수이므로 관찰 불가
       */
      private boolean isVariableInMethodScope(CtLocalVariable variable, CtMethod method) {
          if (variable == null || method == null) {
              return false;
          }

          // ★ 먼저 변수의 부모를 확인: 루프나 조건문에서 직접 선언된 변수인지 체크
          CtElement directParent = variable.getParent();
          
          // for/while 루프의 제어 변수 확인
          if (directParent instanceof CtLoop) {
              // 변수가 루프의 직접적인 부모인 경우 → 루프 제어 변수
              // 예: for (int i = 0; ...) 에서 i
              return false;
          }
          
          // if/switch 제어문 내의 변수 확인
          if (directParent instanceof CtIf || directParent instanceof CtSwitch) {
              return false;
          }

          // Get the parent element of the variable
          CtElement parent = variable.getParent();

          // Keep going up the parent chain until we find a CtBlock or CtMethod
          while (parent != null) {
              if (parent instanceof CtMethod) {
                  // If we reached the method directly, it's method-level scope
                  return parent.equals(method);
              } else if (parent instanceof CtBlock) {
                  // Check if this block is the method's body
                  CtBlock block = (CtBlock) parent;
                  CtElement blockParent = block.getParent();

                  if (blockParent instanceof CtMethod && blockParent.equals(method)) {
                      // This is the method's main body block - method level scope
                      return true;
                  } else if (blockParent instanceof CtLoop ||
                            blockParent instanceof CtIf ||
                            blockParent instanceof CtTry ||
                            blockParent instanceof CtSwitch) {
                      // This is a block inside a control structure - not method level scope
                      return false;
                  }
              }
              parent = parent.getParent();
          }

          return false;
      }


    private boolean isLastStmt(CtStatement stmt, List<CtStatement> stmts) {
        if (stmts == null || stmts.isEmpty()) {
            return false;
        }
        for (int i = stmts.size() - 1; i >= 0; i--) {
            CtStatement currentStmt = stmts.get(i);

            // toString() 호출을 try-catch로 감싸서 중첩 클래스 문제 해결
            try {
                if (safeToString(currentStmt).contains("RegressionOracles.RegressionUtil.Logger.observe(")) {
                    continue;
                }
            } catch (Exception e) {
                // toString() 실패 시 다른 방법으로 체크
                System.err.println("[WARN] safeToString() failed for statement, using alternative check: " + e.getMessage());
                // CtInvocation을 직접 체크하여 Logger.observe 호출인지 확인
                if (currentStmt instanceof CtInvocation) {
                    CtInvocation<?> invocation = (CtInvocation<?>) currentStmt;
                    if (invocation.getExecutable() != null && 
                        invocation.getExecutable().getSimpleName().equals("observe")) {
                        continue;
                    }
                }
            }
            if (TestCaseGenerator.getMUT(currentStmt) != null) {
                return currentStmt == stmt; 
            }
        }

        return false;
    }

}
