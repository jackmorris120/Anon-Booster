package RegressionOracles;

import RegressionOracles.RegressionUtil.Assertion;
import RegressionOracles.RegressionUtil.Logger;
import RegressionOracles.RegressionUtil.Util;
import org.junit.Assert;
import spoon.reflect.code.*;
import spoon.reflect.declaration.CtClass;
import spoon.reflect.declaration.CtMethod;
import spoon.reflect.declaration.CtParameter;
import spoon.reflect.factory.Factory;
import spoon.reflect.reference.CtExecutableReference;
import spoon.reflect.reference.CtTypeReference;
import utils.Config;

import java.text.NumberFormat;
import java.text.ParsePosition;
import java.util.List;
import java.util.Map;

public class AssertionAdder {
    // Debug flag for assertion transformation
    private static final boolean DEBUG_ASSERTION_TRANSFORM = false;  // 디버깅 비활성화
    
    private Factory factory;

    public AssertionAdder(Factory factory) {
        this.factory = factory;
    }

    public CtMethod addAssertion(CtMethod testMethod, Map<CtMethod, List<CtLocalVariable>> localVariablesPerTestMethod,
            Map<CtMethod, List<CtLocalVariable>> localVariablesPrimitive) {
         if (DEBUG_ASSERTION_TRANSFORM) {
              System.out.println("[AssertionAdder] ========================================");
              System.out.println("[AssertionAdder] Starting addAssertion for test: " + testMethod.getSimpleName());
              System.out.println("[AssertionAdder] localVariablesPerTestMethod size: " + localVariablesPerTestMethod.size());
              System.out.println("[AssertionAdder] localVariablesPrimitive size: " + localVariablesPrimitive.size());
          }
          
          final CtClass testClass = testMethod.getParent(CtClass.class);
          
          // [핵심 수정] Map 키 매칭: testMethod의 이름과 시그니처로 원본 메서드를 찾기
          List<CtLocalVariable> varsOfMethod = null;
          List<CtLocalVariable> varsOfPrimitive = null;
          
          // testMethod와 이름/시그니처가 일치하는 메서드를 찾아서 Map에서 값을 꺼냅니다
          for (CtMethod mapKey : localVariablesPerTestMethod.keySet()) {
              if (mapKey.getSimpleName().equals(testMethod.getSimpleName())) {
                  varsOfMethod = localVariablesPerTestMethod.get(mapKey);
                  if (DEBUG_ASSERTION_TRANSFORM) {
                      System.out.println("[AssertionAdder] Found varsOfMethod with " + (varsOfMethod != null ? varsOfMethod.size() : 0) + " variables");
                  }
                  break;
              }
          }
          
          for (CtMethod mapKey : localVariablesPrimitive.keySet()) {
              if (mapKey.getSimpleName().equals(testMethod.getSimpleName())) {
                  varsOfPrimitive = localVariablesPrimitive.get(mapKey);
                  if (DEBUG_ASSERTION_TRANSFORM) {
                      System.out.println("[AssertionAdder] Found varsOfPrimitive with " + (varsOfPrimitive != null ? varsOfPrimitive.size() : 0) + " variables");
                  }
                  break;
              }
          }
          
          testClass.removeMethod(testMethod);
          final CtMethod<?> clone = testMethod.clone();

          // Use class name as testName for Logger.observations lookup (matches what ObserverInstrumenter uses)
          String testName = testClass.getSimpleName();
          
          // Track variables that already have assertions added
          java.util.Set<String> processedVariables = new java.util.HashSet<>();

           // Check the first condition.
           if (varsOfMethod != null) {
               if (DEBUG_ASSERTION_TRANSFORM) {
                   System.out.println("[AssertionAdder] Adding assertion getter for " + varsOfMethod.size() + " getter variables");
               }
               addAssertionGetter(testName, clone, varsOfMethod, processedVariables);
           }

            // Check the second condition.
            if (varsOfPrimitive != null) {
                if (DEBUG_ASSERTION_TRANSFORM) {
                    System.out.println("[AssertionAdder] Adding assertion primitive for " + varsOfPrimitive.size() + " primitive variables");
                }
                addAssertionPrimitive(testName, clone, varsOfPrimitive, processedVariables);
            }
            
            // [NEW] MUT 반환값 변수(xxx_mut)에 대한 assertion 추가
            // Note: _mut 변수는 addAssertionGetter에서도 처리될 수 있으므로,
            // 이미 assertion이 추가된 경우는 건너뜀
            if (DEBUG_ASSERTION_TRANSFORM) {
                System.out.println("[AssertionAdder] Adding assertion for MUT variable");
            }
            addAssertionForMUTVariable(testName, clone, processedVariables);

           testClass.addMethod(clone);
           
           if (DEBUG_ASSERTION_TRANSFORM) {
               System.out.println("[AssertionAdder] ========================================");
           }
           
            return clone;
        }

       /**
        * MUT 반환값 변수(xxx_mut 패턴)에 대한 assertion을 추가합니다.
        * RecursiveTestCaseGenerator에서 생성된 MUT 변수는 localVariablesPerTestMethod에 포함되지 않으므로 별도로 처리합니다.
        * 
        * @param testName 테스트 클래스 이름
        * @param testMethod 테스트 메서드
        * @param processedVariables 이미 assertion이 추가된 변수들의 집합 (중복 방지)
        */
       private void addAssertionForMUTVariable(String testName, CtMethod<?> testMethod, java.util.Set<String> processedVariables) {
           Map<String, List<Assertion>> observationMap = Logger.observations;
           
           if (!observationMap.containsKey(testName)) {
               if (DEBUG_ASSERTION_TRANSFORM) {
                   System.out.println("[AssertionAdder] No observations found for testName: " + testName);
               }
               return;
           }
           
           // 메서드의 모든 로컬 변수를 검사
           List<CtLocalVariable> allLocalVars = testMethod.getBody().getElements(
               new spoon.reflect.visitor.filter.TypeFilter<>(CtLocalVariable.class));
           
           if (DEBUG_ASSERTION_TRANSFORM) {
               System.out.println("[AssertionAdder] Checking " + allLocalVars.size() + " local variables for _mut pattern");
           }
           
           int mutVariableCount = 0;
           for (CtLocalVariable var : allLocalVars) {
               // _mut로 끝나는 변수를 찾기 (MUT 반환값 변수)
               if (!var.getSimpleName().endsWith("_mut")) {
                   continue;
               }
               
               // 이미 처리된 변수는 건너뜀 (중복 방지)
               if (processedVariables.contains(var.getSimpleName())) {
                   if (DEBUG_ASSERTION_TRANSFORM) {
                       System.out.println("[AssertionAdder] Skipping MUT variable already processed: " + var.getSimpleName());
                   }
                   continue;
               }
               
               mutVariableCount++;
               if (DEBUG_ASSERTION_TRANSFORM) {
                   System.out.println("[AssertionAdder] Processing MUT variable: " + var.getSimpleName() + " (type: " + var.getType().getQualifiedName() + ")");
               }
              
               // Logger.observations에서 이 변수에 대한 관찰 데이터를 찾기
               String varKey = var.getSimpleName();
               List<Assertion> allAssertions = observationMap.get(testName);
               
               if (DEBUG_ASSERTION_TRANSFORM) {
                   System.out.println("[AssertionAdder]   🔎 Looking for MUT observations");
                   System.out.println("[AssertionAdder]   Variable key: " + varKey);
                   System.out.println("[AssertionAdder]   Total observations: " + (allAssertions != null ? allAssertions.size() : 0));
                   if (allAssertions != null) {
                       for (Assertion obs : allAssertions) {
                           System.out.println("[AssertionAdder]     - Observation key: \"" + obs.getKey() + "\"");
                           System.out.println("[AssertionAdder]       Getters: " + (obs.getGetters() != null ? obs.getGetters().getClass().getSimpleName() + " = " + obs.getGetters() : "null"));
                       }
                   }
               }
               
               boolean foundMatch = false;
                for (Assertion obs : allAssertions) {
                    // 키 매칭 전략:
                    // 1. 정확한 매칭: "string_mut" == "string_mut"
                    // 2. 단일 변수명 관찰: "local$string_mut"
                    // 3. 접두사 + 변수명: ".* #local$string_mut" (e.g., "String#isEmpty#local$string_mut")
                    // 제외: "local$string_mut.[String]" (타입 정보만)
                    
                    String obsKey = obs.getKey();
                    CtTypeReference<?> varType = var.getType();
                    boolean keyMatches = false;
                    
                    // 정확한 매칭 (우선순위 1)
                    if (varKey.equals(obsKey)) {
                        keyMatches = true;
                        if (DEBUG_ASSERTION_TRANSFORM) {
                            System.out.println("[AssertionAdder]   ✅ EXACT KEY MATCH: " + obsKey);
                        }
                    }
                    // 변수명만 있는 관찰: "local$string_mut"
                    else if (("local$" + varKey).equals(obsKey)) {
                        keyMatches = true;
                        if (DEBUG_ASSERTION_TRANSFORM) {
                            System.out.println("[AssertionAdder]   ✅ LOCAL VAR KEY MATCH: " + obsKey);
                        }
                    }
                    // 메서드 호출 결과: "String#isEmpty#local$string_mut" (하지만 메인 변수 타입이 String이면 제외)
                    else if (obsKey.matches(".*#local\\$" + varKey + "$") && !(varType != null && "java.lang.String".equals(varType.getQualifiedName()))) {
                        keyMatches = true;
                        if (DEBUG_ASSERTION_TRANSFORM) {
                            System.out.println("[AssertionAdder]   ✅ METHOD RESULT KEY MATCH: " + obsKey);
                        }
                    }
                    // 제외: 타입 정보만 있는 경우 (e.g., "local$string_mut.[String]")
                    else if (obsKey.contains("[") && obsKey.contains("]")) {
                        keyMatches = false;
                        if (DEBUG_ASSERTION_TRANSFORM) {
                            System.out.println("[AssertionAdder]   ⏭️  SKIPPING TYPE-ONLY observation: " + obsKey);
                        }
                    }
                    
                    if (keyMatches) {
                        foundMatch = true;
                    }
                    
                    if (keyMatches) {
                        // 이 변수에 대한 assertion을 추가합니다
                        Object got = obs.getGetters();
                        String raw = String.valueOf(got);
                       
                       if (DEBUG_ASSERTION_TRANSFORM) {
                           System.out.println("[AssertionAdder]   ✓ MATCH FOUND for key: " + varKey);
                           System.out.println("[AssertionAdder]   Value: " + (raw.length() > 60 ? raw.substring(0, 60) + "..." : raw));
                       }
                      
                        if (raw.equals("null")) {
                            // null인 경우
                            if (DEBUG_ASSERTION_TRANSFORM) {
                                System.out.println("[AssertionAdder]   📝 Adding assertNull for " + var.getSimpleName());
                            }
                            CtVariableAccess varRead = factory.Code().createVariableRead(var.getReference(), false);
                            testMethod.getBody().insertEnd(createAssertUnary("assertNull", varRead));
                        } else if (varType != null && varType.isPrimitive()) {
                            // Primitive 타입인 경우 (int, boolean, double 등)
                            if (DEBUG_ASSERTION_TRANSFORM) {
                                System.out.println("[AssertionAdder] 📝 Primitive type for assertion");
                                System.out.println("[AssertionAdder]   Type: " + varType.getSimpleName());
                                System.out.println("[AssertionAdder]   Value: " + raw);
                            }
                            CtVariableAccess varRead = factory.Code().createVariableRead(var.getReference(), false);
                            CtExpression expected = factory.createCodeSnippetExpression(raw);
                            if (expected != null) {
                                CtInvocation inv = createAssert("assertEquals", expected, varRead);
                                testMethod.getBody().insertEnd(inv);
                                if (DEBUG_ASSERTION_TRANSFORM) {
                                    System.out.println("[AssertionAdder] ✅ Primitive assertion added");
                                }
                            }
                        } else if (varType != null && !varType.isPrimitive() && !"java.lang.String".equals(varType.getQualifiedName())) {
                            // Object 타입인 경우 - toString 우선, 그 다음 equals 오버라이드 확인
                            if (DEBUG_ASSERTION_TRANSFORM) {
                                System.out.println("\n[AssertionAdder] 🔍 Object type variable detected!");
                                System.out.println("[AssertionAdder]   Variable: " + var.getSimpleName());
                                System.out.println("[AssertionAdder]   Type: " + varType.getQualifiedName());
                                System.out.println("[AssertionAdder]   Value: " + (raw.length() > 60 ? raw.substring(0, 60) + "..." : raw));
                            }
                            
                             // toString 오버라이드 확인 (우선순위 1)
                               if (ObjectMethodHelper.hasToStringOverride(varType) || ObjectMethodHelper.hasToStringOverrideRuntime(got)) {
                                  if (DEBUG_ASSERTION_TRANSFORM) {
                                      System.out.println("[AssertionAdder] ✅ DECISION: Use toString().equals() (toString override found)");
                                      System.out.println("[AssertionAdder]   Pattern: Assert.assertEquals(expected, " + var.getSimpleName() + ".toString())");
                                  }
                                  
                                  // Object의 toString() 결과에서 STRING_IDENTIFIER 제거
                                  String expectedValue = raw;
                                  if (raw.startsWith(Config.STRING_IDENTIFIER)) {
                                      expectedValue = raw.replace(Config.STRING_IDENTIFIER, "");
                                      if (DEBUG_ASSERTION_TRANSFORM) {
                                          System.out.println("[AssertionAdder] 🔧 Removed STRING_IDENTIFIER prefix from toString result");
                                          System.out.println("[AssertionAdder]   Original: " + raw);
                                          System.out.println("[AssertionAdder]   Cleaned: " + expectedValue);
                                      }
                                  }
                                  
                                  // 1000자 제한 적용
                                  if (expectedValue.length() < 1000) {
                                      CtVariableAccess varRead = factory.Code().createVariableRead(var.getReference(), false);
                                      CtCodeSnippetExpression toStringCall = factory.createCodeSnippetExpression(
                                          var.getSimpleName() + ".toString()");
                                      CtExpression expectedStr = factory.createLiteral(expectedValue);
                                      if (expectedStr != null) {
                                          CtInvocation inv = createAssert("assertEquals", expectedStr, toStringCall);
                                          testMethod.getBody().insertEnd(inv);
                                          if (DEBUG_ASSERTION_TRANSFORM) {
                                              System.out.println("[AssertionAdder] ✅ Assertion added successfully");
                                          }
                                      }
                                  } else {
                                      if (DEBUG_ASSERTION_TRANSFORM) {
                                          System.out.println("[AssertionAdder] ⏭️  Value too long (>= 1000 chars), skipping assertion");
                                      }
                                  }
                              }
                             // equals 오버라이드 확인 (우선순위 2)
                               else if (ObjectMethodHelper.hasEqualsOverride(varType) || ObjectMethodHelper.hasEqualsOverrideRuntime(got)) {
                                  if (DEBUG_ASSERTION_TRANSFORM) {
                                      System.out.println("[AssertionAdder] ✅ DECISION: Use assertEquals (equals override found)");
                                      System.out.println("[AssertionAdder]   Pattern: Assert.assertEquals(expected, " + var.getSimpleName() + ")");
                                  }
                                  
                                  // Object의 equals() 결과에서 STRING_IDENTIFIER 제거
                                  String expectedValue = raw;
                                  if (raw.startsWith(Config.STRING_IDENTIFIER)) {
                                      expectedValue = raw.replace(Config.STRING_IDENTIFIER, "");
                                      if (DEBUG_ASSERTION_TRANSFORM) {
                                          System.out.println("[AssertionAdder] 🔧 Removed STRING_IDENTIFIER prefix from equals value");
                                          System.out.println("[AssertionAdder]   Original: " + raw);
                                          System.out.println("[AssertionAdder]   Cleaned: " + expectedValue);
                                      }
                                  }
                                  
                                  // 1000자 제한 적용
                                  if (expectedValue.length() < 1000) {
                                      CtVariableAccess varRead = factory.Code().createVariableRead(var.getReference(), false);
                                      CtExpression expected = factory.createCodeSnippetExpression(expectedValue);
                                      if (expected != null) {
                                          CtInvocation inv = createAssert("assertEquals", expected, varRead);
                                          testMethod.getBody().insertEnd(inv);
                                          if (DEBUG_ASSERTION_TRANSFORM) {
                                              System.out.println("[AssertionAdder] ✅ Assertion added successfully");
                                          }
                                      }
                                  } else {
                                      if (DEBUG_ASSERTION_TRANSFORM) {
                                          System.out.println("[AssertionAdder] ⏭️  Value too long (>= 1000 chars), skipping assertion");
                                      }
                                   }
                               } else {
                                 if (DEBUG_ASSERTION_TRANSFORM) {
                                     System.out.println("[AssertionAdder] ⏭️  No equals/toString override, skipping Object assertion");
                                 }
                             }
                       } else if (varType != null && "java.lang.String".equals(varType.getQualifiedName())) {
                           // String 타입인 경우
                           if (DEBUG_ASSERTION_TRANSFORM) {
                               System.out.println("[AssertionAdder]   Adding String assertion for " + var.getSimpleName());
                           }
                           CtVariableAccess varRead = factory.Code().createVariableRead(var.getReference(), false);
                           CtExpression expected = null;
                           
                            if (raw.startsWith(Config.STRING_IDENTIFIER)) {
                                String s = raw.replace(Config.STRING_IDENTIFIER, "");
                                // 특수문자 필터링 제거 - 모든 String assertion 생성 (빈 문자열 포함)
                                if (s.length() < 1000) {
                                    expected = factory.createLiteral(s);
                                    if (expected != null) {
                                        CtInvocation inv = createAssert("assertEquals", expected, varRead);
                                        testMethod.getBody().insertEnd(inv);
                                    }
                                }
                             } else {
                                 expected = factory.createCodeSnippetExpression(raw);
                                 if (expected != null) {
                                     CtInvocation inv = createAssert("assertEquals", expected, varRead);
                                     testMethod.getBody().insertEnd(inv);
                                 }
                             }
                        }
                        
                        break; // 한 건만 소비
                   }
               }
               
               if (DEBUG_ASSERTION_TRANSFORM && !foundMatch) {
                   System.out.println("[AssertionAdder]   ❌ NO KEY MATCH for: " + varKey);
               }
          }
          
          if (DEBUG_ASSERTION_TRANSFORM) {
              System.out.println("[AssertionAdder] Processed " + mutVariableCount + " MUT variables");
          }
      }

      private void addAssertionPrimitive(String testName, CtMethod<?> testMethod, List<CtLocalVariable> ctLocalVariables) {
           this.addAssertionPrimitive(testName, testMethod, ctLocalVariables, new java.util.HashSet<>());
       }
      
      private void addAssertionPrimitive(String testName, CtMethod<?> testMethod, List<CtLocalVariable> ctLocalVariables, java.util.Set<String> processedVariables) {
           if (DEBUG_ASSERTION_TRANSFORM) {
               System.out.println("[AssertionAdder] Starting addAssertionPrimitive for " + ctLocalVariables.size() + " variables");
           }
           int processedCount = 0;
           for (CtLocalVariable var : ctLocalVariables) {
               this.addAssertionPrimitive(testName, testMethod, var);
               processedVariables.add(var.getSimpleName());
               processedCount++;
           }
           if (DEBUG_ASSERTION_TRANSFORM) {
               System.out.println("[AssertionAdder] Completed addAssertionPrimitive for " + processedCount + " variables");
           }
       }

      void addAssertionPrimitive(String testName, CtMethod testMethod, CtLocalVariable localVariable) {
          if (DEBUG_ASSERTION_TRANSFORM) {
              System.out.println("[AssertionAdder] Processing primitive variable: " + localVariable.getSimpleName());
          }
         CtExpression assigned = Util.assignment(factory, localVariable);
         CtTypeReference assignedType = assigned.getType();
         String key = Util.getKey(localVariable);
         Map<String, List<Assertion>> observationMap = Logger.observations;

         if (observationMap.containsKey(testName)) {
             List<Assertion> observers = observationMap.get(testName);
             for (Assertion observer : observers) {
                 if (key.equals(observer.getKey())) {
                     CtInvocation assignmentToAssert = null;
                     
                     if (assignedType == null || assignedType.isArray()) {
                         continue;
                     }
                     
                      // 특수문자 필터링 제거 - char 타입 처리
                      if (assignedType.getSimpleName().equals("char")) {
                          Object rawValue = observer.getGetters();
                          
                          if (rawValue instanceof Character) {
                              char charValue = (Character) rawValue;
                              CtExpression expected = factory.createLiteral(charValue);
                              assignmentToAssert = createAssert("assertEquals",
                                      expected, //expected
                                      assigned); //actual
                          } else {
                              String strValue = rawValue.toString();
                              CtExpression expected = createCharLiteralFromString(strValue);
                              if (expected != null) {
                                  assignmentToAssert = createAssert("assertEquals",
                                          expected, //expected
                                          assigned); //actual
                              }
                          }
                          
                          if (assignmentToAssert != null) {
                              testMethod.getBody().insertEnd(assignmentToAssert);
                          }
                          continue;
                      }
                     
                      if (assignedType.getSimpleName().equals("double")) {
                          String doubleStr = observer.getGetters().toString();
                          // NaN, Infinity 값들은 스킵 (코드 생성 불가)
                          if (!doubleStr.contains("NaN") && !doubleStr.contains("Infinity")) {
                              assignmentToAssert = createAssert("assertEquals",
                                      factory.createCodeSnippetExpression(doubleStr), //expected
                                      assigned, //actual
                                      factory.createCodeSnippetExpression("0.01")); //delta
                          }
                      } else if (assignedType.getSimpleName().equals("float")) {
                          String floatStr = observer.getGetters().toString();
                          // NaN, Infinity 값들은 스킵 (코드 생성 불가)
                          if (!floatStr.contains("NaN") && !floatStr.contains("Infinity")) {
                              assignmentToAssert = createAssert("assertEquals",
                                      factory.createCodeSnippetExpression(floatStr), //expected
                                      assigned, //actual
                                      factory.createCodeSnippetExpression("0.01F")); //delta
                          }
                      } else if (assignedType.getSimpleName().equals("long")) {
                          String expected = observer.getGetters().toString();
                          // null 값은 제외
                          if (expected != null && !expected.equals("null")) {
                              if (!expected.endsWith("L"))
                                  expected = expected + "L";
                              assignmentToAssert = createAssert("assertEquals",
                                      factory.createCodeSnippetExpression(expected), //expected
                                      assigned); //actual
                          }
                     } else {
                         CtExpression expected = null;
                         if (!observer.getGetters().toString().startsWith(Config.STRING_IDENTIFIER)) {
                             String rawValue = observer.getGetters().toString();
                             expected = factory.createCodeSnippetExpression(formatNumericLiteral(rawValue));
                         } else {
                             if (isNumeric(observer.getGetters().toString()) && observer.getGetters().toString().length() < 1000)
                                 expected = factory.createLiteral(observer.getGetters().toString().replace(Config.STRING_IDENTIFIER, ""));
                         }
                         if (expected != null) {
                             assignmentToAssert = createAssert("assertEquals",
                                     expected, //expected
                                     assigned); //actual
                         }
                     }
                     if (assignmentToAssert != null) {
                         testMethod.getBody().insertEnd(assignmentToAssert);
                     }
                 }
             }
         }
     }

      private void addAssertionGetter(String testName, CtMethod<?> testMethod, List<CtLocalVariable> ctLocalVariables) {
          this.addAssertionGetter(testName, testMethod, ctLocalVariables, new java.util.HashSet<>());
      }
      
      private void addAssertionGetter(String testName, CtMethod<?> testMethod, List<CtLocalVariable> ctLocalVariables, java.util.Set<String> processedVariables) {
          if (DEBUG_ASSERTION_TRANSFORM) {
              System.out.println("[AssertionAdder] Starting addAssertionGetter for " + ctLocalVariables.size() + " variables");
          }
          int processedCount = 0;
          for (CtLocalVariable var : ctLocalVariables) {
              this.addAssertionGetter(testName, testMethod, var);
              processedVariables.add(var.getSimpleName());
              processedCount++;
          }
          if (DEBUG_ASSERTION_TRANSFORM) {
              System.out.println("[AssertionAdder] Completed addAssertionGetter for " + processedCount + " variables");
          }
      }

     public static CtInvocation createAssertUnary(String name, CtExpression param) {
        final Factory factory = param.getFactory();
        CtTypeAccess accessToAssert = factory.createTypeAccess(factory.createCtTypeReference(Assert.class));
        CtExecutableReference ref = factory.Executable()
            .createReference(factory.Type().get(Assert.class)
            .getMethodsByName(name).stream()
            .filter(m -> m.getParameters().size() == 1)
            .findFirst().get());
        return factory.createInvocation(accessToAssert, ref, param);
    }


    /**
     * 하나의 로컬 변수(localVariable)에 대해
     * 1) 변수 자체 값에 대한 어서션
     * 2) 해당 변수의 getter 호출 결과에 대한 어서션
     * 을 추가한다.
     *
     * 확장 포인트:
     *  - 특수 타입(배열/컬렉션/맵/Optional/BigDecimal/Enum/Date/Time) 우선 처리
     *  - 부동소수(double/float)는 assertClose(상대오차)로 통일
     *  - String은 리터럴 우선(길이 제한), 필요 시 스니펫
     *  - 기타 정수형/char/long은 기존 로직 유지
     */
     private void addAssertionGetter(String testName, CtMethod<?> testMethod, CtLocalVariable localVariable) {
         if (DEBUG_ASSERTION_TRANSFORM) {
             System.out.println("[AssertionAdder] Processing getter variable: " + localVariable.getSimpleName());
         }
         
         Map<String, List<Assertion>> observationMap = Logger.observations;
         if (!observationMap.containsKey(testName)) {
             if (DEBUG_ASSERTION_TRANSFORM) {
                 System.out.println("[AssertionAdder]   No observations found for testName: " + testName);
             }
             return;
         }

         final List<Assertion> allAssertions = observationMap.get(testName);
        final String varKey = RegressionOracles.RegressionUtil.Util.getKey(localVariable);
        final CtVariableAccess varRead = factory.Code().createVariableRead(localVariable.getReference(), false);
        final CtTypeReference<?> varType = localVariable.getType();

         // =========================
         // 1) 변수 자체 값에 대한 assertion
         // =========================
         for (Assertion obs : allAssertions) {
             if (!varKey.equals(obs.getKey())) continue;

             Object got = obs.getGetters();
             String raw = null;
             try {
                 raw = String.valueOf(got);
             } catch (Exception e) {
                 // toString() 메서드가 예외를 던지는 경우 (예: CharacterReader)
                 // 이 경우 해당 변수는 assertion 대상에서 제외
                 if (DEBUG_ASSERTION_TRANSFORM) {
                     System.out.println("[AssertionAdder]   Skipping assertion - toString() failed: " + e.getMessage());
                 }
                 break;
             }
             
             // raw가 null인 경우 스킵 (초기화 실패)
             if (raw == null) {
                 if (DEBUG_ASSERTION_TRANSFORM) {
                     System.out.println("[AssertionAdder]   Skipping assertion - raw value is null");
                 }
                 break;
             }
             
             if (DEBUG_ASSERTION_TRANSFORM) {
                 System.out.println("[AssertionAdder]   Adding assertion for variable value");
                 System.out.println("[AssertionAdder]     Value: " + (raw.length() > 60 ? raw.substring(0, 60) + "..." : raw));
             }

            // ---- (a) null ----
            if ("null".equals(raw)) {
                testMethod.getBody().insertEnd(createAssertUnary("assertNull", varRead.clone()));
                break; // 이 변수에 대한 관찰 한 건만 소비
            }

            // ---- (b) 특수 타입 우선 처리 (기본 타입만 assertion 생성) ----
            if (varType != null) {
                // 배열 - 길이만 비교
                if (varType.isArray() && tryAssertArrayEq(varType, varRead.clone(), /*expectedCode=*/raw, testMethod)) break;
                // 컬렉션 - 크기만 비교
                if (isCollection(varType) && tryAssertCollection(varType, varRead.clone(), /*expectedListCode=*/raw, testMethod)) break;
                // 맵 - 크기만 비교
                if (isMap(varType) && tryAssertMap(varType, varRead.clone(), /*expectedMapCode=*/raw, testMethod)) break;
                // Optional - 존재 여부 및 값 비교 (값이 기본 타입일 때)
                if (isOptional(varType) && tryAssertOptional(varType,varRead.clone(),raw,extractOptionalValueCode(got), testMethod)) break;
                // BigDecimal - compareTo 비교
                if (isBigDecimal(varType) && tryAssertBigDecimal(varType, varRead.clone(), /*expectedCode=*/raw, testMethod)) break;
                // [SKIP] Enum, Date/Time, 기타 복잡한 타입 - toString 기반 assertion 불가
                // Enum과 Date/Time은 단순 문자열로 저장되어 올바른 assertion 생성 불가능
                // 예: Enum "noQuirks" → org.jsoup.nodes.Document$QuirksMode.noQuirks 변환 불가능
            }

            // ---- (c) primitive (실수는 상대오차) ----
            if (varType != null && varType.isPrimitive()) {
                String simple = varType.getSimpleName();

                 // double/float → 상대오차 assert
                 if ("double".equals(simple) || "float".equals(simple)) {
                     // NaN, Infinity 값들은 스킵 (코드 생성 불가)
                     if (!raw.contains("NaN") && !raw.contains("Infinity")) {
                         CtExpression expected = factory.createCodeSnippetExpression(raw);
                         testMethod.getBody().insertEnd(assertClose(expected, varRead.clone()));
                         break;
                     }
                 }

                // char
                if ("char".equals(simple)) {
                    CtExpression expected;
                    if (got instanceof Character) {
                        expected = factory.createLiteral((Character) got);
                    } else {
                        expected = createCharLiteralFromString(raw);
                    }
                    if (expected != null) {
                        testMethod.getBody().insertEnd(createAssert("assertEquals", expected, varRead.clone()));
                    }
                    break;
                }

                 // long
                 if ("long".equals(simple)) {
                     // null 값은 제외
                     if (!raw.equals("null")) {
                         String expectedCode = raw.endsWith("L") ? raw : (raw + "L");
                         testMethod.getBody().insertEnd(createAssert(
                             "assertEquals",
                             factory.createCodeSnippetExpression(expectedCode),
                             varRead.clone()
                         ));
                         break;
                     }
                 }

                // 그 외 정수형/boolean
                CtExpression expectedNum = factory.createCodeSnippetExpression(formatNumericLiteral(raw));
                if (expectedNum != null) {
                    testMethod.getBody().insertEnd(createAssert("assertEquals", expectedNum, varRead.clone()));
                }
                break;
            }

            // ---- (d) String ----
            if (varType != null && "java.lang.String".equals(varType.getQualifiedName())) {
                CtExpression expected = null;
                if (raw != null && raw.startsWith(Config.STRING_IDENTIFIER)) {
                    String s = raw.replace(Config.STRING_IDENTIFIER, "");
                    if (s.length() < 1000) {
                        expected = factory.createLiteral(s);
                    }
                } else {
                    expected = factory.createCodeSnippetExpression(raw);
                }
                if (expected != null) {
                    testMethod.getBody().insertEnd(createAssert("assertEquals", expected, varRead.clone()));
                }
                break;
            }

             // ---- (e) 그 외 객체 타입: 런타임 toString() 의미성 체크 후 equals/toString 오버라이드 ----
             if (varType != null && !varType.isPrimitive() && !"java.lang.String".equals(varType.getQualifiedName())) {
                 if (DEBUG_ASSERTION_TRANSFORM) {
                     System.out.println("[AssertionAdder] 🔍 Object type in addAssertionGetter detected!");
                     System.out.println("[AssertionAdder]   Variable: " + localVariable.getSimpleName());
                     System.out.println("[AssertionAdder]   Type: " + varType.getQualifiedName());
                     System.out.println("[AssertionAdder]   Value: " + (raw.length() > 60 ? raw.substring(0, 60) + "..." : raw));
                 }
                 
                 // [중요] 런타임 toString() 결과가 의미있는 데이터인지 먼저 확인
                 if (!ObjectMethodHelper.isToStringMeaningful(got)) {
                     if (DEBUG_ASSERTION_TRANSFORM) {
                         System.out.println("[AssertionAdder] ⏭️  toString() is address format, skipping Object assertion");
                     }
                 }
                   // 컴파일 타임 + 런타임 toString 오버라이드 확인 (우선순위 1)
                    if (ObjectMethodHelper.hasToStringOverride(varType) || ObjectMethodHelper.hasToStringOverrideRuntime(got)) {
                        if (DEBUG_ASSERTION_TRANSFORM) {
                            System.out.println("[AssertionAdder] ✅ DECISION: Use toString().equals() (toString override found + meaningful toString)");
                        }
                        
                        // Object의 toString() 결과에서 STRING_IDENTIFIER 제거
                        String expectedValue = raw;
                        if (raw != null && raw.startsWith(Config.STRING_IDENTIFIER)) {
                            expectedValue = raw.replace(Config.STRING_IDENTIFIER, "");
                            if (DEBUG_ASSERTION_TRANSFORM) {
                                System.out.println("[AssertionAdder] 🔧 Removed STRING_IDENTIFIER prefix from toString result");
                                System.out.println("[AssertionAdder]   Original: " + raw);
                                System.out.println("[AssertionAdder]   Cleaned: " + expectedValue);
                            }
                        }
                        
                        // 1000자 제한 적용
                        if (expectedValue.length() < 1000) {
                            CtCodeSnippetExpression toStringCall = factory.createCodeSnippetExpression(
                                localVariable.getSimpleName() + ".toString()");
                            CtExpression expectedStr = factory.createLiteral(expectedValue);
                            if (expectedStr != null) {
                                testMethod.getBody().insertEnd(createAssert("assertEquals", expectedStr, toStringCall));
                                break;
                            }
                        } else {
                            if (DEBUG_ASSERTION_TRANSFORM) {
                                System.out.println("[AssertionAdder] ⏭️  Value too long (>= 1000 chars), skipping assertion");
                            }
                        }
                    }
                    // 컴파일 타임 + 런타임 equals 오버라이드 확인 (우선순위 2)
                    else if (ObjectMethodHelper.hasEqualsOverride(varType) || ObjectMethodHelper.hasEqualsOverrideRuntime(got)) {
                        if (DEBUG_ASSERTION_TRANSFORM) {
                            System.out.println("[AssertionAdder] ✅ DECISION: Use assertEquals (equals override found + meaningful toString)");
                        }
                        
                        // Object의 equals() 결과에서 STRING_IDENTIFIER 제거
                        String expectedValue = raw;
                        if (raw != null && raw.startsWith(Config.STRING_IDENTIFIER)) {
                            expectedValue = raw.replace(Config.STRING_IDENTIFIER, "");
                            if (DEBUG_ASSERTION_TRANSFORM) {
                                System.out.println("[AssertionAdder] 🔧 Removed STRING_IDENTIFIER prefix from equals value");
                                System.out.println("[AssertionAdder]   Original: " + raw);
                                System.out.println("[AssertionAdder]   Cleaned: " + expectedValue);
                            }
                        }
                        
                        // 1000자 제한 적용
                        if (expectedValue.length() < 1000) {
                            CtExpression expected = factory.createLiteral(expectedValue);
                            if (expected != null) {
                                testMethod.getBody().insertEnd(createAssert("assertEquals", expected, varRead.clone()));
                                break;
                            }
                        } else {
                            if (DEBUG_ASSERTION_TRANSFORM) {
                                System.out.println("[AssertionAdder] ⏭️  Value too long (>= 1000 chars), skipping assertion");
                            }
                        }
                    }
             }
             break;
        }

         // =================================
         // 2) getter 호출 결과에 대한 assertion
         // =================================
         List<CtMethod> getters = Util.getGetters(localVariable);
         
         if (DEBUG_ASSERTION_TRANSFORM) {
             System.out.println("[AssertionAdder]   Found " + getters.size() + " getters for " + localVariable.getSimpleName());
         }
         
          getters.forEach(getter -> {
              if (DEBUG_ASSERTION_TRANSFORM) {
                  System.out.println("[AssertionAdder]   Processing getter: " + getter.getSimpleName());
              }
             String key = Util.getKey(getter, localVariable);
             CtInvocation invocationToGetter = Util.invok(getter, localVariable);
             CtTypeReference<?> retType = getter.getType();

             for (Assertion observer : allAssertions) {
                 if (!key.equals(observer.getKey())) continue;

                 String raw;
                 try {
                     raw = observer.getGetters().toString();
                 } catch (Exception e) {
                     // toString() 메서드가 예외를 던지는 경우
                     if (DEBUG_ASSERTION_TRANSFORM) {
                         System.out.println("[AssertionAdder]   Skipping getter assertion - toString() failed: " + e.getMessage());
                     }
                     continue;
                 }

                // ---- (a) null ----
                if ("null".equals(raw)) {
                    testMethod.getBody().insertEnd(createAssertUnary("assertNull", invocationToGetter));
                    break;
                }

                // ---- (b) 특수 타입 우선 처리 (기본 타입만 assertion 생성) ----
                if (retType != null) {
                    if (retType.isArray() && tryAssertArrayEq(retType, invocationToGetter, raw, testMethod)) break;
                    if (isCollection(retType) && tryAssertCollection(retType, invocationToGetter, raw, testMethod)) break;
                    if (isMap(retType) && tryAssertMap(retType, invocationToGetter, raw, testMethod)) break;
                    if (isOptional(retType) && tryAssertOptional(
                            retType,
                            invocationToGetter,
                            /*presenceLiteral=*/raw,
                            /*valueCode=*/extractOptionalValueCode(observer.getGetters()),
                            testMethod)) break;
                    if (isBigDecimal(retType) && tryAssertBigDecimal(retType, invocationToGetter, raw, testMethod)) break;
                    // [SKIP] Enum, Date/Time, 기타 복잡한 타입 - toString 기반 assertion 불가
                }

                // ---- (c) primitive (실수는 상대오차) ----
                if (retType != null && retType.isPrimitive()) {
                    String simple = retType.getSimpleName();

                     if ("double".equals(simple) || "float".equals(simple)) {
                         // NaN, Infinity 값들은 스킵 (코드 생성 불가)
                         if (!raw.contains("NaN") && !raw.contains("Infinity")) {
                             CtExpression expected = factory.createCodeSnippetExpression(raw);
                             testMethod.getBody().insertEnd(assertClose(expected, invocationToGetter));
                             break;
                         }
                     }

                     if ("char".equals(simple)) {
                         CtExpression expected = createCharLiteralFromString(raw);
                         if (expected != null) {
                             testMethod.getBody().insertEnd(createAssert("assertEquals", expected, invocationToGetter));
                         }
                         break;
                     }

                      if ("long".equals(simple)) {
                          // null 값은 제외
                          if (!raw.equals("null")) {
                              // ★ 수정: 파일 크기처럼 보이는 큰 숫자는 assertion 생성 안 함
                              // 예: getFreeSpace(), getTotalSpace(), getUsableSpace() 등의 반환값
                              if (looksLikeFileSize(raw)) {
                                  if (DEBUG_ASSERTION_TRANSFORM) {
                                      System.out.println("[AssertionAdder]   Skipping file size assertion: " + raw);
                                  }
                                  break;
                              }
                              
                              String expectedCode = raw.endsWith("L") ? raw : (raw + "L");
                              testMethod.getBody().insertEnd(createAssert(
                                  "assertEquals",
                                  factory.createCodeSnippetExpression(expectedCode),
                                  invocationToGetter
                              ));
                              break;
                          }
                      }

                    CtExpression expectedNum = factory.createCodeSnippetExpression(formatNumericLiteral(raw));
                    if (expectedNum != null) {
                        testMethod.getBody().insertEnd(createAssert("assertEquals", expectedNum, invocationToGetter));
                    }
                    break;
                }

                 // ---- (d) String 반환 ----
                 if (retType != null && "java.lang.String".equals(retType.getQualifiedName())) {
                     // ★ 수정: 파일 경로 형식의 값은 assertion 생성 안 함
                     // 파일 경로는 시스템 환경에 따라 다르므로 고정된 값으로 비교할 수 없음
                     if (isFilePath(raw)) {
                         if (DEBUG_ASSERTION_TRANSFORM) {
                             System.out.println("[AssertionAdder]   Skipping file path assertion: " + raw);
                         }
                         break;
                     }
                     
                    CtExpression expected = null;
                    if (raw != null && raw.startsWith(Config.STRING_IDENTIFIER)) {
                         String s = raw.replace(Config.STRING_IDENTIFIER, "");
                         if (s.length() < 1000) {
                             expected = factory.createLiteral(s);
                         }
                     } else {
                         expected = factory.createCodeSnippetExpression(raw);
                     }
                     if (expected != null) {
                         testMethod.getBody().insertEnd(createAssert("assertEquals", expected, invocationToGetter));
                     }
                     break;
                 }

                 // ---- (e) 그 외 객체 타입: 런타임 toString() 의미성 체크 후 equals/toString 오버라이드 ----
                 if (retType != null && !retType.isPrimitive() && !"java.lang.String".equals(retType.getQualifiedName())) {
                     if (DEBUG_ASSERTION_TRANSFORM) {
                         System.out.println("[AssertionAdder] 🔍 Object type in getter result detected!");
                         System.out.println("[AssertionAdder]   Getter: " + getter.getSimpleName());
                         System.out.println("[AssertionAdder]   Return Type: " + retType.getQualifiedName());
                         System.out.println("[AssertionAdder]   Value: " + (raw.length() > 60 ? raw.substring(0, 60) + "..." : raw));
                     }
                     
                     // [중요] 런타임 toString() 결과가 의미있는 데이터인지 먼저 확인
                     if (!ObjectMethodHelper.isToStringMeaningful(observer.getGetters())) {
                         if (DEBUG_ASSERTION_TRANSFORM) {
                             System.out.println("[AssertionAdder] ⏭️  toString() is address format, skipping Object assertion");
                         }
                     }
                       // 컴파일 타임 + 런타임 toString 오버라이드 확인 (우선순위 1)
                        if (ObjectMethodHelper.hasToStringOverride(retType) || ObjectMethodHelper.hasToStringOverrideRuntime(observer.getGetters())) {
                            if (DEBUG_ASSERTION_TRANSFORM) {
                                System.out.println("[AssertionAdder] ✅ DECISION: Use toString().equals() (toString override found + meaningful toString)");
                            }
                            
                            // Object의 toString() 결과에서 STRING_IDENTIFIER 제거
                            String expectedValue = raw;
                            if (raw != null && raw.startsWith(Config.STRING_IDENTIFIER)) {
                                expectedValue = raw.replace(Config.STRING_IDENTIFIER, "");
                                if (DEBUG_ASSERTION_TRANSFORM) {
                                    System.out.println("[AssertionAdder] 🔧 Removed STRING_IDENTIFIER prefix from getter toString result");
                                    System.out.println("[AssertionAdder]   Original: " + raw);
                                    System.out.println("[AssertionAdder]   Cleaned: " + expectedValue);
                                }
                            }
                            
                            // 1000자 제한 적용
                            if (expectedValue.length() < 1000) {
                                CtCodeSnippetExpression toStringCall = factory.createCodeSnippetExpression(
                                    "(" + invocationToGetter.toString() + ").toString()");
                                CtExpression expectedStr = factory.createLiteral(expectedValue);
                                if (expectedStr != null) {
                                    testMethod.getBody().insertEnd(createAssert("assertEquals", expectedStr, toStringCall));
                                    break;
                                }
                            } else {
                                if (DEBUG_ASSERTION_TRANSFORM) {
                                    System.out.println("[AssertionAdder] ⏭️  Value too long (>= 1000 chars), skipping assertion");
                                }
                            }
                        }
                       // 컴파일 타임 + 런타임 equals 오버라이드 확인 (우선순위 2)
                        else if (ObjectMethodHelper.hasEqualsOverride(retType) || ObjectMethodHelper.hasEqualsOverrideRuntime(observer.getGetters())) {
                            if (DEBUG_ASSERTION_TRANSFORM) {
                                System.out.println("[AssertionAdder] ✅ DECISION: Use assertEquals (equals override found + meaningful toString)");
                            }
                            
                            // Object의 equals() 결과에서 STRING_IDENTIFIER 제거
                            String expectedValue = raw;
                            if (raw.startsWith(Config.STRING_IDENTIFIER)) {
                                expectedValue = raw.replace(Config.STRING_IDENTIFIER, "");
                                if (DEBUG_ASSERTION_TRANSFORM) {
                                    System.out.println("[AssertionAdder] 🔧 Removed STRING_IDENTIFIER prefix from getter equals value");
                                    System.out.println("[AssertionAdder]   Original: " + raw);
                                    System.out.println("[AssertionAdder]   Cleaned: " + expectedValue);
                                }
                            }
                            
                            // 1000자 제한 적용
                            if (expectedValue.length() < 1000) {
                                CtExpression expected = factory.createLiteral(expectedValue);
                                if (expected != null) {
                                    testMethod.getBody().insertEnd(createAssert("assertEquals", expected, invocationToGetter));
                                    break;
                                }
                            } else {
                                if (DEBUG_ASSERTION_TRANSFORM) {
                                    System.out.println("[AssertionAdder] ⏭️  Value too long (>= 1000 chars), skipping assertion");
                                }
                            }
                        }
                 }
                 break;
            }
        });
    }



    public static CtInvocation createAssert(String name, CtExpression... parameters) {
         final Factory factory = parameters[0].getFactory();
         CtTypeAccess accessToAssert =
                 factory.createTypeAccess(factory.createCtTypeReference(Assert.class));
         
         java.util.List<CtMethod<?>> assertMethods = factory.Type().get(Assert.class).getMethodsByName(name);
         CtExecutableReference assertEquals = null;
         
         if (parameters.length == 3) {
             for (CtMethod<?> method : assertMethods) {
                 if (method.getParameters().size() == 3) {
                     assertEquals = method.getReference();
                     break;
                 }
             }
         } else if (parameters.length == 2) {
             for (CtMethod<?> method : assertMethods) {
                 java.util.List<CtParameter<?>> methodParams = method.getParameters();
                 if (methodParams.size() == 2) {
                     CtTypeReference<?> param0Type = methodParams.get(0).getType();
                     boolean isNonArrayObjectOverload = param0Type.getQualifiedName() != null &&
                                                       "java.lang.Object".equals(param0Type.getQualifiedName());
                     if (isNonArrayObjectOverload) {
                         assertEquals = method.getReference();
                         break;
                     }
                 }
             }
             
             if (assertEquals == null) {
                 for (CtMethod<?> method : assertMethods) {
                     java.util.List<CtParameter<?>> methodParams = method.getParameters();
                     if (methodParams.size() == 2) {
                         CtTypeReference<?> param0Type = methodParams.get(0).getType();
                         if (!param0Type.isArray()) {
                             assertEquals = method.getReference();
                             break;
                         }
                     }
                 }
             }
             
             if (assertEquals == null && !assertMethods.isEmpty()) {
                 assertEquals = assertMethods.get(0).getReference();
             }
         } else {
             if (!assertMethods.isEmpty()) {
                 assertEquals = assertMethods.get(0).getReference();
             }
         }
         
         if (assertEquals == null) {
             assertEquals = assertMethods.get(0).getReference();
         }
         
         if (parameters.length == 3) {
             return factory.createInvocation(
                     accessToAssert,
                     assertEquals,
                     parameters[0],
                     parameters[1],
                     parameters[2]);
         } else {
             return factory.createInvocation(
                     accessToAssert,
                     assertEquals,
                     parameters[0],
                     parameters[1]);
         }
     }

    public static boolean isNumeric(String str) {
        NumberFormat formatter = NumberFormat.getInstance();
        ParsePosition pos = new ParsePosition(0);
        formatter.parse(str, pos);
        return str.length() == pos.getIndex();
    }

     private String formatNumericLiteral(String value) {
         if (!isNumeric(value)) {
             return value;
         }

         try {
             // Check if it's a decimal number (contains . or scientific notation)
             if (value.contains(".") || value.toLowerCase().contains("e")) {
                 double doubleVal = Double.parseDouble(value);
                 // Use L suffix for very large whole numbers that exceed int range
                 if (doubleVal == Math.floor(doubleVal) && doubleVal > Integer.MAX_VALUE) {
                     return String.valueOf((long)doubleVal) + "L";
                 }
                 return value + "D";
             }

             // Integer number - check if it exceeds int range
             long longVal = Long.parseLong(value);
             if (longVal > Integer.MAX_VALUE || longVal < Integer.MIN_VALUE) {
                 return value + "L";
             }

             return value;
         } catch (NumberFormatException e) {
             return value;
         }
     }
     
     /**
      * char 리터럴 생성 - 특수문자 이스케이프 처리
      * Logger.observe()로 관찰된 char 값을 올바른 char 리터럴 코드로 변환
      * 
      * 예: 실제 개행 문자 → '\n', 역슬래시 → '\\', 탭 → '\t'
      */
     private CtExpression createCharLiteral(String raw) {
         if (raw == null || raw.length() == 0) {
             return factory.createLiteral('\0');
         }
         
         // 숫자 문자열인 경우 (char 코드값으로 전달됨)
         try {
             int codePoint = Integer.parseInt(raw);
             if (codePoint >= 0 && codePoint <= 0xFFFF) {
                 return factory.createLiteral((char) codePoint);
             }
         } catch (NumberFormatException e) {
             // 숫자가 아니므로 실제 문자 처리
         }
         
         // 첫 번째 문자 추출 (관찰된 실제 char 값)
         char c = raw.charAt(0);
         
         // Spoon의 createLiteral은 자동으로 이스케이프를 처리해줍니다!
         // '\n' → '\n', '\\' → '\\', '\t' → '\t' 등
         return factory.createLiteral(c);
     }
     
      /**
       * Assertion.getGetters()가 반환한 문자열에서 char 리터럴 생성
       * Assertion은 Character를 "'x'" 형태로 감싸므로 이를 처리
       */
      private CtExpression createCharLiteralFromString(String str) {
          if (str == null || str.length() == 0) {
              return factory.createLiteral('\0');
          }
          
          // "'x'" 형태이면 작은따옴표 제거
          if (str.length() >= 2 && str.startsWith("'") && str.endsWith("'")) {
              String inner = str.substring(1, str.length() - 1);
              if (inner.length() == 0) {
                  // '' → null 문자나 특수문자일 가능성
                  return factory.createLiteral('\0');
              } else if (inner.length() == 1) {
                  return factory.createLiteral(inner.charAt(0));
              }
          }
          
          // 일반 문자열이면 첫 문자 사용
          return createCharLiteral(str);
      }

    // Assertion Augmentation Utils
    private boolean isCollection(CtTypeReference<?> t) {
        if (t == null) return false;
        String qn = t.getQualifiedName();
        return qn != null && (qn.equals("java.util.Collection") || qn.startsWith("java.util.List") || qn.startsWith("java.util.Set") || qn.startsWith("java.util.Queue"));
    }
    private boolean isMap(CtTypeReference<?> t) {
        if (t == null) return false;
        String qn = t.getQualifiedName();
        return qn != null && qn.startsWith("java.util.Map");
    }
    private boolean isOptional(CtTypeReference<?> t) {
        if (t == null) return false;
        String qn = t.getQualifiedName();
        return "java.util.Optional".equals(qn) || "java.util.OptionalInt".equals(qn) ||
            "java.util.OptionalLong".equals(qn) || "java.util.OptionalDouble".equals(qn);
    }
    private boolean isBigDecimal(CtTypeReference<?> t) {
        return t != null && "java.math.BigDecimal".equals(t.getQualifiedName());
    }
    private boolean isEnum(CtTypeReference<?> t) {
        return t != null && t.isSubtypeOf(factory.Type().createReference(Enum.class));
    }
    private boolean isDateLike(CtTypeReference<?> t) {
        if (t == null) return false;
        String qn = t.getQualifiedName();
        return "java.util.Date".equals(qn) || "java.time.Instant".equals(qn) ||
            "java.time.LocalDate".equals(qn) || "java.time.LocalDateTime".equals(qn) ||
            "java.time.OffsetDateTime".equals(qn) || "java.time.ZonedDateTime".equals(qn);
    }

     private CtInvocation assertClose(CtExpression expected, CtExpression actual) {
         // delta = max(1e-9, 1e-6 * max(1.0, abs(expected)))
         CtExpression delta = factory.createCodeSnippetExpression(
             "java.lang.Math.max(1e-9, 1e-6 * java.lang.Math.max(1.0, java.lang.Math.abs(" + expected + ")))"
         );
         return createAssert("assertEquals", expected, actual, delta);
     }
     
     /**
      * ★ 새로운 메서드: 값이 파일 경로 형식인지 확인
      * 파일 경로는 시스템 환경에 따라 다르므로 assertion 대상에서 제외
      * 예: /home/sangjune/data1/regression/gen_tests/...
      *      /tmp/test3.xml8454236694702309660.null
      *      C:\Users\...
      */
     private boolean isFilePath(String value) {
         if (value == null || value.isEmpty()) {
             return false;
         }
         
         // 파일 경로 패턴 감지
         // 1. Unix/Linux 절대 경로: / 로 시작
         if (value.startsWith("/")) {
             return true;
         }
         
         // 2. Windows 절대 경로: C:\ 또는 D:\ 등
         if (value.matches("^[a-zA-Z]:\\\\.*")) {
             return true;
         }
         
         // 3. 상대 경로 but 디렉토리 구분자 포함 (예: ./path, ../path, path/to/file)
         // 파일 경로처럼 보이는 경우는 제외하기 위해 신중하게 판단
         if (value.contains("/") || value.contains("\\")) {
             // 임시 파일명 패턴 (예: test3.xml8454236694702309660.null)
             if (value.contains("xml") || value.contains("file") || value.contains("tmp")) {
                 return true;
             }
             // 여러 디렉토리 레벨이 있는 경우 (예: /path/to/file)
             int pathSeparators = (int) value.chars().filter(c -> c == '/' || c == '\\').count();
             if (pathSeparators >= 2) {
                 return true;
             }
         }
         
         return false;
     }
     
     /**
      * ★ 새로운 메서드: Long 값이 파일 크기처럼 보이는지 확인
      * 파일 크기 관련 메서드의 반환값은 시스템 환경에 따라 다름
      * 예: getFreeSpace(), getTotalSpace(), getUsableSpace() 등
      * 특징: 매우 큰 수 (보통 1GB 이상의 바이트 단위)
      */
     private boolean looksLikeFileSize(String value) {
         if (value == null || value.isEmpty()) {
             return false;
         }
         
         try {
             long num = Long.parseLong(value);
             
             // 파일 크기는 보통 매우 큼 (1GB 이상 = 1,000,000,000 바이트)
             // 일반적인 테스트 데이터는 이 범위를 벗어남
             // 1MB 이상을 기준으로 (1,000,000)
             if (num >= 1_000_000) {
                 return true;
             }
         } catch (NumberFormatException e) {
             // long 형식이 아니면 false
         }
         
         return false;
     }

     // === 2.3 배열/컬렉션/맵/Optional/BigDecimal/Enum/Date assert 헬퍼 ===
     private boolean tryAssertArrayEq(CtTypeReference<?> type, CtExpression actual, String expectedCode, CtMethod<?> owner) {
         if (type == null || !type.isArray()) return false;
         
         try {
             // 2D 배열 여부 확인 (toString() 형식: [[Ljava.lang.String;@hashcode)
             boolean is2DArray = expectedCode != null && 
                                 (expectedCode.contains("[L") || expectedCode.startsWith("[[")) && 
                                 expectedCode.contains("@");
             
              if (is2DArray) {
                  if (DEBUG_ASSERTION_TRANSFORM) {
                      System.out.println("[AssertionAdder] Detected 2D array: " + 
                          (expectedCode.length() > 100 ? expectedCode.substring(0, 100) + "..." : expectedCode));
                  }
                  
                  // 2D 배열은 null 아닌지만 확인 (값 비교는 불가능)
                  owner.getBody().insertEnd(createAssertUnary("assertNotNull", actual));
                  
                  if (DEBUG_ASSERTION_TRANSFORM) {
                      System.out.println("[AssertionAdder] Skipping value assertion for 2D array (toString format not suitable)");
                  }
                  return true;
              }
             
               // 1D 배열: 길이와 첫 번째 요소 비교
               int expectedLength = parseArrayLength(expectedCode);
               
               if (expectedLength >= 0) {
                   // 배열 길이 비교
                   owner.getBody().insertEnd(createAssert("assertEquals",
                       factory.createCodeSnippetExpression(String.valueOf(expectedLength)),
                       factory.createCodeSnippetExpression(actual + ".length")));
                   
                   if (DEBUG_ASSERTION_TRANSFORM) {
                       System.out.println("[AssertionAdder] Array assertion: length=" + expectedLength);
                   }
                   
                   // [NEW] 길이가 1 이상이면 첫 번째와 마지막 요소값 비교
                   if (expectedLength > 0) {
                       String firstElementValue = extractFirstElementFromArray(expectedCode);
                       if (firstElementValue != null && !firstElementValue.isEmpty()) {
                           if (DEBUG_ASSERTION_TRANSFORM) {
                               System.out.println("[AssertionAdder]   First element value: " + 
                                   (firstElementValue.length() > 60 ? firstElementValue.substring(0, 60) + "..." : firstElementValue));
                           }
                           
                           CtExpression firstElementActual = factory.createCodeSnippetExpression(actual + "[0]");
                           CtExpression expectedFirstElement = factory.createLiteral(firstElementValue);
                           
                           if (expectedFirstElement != null) {
                               owner.getBody().insertEnd(createAssert("assertEquals", expectedFirstElement, firstElementActual));
                               if (DEBUG_ASSERTION_TRANSFORM) {
                                   System.out.println("[AssertionAdder]   First element assertion added");
                               }
                           }
                       }
                       
                       // 길이가 2 이상이면 마지막 요소값도 비교
                       if (expectedLength > 1) {
                           String lastElementValue = extractLastElementFromArray(expectedCode);
                           if (lastElementValue != null && !lastElementValue.isEmpty()) {
                               if (DEBUG_ASSERTION_TRANSFORM) {
                                   System.out.println("[AssertionAdder]   Last element value: " + 
                                       (lastElementValue.length() > 60 ? lastElementValue.substring(0, 60) + "..." : lastElementValue));
                               }
                               
                               CtExpression lastElementActual = factory.createCodeSnippetExpression(actual + "[" + actual + ".length-1]");
                               CtExpression expectedLastElement = factory.createLiteral(lastElementValue);
                               
                               if (expectedLastElement != null) {
                                   owner.getBody().insertEnd(createAssert("assertEquals", expectedLastElement, lastElementActual));
                                   if (DEBUG_ASSERTION_TRANSFORM) {
                                       System.out.println("[AssertionAdder]   Last element assertion added");
                                   }
                               }
                           }
                       }
                   }
               } else {
                   // 파싱 실패 시 null 체크만
                   if (DEBUG_ASSERTION_TRANSFORM) {
                       System.out.println("[AssertionAdder] Array assertion failed to parse length, using assertNotNull instead");
                   }
                   owner.getBody().insertEnd(createAssertUnary("assertNotNull", actual));
               }
          } catch (Exception e) {
              // 예외 발생 시 null 체크만
              if (DEBUG_ASSERTION_TRANSFORM) {
                  System.out.println("[AssertionAdder] Array assertion exception: " + e.getMessage() + ", using assertNotNull");
              }
              owner.getBody().insertEnd(createAssertUnary("assertNotNull", actual));
          }
         return true;
     }
     
      /**
       * 배열 길이 추출
       * {a, b, c} 또는 [a, b, c] 또는 {} 또는 [] → 길이
       */
      private int parseArrayLength(String arrayCode) {
          if (arrayCode == null || arrayCode.trim().isEmpty()) {
              return -1;
          }
          
          try {
              String trimmed = arrayCode.trim();
              
              // {} 또는 [] 형식 (빈 배열)
              if (trimmed.equals("{}") || trimmed.equals("[]")) {
                  return 0;
              }
              
              // {a, b, c} 또는 [a, b, c] 형식
              if ((trimmed.startsWith("{") || trimmed.startsWith("[")) && 
                  (trimmed.endsWith("}") || trimmed.endsWith("]"))) {
                  
                  String inner = trimmed.substring(1, trimmed.length() - 1);
                  if (inner.trim().isEmpty()) {
                      return 0;
                  }
                  
                  int count = 1;
                  int braceDepth = 0;
                  boolean inString = false;
                  
                  for (int i = 0; i < inner.length(); i++) {
                      char c = inner.charAt(i);
                      if (c == '"' && (i == 0 || inner.charAt(i - 1) != '\\')) {
                          inString = !inString;
                      } else if (!inString) {
                          if (c == '{' || c == '[') {
                              braceDepth++;
                          } else if (c == '}' || c == ']') {
                              braceDepth--;
                          } else if (c == ',' && braceDepth == 0) {
                              count++;
                          }
                      }
                  }
                  
                  return count;
              }
              
              return -1;
          } catch (Exception e) {
              return -1;
          }
      }
      
      /**
       * 배열의 첫 번째 요소 추출
       * {a, b, c} 또는 [a, b, c] 또는 {} 또는 [] → 첫 요소
       */
      private String parseFirstArrayElement(String arrayCode) {
          if (arrayCode == null || arrayCode.trim().isEmpty()) {
              return null;
          }
          
          try {
              String trimmed = arrayCode.trim();
              
              // {} 또는 [] 형식 (빈 배열)
              if (trimmed.equals("{}") || trimmed.equals("[]")) {
                  return null;
              }
              
              // {a, b, c} 또는 [a, b, c] 형식
              if ((trimmed.startsWith("{") || trimmed.startsWith("[")) && 
                  (trimmed.endsWith("}") || trimmed.endsWith("]"))) {
                  
                  String inner = trimmed.substring(1, trimmed.length() - 1).trim();
                  if (inner.isEmpty()) {
                      return null;
                  }
                  
                  int endIdx = 0;
                  int braceDepth = 0;
                  boolean inString = false;
                  
                  for (int i = 0; i < inner.length(); i++) {
                      char c = inner.charAt(i);
                      if (c == '"' && (i == 0 || inner.charAt(i - 1) != '\\')) {
                          inString = !inString;
                      } else if (!inString) {
                          if (c == '{' || c == '[') {
                              braceDepth++;
                          } else if (c == '}' || c == ']') {
                              braceDepth--;
                          } else if (c == ',' && braceDepth == 0) {
                              endIdx = i;
                              break;
                          }
                      }
                      endIdx = i + 1;
                  }
                  
                  String firstElement = inner.substring(0, endIdx).trim();
                  
                  // 이미 따옴표로 감싸져 있으면 그대로 사용
                  if (firstElement.startsWith("\"") || firstElement.startsWith("'")) {
                      return firstElement;
                  }
                  
                  // 문자열이면 리터럴로 감싸기
                  if (!firstElement.startsWith("\"")) {
                      firstElement = "\"" + escapeJavaString(firstElement) + "\"";
                  }
                  
                  return firstElement;
              }
              
              return null;
          } catch (Exception e) {
              return null;
          }
      }

      private boolean tryAssertCollection(CtTypeReference<?> type, CtExpression actual, String expectedListCode, CtMethod<?> owner) {
          if (!isCollection(type)) return false;
          
          try {
              // expectedListCode를 파싱해서 실제 크기를 얻기
              int expectedSize = parseListSize(expectedListCode);
              
              if (expectedSize >= 0) {
                  // 크기 비교
                  owner.getBody().insertEnd(createAssert("assertEquals",
                      factory.createCodeSnippetExpression(String.valueOf(expectedSize)),
                      factory.createCodeSnippetExpression(actual + ".size()")));
                  
                  if (DEBUG_ASSERTION_TRANSFORM) {
                      System.out.println("[AssertionAdder] Collection assertion: size=" + expectedSize);
                  }
                  
                  // [NEW] 크기가 1 이상이면 첫 번째와 마지막 요소값 비교
                  if (expectedSize > 0) {
                      String firstElementValue = extractFirstElementFromList(expectedListCode);
                      if (firstElementValue != null && !firstElementValue.isEmpty()) {
                          if (DEBUG_ASSERTION_TRANSFORM) {
                              System.out.println("[AssertionAdder]   First element value: " + 
                                  (firstElementValue.length() > 60 ? firstElementValue.substring(0, 60) + "..." : firstElementValue));
                          }
                          
                          CtExpression firstElementActual = factory.createCodeSnippetExpression(actual + ".get(0)");
                          CtExpression expectedFirstElement = factory.createLiteral(firstElementValue);
                          
                          if (expectedFirstElement != null) {
                              owner.getBody().insertEnd(createAssert("assertEquals", expectedFirstElement, firstElementActual));
                              if (DEBUG_ASSERTION_TRANSFORM) {
                                  System.out.println("[AssertionAdder]   First element assertion added");
                              }
                          }
                      }
                      
                      // 크기가 2 이상이면 마지막 요소값도 비교
                      if (expectedSize > 1) {
                          String lastElementValue = extractLastElementFromList(expectedListCode);
                          if (lastElementValue != null && !lastElementValue.isEmpty()) {
                              if (DEBUG_ASSERTION_TRANSFORM) {
                                  System.out.println("[AssertionAdder]   Last element value: " + 
                                      (lastElementValue.length() > 60 ? lastElementValue.substring(0, 60) + "..." : lastElementValue));
                              }
                              
                              CtExpression lastElementActual = factory.createCodeSnippetExpression(actual + ".get(" + actual + ".size()-1)");
                              CtExpression expectedLastElement = factory.createLiteral(lastElementValue);
                              
                              if (expectedLastElement != null) {
                                  owner.getBody().insertEnd(createAssert("assertEquals", expectedLastElement, lastElementActual));
                                  if (DEBUG_ASSERTION_TRANSFORM) {
                                      System.out.println("[AssertionAdder]   Last element assertion added");
                                  }
                              }
                          }
                      }
                  }
                  } else {
                  // 파싱 실패 시에만 null 체크
                  if (DEBUG_ASSERTION_TRANSFORM) {
                      System.out.println("[AssertionAdder] Collection assertion failed to parse size, using assertNotNull instead");
                  }
                  owner.getBody().insertEnd(createAssertUnary("assertNotNull", actual));
              }
          } catch (Exception e) {
              // 예외 발생 시 null 체크만
              if (DEBUG_ASSERTION_TRANSFORM) {
                  System.out.println("[AssertionAdder] Collection assertion exception: " + e.getMessage() + ", using assertNotNull");
              }
              owner.getBody().insertEnd(createAssertUnary("assertNotNull", actual));
          }
          return true;
      }
      
      /**
       * List 코드에서 첫 번째 요소값 추출
       * [[a, b, c]] → a
       * [[obj1, obj2]] → obj1
       * [[]] → null
       */
      private String extractFirstElementFromList(String listCode) {
          if (listCode == null || listCode.trim().isEmpty()) {
              return null;
          }
          
          try {
              String trimmed = listCode.trim();
              
              // [[]] 형식: 빈 리스트
              if (trimmed.equals("[]") || trimmed.equals("[[]]")) {
                  return null;
              }
              
              // [[...]] 형식
              if (trimmed.startsWith("[[") && trimmed.endsWith("]]")) {
                  String inner = trimmed.substring(2, trimmed.length() - 2).trim();
                  if (inner.isEmpty()) {
                      return null;
                  }
                  
                  // 첫 번째 요소 추출 (쉼표 기준)
                  int commaIndex = findFirstCommaOutsideBrackets(inner);
                  if (commaIndex > 0) {
                      return inner.substring(0, commaIndex).trim();
                  } else {
                      // 요소가 하나만 있는 경우
                      return inner.trim();
                  }
              }
          } catch (Exception e) {
              if (DEBUG_ASSERTION_TRANSFORM) {
                  System.out.println("[AssertionAdder] Error extracting first element: " + e.getMessage());
              }
          }
          
          return null;
      }
      
      /**
       * 문자열에서 괄호 밖의 첫 번째 쉼마 위치 찾기
       * "[a, b], c, d" → c 앞의 쉼마 위치
       */
      private int findFirstCommaOutsideBrackets(String str) {
          int bracketDepth = 0;
          for (int i = 0; i < str.length(); i++) {
              char c = str.charAt(i);
              if (c == '[' || c == '{' || c == '(') {
                  bracketDepth++;
              } else if (c == ']' || c == '}' || c == ')') {
                  bracketDepth--;
              } else if (c == ',' && bracketDepth == 0) {
                  return i;
              }
          }
          return -1;
      }
     
     /**
      * [[#@]] 또는 [] 형식의 리스트 코드에서 크기 추출
      * [[a, b, c]] → 3
      * [[a]] → 1
      * [[]] 또는 [] → 0
      */
     private int parseListSize(String listCode) {
         if (listCode == null || listCode.trim().isEmpty()) {
             return -1;
         }
         
         try {
             String trimmed = listCode.trim();
             
             // [] 형식 (빈 리스트)
             if (trimmed.equals("[]")) {
                 return 0;
             }
             
             // [[]] 또는 [[...]] 형식
             if (trimmed.startsWith("[[") && trimmed.endsWith("]]")) {
                 String inner = trimmed.substring(2, trimmed.length() - 2);
                 if (inner.trim().isEmpty()) {
                     return 0;  // [[]] → 0
                 }
                 
                 // 쉼표로 분리된 요소 개수 세기
                 int count = 1;
                 int braceDepth = 0;
                 boolean inString = false;
                 
                 for (int i = 0; i < inner.length(); i++) {
                     char c = inner.charAt(i);
                     if (c == '"' && (i == 0 || inner.charAt(i - 1) != '\\')) {
                         inString = !inString;
                     } else if (!inString) {
                         if (c == '{' || c == '[') {
                             braceDepth++;
                         } else if (c == '}' || c == ']') {
                             braceDepth--;
                         } else if (c == ',' && braceDepth == 0) {
                             count++;
                         }
                     }
                 }
                 
                 return count;
             }
             
             // [a, b, c] 형식 (가능하면)
             if (trimmed.startsWith("[") && trimmed.endsWith("]")) {
                 String inner = trimmed.substring(1, trimmed.length() - 1);
                 if (inner.trim().isEmpty()) {
                     return 0;
                 }
                 
                 int count = 1;
                 int braceDepth = 0;
                 boolean inString = false;
                 
                 for (int i = 0; i < inner.length(); i++) {
                     char c = inner.charAt(i);
                     if (c == '"' && (i == 0 || inner.charAt(i - 1) != '\\')) {
                         inString = !inString;
                     } else if (!inString) {
                         if (c == '{' || c == '[') {
                             braceDepth++;
                         } else if (c == '}' || c == ']') {
                             braceDepth--;
                         } else if (c == ',' && braceDepth == 0) {
                             count++;
                         }
                     }
                 }
                 
                 return count;
             }
             
             return -1;
         } catch (Exception e) {
             return -1;
         }
     }
     
     /**
      * [[#@]] 또는 [] 형식에서 첫 번째 요소 추출
      * [[abc]] → "abc"
      * [[a, b, c]] → "a"
      * [] → null (빈 리스트)
      */
     private String parseFirstElement(String listCode) {
         if (listCode == null || listCode.trim().isEmpty()) {
             return null;
         }
         
         try {
             String trimmed = listCode.trim();
             
             // [] 형식 (빈 리스트)
             if (trimmed.equals("[]")) {
                 return null;
             }
             
             // [[]] 형식 (빈 리스트 표현)
             if (trimmed.equals("[[]]")) {
                 return null;
             }
             
             // [[...]] 형식
             if (trimmed.startsWith("[[") && trimmed.endsWith("]]")) {
                 String inner = trimmed.substring(2, trimmed.length() - 2).trim();
                 if (inner.isEmpty()) {
                     return null;
                 }
                 
                 // 첫 번째 요소까지 추출
                 int endIdx = 0;
                 int braceDepth = 0;
                 boolean inString = false;
                 
                 for (int i = 0; i < inner.length(); i++) {
                     char c = inner.charAt(i);
                     if (c == '"' && (i == 0 || inner.charAt(i - 1) != '\\')) {
                         inString = !inString;
                     } else if (!inString) {
                         if (c == '{' || c == '[') {
                             braceDepth++;
                         } else if (c == '}' || c == ']') {
                             braceDepth--;
                         } else if (c == ',' && braceDepth == 0) {
                             endIdx = i;
                             break;
                         }
                     }
                     endIdx = i + 1;
                 }
                 
                 String firstElement = inner.substring(0, endIdx).trim();
                 
                 // 이미 따옴표로 감싸져 있으면 그대로 사용
                 if (firstElement.startsWith("\"") || firstElement.startsWith("'")) {
                     return firstElement;
                 }
                 
                 // 문자열이면 리터럴로 감싸기
                 if (!firstElement.startsWith("\"")) {
                     firstElement = "\"" + escapeJavaString(firstElement) + "\"";
                 }
                 
                 return firstElement;
             }
             
             // [a, b, c] 형식
             if (trimmed.startsWith("[") && trimmed.endsWith("]")) {
                 String inner = trimmed.substring(1, trimmed.length() - 1).trim();
                 if (inner.isEmpty()) {
                     return null;
                 }
                 
                 int endIdx = 0;
                 int braceDepth = 0;
                 boolean inString = false;
                 
                 for (int i = 0; i < inner.length(); i++) {
                     char c = inner.charAt(i);
                     if (c == '"' && (i == 0 || inner.charAt(i - 1) != '\\')) {
                         inString = !inString;
                     } else if (!inString) {
                         if (c == '{' || c == '[') {
                             braceDepth++;
                         } else if (c == '}' || c == ']') {
                             braceDepth--;
                         } else if (c == ',' && braceDepth == 0) {
                             endIdx = i;
                             break;
                         }
                     }
                     endIdx = i + 1;
                 }
                 
                 String firstElement = inner.substring(0, endIdx).trim();
                 
                 if (firstElement.startsWith("\"") || firstElement.startsWith("'")) {
                     return firstElement;
                 }
                 
                 if (!firstElement.startsWith("\"")) {
                     firstElement = "\"" + escapeJavaString(firstElement) + "\"";
                 }
                 
                 return firstElement;
             }
             
             return null;
         } catch (Exception e) {
             return null;
         }
     }

      private boolean tryAssertMap(CtTypeReference<?> type, CtExpression actual, String expectedMapCode, CtMethod<?> owner) {
          if (!isMap(type)) return false;
          
          try {
              // expectedMapCode를 파싱해서 실제 크기를 얻기
              int expectedSize = parseMapSize(expectedMapCode);
              
              if (expectedSize >= 0) {
                  // 크기만 비교 (안정성 우선)
                  owner.getBody().insertEnd(createAssert("assertEquals",
                      factory.createCodeSnippetExpression(String.valueOf(expectedSize)),
                      factory.createCodeSnippetExpression(actual + ".size()")));
                  
                  if (DEBUG_ASSERTION_TRANSFORM) {
                      System.out.println("[AssertionAdder] Map assertion: size only (expected=" + expectedSize + ")");
                  }
              } else {
                  // 파싱 실패 시에만 null 체크
                  if (DEBUG_ASSERTION_TRANSFORM) {
                      System.out.println("[AssertionAdder] Map assertion failed to parse size, using assertNotNull instead");
                  }
                  owner.getBody().insertEnd(createAssertUnary("assertNotNull", actual));
              }
          } catch (Exception e) {
              // 예외 발생 시 null 체크만
              if (DEBUG_ASSERTION_TRANSFORM) {
                  System.out.println("[AssertionAdder] Map assertion exception: " + e.getMessage() + ", using assertNotNull");
              }
              owner.getBody().insertEnd(createAssertUnary("assertNotNull", actual));
          }
          return true;
      }
     
     /**
      * Map 크기 추출 (간단한 경우만 지원)
      * {} 또는 {key=value, ...} 형식 모두 지원
      */
     private int parseMapSize(String mapCode) {
         if (mapCode == null || mapCode.trim().isEmpty()) {
             return -1;
         }
         
         try {
             String trimmed = mapCode.trim();
             
             // {} 형식 (빈 Map)
             if (trimmed.equals("{}")) {
                 return 0;
             }
             
             // {key=value, ...} 형식에서 쉼표 개수 + 1로 크기 추정
             if (trimmed.startsWith("{") && trimmed.endsWith("}")) {
                 String inner = trimmed.substring(1, trimmed.length() - 1);
                 if (inner.trim().isEmpty()) {
                     return 0;  // {} → 0
                 }
                 
                 int count = 1;
                 int braceDepth = 0;
                 boolean inString = false;
                 
                 for (int i = 0; i < inner.length(); i++) {
                     char c = inner.charAt(i);
                     if (c == '"' && (i == 0 || inner.charAt(i - 1) != '\\')) {
                         inString = !inString;
                     } else if (!inString) {
                         if (c == '{' || c == '[') {
                             braceDepth++;
                         } else if (c == '}' || c == ']') {
                             braceDepth--;
                         } else if (c == ',' && braceDepth == 0) {
                             count++;
                         }
                     }
                 }
                 
                 return count;
             }
             
             return -1;
         } catch (Exception e) {
             return -1;
         }
     }
     
     /**
      * Map의 첫 번째 키 추출
      * {key=value, ...} 또는 {} 형식 지원
      */
     private String parseFirstMapKey(String mapCode) {
         if (mapCode == null || mapCode.trim().isEmpty()) {
             return null;
         }
         
         try {
             String trimmed = mapCode.trim();
             
             // {} 형식 (빈 Map)
             if (trimmed.equals("{}")) {
                 return null;
             }
             
             // {key=value, ...} 형식에서 key 부분만 추출
             if (trimmed.startsWith("{") && trimmed.endsWith("}")) {
                 String inner = trimmed.substring(1, trimmed.length() - 1).trim();
                 if (inner.isEmpty()) {
                     return null;
                 }
                 
                 // = 위치 찾기
                 int eqIdx = -1;
                 boolean inString = false;
                 int braceDepth = 0;
                 
                 for (int i = 0; i < inner.length(); i++) {
                     char c = inner.charAt(i);
                     if (c == '"' && (i == 0 || inner.charAt(i - 1) != '\\')) {
                         inString = !inString;
                     } else if (!inString) {
                         if (c == '{' || c == '[') {
                             braceDepth++;
                         } else if (c == '}' || c == ']') {
                             braceDepth--;
                         } else if (c == '=' && braceDepth == 0) {
                             eqIdx = i;
                             break;
                         }
                     }
                 }
                 
                 if (eqIdx > 0) {
                     String key = inner.substring(0, eqIdx).trim();
                     
                     // 이미 따옴표로 감싸져 있으면 그대로 사용
                     if (key.startsWith("\"") || key.startsWith("'")) {
                         return key;
                     }
                     
                     // 문자열이면 리터럴로 감싸기
                     if (!key.startsWith("\"")) {
                         key = "\"" + escapeJavaString(key) + "\"";
                     }
                     
                     return key;
                 }
             }
         } catch (Exception e) {
             // 무시
         }
         
         return null;
     }

    private boolean tryAssertOptional(CtTypeReference<?> type, CtExpression actual, String presenceLiteral, String valueCode, CtMethod<?> owner) {
        if (!isOptional(type)) return false;
        // presence
        if ("true".equals(presenceLiteral)) {
            owner.getBody().insertEnd(createAssertUnary("assertTrue",
                factory.createCodeSnippetExpression(actual + ".isPresent()")));
            if (valueCode != null) {
                owner.getBody().insertEnd(createAssert("assertEquals",
                    factory.createCodeSnippetExpression(valueCode),
                    factory.createCodeSnippetExpression(actual + ".get()")));
            }
        } else {
            owner.getBody().insertEnd(createAssertUnary("assertFalse",
                factory.createCodeSnippetExpression(actual + ".isPresent()")));
        }
        return true;
    }

    private boolean tryAssertBigDecimal(CtTypeReference<?> type, CtExpression actual, String expectedCode, CtMethod<?> owner) {
        if (!isBigDecimal(type)) return false;
        
        // expectedCode가 단순 문자열이면 new BigDecimal()로 감싸기
        // 예: "12.34" -> new java.math.BigDecimal("12.34")
        String bigDecimalExpr;
        if (expectedCode.startsWith("new java.math.BigDecimal")) {
            // 이미 BigDecimal 객체 생성식이면 그대로 사용
            bigDecimalExpr = expectedCode;
        } else {
            // 숫자 문자열이면 BigDecimal로 감싸기
            bigDecimalExpr = "new java.math.BigDecimal(\"" + expectedCode + "\")";
        }
        
        if (DEBUG_ASSERTION_TRANSFORM) {
            System.out.println("[AssertionAdder] BigDecimal assertion: " + expectedCode + " -> " + bigDecimalExpr);
        }
        
        // compareTo == 0
        owner.getBody().insertEnd(createAssert("assertEquals",
            factory.createCodeSnippetExpression("0"),
            factory.createCodeSnippetExpression("(" + bigDecimalExpr + ").compareTo(" + actual + ")")));
        return true;
    }

    private boolean tryAssertEnum(CtTypeReference<?> type, CtExpression actual, String expectedEnumCode, CtMethod<?> owner) {
        if (!isEnum(type)) return false;
        
        // enum 값을 fully qualified name으로 변환
        // 예: "noQuirks" -> "org.jsoup.nodes.Document.QuirksMode.noQuirks"
        String enumTypeName = type.getQualifiedName();
        String fullEnumValue = enumTypeName + "." + expectedEnumCode;
        
        if (DEBUG_ASSERTION_TRANSFORM) {
            System.out.println("[AssertionAdder] Enum assertion: " + expectedEnumCode + " -> " + fullEnumValue);
        }
        
        owner.getBody().insertEnd(createAssert("assertEquals",
            factory.createCodeSnippetExpression(fullEnumValue),
            actual));
        return true;
    }

    private boolean tryAssertDateLike(CtTypeReference<?> type, CtExpression actual, String expectedEpochMs, CtMethod<?> owner) {
        if (!isDateLike(type)) return false;
        // epochMillis 기준 비교 (관찰단에서 epochMillis 기록)
        owner.getBody().insertEnd(createAssert("assertEquals",
            factory.createCodeSnippetExpression(expectedEpochMs),
            factory.createCodeSnippetExpression("(" + actual + " instanceof java.util.Date) ? ((java.util.Date)" + actual + ").getTime() : " +
                "(" + actual + " instanceof java.time.Instant ? java.time.Date.from((java.time.Instant)" + actual + ").getTime() : " +
                "java.time.ZonedDateTime.of((" + actual + " instanceof java.time.LocalDateTime ? (java.time.LocalDateTime)" + actual + " : " +
                "(" + actual + " instanceof java.time.LocalDate ? ((java.time.LocalDate)" + actual + ").atStartOfDay() : " +
                "(" + actual + " instanceof java.time.OffsetDateTime ? ((java.time.OffsetDateTime)" + actual + ").toLocalDateTime() : null))), " +
                "java.time.ZoneId.systemDefault()).toInstant().toEpochMilli())")));
        return true;
    }

    // Optional 계열 관찰값에서 expected "코드 스니펫"을 만들어 반환.
    // - Optional<T> : present면 T를 코드 리터럴로 변환, 아니면 null
    // - OptionalInt/Long/Double : present면 해당 원시 리터럴로 변환
    // - 지원 타입: String, Character, Integer/Short/Byte, Long, Float, Double, Boolean,
    //             BigDecimal, Enum
    // - 그 외(Date/Time/복잡 객체)는 null 반환(= presence만 assert)
    private String extractOptionalValueCode(Object got) {
        if (got == null) return null;

        try {
            // java.util.Optional
            if (got instanceof java.util.Optional) {
                java.util.Optional<?> opt = (java.util.Optional<?>) got;
                if (!opt.isPresent()) return null;
                return toJavaLiteralCode(opt.get());
            }
            // OptionalInt / OptionalLong / OptionalDouble
            if (got instanceof java.util.OptionalInt) {
                java.util.OptionalInt oi = (java.util.OptionalInt) got;
                return oi.isPresent() ? String.valueOf(oi.getAsInt()) : null;
            }
            if (got instanceof java.util.OptionalLong) {
                java.util.OptionalLong ol = (java.util.OptionalLong) got;
                return ol.isPresent() ? (ol.getAsLong() + "L") : null;
            }
            if (got instanceof java.util.OptionalDouble) {
                java.util.OptionalDouble od = (java.util.OptionalDouble) got;
                if (!od.isPresent()) return null;
                double v = od.getAsDouble();
                // double 리터럴: 소수점이 없으면 ".0" 붙여 안전하게
                String s = Double.toString(v);
                if (!s.contains(".") && !s.toLowerCase().contains("e")) s = s + ".0";
                return s;
            }

            // 관찰단이 문자열로 실어준 경우 처리
            if (got instanceof String) {
                String raw = (String) got;

                // Config.STRING_IDENTIFIER 접두라면 실제 문자열로 간주하여 리터럴 생성
                if (raw.startsWith(Config.STRING_IDENTIFIER)) {
                    String s = raw.replace(Config.STRING_IDENTIFIER, "");
                    return "\"" + escapeJavaString(s) + "\"";
                }

                // 숫자/불리언 등 단순 리터럴이거나, 이미 "new BigDecimal(...)" 같은 코드 스니펫일 수도 있음
                // 여기서는 그대로 돌려보내고, 실패 시 컴파일러가 잡게 둡니다.
                return raw;
            }

            // 그 외: 직접 리터럴 시도
            return toJavaLiteralCode(got);

        } catch (Exception ignored) {
            return null; // 변환 불가 → 값 비교는 생략(존재만 assert)
        }
    }

    // ===== 내부 보조 =====

    private String toJavaLiteralCode(Object v) {
        if (v == null) return null;

        if (v instanceof String) {
            return "\"" + escapeJavaString((String) v) + "\"";
        }
        if (v instanceof Character) {
            return "'" + escapeJavaChar((Character) v) + "'";
        }
        if (v instanceof Boolean) {
            return v.toString();
        }
        if (v instanceof Integer || v instanceof Short || v instanceof Byte) {
            return v.toString();
        }
        if (v instanceof Long) {
            return v.toString() + "L";
        }
        if (v instanceof Float) {
            // F 접미사
            Float f = (Float) v;
            String s = f.toString();
            if (!s.contains(".") && !s.toLowerCase().contains("e")) s = s + ".0";
            return s + "F";
        }
        if (v instanceof Double) {
            // double 리터럴
            Double d = (Double) v;
            String s = d.toString();
            if (!s.contains(".") && !s.toLowerCase().contains("e")) s = s + ".0";
            return s;
        }
        if (v instanceof java.math.BigDecimal) {
            // BigDecimal은 문자열 생성자 사용을 권장
            return "new java.math.BigDecimal(\"" + escapeJavaString(((java.math.BigDecimal) v).toString()) + "\")";
        }
        if (v instanceof Enum) {
            Enum<?> e = (Enum<?>) v;
            return e.getClass().getName() + "." + e.name();
        }

        // Date/Time 및 복잡 객체: 타입 미스매치/생성자 복잡성 때문에 값 비교는 생략
        return null;
    }

    private String escapeJavaString(String s) {
        StringBuilder sb = new StringBuilder(s.length() + 16);
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            switch (c) {
                case '\\': sb.append("\\\\"); break;
                case '\"': sb.append("\\\""); break;
                case '\n': sb.append("\\n"); break;
                case '\r': sb.append("\\r"); break;
                case '\t': sb.append("\\t"); break;
                case '\b': sb.append("\\b"); break;
                case '\f': sb.append("\\f"); break;
                default:
                    if (c < 32 || c == 0x2028 || c == 0x2029) {
                        String hex = String.format("\\u%04X", (int) c);
                        sb.append(hex);
                    } else {
                        sb.append(c);
                    }
            }
        }
        return sb.toString();
    }

    private String escapeJavaChar(char c) {
        switch (c) {
            case '\\': return "\\\\";
            case '\'': return "\\'";
            case '\n': return "\\n";
            case '\r': return "\\r";
            case '\t': return "\\t";
            case '\b': return "\\b";
            case '\f': return "\\f";
            default:
                if (c < 32 || c == 0x2028 || c == 0x2029) {
                    return String.format("\\u%04X", (int) c);
                }
                return String.valueOf(c);
        }
    }

    private String sanitizeListPlaceholderToCode(String raw) {
    // [[abc]] → Arrays.asList("abc")
    if (raw != null && raw.startsWith("[[") && raw.endsWith("]]")) {
        String inner = raw.substring(2, raw.length()-2);
        // 쉼표 분리가 이미 되어 있다면 split 후 각 항목을 리터럴화
        if (!inner.contains(",")) {
            return "java.util.Arrays.asList(\"" + inner.replace("\"","\\\"") + "\")";
        }
        // 필요시 다원소도 처리
        String[] parts = inner.split("\\s*,\\s*");
        StringBuilder sb = new StringBuilder("java.util.Arrays.asList(");
        for (int i=0;i<parts.length;i++) {
            if (i>0) sb.append(", ");
            sb.append("\"").append(parts[i].replace("\"","\\\"")).append("\"");
        }
        sb.append(")");
        return sb.toString();
    }
    return raw;
}


      /**
       * 배열 코드에서 첫 번째 요소값 추출
       * [a, b, c] → a
       * [obj1, obj2] → obj1
       * [] → null
       */
     private String extractFirstElementFromArray(String arrayCode) {
         if (arrayCode == null || arrayCode.trim().isEmpty()) {
             return null;
         }
         
         try {
             String trimmed = arrayCode.trim();
             
             // [] 형식: 빈 배열
             if (trimmed.equals("[]")) {
                 return null;
             }
             
             // [element1, element2, ...] 형식
             if (trimmed.startsWith("[") && trimmed.endsWith("]")) {
                 String inner = trimmed.substring(1, trimmed.length() - 1).trim();
                 if (inner.isEmpty()) {
                     return null;
                 }
                 
                 // 첫 번째 요소 추출 (쉼표 기준)
                 int commaIndex = findFirstCommaOutsideBrackets(inner);
                 if (commaIndex > 0) {
                     return inner.substring(0, commaIndex).trim();
                 } else {
                     // 요소가 하나만 있는 경우
                     return inner.trim();
                 }
             }
         } catch (Exception e) {
             if (DEBUG_ASSERTION_TRANSFORM) {
                 System.out.println("[AssertionAdder] Error extracting first element from array: " + e.getMessage());
             }
         }
         
         return null;
     }
     
     /**
      * List 코드에서 마지막 요소값 추출
      * [[a, b, c]] → c
      * [[obj1, obj2]] → obj2
      * [[a]] → a
      */
     private String extractLastElementFromList(String listCode) {
         if (listCode == null || listCode.trim().isEmpty()) {
             return null;
         }
         
         try {
             String trimmed = listCode.trim();
             
             // [[]] 형식: 빈 리스트
             if (trimmed.equals("[]") || trimmed.equals("[[]]")) {
                 return null;
             }
             
             // [[...]] 형식
             if (trimmed.startsWith("[[") && trimmed.endsWith("]]")) {
                 String inner = trimmed.substring(2, trimmed.length() - 2).trim();
                 if (inner.isEmpty()) {
                     return null;
                 }
                 
                 // 마지막 요소 추출 (역순 쉼표 기준)
                 int lastCommaIndex = findLastCommaOutsideBrackets(inner);
                 if (lastCommaIndex > 0) {
                     return inner.substring(lastCommaIndex + 1).trim();
                 } else {
                     // 요소가 하나만 있는 경우
                     return inner.trim();
                 }
             }
         } catch (Exception e) {
             if (DEBUG_ASSERTION_TRANSFORM) {
                 System.out.println("[AssertionAdder] Error extracting last element from list: " + e.getMessage());
             }
         }
         
         return null;
     }
     
     /**
      * 배열 코드에서 마지막 요소값 추출
      * [a, b, c] → c
      * [obj1, obj2] → obj2
      * [a] → a
      */
     private String extractLastElementFromArray(String arrayCode) {
         if (arrayCode == null || arrayCode.trim().isEmpty()) {
             return null;
         }
         
         try {
             String trimmed = arrayCode.trim();
             
             // [] 형식: 빈 배열
             if (trimmed.equals("[]")) {
                 return null;
             }
             
             // [element1, element2, ...] 형식
             if (trimmed.startsWith("[") && trimmed.endsWith("]")) {
                 String inner = trimmed.substring(1, trimmed.length() - 1).trim();
                 if (inner.isEmpty()) {
                     return null;
                 }
                 
                 // 마지막 요소 추출 (역순 쉼표 기준)
                 int lastCommaIndex = findLastCommaOutsideBrackets(inner);
                 if (lastCommaIndex > 0) {
                     return inner.substring(lastCommaIndex + 1).trim();
                 } else {
                     // 요소가 하나만 있는 경우
                     return inner.trim();
                 }
             }
         } catch (Exception e) {
             if (DEBUG_ASSERTION_TRANSFORM) {
                 System.out.println("[AssertionAdder] Error extracting last element from array: " + e.getMessage());
             }
         }
         
         return null;
     }
     
     /**
      * 문자열에서 괄호 밖의 마지막 쉼표 위치 찾기
      * "a, [b, c], d" → d 앞의 쉼마 위치
      */
     private int findLastCommaOutsideBrackets(String str) {
         int bracketDepth = 0;
         for (int i = str.length() - 1; i >= 0; i--) {
             char c = str.charAt(i);
             if (c == ']' || c == '}' || c == ')') {
                 bracketDepth++;
             } else if (c == '[' || c == '{' || c == '(') {
                 bracketDepth--;
             } else if (c == ',' && bracketDepth == 0) {
                 return i;
             }
         }
         return -1;
     }


}
