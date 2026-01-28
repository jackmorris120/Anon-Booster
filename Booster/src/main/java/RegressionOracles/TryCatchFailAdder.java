package RegressionOracles;

import dk.brics.automaton.RegExp;
import org.evosuite.PackageInfo;
import org.junit.runner.notification.Failure;
import spoon.Launcher;
import spoon.reflect.code.*;
import spoon.reflect.declaration.CtClass;
import spoon.reflect.declaration.CtMethod;
import spoon.reflect.factory.Factory;
import spoon.support.reflect.code.CtBlockImpl;
import spoon.reflect.reference.CtExecutableReference;
import spoon.reflect.reference.CtTypeReference;
import utils.Config;
import utils.Pair;
import spoon.reflect.cu.SourcePosition;
import spoon.reflect.declaration.CtElement;

import spoon.reflect.visitor.filter.TypeFilter;

import java.net.URLClassLoader;
import java.util.*;

public class TryCatchFailAdder {
    // Debug flag for oracle transformation
    private static final boolean DEBUG_ORACLE_TRANSFORM = false;
    
    /**
     * Store original failing statement extracted from executedFileContent (Logger 포함된 파일)
     * Key: "ClassName:methodName"
     * Value: Failing statement의 string 표현 (Logger 제거 전)
     */
    public static final Map<String, String> ORIGINAL_FAILING_STATEMENT = new HashMap<>();
    
    /**
     * Store original test method statements BEFORE Oracle observation code is added
     * Key: "ClassName:methodName" (e.g., "DocumentTest_P_setTextPreservesDocumentStructure_1:documentTest_P_setTextPreservesDocumentStructure_1")
     * Value: Map of original statements indexed by their position in the test method
     */
    public static final Map<String, List<CtStatement>> ORIGINAL_TEST_STATEMENTS = new HashMap<>();
    
    /**
     * Store original test method itself for reference
     * Key: "ClassName:methodName"
     * Value: Original CtMethod before Oracle code addition
     */
    public static final Map<String, CtMethod> ORIGINAL_TEST_METHODS = new HashMap<>();
    /**
      * Find the first meaningful frame in the stack trace for exception verification
      * Returns the topmost frame (could be test class or CUT class)
      * The caller (isValidSource) will decide if it's suitable for verifyException
      */
    private static StackTraceElement findCUTFrame(StackTraceElement[] stackTrace) {
        if (stackTrace == null || stackTrace.length == 0) {
            return null;
        }
        
        // Find first non-JUnit, non-reflection frame
        for (int i = 0; i < stackTrace.length; i++) {
            StackTraceElement frame = stackTrace[i];
            String className = frame.getClassName();
            
            // Skip JUnit and reflection frames only
            if (className.startsWith("org.junit.") ||
                className.startsWith("java.lang.reflect.") ||
                className.startsWith("sun.reflect.") ||
                className.startsWith("jdk.internal.reflect.")) {
                continue;
            }
            
            // Return first meaningful frame (could be test class or CUT)
            return frame;
        }
        
        // Fallback: return first frame if no suitable frame found
        return stackTrace[0];
    }

    private static boolean crashPointMatch(CtStatement stmt, StackTraceElement crashPoint) {
        // 1. 일반 메서드 호출(CtInvocation) 확인
        List<CtInvocation<?>> invocations = stmt.getElements(new TypeFilter<>(CtInvocation.class));
        for (CtInvocation<?> invocation : invocations) {
            if (invocation.getExecutable() == null || invocation.getExecutable().getDeclaringType() == null) {
                continue;
            }
            // 메서드 이름과 해당 메서드가 선언된 클래스의 이름을 함께 비교
            String invocationMethodName = invocation.getExecutable().getSimpleName();
            String invocationClassName = invocation.getExecutable().getDeclaringType().getQualifiedName();

            if (invocationMethodName.equals(crashPoint.getMethodName()) &&
                    invocationClassName.equals(crashPoint.getClassName())) {
                return true;
            }
        }

        // 2. 생성자 호출(CtConstructorCall) 확인
        List<CtConstructorCall<?>> constructorCalls = stmt.getElements(new TypeFilter<>(CtConstructorCall.class));
        if (!constructorCalls.isEmpty()) {
            String crashClassName = crashPoint.getClassName().replace('$', '.'); // Inner class 처리
            String crashMethodName = crashPoint.getMethodName();

            for (CtConstructorCall<?> call : constructorCalls) {
                if (call.getExecutable() == null || call.getExecutable().getDeclaringType() == null) {
                    continue;
                }
                String constructorClassName = call.getExecutable().getDeclaringType().getQualifiedName();
                String constructorSimpleName = call.getExecutable().getDeclaringType().getSimpleName();

                // StackTrace에서 생성자는 "<init>" 또는 클래스의 Simple Name으로 표시될 수 있음
                boolean isConstructorNameMatch = crashMethodName.equals("<init>")
                        || crashMethodName.equals(constructorSimpleName);

                if (isConstructorNameMatch && constructorClassName.equals(crashClassName)) {
                    return true;
                }
            }
        }

        return false; // 일치하는 호출을 찾지 못한 경우
    }

    public static Pair<CtMethod, String> addTryCatchFail(CtMethod testMethod, Failure failure, Launcher launcher,
            String executedFileContent) {
        if (DEBUG_ORACLE_TRANSFORM) {
            System.out.println("[TryCatchFailAdder] ========================================");
            System.out.println("[TryCatchFailAdder] Starting addTryCatchFail for test: " + testMethod.getSimpleName());
            System.out.println("[TryCatchFailAdder] Exception: " + failure.getException().getClass().getName());
            System.out.println("[TryCatchFailAdder] Config.ENABLE_MULTIPLE_ORACLE_GEN: " + Config.ENABLE_MULTIPLE_ORACLE_GEN);
            System.out.println("[TryCatchFailAdder] Config.ENABLE_WHOLE_WRAP_ORACLE_GEN: " + Config.ENABLE_WHOLE_WRAP_ORACLE_GEN);
        }
        
        // Config 옵션에 따른 Oracle 생성 방식 결정
        if (Config.ENABLE_MULTIPLE_ORACLE_GEN) {
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TryCatchFailAdder] MODE: MULTIPLE_ORACLE_GEN (반복 실행 및 Oracle 재생성)");
            }
            return addTryCatchFailWithMultipleGeneration(testMethod, failure, launcher, executedFileContent);
        } else if (Config.ENABLE_WHOLE_WRAP_ORACLE_GEN) {
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TryCatchFailAdder] MODE: WHOLE_WRAP_ORACLE_GEN (전체 메서드 wrap)");
            }
            return addTryCatchFailWithWholeWrap(testMethod, failure, launcher, executedFileContent);
        } else {
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TryCatchFailAdder] MODE: DEFAULT (현재 로직 유지)");
            }
            return addTryCatchFailDefault(testMethod, failure, launcher, executedFileContent);
        }
    }
    
    /**
     * 기존 기능 유지: 초기 Crashing Point에 대한 Try-Catch만 추가
     */
    private static Pair<CtMethod, String> addTryCatchFailDefault(CtMethod testMethod, Failure failure, Launcher launcher,
            String executedFileContent) {
        if (DEBUG_ORACLE_TRANSFORM) {
            System.out.println("[TryCatchFailAdder] ========================================");
            System.out.println("[TryCatchFailAdder] Starting addTryCatchFailDefault for test: " + testMethod.getSimpleName());
            System.out.println("[TryCatchFailAdder] Exception: " + failure.getException().getClass().getName());
        }
        
        Throwable exception = failure.getException();
        if (exception == null) return null;

        StackTraceElement[] stackTrace = exception.getStackTrace();
        if (stackTrace.length == 0) return null;
        
        if (DEBUG_ORACLE_TRANSFORM) {
            System.out.println("[TryCatchFailAdder] Stack trace details:");
            for (int idx = 0; idx < Math.min(stackTrace.length, 15); idx++) {
                StackTraceElement elem = stackTrace[idx];
                String fileName = elem.getFileName() != null ? elem.getFileName() : "Unknown";
                boolean isNative = elem.isNativeMethod();
                String nativeTag = isNative ? " (native)" : "";
                System.out.println("[TryCatchFailAdder]   [" + idx + "] " + 
                    elem.getClassName() + "." + 
                    elem.getMethodName() + "(" + fileName + ":" + 
                    elem.getLineNumber() + ")" + nativeTag);
            }
            if (stackTrace.length > 15) {
                System.out.println("[TryCatchFailAdder]   ... (" + (stackTrace.length - 15) + " more frames)");
            }
            System.out.println("[TryCatchFailAdder] Total stack frames: " + stackTrace.length);
        }

        String errorType = exception.getClass().getName();
        String originalErrorType = errorType; // Store original for fail message and source verification

        if (!errorType.matches("^[a-zA-Z_$][a-zA-Z\\d_$]*(\\$[a-zA-Z_$][a-zA-Z\\d_$]*)*(\\.[a-zA-Z_$][a-zA-Z\\d_$]*(\\$[a-zA-Z_$][a-zA-Z\\d_$]*)*)*$")) {
            errorType = "java.lang.RuntimeException";
        }

        CtClass<?> testCtClass = null;
        try {
            testCtClass = testMethod.getParent(CtClass.class);
        } catch (Exception e) {
            // 동적 생성된 테스트의 경우 parent가 없을 수 있음
        }
        
         CtMethod ctMethod = testMethod.clone();
         Factory factory = launcher.getFactory();
         
         // ✅ Use executedFileContent-based statement extraction and matching
         // This applies the same intelligent matching strategy as WHOLE_WRAP mode:
         // Pass 1: Throwing method priority (from stack trace)
         // Pass 2: Exact string matching (extracted statement from executedFileContent)
         // Pass 3: Fallback methods
         CtStatement failingStmt = findFailingStmtSmart(ctMethod, stackTrace, executedFileContent);

          if (DEBUG_ORACLE_TRANSFORM) {
              System.out.println("[TryCatchFailAdder] Found failing statement: " + 
                  (failingStmt != null ? failingStmt.getClass().getSimpleName() : "null"));
              if (failingStmt != null && !(failingStmt instanceof CtBlockImpl)) {
                  String stmtPreview = failingStmt.toString().replace("\n", " ");
                  if (stmtPreview.length() > 100) stmtPreview = stmtPreview.substring(0, 100) + "...";
                  System.out.println("[TryCatchFailAdder] Statement: " + stmtPreview);
              } else if (failingStmt == null) {
                  System.out.println("[TryCatchFailAdder] WARNING: No failing statement found - will wrap entire method");
                  System.out.println("[TryCatchFailAdder] Stack trace info:");
                  if (stackTrace.length > 0) {
                      System.out.println("[TryCatchFailAdder]   Top frame: " + stackTrace[0].getClassName() + "." + stackTrace[0].getMethodName() + " (line " + stackTrace[0].getLineNumber() + ")");
                  }
                  for (int i = 0; i < Math.min(stackTrace.length, 5); i++) {
                      System.out.println("[TryCatchFailAdder]   [" + i + "] " + stackTrace[i].getClassName() + "." + stackTrace[i].getMethodName() + ":" + stackTrace[i].getLineNumber());
                  }
              }
          }
          
          // [CRITICAL CHECK] failingStmt가 이미 Try-Catch 블록이면 → 이미 처리된 것이므로 null 반환
          if (failingStmt instanceof CtTry) {
              if (DEBUG_ORACLE_TRANSFORM) {
                  System.out.println("[TryCatchFailAdder] Failing statement is already a Try-Catch block!");
                  System.out.println("[TryCatchFailAdder] This means the crash point is already wrapped.");
                  System.out.println("[TryCatchFailAdder] Returning null to skip duplicate wrapping.");
              }
              return null;
          }

          // failingStmt가 중첩된 statement일 경우, top-level statement (for/if/while 등)를 찾음
          CtStatement stmtToWrap = failingStmt;
          if (failingStmt != null && !(failingStmt instanceof CtBlockImpl)) {
              CtStatement topLevelStmt = findTopLevelStatement(failingStmt, ctMethod);
              if (topLevelStmt != null && topLevelStmt != failingStmt) {
                  stmtToWrap = topLevelStmt;
                  if (DEBUG_ORACLE_TRANSFORM) {
                      String preview = topLevelStmt.toString().replace("\n", " ");
                      if (preview.length() > 80) preview = preview.substring(0, 80) + "...";
                      System.out.println("[TryCatchFailAdder] Using top-level statement instead: " + 
                          topLevelStmt.getClass().getSimpleName());
                      System.out.println("[TryCatchFailAdder] Top-level: " + preview);
                  }
              } else if (topLevelStmt == null) {
                  // [NEW] top-level statement가 null (이미 try-catch로 감싸짐)
                  // → 이 경우 oracle을 추가할 수 없으므로 null 반환
                  if (DEBUG_ORACLE_TRANSFORM) {
                      System.out.println("[TryCatchFailAdder] Top-level statement is already wrapped in try-catch, cannot wrap again");
                      System.out.println("[TryCatchFailAdder] Returning null to prevent duplicate wrapping");
                  }
                  return null;
              }
          }
         
         CtBlock<?> parentBlock = null;
         try {
             parentBlock = stmtToWrap.getParent(CtBlock.class);
         } catch (Exception e) {
            // 동적 생성된 테스트의 경우 parent 정보가 부족할 수 있음
        }
        
        if (parentBlock == null) {
            parentBlock = ctMethod.getBody();
            if (parentBlock == null) return null;
        }

        CtStatement anchor = (stmtToWrap instanceof CtStatement && !(stmtToWrap instanceof CtBlock))
                ? (CtStatement) stmtToWrap : null;

        CtElement walker = stmtToWrap;
        try {
            while (walker != null && walker.getParent() != parentBlock) {
                if (walker instanceof CtStatement && !(walker instanceof CtBlock)) {
                    anchor = (CtStatement) walker;
                }
                walker = walker.getParent();
            }
        } catch (Exception e) {
            // walker 순회 중 문제가 발생하면 현재 anchor 사용
        }
        if (anchor == null) return null;

        List<CtStatement> siblings = parentBlock.getStatements();
        int idx = -1;

        for (int i = 0; i < siblings.size(); i++) {
            CtStatement s = siblings.get(i);
            if (s == anchor || s.equals(anchor) || s == stmtToWrap || s.equals(stmtToWrap)) {
                idx = i;
                break;
            }
        }

        if (idx == -1) {
            for (int i = 0; i < siblings.size(); i++) {
                CtStatement s = siblings.get(i);
                boolean contains = (s == anchor) || (s == stmtToWrap);
                if (!contains) {
                    List<CtStatement> children = s.getElements(new TypeFilter<>(CtStatement.class));
                    for (int t = 0; t < children.size(); t++) {
                        CtStatement ch = children.get(t);
                        if (ch == anchor || ch == stmtToWrap) { contains = true; break; }
                    }
                }
                if (contains) { idx = i; anchor = s; break; }
            }
        }

        if (idx == -1) return null;

        // ═══════════════════════════════════════════════════════════════════════════
        // [NEW SIMPLIFIED LOGIC] 단일 statement만 try-catch로 감싸기
        // 변수 선언이 있는 경우: 선언을 try 밖으로 분리하고 초기화만 try 안에
        // ═══════════════════════════════════════════════════════════════════════════
        
        List<CtStatement> preDeclarations = new ArrayList<>();
        CtStatement wrappingStmt = anchor.clone();
        
        // [STEP 1] anchor가 변수 선언문인 경우 → 선언과 초기화 분리
         if (anchor instanceof CtLocalVariable) {
             CtLocalVariable<?> localVar = (CtLocalVariable<?>) anchor;
             String varName = localVar.getSimpleName();
             String typeName = localVar.getType().toString();
             
             if (DEBUG_ORACLE_TRANSFORM) {
                 System.out.println("[TryCatchFailAdder] Variable declaration detected: " + typeName + " " + varName);
                 System.out.println("[TryCatchFailAdder] Separating declaration from initialization");
             }
             
             // 변수 선언만 미리 생성 (null 또는 기본값으로 초기화)
             String defaultValue = getDefaultValueForType(typeName);
             String preDeclarationCode = typeName + " " + varName + " = " + defaultValue + ";";
             CtStatement preDecl = factory.Code().createCodeSnippetStatement(preDeclarationCode);
             preDeclarations.add(preDecl);
             
             if (DEBUG_ORACLE_TRANSFORM) {
                 System.out.println("[TryCatchFailAdder]   Pre-declaration: " + preDeclarationCode);
             }
             
             // 원본에서 초기화 부분만 할당문으로 변경
             if (localVar.getDefaultExpression() != null) {
                 String assignmentCode = varName + " = " + localVar.getDefaultExpression().toString() + ";";
                 wrappingStmt = factory.Code().createCodeSnippetStatement(assignmentCode);
                 
                 if (DEBUG_ORACLE_TRANSFORM) {
                     System.out.println("[TryCatchFailAdder]   Assignment in try: " + assignmentCode);
                 }
             } else {
                 // 초기화가 없다면 원본 그대로 (하지만 이미 선언되었으므로 컴파일 에러 방지)
                 // 빈 statement로 대체하거나 원본 유지
                 wrappingStmt = factory.Code().createCodeSnippetStatement("/* " + varName + " declared above */");
                 
                 if (DEBUG_ORACLE_TRANSFORM) {
                     System.out.println("[TryCatchFailAdder]   No initialization needed");
                 }
             }
         }
         
          // [STEP 1-B] assignment statement인 경우 → 좌변 변수 선언 추출
          // 예: record = records.next(); → record를 미리 선언
          if (anchor instanceof CtAssignment) {
              CtAssignment<?, ?> assignment = (CtAssignment<?, ?>) anchor;
              CtExpression leftSide = assignment.getAssigned();
              
              if (leftSide instanceof CtVariableAccess) {
                  CtVariableAccess varAccess = (CtVariableAccess) leftSide;
                  String varName = varAccess.getVariable().getSimpleName();
                  CtTypeReference<?> varType = null;
                  
                  try {
                      varType = varAccess.getVariable().getType();
                  } catch (Exception e) {
                      if (DEBUG_ORACLE_TRANSFORM) {
                          System.out.println("[TryCatchFailAdder] Could not get type for variable: " + varName);
                      }
                  }
                  
                  if (varType != null && varName != null) {
                      // 변수가 이미 선언되어 있는지 확인
                      boolean alreadyDeclared = isVariableAlreadyDeclared(ctMethod, varName);
                      
                      if (!alreadyDeclared) {
                          String typeName = varType.toString();
                          String defaultValue = getDefaultValueForType(typeName);
                          String preDeclarationCode = typeName + " " + varName + " = " + defaultValue + ";";
                          
                          if (DEBUG_ORACLE_TRANSFORM) {
                              System.out.println("[TryCatchFailAdder] Assignment variable detected: " + typeName + " " + varName);
                              System.out.println("[TryCatchFailAdder]   Pre-declaration: " + preDeclarationCode);
                          }
                          
                          try {
                              CtStatement preDecl = factory.Code().createCodeSnippetStatement(preDeclarationCode);
                              preDeclarations.add(preDecl);
                          } catch (Exception e) {
                              if (DEBUG_ORACLE_TRANSFORM) {
                                  System.out.println("[TryCatchFailAdder] Failed to create pre-declaration: " + e.getMessage());
                              }
                          }
                       } else {
                          if (DEBUG_ORACLE_TRANSFORM) {
                              System.out.println("[TryCatchFailAdder] Assignment variable already declared: " + varName);
                              System.out.println("[TryCatchFailAdder]   Adding null initialization before try block");
                          }
                          
                          // 변수가 이미 선언되었으면, try 블록 밖에서 null로 초기화
                          // 예: record = null; (try-catch 블록 이전)
                          String defaultValue = getDefaultValueForType(varType.toString());
                          String initCode = varName + " = " + defaultValue + ";";
                          
                          try {
                              CtStatement initStmt = factory.Code().createCodeSnippetStatement(initCode);
                              preDeclarations.add(initStmt);
                              
                              if (DEBUG_ORACLE_TRANSFORM) {
                                  System.out.println("[TryCatchFailAdder]   Initialization statement: " + initCode);
                              }
                          } catch (Exception e) {
                              if (DEBUG_ORACLE_TRANSFORM) {
                                  System.out.println("[TryCatchFailAdder] Failed to create initialization: " + e.getMessage());
                              }
                          }
                      }
                  }
              }
          }
        
        // [STEP 2] Try-Catch 블록 생성 (단일 statement만 포함)
        CtTry tryBlock = factory.Core().createTry();
        CtBlock<?> tryBody = factory.Core().createBlock();
        
        // Try body에 wrapping할 statement 추가
        tryBody.addStatement(wrappingStmt);
        
        // Fail assertion 추가
        tryBody.addStatement(factory.Code().createCodeSnippetStatement(
                "org.junit.Assert.fail(\"Expecting exception: " + errorType + "\")"));
        
        tryBlock.setBody(tryBody);
        
        // [STEP 3] Catch 블록 생성
        StackTraceElement cutFrame = findCUTFrame(stackTrace);
        String testMethodName = testMethod.getSimpleName();
        tryBlock.addCatcher(createCatcher(factory, errorType, originalErrorType, cutFrame, true, testMethodName));

        if (DEBUG_ORACLE_TRANSFORM) {
            System.out.println("[TryCatchFailAdder] Try-Catch block created");
            System.out.println("[TryCatchFailAdder]   Pre-declarations: " + preDeclarations.size());
            System.out.println("[TryCatchFailAdder]   Statement to wrap: " + wrappingStmt.toString().substring(0, Math.min(60, wrappingStmt.toString().length())));
        }
        
        // [STEP 4] 변수 선언들을 try 블록 이전에 삽입
        for (int i = preDeclarations.size() - 1; i >= 0; i--) {
            siblings.add(idx, preDeclarations.get(i));
        }
        
        // [STEP 5] 원본 statement를 try-catch 블록으로 교체
        int newIdx = idx + preDeclarations.size();
        siblings.set(newIdx, tryBlock);

        if (testCtClass != null) {
            // Find and remove the exact method by signature comparison
            CtMethod<?> methodToRemove = null;
            for (CtMethod<?> existingMethod : testCtClass.getMethods()) {
                if (existingMethod.getSimpleName().equals(testMethod.getSimpleName()) &&
                    existingMethod.getSignature().equals(testMethod.getSignature())) {
                    methodToRemove = existingMethod;
                    break;
                }
            }
            
            if (methodToRemove != null) {
                testCtClass.removeMethod(methodToRemove);
            }
             testCtClass.addMethod(ctMethod);
         }
         
         if (DEBUG_ORACLE_TRANSFORM) {
             System.out.println("[TryCatchFailAdder] addTryCatchFail completed successfully");
             System.out.println("[TryCatchFailAdder] Try-Catch block inserted");
         }
         
         return new Pair<>(ctMethod, ctMethod.toString());
    }



    /**
     * Creates an enhanced catch block with both exception type and (conditionally) source verification.
     *
     * @param factory Spoon factory for creating AST elements
     * @param errorType The specific exception type we expect to be thrown (sanitized for catch block)
     * @param originalErrorType The original exception type (kept for compatibility; not required here)
     * @param verificationFrame Stack trace frame for source verification
     * @param foundMatch true if failing statement was matched precisely in the test body
     * @param testMethodName the test method name to check if exception is from test class itself
     */
    private static CtCatch createCatcher(Factory factory, String errorType, String originalErrorType,
                                        StackTraceElement verificationFrame, boolean foundMatch, String testMethodName) {
        CtCatch catcher = factory.Core().createCatch();
        CtCatchVariable<? extends Throwable> catchVar = factory.Core().createCatchVariable();
        catchVar.setSimpleName("e");

        // Catch as Throwable for compilation safety; verify concrete type in body.
        CtTypeReference<?> catchTypeRef = factory.Type().createReference("java.lang.Throwable");
        catchTypeRef.setImplicit(false);
        catchVar.setType((CtTypeReference) catchTypeRef);
        catcher.setParameter(catchVar);

        final String sourceClass = (verificationFrame != null) ? verificationFrame.getClassName() : "";
        StringBuilder sb = new StringBuilder();

        // 1) Verify the expected exception type ONLY if errorType doesn't contain the test method name
        // Skip if exception is from test class itself (e.g., TestName$NestedException)
        // because when merging into skeletal class, this class won't exist
        // Note: Use case-insensitive comparison because method name starts with lowercase 'test'
        // but class name starts with uppercase 'Test'
        boolean skipTypeVerification = testMethodName != null && 
            originalErrorType.toLowerCase().contains(testMethodName.toLowerCase());
        
        if (DEBUG_ORACLE_TRANSFORM) {
            System.out.println("[TryCatchFailAdder] Exception type verification check:");
            System.out.println("[TryCatchFailAdder]   testMethodName: " + testMethodName);
            System.out.println("[TryCatchFailAdder]   originalErrorType: " + originalErrorType);
            System.out.println("[TryCatchFailAdder]   errorType: " + errorType);
            System.out.println("[TryCatchFailAdder]   testMethodName == null: " + (testMethodName == null));
            System.out.println("[TryCatchFailAdder]   originalErrorType.toLowerCase().contains(testMethodName.toLowerCase()): " + 
                (testMethodName != null && originalErrorType.toLowerCase().contains(testMethodName.toLowerCase())));
            System.out.println("[TryCatchFailAdder]   skipTypeVerification: " + skipTypeVerification);
        }
        
        if (!skipTypeVerification) {
            // ★ 익명 클래스나 숫자로 끝나는 nested class 체크
            // 예: MathRuntimeException$1, OuterClass$2 등
            // 이런 클래스는 .class로 접근 불가능하므로 Class.forName() 사용
            boolean isAnonymousOrNumericNestedClass = errorType.matches(".*\\$\\d+$");
            
            if (isAnonymousOrNumericNestedClass) {
                // 익명/숫자 nested class는 Class.forName()으로 처리
                sb.append("try {\n");
                sb.append("    org.junit.Assert.assertTrue(\"Expected ")
                .append(errorType)
                .append(" but got \" + e.getClass().getName(), ")
                .append("Class.forName(\"")
                .append(errorType)
                .append("\").isInstance(e));\n");
                sb.append("} catch (ClassNotFoundException cnfe) {\n");
                sb.append("    org.junit.Assert.fail(\"Exception class not found: ")
                .append(errorType)
                .append("\");\n");
                sb.append("}");
            } else {
                // 일반 inner class는 $ → . 변환
                String errorTypeForClassRef = errorType.replace("$", ".");
                sb.append("org.junit.Assert.assertTrue(\"Expected ")
                .append(errorType)
                .append(" but got \" + e.getClass().getName(), ")
                .append(errorTypeForClassRef)
                .append(".class.isInstance(e));");
            }
        } else {
            sb.append("// Exception type verification skipped (exception from test class itself)");
        }

        // 2) EvoSuite-like condition for verifying throw-site (unstable otherwise)
        boolean shouldVerifyThrowSite =
                foundMatch
            && verificationFrame != null
            && isValidSource(sourceClass)
            && errorType.endsWith("Exception")
            && !"TooManyResourcesException".equals(errorType)
            && !errorType.endsWith("FriendlyReminderException");

        if (shouldVerifyThrowSite) {
            sb.append("\norg.evosuite.runtime.EvoAssertions.verifyException(\"")
            .append(sourceClass)
            .append("\", e);");
        } else {
            // If throw-site is test class itself, verify the exception source using stack trace
            if (verificationFrame != null && sourceClass.matches(".*_[MP]_.*")) {
                // 동적 생성된 테스트의 경우, Skeletal Class로 Split될 때 클래스명이 변경될 수 있으므로
                // 클래스명 검증을 스킵하고 대신 스택 트레이스의 상단 프레임이 test class임을 확인
                sb.append("\n// Throw-site verification skipped for dynamically generated test (class name changes during split)");
            } else {
                sb.append("\n// Throw-site verification skipped (condition not met)");
            }
        }

        catcher.setBody(factory.Code().createCodeSnippetStatement(sb.toString()));
        return catcher;
    }


    /**
     * Extract the statement at the given line number from executedFileContent
     * executedFileContent는 Logger가 추가된 실행 파일의 전체 내용
     * 
     * @param executedFileContent Logger가 추가되어 실행된 파일의 전체 내용
     * @param lineNumber Stack trace에서 가져온 line number
     * @param ctMethod 현재 test method (Logger 제거된)
     * @return 추출된 statement의 string 표현 또는 null
     */
    private static String extractStatementFromExecutedFile(String executedFileContent, int lineNumber, CtMethod ctMethod) {
        if (executedFileContent == null || lineNumber <= 0) {
            return null;
        }
        
        try {
            String[] lines = executedFileContent.split("\n");
            
            if (lineNumber > lines.length) {
                if (DEBUG_ORACLE_TRANSFORM) {
                    System.out.println("[TryCatchFailAdder] [STMT-EXTRACT] Line number " + lineNumber + 
                        " exceeds file length " + lines.length);
                }
                return null;
            }
            
            // Line numbers are 1-indexed
            String statementLine = lines[lineNumber - 1].trim();
            
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TryCatchFailAdder] [STMT-EXTRACT] Extracted line " + lineNumber + ": " + statementLine);
                System.out.println("[TryCatchFailAdder] [STMT-EXTRACT] Total lines in executedFileContent: " + lines.length);
                
                // Show surrounding lines for context
                System.out.println("[TryCatchFailAdder] [STMT-EXTRACT] Context:");
                int contextStart = Math.max(0, lineNumber - 5);
                int contextEnd = Math.min(lines.length, lineNumber + 3);
                for (int i = contextStart; i < contextEnd; i++) {
                    String marker = (i == lineNumber - 1) ? " ← TARGET" : "";
                    System.out.println("[TryCatchFailAdder] [STMT-EXTRACT]   Line " + (i + 1) + ": " + 
                        lines[i].trim() + marker);
                }
            }
            
            // Remove Logger.observe statements (우리는 원본 business logic statement만 원함)
            if (statementLine.contains("Logger.observe")) {
                if (DEBUG_ORACLE_TRANSFORM) {
                    System.out.println("[TryCatchFailAdder] [STMT-EXTRACT] Line contains Logger.observe, skipping");
                }
                return null;
            }
            
            return statementLine;
            
        } catch (Exception e) {
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TryCatchFailAdder] [STMT-EXTRACT] Error: " + e.getMessage());
            }
            return null;
        }
    }
    
    /**
     * Parse a statement string to CtStatement using Spoon
     * 
     * @param stmtString Statement의 string 표현
     * @param ctMethod Context를 위한 현재 test method
     * @return Parsed CtStatement 또는 null
     */
    private static CtStatement parseStatementString(String stmtString, CtMethod ctMethod) {
        if (stmtString == null || stmtString.isEmpty()) {
            return null;
        }
        
        try {
            // Spoon Factory를 사용해서 statement parsing
            Factory factory = ctMethod.getFactory();
            
            // 간단한 parsing: CodeSnippetStatement로 변환
            CtCodeSnippetStatement snippetStmt = factory.createCodeSnippetStatement(stmtString);
            
            return snippetStmt;
            
        } catch (Exception e) {
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TryCatchFailAdder] [STMT-PARSE] Error parsing statement: " + e.getMessage());
            }
            return null;
        }
    }

    /**
     * Find failing statement by direct string matching
     * Test method의 모든 statements를 순회하면서 extracted failing statement와 직접 비교
     * 
     * Throwing method를 포함하는 statement를 우선적으로 선택
     * 
     * @param ctMethod Test method
     * @param failingStmtString Extracted failing statement string from executedFileContent
     * @param throwingMethodName Throwing method name (optional, for priority)
     * @param throwingClassName Throwing class name (optional, for priority)
     * @return Matching statement 또는 null
     */
    private static CtStatement findFailingStmtByDirectStringMatching(
            CtMethod ctMethod, 
            String failingStmtString,
            String throwingMethodName,
            String throwingClassName) {
        
        if (ctMethod == null || ctMethod.getBody() == null || failingStmtString == null) {
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TryCatchFailAdder] [STRING-MATCH] Method or statement is null");
            }
            return null;
        }
        
        try {
            List<CtStatement> allStatements = collectAllStatements(ctMethod.getBody());
            String normalizedExtracted = normalizeStatementSignature(failingStmtString);
            
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TryCatchFailAdder] [STRING-MATCH] ===== Direct String Matching =====");
                System.out.println("[TryCatchFailAdder] [STRING-MATCH] Total statements: " + allStatements.size());
                System.out.println("[TryCatchFailAdder] [STRING-MATCH] Looking for: " + failingStmtString);
                System.out.println("[TryCatchFailAdder] [STRING-MATCH] Normalized: " + normalizedExtracted);
                if (throwingMethodName != null) {
                    System.out.println("[TryCatchFailAdder] [STRING-MATCH] Throwing method (priority): " + throwingMethodName);
                }
            }
            
            // First pass: Find statements that contain the throwing method
            CtStatement throwingMethodStmt = null;
            if (throwingMethodName != null) {
                if (DEBUG_ORACLE_TRANSFORM) {
                    System.out.println("[TryCatchFailAdder] [STRING-MATCH] [PASS-1] Starting Pass 1 with throwing method: " + throwingMethodName);
                    System.out.println("[TryCatchFailAdder] [STRING-MATCH] [PASS-1] Total statements to check: " + allStatements.size());
                }
                for (int i = 0; i < allStatements.size(); i++) {
                    CtStatement stmt = allStatements.get(i);
                    String stmtStr = stmt.toString().trim();
                    
                    if (DEBUG_ORACLE_TRANSFORM) {
                        System.out.println("[TryCatchFailAdder] [STRING-MATCH] [PASS-1] Checking stmt #" + i + ": " + 
                            (stmtStr.length() > 80 ? stmtStr.substring(0, 80) + "..." : stmtStr));
                        System.out.println("[TryCatchFailAdder] [STRING-MATCH] [PASS-1]   Contains '" + throwingMethodName + "('? " + 
                            stmtStr.contains(throwingMethodName + "("));
                    }
                    
                    // Check if statement contains the throwing method invocation
                    // Note: We only check for the method name, not the full class name
                    // because the statement might not include the fully qualified class name
                    if (stmtStr.contains(throwingMethodName + "(")) {
                        
                        if (DEBUG_ORACLE_TRANSFORM) {
                            System.out.println("[TryCatchFailAdder] [STRING-MATCH] ⚡ Found statement with throwing method at index " + i);
                            System.out.println("[TryCatchFailAdder] [STRING-MATCH] Statement: " + 
                                (stmtStr.length() > 100 ? stmtStr.substring(0, 100) + "..." : stmtStr));
                        }
                        
                        // Return this statement as it's the most likely crash point
                        try {
                            if (!isAlreadyWrappedInTryCatch(stmt)) {
                                if (DEBUG_ORACLE_TRANSFORM) {
                                    System.out.println("[TryCatchFailAdder] [STRING-MATCH] ✓ Pass 1 SUCCESS: Returning statement with throwing method");
                                }
                                return stmt;
                            }
                        } catch (Exception e) {
                            // If exception checking fails, still return the statement with throwing method
                            // because it's the most likely to be the crash point
                            if (DEBUG_ORACLE_TRANSFORM) {
                                System.out.println("[TryCatchFailAdder] [STRING-MATCH] Pass 1 returning despite parent check error: " + e.getMessage());
                            }
                            return stmt;
                        }
                    }
                }
            }
            
            // Second pass: Iterate statements and find exact match
            for (int i = 0; i < allStatements.size(); i++) {
                CtStatement stmt = allStatements.get(i);
                String stmtStr = stmt.toString().trim();
                String normalizedStmt = normalizeStatementSignature(stmtStr);
                
                if (DEBUG_ORACLE_TRANSFORM) {
                    System.out.println("[TryCatchFailAdder] [STRING-MATCH] Statement #" + i + ": " + 
                        (stmtStr.length() > 80 ? stmtStr.substring(0, 80) + "..." : stmtStr));
                }
                
                // Exact match
                if (normalizedStmt.equals(normalizedExtracted)) {
                    if (DEBUG_ORACLE_TRANSFORM) {
                        System.out.println("[TryCatchFailAdder] [STRING-MATCH] ✓ Exact match at index " + i);
                        System.out.println("[TryCatchFailAdder] [STRING-MATCH] Statement: " + stmtStr);
                    }
                    
                    if (!isAlreadyWrappedInTryCatch(stmt)) {
                        return stmt;
                    }
                }
            }
            
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TryCatchFailAdder] [STRING-MATCH] ✗ No exact match found");
            }
            
        } catch (Exception e) {
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TryCatchFailAdder] [STRING-MATCH] Error: " + e.getMessage());
            }
            e.printStackTrace();
        }
        
        return null;
    }

    /**
     * ✅ NEW: Statement 기반 매칭 - 모든 statement를 순회하며 invocation 찾기
     * 
     * 이 메서드는 다음과 같이 동작합니다:
     * 1. 메서드의 모든 statement 수집
     * 2. 각 statement가 throwingMethodName invocation을 포함하는지 확인
     * 3. 라인 번호와 무관하게 일치하는 statement 반환
     * 
     * 장점:
     * - 라인 번호 변화에 영향받지 않음
     * - Statement 내용 기반 매칭으로 정확도 높음
     * - Line Discrepancy 문제 회피
      */
    
    /**
     * Find the exact failing statement by comparing with saved failing statement string
     * 저장된 failing statement string(executedFileContent에서 추출)을 사용해서
     * 현재 test method(Logger 제거된)에서 equivalent statement 찾기
     * 
     * 알고리즘:
     * 1. ORIGINAL_FAILING_STATEMENT에서 저장된 failing statement string 조회
     * 2. 현재 test method의 모든 statements를 순회
     * 3. 각 statement의 normalized string과 failing statement string 비교
     * 4. 가장 유사한 statement 반환
     * 
     * @param ctMethod 현재 test method (Logger 제거된)
     * @param throwingMethodName throwing method name
     * @param throwingClassName throwing method's class name
     * @return 일치하는 statement 또는 null
     */
    private static CtStatement findFailingStmtByOriginalStatementEquivalence(
            CtMethod ctMethod,
            String throwingMethodName, 
            String throwingClassName) {
        
        if (ctMethod == null || ctMethod.getBody() == null) {
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TryCatchFailAdder] [ORIG-EQUIV] Method or body is null");
            }
            return null;
        }
        
        try {
            // Step 1: 저장된 failing statement string 조회
            String className = null;
            if (ctMethod.getDeclaringType() != null) {
                className = ctMethod.getDeclaringType().getQualifiedName();
            }
            
            if (className == null) {
                if (DEBUG_ORACLE_TRANSFORM) {
                    System.out.println("[TryCatchFailAdder] [ORIG-EQUIV] Cannot determine class name");
                }
                return null;
            }
            
            String testMethodKey = className + ":" + ctMethod.getSimpleName();
            String failingStmtString = ORIGINAL_FAILING_STATEMENT.get(testMethodKey);
            
            if (failingStmtString == null) {
                if (DEBUG_ORACLE_TRANSFORM) {
                    System.out.println("[TryCatchFailAdder] [ORIG-EQUIV] No failing statement found for key: " + testMethodKey);
                    System.out.println("[TryCatchFailAdder] [ORIG-EQUIV] Available keys: " + ORIGINAL_FAILING_STATEMENT.keySet());
                }
                return null;
            }
            
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TryCatchFailAdder] [ORIG-EQUIV] ===== Finding Statement by Original Equivalence =====");
                System.out.println("[TryCatchFailAdder] [ORIG-EQUIV] Test method key: " + testMethodKey);
                System.out.println("[TryCatchFailAdder] [ORIG-EQUIV] Failing statement: " + failingStmtString);
            }
            
            // Step 2: 현재 test method에서 equivalent statement 찾기
            List<CtStatement> currentStatements = ctMethod.getBody().getStatements();
            String normalizedFailingStmt = normalizeStatementSignature(failingStmtString);
            
            for (int i = 0; i < currentStatements.size(); i++) {
                CtStatement currentStmt = currentStatements.get(i);
                String currentStmtString = currentStmt.toString().trim();
                String normalizedCurrentStmt = normalizeStatementSignature(currentStmtString);
                
                // String equivalence check
                if (normalizedCurrentStmt.equals(normalizedFailingStmt)) {
                    if (DEBUG_ORACLE_TRANSFORM) {
                        System.out.println("[TryCatchFailAdder] [ORIG-EQUIV] ✓ Found exact match at index " + i);
                        System.out.println("[TryCatchFailAdder] [ORIG-EQUIV] Statement: " + currentStmtString);
                    }
                    
                    // 이미 try-catch로 감싸져 있는지 확인
                    CtInvocation<?> inv = findInvocationInStatement(
                        currentStmt, throwingMethodName, throwingClassName);
                    if (inv != null && !isAlreadyWrappedInTryCatch(inv)) {
                        return currentStmt;
                    }
                }
            }
            
            // Step 3: Exact match 실패 시, contains check (부분 일치)
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TryCatchFailAdder] [ORIG-EQUIV] No exact match, trying partial match...");
            }
            
            for (int i = 0; i < currentStatements.size(); i++) {
                CtStatement currentStmt = currentStatements.get(i);
                String currentStmtString = currentStmt.toString().trim();
                String normalizedCurrentStmt = normalizeStatementSignature(currentStmtString);
                
                // Partial match: current statement contains failing statement or vice versa
                if (normalizedCurrentStmt.contains(normalizedFailingStmt) || 
                    normalizedFailingStmt.contains(normalizedCurrentStmt)) {
                    
                    if (DEBUG_ORACLE_TRANSFORM) {
                        System.out.println("[TryCatchFailAdder] [ORIG-EQUIV] ✓ Found partial match at index " + i);
                        System.out.println("[TryCatchFailAdder] [ORIG-EQUIV] Statement: " + currentStmtString);
                    }
                    
                    CtInvocation<?> inv = findInvocationInStatement(
                        currentStmt, throwingMethodName, throwingClassName);
                    if (inv != null && !isAlreadyWrappedInTryCatch(inv)) {
                        return currentStmt;
                    }
                }
            }
            
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TryCatchFailAdder] [ORIG-EQUIV] ✗ Could not find matching statement");
            }
            
        } catch (Exception e) {
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TryCatchFailAdder] [ORIG-EQUIV] Error: " + e.getMessage());
            }
            e.printStackTrace();
        }
        
        return null;
    }
    
    /**
     * Find an invocation matching the throwing method name and class in a given statement
     * 주어진 statement에서 throwing method name과 class와 일치하는 invocation 찾기
     */
    private static CtInvocation<?> findInvocationInStatement(
            CtStatement stmt,
            String throwingMethodName,
            String throwingClassName) {
        
        if (stmt == null) return null;
        
        // Case 1: statement 자체가 invocation
        if (stmt instanceof CtInvocation) {
            CtInvocation<?> inv = (CtInvocation<?>) stmt;
            if (invocationMatches(inv, throwingMethodName, throwingClassName)) {
                return inv;
            }
        }
        
        // Case 2: statement 내의 모든 invocations 확인
        List<CtInvocation<?>> allInvocations = stmt.getElements(new TypeFilter<>(CtInvocation.class));
        
        // 마지막 invocation이 일반적으로 MUT (Mutated Under Test)
        for (int i = allInvocations.size() - 1; i >= 0; i--) {
            CtInvocation<?> inv = allInvocations.get(i);
            if (invocationMatches(inv, throwingMethodName, throwingClassName)) {
                return inv;
            }
        }
        
        return null;
    }
    
    /**
     * Check if an invocation matches the throwing method name and class
     */
    private static boolean invocationMatches(
            CtInvocation<?> inv,
            String throwingMethodName,
            String throwingClassName) {
        
        if (inv.getExecutable() == null) return false;
        
        String invName = inv.getExecutable().getSimpleName();
        if (!invName.equals(throwingMethodName)) return false;
        
        if (inv.getExecutable().getDeclaringType() != null) {
            String invClassName = inv.getExecutable().getDeclaringType().getQualifiedName();
            return classNameCompatible(invClassName, throwingClassName);
        }
        
        return true;
    }

     private static CtStatement findStatementByStatementMatching(CtMethod ctMethod,
                                                               String throwingMethodName,
                                                               String throwingClassName,
                                                               String executedFileContent) {
        if (ctMethod == null || ctMethod.getBody() == null) {
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TryCatchFailAdder] [STMT-MATCH] Method or body is null");
            }
            return null;
        }
        
        try {
            // Step 1: 메서드의 모든 statement 수집
            List<CtStatement> allStatements = collectAllStatements(ctMethod.getBody());
            
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TryCatchFailAdder] [STMT-MATCH] ===== Statement-Based Matching =====");
                System.out.println("[TryCatchFailAdder] [STMT-MATCH] Total statements: " + allStatements.size());
                System.out.println("[TryCatchFailAdder] [STMT-MATCH] Looking for: " + throwingMethodName + 
                    " from " + throwingClassName);
            }
            
            // Step 2: 각 statement에서 invocation 찾기
            int stmtIndex = 0;
            for (CtStatement stmt : allStatements) {
                // statement가 invocation인지 확인
                CtInvocation<?> directInvocation = null;
                
                // Case 1: statement 자체가 invocation
                if (stmt instanceof CtInvocation) {
                    directInvocation = (CtInvocation<?>) stmt;
                } else {
                    // Case 2: statement 내에 invocation 포함
                    List<CtInvocation<?>> invocationsInStmt = stmt.getElements(
                        new TypeFilter<>(CtInvocation.class));
                    
                    // 첫 번째 invocation부터 확인 (throwing method는 일반적으로 첫 호출)
                    for (CtInvocation<?> inv : invocationsInStmt) {
                        if (inv.getExecutable() != null && 
                            inv.getExecutable().getSimpleName().equals(throwingMethodName)) {
                            directInvocation = inv;
                            break;  // 첫 번째 일치하는 invocation 사용
                        }
                    }
                    
                    // 일치하는 invocation이 없으면 마지막 invocation 사용 (fallback)
                    if (directInvocation == null && !invocationsInStmt.isEmpty()) {
                        directInvocation = invocationsInStmt.get(invocationsInStmt.size() - 1);
                    }
                }
                
                // Step 3: invocation이 일치하는지 확인
                if (directInvocation != null) {
                    String invName = directInvocation.getExecutable().getSimpleName();
                    
                    if (invName.equals(throwingMethodName)) {
                        // 클래스명 호환성 체크
                        boolean classMatches = true;
                        if (directInvocation.getExecutable().getDeclaringType() != null) {
                            String invClassName = directInvocation.getExecutable().getDeclaringType().getQualifiedName();
                            classMatches = classNameCompatible(invClassName, throwingClassName);
                            
                            // 클래스명 불일치 시에도 메서드명이 일치하면 허용
                            if (!classMatches) {
                                classMatches = true;
                            }
                        }
                        
                        if (classMatches && !isAlreadyWrappedInTryCatch(directInvocation)) {
                            if (DEBUG_ORACLE_TRANSFORM) {
                                String stmtStr = stmt.toString().replace("\n", " ");
                                if (stmtStr.length() > 80) stmtStr = stmtStr.substring(0, 80) + "...";
                                System.out.println("[TryCatchFailAdder] [STMT-MATCH] ✓ Found matching statement #" + stmtIndex);
                                System.out.println("[TryCatchFailAdder] [STMT-MATCH] Statement: " + stmtStr);
                                System.out.println("[TryCatchFailAdder] [STMT-MATCH] Invocation: " + invName);
                            }
                            return stmt;
                        }
                    }
                }
                
                stmtIndex++;
            }
            
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TryCatchFailAdder] [STMT-MATCH] ✗ No matching statement found");
            }
            
        } catch (Exception e) {
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TryCatchFailAdder] [STMT-MATCH] Error: " + e.getMessage());
            }
            e.printStackTrace();
        }
        
        return null;
    }

    /**
     * Stack trace의 메서드/생성자 호출과 정확히 매칭되는 statement 찾기
     * 라인 넘버를 활용하여 다중 호출 중 정확한 invocation 선택
     * 
     * @param ctMethod 대상 메서드
     * @param throwingMethodName throwing 메서드명
     * @param throwingClassName throwing 메서드의 클래스명
     * @param testMethodLineNumber 테스트 메서드의 라인 넘버 (스택 트레이스에서 가져옴)
     * @param executedFileContent 실행된 파일 내용 (동적 생성된 테스트용)
     */
    private static CtStatement findStatementWithThrowingMethodInvocation(CtMethod ctMethod, 
                                                                           String throwingMethodName, 
                                                                           String throwingClassName,
                                                                           int testMethodLineNumber,
                                                                           String executedFileContent) {
         if (ctMethod == null || ctMethod.getBody() == null) {
             return null;
         }
         
         try {
             // 모든 invocation 수집
             List<CtInvocation<?>> allInvocations = ctMethod.getBody()
                 .getElements(new TypeFilter<>(CtInvocation.class));
             
             // throwing method를 호출하는 invocation 찾기
             List<CtInvocation<?>> candidateInvocations = new ArrayList<>();
             
              for (CtInvocation<?> inv : allInvocations) {
                  // 메서드 이름이 일치하는지 확인
                  if (!throwingMethodName.equals(inv.getExecutable().getSimpleName())) {
                      continue;
                  }
                  
                  // 클래스명 호환성 확인 (더 유연한 매칭)
                  boolean classNameMatches = false;
                  if (inv.getExecutable().getDeclaringType() != null) {
                      String invClassName = inv.getExecutable().getDeclaringType().getQualifiedName();
                      
                      // 1) 정확한 클래스 이름 매칭
                      classNameMatches = classNameCompatible(invClassName, throwingClassName);
                      
                      // 2) 매칭 실패 시, 메서드 이름만으로도 인정 (예: Iterator.next vs CSVParser$1.next)
                      if (!classNameMatches) {
                        //   System.out.println("[TryCatchFailAdder]       Class mismatch: " + invClassName + " vs " + 
                        //       throwingClassName + ", but accepting due to method name match: " + throwingMethodName);
                          classNameMatches = true;  // ✅ 메서드 이름이 일치하면 허용
                      }
                  } else {
                      // DeclaringType이 없으면 메서드 이름만으로 판단
                      classNameMatches = true;
                  }
                  
                  if (classNameMatches) {
                      // 이미 try-catch로 감싸진 invocation인지 확인
                      if (isAlreadyWrappedInTryCatch(inv)) {
                          if (DEBUG_ORACLE_TRANSFORM) {
                              System.out.println("[TryCatchFailAdder]       Skipping invocation (already wrapped in try-catch): " + 
                                  inv.getExecutable().getSimpleName());
                          }
                          continue;
                      }
                      candidateInvocations.add(inv);
                  }
              }
             
             // ✅ 항상 출력 (디버깅용)
             if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TryCatchFailAdder]       Found " + candidateInvocations.size() + 
                    " invocations of " + throwingMethodName + " (target line: " + testMethodLineNumber + ")");
             }
             
             // 정확히 하나의 invocation이 있으면 그것을 반환
             if (candidateInvocations.size() == 1) {
                 CtStatement stmt = findContainingStatement(candidateInvocations.get(0));
                 if (stmt != null) {
                     if (DEBUG_ORACLE_TRANSFORM) {
                         System.out.println("[TryCatchFailAdder]       ✓ Exact match: 1 invocation");
                     }
                     return stmt;
                 }
             }
             
              // 여러 개가 있으면 라인 넘버를 활용하여 정확한 것 선택
              if (candidateInvocations.size() > 1) {
                  if (DEBUG_ORACLE_TRANSFORM) {
                      System.out.println("[TryCatchFailAdder]       Found " + candidateInvocations.size() + 
                          " invocations - attempting to match correct one");
                  }
                  
                  CtInvocation<?> selectedInvocation = null;
                  
                  // ✅ STEP 1: executedFileContent 기반 순서 매칭 (동적 생성된 테스트용) - 우선순위 상향
                  if (selectedInvocation == null && executedFileContent != null) {
                      try {
                          String[] lines = executedFileContent.split("\n");
                          
                          if (DEBUG_ORACLE_TRANSFORM) {
                              System.out.println("[TryCatchFailAdder]       [STEP 1.5] Attempting executedFileContent matching");
                              System.out.println("[TryCatchFailAdder]       Target line number: " + testMethodLineNumber);
                              System.out.println("[TryCatchFailAdder]       Total lines in executedFileContent: " + lines.length);
                          }
                          
                          // ✅ 개선: targetLine 찾기 (범위 체크)
                          int targetLineInFile = testMethodLineNumber;
                          String targetLine = null;
                          
                          if (targetLineInFile > 0 && targetLineInFile <= lines.length) {
                              targetLine = lines[targetLineInFile - 1].trim();
                              
                              if (DEBUG_ORACLE_TRANSFORM) {
                                  System.out.println("[TryCatchFailAdder]       Target line [" + targetLineInFile + "]: " + 
                                      (targetLine.length() > 80 ? targetLine.substring(0, 80) + "..." : targetLine));
                              }
                          } else {
                              // 라인 번호 범위 초과 - 동적 생성된 파일에서 메서드 스캔
                              if (DEBUG_ORACLE_TRANSFORM) {
                                  System.out.println("[TryCatchFailAdder]       Line number " + testMethodLineNumber + 
                                      " out of range (1-" + lines.length + "), scanning for method content");
                              }
                          }
                          
                          // ✅ STEP 1-A: targetLine이 있으면 그것으로 매칭
                          if (targetLine != null && !targetLine.isEmpty()) {
                              if (DEBUG_ORACLE_TRANSFORM) {
                                  System.out.println("[TryCatchFailAdder]       Trying to match " + candidateInvocations.size() + 
                                      " invocations to target line");
                              }
                              
                              // 각 invocation을 문자열로 변환하여 매칭
                              for (int idx = 0; idx < candidateInvocations.size(); idx++) {
                                  CtInvocation<?> inv = candidateInvocations.get(idx);
                                  String invStr = inv.toString().trim();
                                  
                                  // 정확한 invocation 문자열이 targetLine에 포함되는지 확인
                                  if (targetLine.contains(invStr)) {
                                      selectedInvocation = inv;
                                      if (DEBUG_ORACLE_TRANSFORM) {
                                          System.out.println("[TryCatchFailAdder]       ✓ Matched invocation #" + idx + 
                                              " (exact match in target line)");
                                      }
                                      break;
                                  }
                              }
                          }
                          
                          // ✅ STEP 1-B: 실패하면 메서드 내 모든 invocation 찾기
                          if (selectedInvocation == null) {
                              if (DEBUG_ORACLE_TRANSFORM) {
                                  System.out.println("[TryCatchFailAdder]       Exact line match failed, scanning method body...");
                              }
                              
                              // 메서드 시작 라인 찾기
                              int methodStartLine = -1;
                              for (int i = 0; i < lines.length; i++) {
                                  String line = lines[i].trim();
                                  if (line.contains("void " + throwingMethodName + "(") || 
                                      line.contains("public void " + throwingMethodName)) {
                                      methodStartLine = i;
                                      break;
                                  }
                              }
                              
                              if (methodStartLine >= 0) {
                                  if (DEBUG_ORACLE_TRANSFORM) {
                                      System.out.println("[TryCatchFailAdder]       Found method at line " + (methodStartLine + 1));
                                  }
                                  
                                  // 메서드 내에서 각 invocation 찾기 (나타나는 순서대로)
                                  java.util.List<Integer> invocationLines = new java.util.ArrayList<>();
                                  for (int i = methodStartLine; i < lines.length && i < methodStartLine + 50; i++) {
                                      String line = lines[i];
                                      for (CtInvocation<?> inv : candidateInvocations) {
                                          String invShort = inv.getExecutable().getSimpleName() + "(";
                                          if (line.contains(invShort)) {
                                              invocationLines.add(i);
                                              break;
                                          }
                                      }
                                  }
                                  
                                  if (DEBUG_ORACLE_TRANSFORM) {
                                      System.out.println("[TryCatchFailAdder]       Found " + invocationLines.size() + 
                                          " invocation lines in method body");
                                  }
                                  
                                  // 가장 가까운 invocation 라인 찾기
                                  if (!invocationLines.isEmpty()) {
                                      int closestLine = invocationLines.get(0);
                                      int minDiff = Math.abs(closestLine - (testMethodLineNumber - 1));
                                      int closestIdx = 0;
                                      
                                      for (int i = 1; i < invocationLines.size(); i++) {
                                          int diff = Math.abs(invocationLines.get(i) - (testMethodLineNumber - 1));
                                          if (diff < minDiff) {
                                              minDiff = diff;
                                              closestLine = invocationLines.get(i);
                                              closestIdx = i;
                                          }
                                      }
                                      
                                      if (closestIdx < candidateInvocations.size()) {
                                          selectedInvocation = candidateInvocations.get(closestIdx);
                                          if (DEBUG_ORACLE_TRANSFORM) {
                                              System.out.println("[TryCatchFailAdder]       ✓ Selected invocation #" + closestIdx + 
                                                  " (closest to target line, diff: " + minDiff + " lines)");
                                          }
                                      }
                                  }
                              }
                          }
                          
                      } catch (Exception e) {
                          if (DEBUG_ORACLE_TRANSFORM) {
                              System.out.println("[TryCatchFailAdder]       executedFileContent matching failed: " + e.getMessage());
                          }
                          e.printStackTrace();
                      }
                  }
                  
                  // ✅ STEP 2: 정확한 라인 넘버 매칭 (SourcePosition 사용)
                  if (selectedInvocation == null) {
                      if (DEBUG_ORACLE_TRANSFORM) {
                          System.out.println("[TryCatchFailAdder]       [STEP 2] Attempting SourcePosition line matching");
                      }
                      
                      for (CtInvocation<?> inv : candidateInvocations) {
                          SourcePosition pos = inv.getPosition();
                          if (pos != null && pos.isValidPosition()) {
                              int invLine = pos.getLine();
                              
                              // 정확한 라인 매칭 또는 범위 내 매칭
                              if (invLine == testMethodLineNumber || 
                                  (pos.getLine() <= testMethodLineNumber && testMethodLineNumber <= pos.getEndLine())) {
                                  selectedInvocation = inv;
                                  if (DEBUG_ORACLE_TRANSFORM) {
                                      System.out.println("[TryCatchFailAdder]       ✓ Matched at line " + invLine);
                                  }
                                  break;
                              }
                          }
                      }
                  }
                  
                  // ✅ STEP 3: 모든 매칭 실패시 첫 번째 선택
                  if (selectedInvocation == null) {
                      selectedInvocation = candidateInvocations.get(0);
                      if (DEBUG_ORACLE_TRANSFORM) {
                          System.out.println("[TryCatchFailAdder]       All matching failed - using first invocation as fallback");
                      }
                  }
                 
                 CtStatement stmt = findContainingStatement(selectedInvocation);
                 if (stmt != null) {
                     if (DEBUG_ORACLE_TRANSFORM) {
                         System.out.println("[TryCatchFailAdder]       ✓ Selected invocation for wrapping");
                     }
                     return stmt;
                 }
             }
             
         } catch (Exception e) {
             if (DEBUG_ORACLE_TRANSFORM) {
                 System.out.println("[TryCatchFailAdder]       Exception: " + e.getMessage());
                 e.printStackTrace();
             }
         }
         
         return null;
     }
    
    /**
     * Backward compatibility overload with testMethodName
     */
    private static CtCatch createCatcher(Factory factory, String errorType, String originalErrorType, 
                                        StackTraceElement verificationFrame, boolean foundMatch) {
        return createCatcher(factory, errorType, originalErrorType, verificationFrame, foundMatch, null);
    }

    private static CtStatement nearestNonBlockStmt(CtElement elem) {
        CtElement p = elem;
        try {
            while (p != null && !(p instanceof CtMethod)) {
                if (p instanceof CtStatement && !(p instanceof CtBlock)) {
                    return (CtStatement) p;
                }
                p = p.getParent();
            }
        } catch (Exception e) {
            // elem 자체가 statement면 반환
            if (elem instanceof CtStatement && !(elem instanceof CtBlock)) {
                return (CtStatement) elem;
            }
        }
        return null;
    }

    private static CtStatement findStmtCoveringLine(CtMethod method, int line) {
        if (method == null || method.getBody() == null) return null;
        CtStatement best = null;

        for (CtStatement st : method.getBody().getStatements()) {
            for (CtStatement leaf : st.getElements(new TypeFilter<>(CtStatement.class))) {
                if (leaf instanceof CtBlock) continue;
                SourcePosition pos = leaf.getPosition();
                if (pos != null && pos.isValidPosition()) {
                    if (pos.getLine() <= line && line <= pos.getEndLine()) {
                        // 더 작은(좁은) 범위를 선택
                        if (best == null) best = leaf;
                        else {
                            SourcePosition bpos = best.getPosition();
                            int bSpan = (bpos.getEndLine() - bpos.getLine());
                            int lSpan = (pos.getEndLine() - pos.getLine());
                            if (lSpan <= bSpan) {
                                best = leaf;
                            }
                        }
                    }
                }
            }
        }
        
        return best;
    }
    
    /**
     * 실행된 파일 내용을 사용해서 정확한 statement 찾기
     * 
     * @param ctMethod            테스트 메서드
     * @param targetLineNumber    Stack trace의 라인 번호 (executed file 기준)
     * @param executedFileContent 실행된 파일의 전체 내용
     * @param matchingInvocations 매칭 가능한 invocation 목록
     * @param helperMethodName    Stack trace의 helper method 이름 (실패한 메서드)
     * @return 매칭되는 statement 또는 null
     */
    private static CtStatement findStmtUsingExecutedFileContent(CtMethod ctMethod, int targetLineNumber,
            String executedFileContent, List<CtInvocation<?>> matchingInvocations, String helperMethodName) {
        try {
            String[] executedLines = executedFileContent.split("\n");
            if (targetLineNumber < 1 || targetLineNumber > executedLines.length) {
                // System.out.println("[TRY-CATCH-DEBUG] Target line " + targetLineNumber + "
                // out of range (1-" + executedLines.length + ")");
                return null;
            }

            // 1. executedFileContent에서 method 시작 라인 찾기
            String methodName = ctMethod.getSimpleName();
            int methodStartLineInExecutedFile = -1;
            for (int i = 0; i < executedLines.length; i++) {
                String line = executedLines[i].trim();
                // "public void methodName() throws" 패턴 찾기
                if (line.contains("void " + methodName + "(") || line.contains("void " + methodName + " (")) {
                    methodStartLineInExecutedFile = i + 1; // 1-based
                    // System.out.println("[TRY-CATCH-DEBUG] Found method start at executed file
                    // line " + methodStartLineInExecutedFile + ": " + line);
                    break;
                }
            }

            if (methodStartLineInExecutedFile == -1) {
                // System.out.println("[TRY-CATCH-DEBUG] Could not find method start in executed
                // file");
                return null;
            }

            // 2. Stack trace line을 testMethod relative line으로 변환
            // testMethod는 annotation부터 시작하므로 @Test 라인 찾기
            int annotationLineInExecutedFile = methodStartLineInExecutedFile - 1;
            while (annotationLineInExecutedFile > 0) {
                String line = executedLines[annotationLineInExecutedFile - 1].trim();
                if (line.startsWith("@Test") || line.startsWith("@org.junit.Test")) {
                    break;
                }
                annotationLineInExecutedFile--;
            }

            // testMethod의 line 0 = @Test annotation line in executed file
            int testMethodRelativeLine = targetLineNumber - annotationLineInExecutedFile;
            // System.out.println("[TRY-CATCH-DEBUG] Stack trace line " + targetLineNumber +
            // " → testMethod relative line " + testMethodRelativeLine);
            // System.out.println("[TRY-CATCH-DEBUG] (annotationLine in executedFile: " +
            // annotationLineInExecutedFile + ")");

            // 3. testMethod.toString()에서 해당 라인의 source code 찾기
            String[] testMethodLines = ctMethod.toString().split("\n");
            if (testMethodRelativeLine < 0 || testMethodRelativeLine >= testMethodLines.length) {
                // System.out.println("[TRY-CATCH-DEBUG] testMethod relative line " +
                // testMethodRelativeLine + " out of range (0-" + (testMethodLines.length - 1) +
                // ")");
                return null;
            }

            String targetLineSource = testMethodLines[testMethodRelativeLine].trim();
            // System.out.println("[TRY-CATCH-DEBUG] testMethod line " +
            // testMethodRelativeLine + ": " + targetLineSource);

            // 4. Line이 메서드 종료 괄호나 빈 줄이면, helper method name으로 찾기
            if (targetLineSource.equals("}") || targetLineSource.isEmpty() || targetLineSource.equals("{")) {
                // System.out.println("[TRY-CATCH-DEBUG] Target line is structural (}, {, or
                // empty) - selecting last invocation of: " + helperMethodName);

                if (!matchingInvocations.isEmpty()) {
                    CtInvocation<?> lastInvocation = matchingInvocations.get(matchingInvocations.size() - 1);
                    CtStatement stmt = findContainingStatement(lastInvocation);
                    if (stmt != null) {
                        // System.out.println("[TRY-CATCH-DEBUG] ✓ Selected last invocation");
                        return stmt;
                    }
                }
            }

            // 5. testMethod의 각 statement를 line number로 매핑 (순서 보장을 위해 List 사용)
            List<CtStatement> bodyStmts = ctMethod.getBody().getStatements();
            java.util.List<Integer> mappedLines = new java.util.ArrayList<>();
            java.util.List<CtStatement> mappedStmts = new java.util.ArrayList<>();

            for (CtStatement stmt : bodyStmts) {
                String stmtSource = stmt.toString();
                String stmtFirstLine = stmtSource.split("\n")[0].trim();

                // testMethod.toString()에서 이 statement의 첫 라인 찾기
                for (int lineIdx = 0; lineIdx < testMethodLines.length; lineIdx++) {
                    String currentLine = testMethodLines[lineIdx].trim();

                    if (currentLine.equals(stmtFirstLine) ||
                            (stmtFirstLine.length() > 10 && currentLine.contains(stmtFirstLine.substring(0, 10)))) {

                        // 중복 방지: 이미 매핑된 라인은 건너뛰고 다음 매칭 찾기
                        if (mappedLines.contains(lineIdx)) {
                            continue; // 이 line은 이미 매핑됨, 다음 line 체크
                        }

                        // 매핑
                        mappedLines.add(lineIdx);
                        mappedStmts.add(stmt);
                        // System.out.println("[TRY-CATCH-DEBUG] Mapped statement at testMethod line " +
                        // lineIdx + ": " +
                        // stmtFirstLine.substring(0, Math.min(60, stmtFirstLine.length())));
                        break;
                    }
                }
            }

            // 6. testMethodRelativeLine에 해당하는 statement 찾기 (첫 번째 매칭 사용)
            for (int i = 0; i < mappedLines.size(); i++) {
                if (mappedLines.get(i) == testMethodRelativeLine) {
                    CtStatement targetStmt = mappedStmts.get(i);
                    // System.out.println("[TRY-CATCH-DEBUG] ✓ Found exact statement at testMethod
                    // line " + testMethodRelativeLine);

                    // 이 statement가 matchingInvocations 중 하나를 포함하는지 확인
                    for (CtInvocation<?> inv : matchingInvocations) {
                        CtStatement containingStmt = findContainingStatement(inv);
                        if (containingStmt == targetStmt) {
                            // System.out.println("[TRY-CATCH-DEBUG] ✓ Statement contains the matching
                            // invocation");
                            return containingStmt;
                        }
                    }

                    // invocation이 아니어도 해당 statement 반환
                    return targetStmt;
                }
            }

            // System.out.println("[TRY-CATCH-DEBUG] No statement matched testMethod line "
            // + testMethodRelativeLine);
        } catch (Exception e) {
            // System.out.println("[TRY-CATCH-DEBUG] Failed to match using executed file
            // content: " + e.getMessage());
            e.printStackTrace();
        }

        return null;
    }

    /**
     * 실행된 파일 내용을 사용해서 정확한 statement 찾기 (Constructor 버전)
     */
    private static CtStatement findStmtUsingExecutedFileContentForConstructor(CtMethod ctMethod, int targetLineNumber,
            String executedFileContent, List<CtConstructorCall<?>> matchingConstructorCalls) {
        try {
            String[] executedLines = executedFileContent.split("\n");
            if (targetLineNumber < 1 || targetLineNumber > executedLines.length) {
                // System.out.println("[TRY-CATCH-DEBUG] Target line " + targetLineNumber + "
                // out of range (1-" + executedLines.length + ")");
                return null;
            }

            // 1. executedFileContent에서 method 시작 라인 찾기
            String methodName = ctMethod.getSimpleName();
            int methodStartLineInExecutedFile = -1;
            for (int i = 0; i < executedLines.length; i++) {
                String line = executedLines[i].trim();
                if (line.contains("void " + methodName + "(") || line.contains("void " + methodName + " (")) {
                    methodStartLineInExecutedFile = i + 1; // 1-based
                    // System.out.println("[TRY-CATCH-DEBUG] Found method start at executed file
                    // line " + methodStartLineInExecutedFile);
                    break;
                }
            }

            if (methodStartLineInExecutedFile == -1) {
                // System.out.println("[TRY-CATCH-DEBUG] Could not find method start in executed
                // file");
                return null;
            }

            // 2. @Test annotation line 찾기
            int annotationLineInExecutedFile = methodStartLineInExecutedFile - 1;
            while (annotationLineInExecutedFile > 0) {
                String line = executedLines[annotationLineInExecutedFile - 1].trim();
                if (line.startsWith("@Test") || line.startsWith("@org.junit.Test")) {
                    break;
                }
                annotationLineInExecutedFile--;
            }

            // 3. testMethod relative line 계산
            int testMethodRelativeLine = targetLineNumber - annotationLineInExecutedFile;
            // System.out.println("[TRY-CATCH-DEBUG] Stack trace line " + targetLineNumber +
            // " → testMethod relative line " + testMethodRelativeLine);

            // 4. testMethod.toString()에서 해당 라인의 source code 찾기
            String[] testMethodLines = ctMethod.toString().split("\n");
            if (testMethodRelativeLine < 0 || testMethodRelativeLine >= testMethodLines.length) {
                // System.out.println("[TRY-CATCH-DEBUG] testMethod relative line out of
                // range");
                return null;
            }

            String targetLineSource = testMethodLines[testMethodRelativeLine].trim();
            // System.out.println("[TRY-CATCH-DEBUG] testMethod line " +
            // testMethodRelativeLine + ": " + targetLineSource);

            // 5. testMethod의 각 statement를 line number로 매핑 (순서 보장을 위해 List 사용)
            List<CtStatement> bodyStmts = ctMethod.getBody().getStatements();
            java.util.List<Integer> mappedLines = new java.util.ArrayList<>();
            java.util.List<CtStatement> mappedStmts = new java.util.ArrayList<>();

            for (CtStatement stmt : bodyStmts) {
                String stmtSource = stmt.toString();
                String stmtFirstLine = stmtSource.split("\n")[0].trim();

                // testMethod.toString()에서 이 statement의 첫 라인 찾기
                for (int lineIdx = 0; lineIdx < testMethodLines.length; lineIdx++) {
                    String currentLine = testMethodLines[lineIdx].trim();

                    if (currentLine.equals(stmtFirstLine) ||
                            (stmtFirstLine.length() > 10 && currentLine.contains(stmtFirstLine.substring(0, 10)))) {

                        // 중복 방지: 이미 매핑된 라인은 건너뛰고 다음 매칭 찾기
                        if (mappedLines.contains(lineIdx)) {
                            continue; // 이 line은 이미 매핑됨, 다음 line 체크
                        }

                        // 매핑
                        mappedLines.add(lineIdx);
                        mappedStmts.add(stmt);
                        // System.out.println("[TRY-CATCH-DEBUG] Mapped constructor statement at
                        // testMethod line " + lineIdx + ": " +
                        // stmtFirstLine.substring(0, Math.min(60, stmtFirstLine.length())));
                        break;
                    }
                }
            }

            // 6. testMethodRelativeLine에 해당하는 statement 찾기 (첫 번째 매칭 사용)
            for (int i = 0; i < mappedLines.size(); i++) {
                if (mappedLines.get(i) == testMethodRelativeLine) {
                    CtStatement targetStmt = mappedStmts.get(i);
                    // System.out.println("[TRY-CATCH-DEBUG] ✓ Found exact statement at testMethod
                    // line " + testMethodRelativeLine);

                    // 이 statement가 matchingConstructorCalls 중 하나를 포함하는지 확인
                    for (CtConstructorCall<?> call : matchingConstructorCalls) {
                        CtStatement containingStmt = findContainingStatement(call);
                        if (containingStmt == targetStmt) {
                            // System.out.println("[TRY-CATCH-DEBUG] ✓ Statement contains the matching constructor");
                            return containingStmt;
                        }
                    }

                    // constructor가 아니어도 해당 statement 반환
                    return targetStmt;
                }
            }

            // System.out.println("[TRY-CATCH-DEBUG] No statement matched testMethod line "
            // + testMethodRelativeLine);
        } catch (Exception e) {
            // System.out.println("[TRY-CATCH-DEBUG] Failed to match using executed file
            // content: " + e.getMessage());
            e.printStackTrace();
        }

        return null;
    }

    /**
     * 동적 생성된 테스트에서 소스 위치 정보가 불완전할 때 사용하는 공격적 라인 매칭
     * method.toString()을 라인별로 분석해서 target line에 해당하는 statement 찾기
     */
    /**
     * executedFileContent를 사용하여 중첩된 statement까지 찾기
     */
    private static CtStatement findStmtUsingExecutedFileContentWithNested(CtMethod ctMethod, int targetLineNumber,
            String executedFileContent) {
        try {
            String[] executedLines = executedFileContent.split("\n");
            if (targetLineNumber < 1 || targetLineNumber > executedLines.length) {
                return null;
            }

            // 1. executedFileContent에서 method 시작 라인 찾기
            String methodName = ctMethod.getSimpleName();
            int methodStartLineInExecutedFile = -1;
            for (int i = 0; i < executedLines.length; i++) {
                String line = executedLines[i].trim();
                if (line.contains("void " + methodName + "(") || line.contains("void " + methodName + " (")) {
                    methodStartLineInExecutedFile = i + 1; // 1-based
                    break;
                }
            }

            if (methodStartLineInExecutedFile == -1) {
                return null;
            }

            // 2. @Test annotation line 찾기
            int annotationLineInExecutedFile = methodStartLineInExecutedFile - 1;
            while (annotationLineInExecutedFile > 0) {
                String line = executedLines[annotationLineInExecutedFile - 1].trim();
                if (line.startsWith("@Test") || line.startsWith("@org.junit.Test")) {
                    break;
                }
                annotationLineInExecutedFile--;
            }

            // 3. testMethod relative line 계산
            int testMethodRelativeLine = targetLineNumber - annotationLineInExecutedFile;
            
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TryCatchFailAdder]   Stack trace line " + targetLineNumber + 
                    " → testMethod relative line " + testMethodRelativeLine);
            }

            // 4. testMethod.toString()의 각 라인과 statement 매핑
            String[] testMethodLines = ctMethod.toString().split("\n");
            if (testMethodRelativeLine < 0 || testMethodRelativeLine >= testMethodLines.length) {
                return null;
            }

            String targetLineSource = testMethodLines[testMethodRelativeLine].trim();
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TryCatchFailAdder]   Target line source: " + 
                    (targetLineSource.length() > 60 ? targetLineSource.substring(0, 60) + "..." : targetLineSource));
            }

            // 5. 모든 statement를 수집하고 라인 매핑
            List<CtStatement> allStmts = collectAllStatements(ctMethod.getBody());
            java.util.List<Integer> mappedLines = new java.util.ArrayList<>();
            java.util.List<CtStatement> mappedStmts = new java.util.ArrayList<>();
            java.util.Set<Integer> usedLines = new java.util.HashSet<>();  // 중복 매핑 방지

            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TryCatchFailAdder]   Mapping " + allStmts.size() + " statements to lines...");
            }

            for (CtStatement stmt : allStmts) {
                String stmtSource = stmt.toString();
                String stmtFirstLine = stmtSource.split("\n")[0].trim();

                // testMethod.toString()에서 이 statement의 첫 라인 찾기
                int bestMatchLine = -1;
                int bestMatchScore = 0;  // 매칭 점수 (높을수록 정확)
                
                for (int lineIdx = 0; lineIdx < testMethodLines.length; lineIdx++) {
                    // 이미 사용된 라인은 스킵
                    if (usedLines.contains(lineIdx)) {
                        continue;
                    }
                    
                    String currentLine = testMethodLines[lineIdx].trim();
                    int score = 0;
                    
                    // 1순위: 완전 일치
                    if (currentLine.equals(stmtFirstLine)) {
                        score = 100;
                    }
                    // 2순위: 라인이 statement를 포함 (긴 매칭 우선)
                    else if (currentLine.contains(stmtFirstLine) && stmtFirstLine.length() > 20) {
                        score = 80;
                    }
                    // 3순위: statement가 라인을 포함
                    else if (stmtFirstLine.contains(currentLine) && currentLine.length() > 20) {
                        score = 70;
                    }
                    // 4순위: 부분 매칭 (최소 30자)
                    else if (stmtFirstLine.length() > 30 && currentLine.contains(stmtFirstLine.substring(0, 30))) {
                        score = 50;
                    }
                    
                    if (score > bestMatchScore) {
                        bestMatchScore = score;
                        bestMatchLine = lineIdx;
                    }
                }
                
                if (bestMatchLine != -1 && bestMatchScore >= 50) {
                    mappedLines.add(bestMatchLine);
                    mappedStmts.add(stmt);
                    usedLines.add(bestMatchLine);
                    
                    if (DEBUG_ORACLE_TRANSFORM) {
                        String preview = stmtFirstLine.length() > 60 ? stmtFirstLine.substring(0, 60) + "..." : stmtFirstLine;
                        System.out.println("[TryCatchFailAdder]     Mapped line " + bestMatchLine + 
                            " (score: " + bestMatchScore + "): " + preview);
                    }
                }
            }

            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TryCatchFailAdder]   Successfully mapped " + mappedLines.size() + 
                    " statements to lines");
                System.out.println("[TryCatchFailAdder]   Target relative line: " + testMethodRelativeLine);
            }

            // 6. target line과 정확히 일치하는 statement 찾기
            for (int i = 0; i < mappedLines.size(); i++) {
                if (mappedLines.get(i) == testMethodRelativeLine) {
                    if (DEBUG_ORACLE_TRANSFORM) {
                        System.out.println("[TryCatchFailAdder]   ✓ Found exact match at line " + testMethodRelativeLine);
                        String stmtPreview = mappedStmts.get(i).toString().replace("\n", " ");
                        if (stmtPreview.length() > 80) stmtPreview = stmtPreview.substring(0, 80) + "...";
                        System.out.println("[TryCatchFailAdder]   Statement: " + stmtPreview);
                    }
                    return mappedStmts.get(i);
                }
            }

            // 7. 가장 가까운 statement 찾기 (허용 범위를 1줄로 줄임)
            int closestIdx = -1;
            int minDiff = Integer.MAX_VALUE;
            for (int i = 0; i < mappedLines.size(); i++) {
                int diff = Math.abs(mappedLines.get(i) - testMethodRelativeLine);
                if (diff < minDiff) {
                    minDiff = diff;
                    closestIdx = i;
                }
            }

            if (closestIdx != -1 && minDiff <= 1) {  // ✅ 2 → 1로 변경 (정확도 향상)
                if (DEBUG_ORACLE_TRANSFORM) {
                    System.out.println("[TryCatchFailAdder]   Found closest match (diff: " + minDiff + " lines)");
                    System.out.println("[TryCatchFailAdder]   Mapped line: " + mappedLines.get(closestIdx));
                    String stmtPreview = mappedStmts.get(closestIdx).toString().replace("\n", " ");
                    if (stmtPreview.length() > 80) stmtPreview = stmtPreview.substring(0, 80) + "...";
                    System.out.println("[TryCatchFailAdder]   Statement: " + stmtPreview);
                }
                return mappedStmts.get(closestIdx);
            } else if (closestIdx != -1) {
                if (DEBUG_ORACLE_TRANSFORM) {
                    System.out.println("[TryCatchFailAdder]   ✗ Closest match is too far (diff: " + minDiff + 
                        " lines, threshold: 1)");
                    System.out.println("[TryCatchFailAdder]   Not using this match to avoid incorrect wrapping");
                }
            }

        } catch (Exception e) {
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TryCatchFailAdder]   Error in findStmtUsingExecutedFileContentWithNested: " + e.getMessage());
            }
        }

        return null;
    }
    
    /**
     * ✅ NEW: Statement 객체 기반으로 실패한 statement 찾기 (라인 번호 무관)
     * 
     * 이 메서드는 다음 순서로 statement를 찾습니다:
     * 1. 모든 statement를 수집
     * 2. 각 statement와 targetStatement를 비교 (equals 기반)
     * 3. 일치하는 statement 반환
     */
    private static CtStatement findStatementByEquivalence(CtMethod ctMethod, CtStatement targetStatement) {
        if (targetStatement == null) {
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TryCatchFailAdder] [EQUIVALENCE] Target statement is null, cannot search");
            }
            return null;
        }
        
        if (DEBUG_ORACLE_TRANSFORM) {
            System.out.println("[TryCatchFailAdder] [EQUIVALENCE] Searching for equivalent statement");
            String targetSig = normalizeStatementSignature(targetStatement.toString());
            System.out.println("[TryCatchFailAdder] [EQUIVALENCE] Target signature: " + 
                (targetSig.length() > 100 ? targetSig.substring(0, 100) + "..." : targetSig));
        }
        
        // 메서드의 모든 statement 수집
        List<CtStatement> allStatements = collectAllStatements(ctMethod.getBody());
        
        if (DEBUG_ORACLE_TRANSFORM) {
            System.out.println("[TryCatchFailAdder] [EQUIVALENCE] Total statements in method: " + allStatements.size());
        }
        
        // 각 statement와 비교
        for (int i = 0; i < allStatements.size(); i++) {
            CtStatement stmt = allStatements.get(i);
            
            if (isStatementEquivalent(stmt, targetStatement)) {
                if (DEBUG_ORACLE_TRANSFORM) {
                    String stmtSig = normalizeStatementSignature(stmt.toString());
                    System.out.println("[TryCatchFailAdder] [EQUIVALENCE] ✓ Found matching statement at index " + i);
                    System.out.println("[TryCatchFailAdder] [EQUIVALENCE]   Signature: " + 
                        (stmtSig.length() > 100 ? stmtSig.substring(0, 100) + "..." : stmtSig));
                }
                return stmt;
            }
        }
        
        if (DEBUG_ORACLE_TRANSFORM) {
            System.out.println("[TryCatchFailAdder] [EQUIVALENCE] ✗ No matching statement found");
        }
        
        return null;
    }
    
    /**
     * ✅ NEW: Stack trace 라인과 executedFileContent 라인의 불일치 분석
     */
    private static void analyzeLineDiscrepancy(StackTraceElement[] stackTrace, 
                                              String executedFileContent,
                                              String testMethodName) {
        // 테스트 메서드 프레임 찾기
        StackTraceElement testFrame = null;
        for (StackTraceElement frame : stackTrace) {
            if (frame.getMethodName().equals(testMethodName) || 
                frame.getClassName().contains("_P_") || 
                frame.getClassName().contains("_M_")) {
                if (frame.getLineNumber() > 0) {
                    testFrame = frame;
                    break;
                }
            }
        }
        
        if (testFrame == null) {
            System.out.println("[TryCatchFailAdder]   [ANALYSIS] Test frame not found in stack trace");
            return;
        }
        
        int stackTraceLineNum = testFrame.getLineNumber();
        System.out.println("[TryCatchFailAdder]   [ANALYSIS] Stack trace line: " + stackTraceLineNum);
        
        // executedFileContent에서 해당 라인 찾기
        String[] lines = executedFileContent.split("\n");
        System.out.println("[TryCatchFailAdder]   [ANALYSIS] Total lines in executedFileContent: " + lines.length);
        
        // 메서드 시작 위치 찾기
        int methodStartLine = -1;
        for (int i = 0; i < lines.length; i++) {
            String line = lines[i].trim();
            if ((line.contains("void " + testMethodName) || 
                 line.contains("public void " + testMethodName)) && 
                line.contains("(")) {
                methodStartLine = i + 1;
                break;
            }
        }
        
        System.out.println("[TryCatchFailAdder]   [ANALYSIS] Method start line: " + 
            (methodStartLine > 0 ? methodStartLine : "NOT FOUND"));
        
        // 범위 체크
        if (stackTraceLineNum <= 0 || stackTraceLineNum > lines.length) {
            System.out.println("[TryCatchFailAdder]   [ANALYSIS] ⚠️  Line number OUT OF RANGE");
            System.out.println("[TryCatchFailAdder]   [ANALYSIS] Stack trace says: " + stackTraceLineNum + 
                ", but executedFileContent only has " + lines.length + " lines");
            
            // 메서드 내 라인들 출력
            if (methodStartLine > 0) {
                System.out.println("[TryCatchFailAdder]   [ANALYSIS] Method body lines:");
                int end = Math.min(lines.length, methodStartLine + 30);
                for (int i = methodStartLine - 1; i < end; i++) {
                    System.out.println("[TryCatchFailAdder]     [" + (i + 1) + "] " + 
                        (lines[i].length() > 80 ? lines[i].substring(0, 80) + "..." : lines[i]));
                }
            }
        } else {
            String targetLine = lines[stackTraceLineNum - 1];
            System.out.println("[TryCatchFailAdder]   [ANALYSIS] Target line content: " + 
                (targetLine.length() > 100 ? targetLine.substring(0, 100) + "..." : targetLine));
            
            // 주변 컨텍스트 출력
            System.out.println("[TryCatchFailAdder]   [ANALYSIS] Context (lines " + 
                Math.max(1, stackTraceLineNum - 2) + "-" + Math.min(lines.length, stackTraceLineNum + 2) + "):");
            int start = Math.max(0, stackTraceLineNum - 3);
            int end = Math.min(lines.length, stackTraceLineNum + 3);
            for (int i = start; i < end; i++) {
                String marker = (i == stackTraceLineNum - 1) ? " ← STACK TRACE" : "";
                System.out.println("[TryCatchFailAdder]     [" + (i + 1) + "] " + lines[i] + marker);
            }
        }
    }
    
    /**
     * ✅ NEW: 두 Statement가 동등한지 비교 (라인 번호 무관)
     * - equals() 직접 비교
     * - toString() 시그니처 비교
     */
    public static boolean isStatementEquivalent(CtStatement stmt1, CtStatement stmt2) {
        if (stmt1 == null || stmt2 == null) {
            return false;
        }
        
        // Method 1: 객체 직접 비교 (메모리 주소)
        if (stmt1 == stmt2) {
            return true;
        }
        
        // Method 2: Spoon equals() 비교 (내용 비교)
        try {
            if (stmt1.equals(stmt2)) {
                return true;
            }
        } catch (Exception e) {
            // equals() 실패 무시
        }
        
        // Method 3: 문자열 시그니처 비교 (정규화된 비교)
        try {
            String sig1 = normalizeStatementSignature(stmt1.toString());
            String sig2 = normalizeStatementSignature(stmt2.toString());
            
            if (!sig1.isEmpty() && sig1.equals(sig2)) {
                if (DEBUG_ORACLE_TRANSFORM) {
                    System.out.println("[TryCatchFailAdder]   ✓ Statements match by signature comparison");
                }
                return true;
            }
        } catch (Exception e) {
            // 시그니처 비교 실패 무시
        }
        
        return false;
    }
    
    /**
     * Statement 시그니처 정규화 (비교용)
     * - 공백 정규화
     * - 새줄 제거
     * - trim()
     */
    private static String normalizeStatementSignature(String stmt) {
        if (stmt == null) return "";
        // 모든 공백 정규화
        String normalized = stmt.replaceAll("\\s+", " ").trim();
        // 세미콜론 제거 (선택사항)
        normalized = normalized.replaceAll(";\\s*$", "");
        return normalized;
    }
    
    /**
     * 재귀적으로 모든 statement를 수집 (중첩된 for/if/while 등 포함)
     */
    private static List<CtStatement> collectAllStatements(CtBlock<?> block) {
        List<CtStatement> result = new ArrayList<>();
        if (block == null) return result;
        
        for (CtStatement stmt : block.getStatements()) {
            result.add(stmt);
            
            // For loop 내부 검사
            if (stmt instanceof CtFor) {
                CtFor forLoop = (CtFor) stmt;
                if (forLoop.getBody() instanceof CtBlock) {
                    result.addAll(collectAllStatements((CtBlock<?>) forLoop.getBody()));
                }
            }
            // Foreach loop 내부 검사
            else if (stmt instanceof CtForEach) {
                CtForEach forEach = (CtForEach) stmt;
                if (forEach.getBody() instanceof CtBlock) {
                    result.addAll(collectAllStatements((CtBlock<?>) forEach.getBody()));
                }
            }
            // While loop 내부 검사
            else if (stmt instanceof CtWhile) {
                CtWhile whileLoop = (CtWhile) stmt;
                if (whileLoop.getBody() instanceof CtBlock) {
                    result.addAll(collectAllStatements((CtBlock<?>) whileLoop.getBody()));
                }
            }
            // Do-While loop 내부 검사
            else if (stmt instanceof CtDo) {
                CtDo doLoop = (CtDo) stmt;
                if (doLoop.getBody() instanceof CtBlock) {
                    result.addAll(collectAllStatements((CtBlock<?>) doLoop.getBody()));
                }
            }
            // If statement 내부 검사
            else if (stmt instanceof CtIf) {
                CtIf ifStmt = (CtIf) stmt;
                if (ifStmt.getThenStatement() instanceof CtBlock) {
                    result.addAll(collectAllStatements((CtBlock<?>) ifStmt.getThenStatement()));
                }
                if (ifStmt.getElseStatement() instanceof CtBlock) {
                    result.addAll(collectAllStatements((CtBlock<?>) ifStmt.getElseStatement()));
                }
            }
            // Try-Catch 내부 검사
            else if (stmt instanceof CtTry) {
                CtTry tryStmt = (CtTry) stmt;
                if (tryStmt.getBody() instanceof CtBlock) {
                    result.addAll(collectAllStatements((CtBlock<?>) tryStmt.getBody()));
                }
                for (CtCatch catcher : tryStmt.getCatchers()) {
                    if (catcher.getBody() instanceof CtBlock) {
                        result.addAll(collectAllStatements((CtBlock<?>) catcher.getBody()));
                    }
                }
                if (tryStmt.getFinalizer() instanceof CtBlock) {
                    result.addAll(collectAllStatements((CtBlock<?>) tryStmt.getFinalizer()));
                }
            }
            // Switch statement 내부 검사
            else if (stmt instanceof CtSwitch) {
                CtSwitch<?> switchStmt = (CtSwitch<?>) stmt;
                for (CtCase<?> caseStmt : switchStmt.getCases()) {
                    if (caseStmt.getStatements() != null) {
                        for (CtStatement caseBodyStmt : caseStmt.getStatements()) {
                            result.add(caseBodyStmt);
                        }
                    }
                }
            }
        }
        
        return result;
    }
    
    private static CtStatement findStmtCoveringLineAggressive(CtMethod method, int targetLine) {
        if (method == null || method.getBody() == null) return null;

        try {
            // 1. 메서드 소스를 라인별로 분리
            String methodSource = method.toString();
            String[] methodLines = methodSource.split("\n");

            // 2. 모든 statement를 재귀적으로 수집 (중첩된 것 포함)
            List<CtStatement> allStmts = collectAllStatements(method.getBody());
            if (allStmts.isEmpty())
                return null;

            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TryCatchFailAdder]   Collected " + allStmts.size() + " statements (including nested)");
            }

            // 3. 각 statement가 메서드 소스의 몇 번째 라인에 있는지 찾기
            java.util.Map<CtStatement, Integer> stmtToRelativeLine = new java.util.HashMap<>();

            for (CtStatement stmt : allStmts) {
                String stmtSource = stmt.toString();
                String stmtFirstLine = stmtSource.split("\n")[0].trim();

                // 메서드 소스에서 이 statement의 첫 라인 찾기
                for (int lineIdx = 0; lineIdx < methodLines.length; lineIdx++) {
                    String currentLine = methodLines[lineIdx].trim();

                    // statement 시작 부분과 매칭
                    if (currentLine.startsWith(stmtFirstLine) ||
                            (stmtFirstLine.length() > 10 && currentLine.contains(stmtFirstLine.substring(0, 10)))) {
                        stmtToRelativeLine.put(stmt, lineIdx);
                        
                        if (DEBUG_ORACLE_TRANSFORM) {
                            String preview = stmtFirstLine.length() > 50 ? stmtFirstLine.substring(0, 50) + "..." : stmtFirstLine;
                            System.out.println("[TryCatchFailAdder]     Mapped line " + lineIdx + ": " + preview);
                        }
                        break;
                    }
                }
            }

            // 3. 메서드 시작 라인 추정
            Integer methodStartLine = null;

            // 먼저 SourcePosition에서 시도
            if (method.getPosition() != null && method.getPosition().isValidPosition()) {
                methodStartLine = method.getPosition().getLine();
                // System.out.println("[TRY-CATCH-DEBUG] Method start line from SourcePosition:
                // " + methodStartLine);
             } else {
                 // 첫 statement의 상대 위치로 역산
                 if (!allStmts.isEmpty() && stmtToRelativeLine.containsKey(allStmts.get(0))) {
                     int firstStmtRelativeLine = stmtToRelativeLine.get(allStmts.get(0));
                     methodStartLine = targetLine - firstStmtRelativeLine;
                    // System.out.println("[TRY-CATCH-DEBUG] Estimated method start line: " +
                    // methodStartLine +
                    // " (target: " + targetLine + ", first stmt relative: " + firstStmtRelativeLine
                    // + ")");
                }
            }

            // 4. target line과 가장 가까운 statement 찾기
            if (methodStartLine != null) {
                CtStatement bestMatch = null;
                int minDiff = Integer.MAX_VALUE;

                for (java.util.Map.Entry<CtStatement, Integer> entry : stmtToRelativeLine.entrySet()) {
                    int absoluteLine = methodStartLine + entry.getValue();
                    int diff = Math.abs(absoluteLine - targetLine);

                    if (diff < minDiff) {
                        minDiff = diff;
                        bestMatch = entry.getKey();
                    }

                    // 정확히 일치하면 바로 반환
                    if (absoluteLine == targetLine) {
                        // System.out.println("[TRY-CATCH-DEBUG] Found exact match at line " +
                        // targetLine);
                        return entry.getKey();
                    }
                }

                if (bestMatch != null) {
                    // System.out.println("[TRY-CATCH-DEBUG] Found closest match (diff: " + minDiff
                    // + ")");
                    return bestMatch;
                }
            }

        } catch (Exception e) {
            // System.out.println("[TRY-CATCH-DEBUG] Line-by-line matching failed: " +
            // e.getMessage());
        }

        // 5. Fallback: 휴리스틱 방식
        // System.out.println("[TRY-CATCH-DEBUG] Falling back to heuristic approach");

        List<CtStatement> allStatements = new ArrayList<>();
        for (CtStatement st : method.getBody().getStatements()) {
            allStatements.add(st);
        }

        // 메서드 호출문 우선
        for (CtStatement stmt : allStatements) {
            if (stmt instanceof CtInvocation ||
                    stmt.getElements(new TypeFilter<>(CtInvocation.class)).size() > 0) {
                return stmt;
            }
        }

        // constructor call
        for (CtStatement stmt : allStatements) {
            if (stmt instanceof CtConstructorCall ||
                stmt.getElements(new TypeFilter<>(CtConstructorCall.class)).size() > 0) {
                return stmt;
            }
        }

        // 첫 번째 non-variable statement
        for (CtStatement stmt : allStatements) {
            if (!(stmt instanceof CtLocalVariable)) {
                return stmt;
            }
        }

        return null;
    }
    
    /**
     * 전체 메서드를 try-catch로 감싸는 새로운 메서드 반환
     * 여러 ambiguous invocation이 있을 때 사용
     */
    private static CtStatement createFullMethodWrapper(CtMethod ctMethod, CtClass<?> testCtClass, 
                                                     Factory factory, String errorType, StackTraceElement[] stackTrace) {
         // 기존의 createFullTryCatchBlock 메서드를 재사용
         // 하지만 이 경우에는 전체 메서드를 반환하는 대신 try 구문만 반환
         CtTry tryBlock = factory.Core().createTry();
         CtBlock<?> tryBody = factory.Core().createBlock();
         
         // 메서드의 모든 기존 구문들을 try 블록에 추가
         List<CtStatement> allStatements = new ArrayList<>(ctMethod.getBody().getStatements());
         for (CtStatement stmt : allStatements) {
             tryBody.addStatement(stmt.clone());
         }
         
         // fail statement 추가
         tryBody.addStatement(factory.Code().createCodeSnippetStatement(
                 "org.junit.Assert.fail(\"Expecting exception: " + errorType + "\")"));
         
         tryBlock.setBody(tryBody);
         
         // Universal approach: Always create catcher for the actual exception that occurred
         StackTraceElement cutFrame = findCUTFrame(stackTrace);
         String testMethodName = ctMethod.getSimpleName();
         String originalErrorType = errorType;  // Store original type for fail message
         
         // ✅ createCatcher 호출에 필요한 모든 파라미터 전달
         tryBlock.addCatcher(createCatcher(factory, errorType, originalErrorType, cutFrame, false, testMethodName));
         
         return tryBlock;
     }

    private static boolean classNameCompatible(String a, String b) {
        if (a.equals(b)) return true;
        // 내부클래스, simple name, 패키지 불일치까지 완화
        if (a.startsWith(b + "$") || b.startsWith(a + "$")) return true;
        String as = a.substring(a.lastIndexOf('.') + 1);
        String bs = b.substring(b.lastIndexOf('.') + 1);
        return as.equals(bs);
    }

    private static CtStatement findFailingStmtSmart(CtMethod ctMethod, StackTraceElement[] stackTrace,
            String executedFileContent) {
        if (ctMethod == null || ctMethod.getBody() == null) return null;

        // System.out.println("[TRY-CATCH-DEBUG] Attempting direct match for failing
        // statement...");
        // 간단한 직접 매칭 시도
        CtStatement directMatch = findFailingStmtByDirectMatch(ctMethod, stackTrace, executedFileContent);
        if (directMatch != null) {
            // System.out.println("[TRY-CATCH-DEBUG] Direct match succeeded");
            return directMatch;
        }

        // 직접 매칭 실패시 전체 메서드를 try-catch로 감싸도록 특별한 마커 반환
        // System.out.println("[TRY-CATCH-DEBUG] Direct match failed - will wrap entire
        // method");
        return new CtBlockImpl(); // 빈 블록을 marker로 사용
    }

    /**
     * Stack trace의 메서드/생성자 호출과 정확히 매칭되는 statement 찾기
     * 
     * ✅ NEW: Statement 기반 매칭을 우선으로 시도!
     */
    private static CtStatement findFailingStmtByDirectMatch(CtMethod ctMethod, StackTraceElement[] stackTrace,
            String executedFileContent) {
        
        if (DEBUG_ORACLE_TRANSFORM) {
            System.out.println("[TryCatchFailAdder] ===== STATEMENT-BASED MATCHING (Priority) =====");
        }
        
        // ✅ NEW: Step 0 - Statement 기반 매칭을 먼저 시도!
        // Stack trace에서 throwing method 정보 추출
        if (stackTrace.length > 0) {
            // Case 1: 테스트 메서드 프레임 자체에서 예외 발생 (stackTrace[0] = 테스트 메서드)
            // Case 2: 이전 프레임이 있는 경우 (stackTrace[i-1] = throwing method)
            
            StackTraceElement testFrame = null;
            StackTraceElement throwingFrame = null;
            
            for (int i = 0; i < stackTrace.length; i++) {
                StackTraceElement frame = stackTrace[i];
                
                // 테스트 프레임: _P_, _M_ 패턴 포함 (동적 생성된 테스트)
                if (frame.getClassName().matches(".*_[PM]_.*") && frame.getLineNumber() > 0) {
                    testFrame = frame;
                    
                    // Case 1: 이전 프레임이 있으면 그것이 throwing frame
                    if (i > 0) {
                        throwingFrame = stackTrace[i - 1];
                    }
                    // Case 2: 이전 프레임이 없으면 (i == 0), 테스트 메서드 자체에서 예외
                    // → 이 경우 마지막 invocation을 찾아야 함
                    
                    break;
                }
            }
            
            // ✅ Throwing method와 class 정보 추출
            if (testFrame != null) {
                String throwingMethodName = null;
                String throwingClassName = null;
                boolean isDirectTestFailure = false;
                
                if (throwingFrame != null) {
                    // Case 1: 이전 프레임이 있는 경우
                    throwingMethodName = throwingFrame.getMethodName();
                    throwingClassName = throwingFrame.getClassName();
                } else {
                    // Case 2: 테스트 메서드 자체에서 예외 (첫 프레임)
                    // → 테스트 메서드의 마지막 invocation을 찾기
                    isDirectTestFailure = true;
                    if (DEBUG_ORACLE_TRANSFORM) {
                        System.out.println("[TryCatchFailAdder] [STMT-MATCH] Direct test failure detected");
                        System.out.println("[TryCatchFailAdder] [STMT-MATCH] Exception occurred in test method itself");
                    }
                }
                
                if (throwingMethodName != null && throwingClassName != null) {
                    if (DEBUG_ORACLE_TRANSFORM) {
                        System.out.println("[TryCatchFailAdder] [STMT-MATCH] Throwing method: " + 
                            throwingMethodName + " from " + throwingClassName);
                        System.out.println("[TryCatchFailAdder] [STMT-MATCH] Test frame line number: " + testFrame.getLineNumber());
                    }
                    
                    // ✅ STEP 1: executedFileContent에서 stack trace line number의 statement 추출 및 저장
                    String failingStmtFromExecutedFile = extractStatementFromExecutedFile(
                        executedFileContent, testFrame.getLineNumber(), ctMethod);
                    
                    if (failingStmtFromExecutedFile != null) {
                        String testMethodKey = null;
                        if (ctMethod.getDeclaringType() != null) {
                            testMethodKey = ctMethod.getDeclaringType().getQualifiedName() + ":" + ctMethod.getSimpleName();
                        } else {
                            // Fallback: use simple method name if declaring type is unavailable
                            testMethodKey = "UNKNOWN:" + ctMethod.getSimpleName();
                            if (DEBUG_ORACLE_TRANSFORM) {
                                System.out.println("[TryCatchFailAdder] [STMT-EXTRACT] Warning: Using fallback key because declaring type is null");
                            }
                        }
                        
                        // Store the failing statement string
                        ORIGINAL_FAILING_STATEMENT.put(testMethodKey, failingStmtFromExecutedFile);
                        
                        if (DEBUG_ORACLE_TRANSFORM) {
                            System.out.println("[TryCatchFailAdder] [STMT-EXTRACT] ✓ Extracted failing statement from executed file");
                            System.out.println("[TryCatchFailAdder] [STMT-EXTRACT] Line " + testFrame.getLineNumber() + ": " + failingStmtFromExecutedFile);
                        }
                    }
                    
                    // ✅ PRIORITY 1: Direct string matching with extracted failing statement
                    // executedFileContent에서 추출한 failing statement와 직접 비교
                    CtStatement stringMatchStmt = findFailingStmtByDirectStringMatching(
                        ctMethod, failingStmtFromExecutedFile, throwingMethodName, throwingClassName);
                    
                    if (stringMatchStmt != null) {
                        if (DEBUG_ORACLE_TRANSFORM) {
                            System.out.println("[TryCatchFailAdder] ✓ SUCCESS: Found via direct string matching!");
                            System.out.println("[TryCatchFailAdder] ================================================");
                        }
                        return stringMatchStmt;
                    }
                    
                    // ✅ PRIORITY 2: Original statement equivalence 기반 매칭 (fallback)
                    CtStatement origStmtMatch = findFailingStmtByOriginalStatementEquivalence(
                        ctMethod, throwingMethodName, throwingClassName);
                    
                    if (origStmtMatch != null) {
                        if (DEBUG_ORACLE_TRANSFORM) {
                            System.out.println("[TryCatchFailAdder] ✓ SUCCESS: Found via original statement equivalence!");
                            System.out.println("[TryCatchFailAdder] ================================================");
                        }
                        return origStmtMatch;
                    }
                    
                    // ✅ PRIORITY 3: Statement 기반 매칭 시도 (fallback)
                    CtStatement stmtMatch = findStatementByStatementMatching(
                        ctMethod, throwingMethodName, throwingClassName, executedFileContent);
                    
                    if (stmtMatch != null) {
                        if (DEBUG_ORACLE_TRANSFORM) {
                            System.out.println("[TryCatchFailAdder] ✓ SUCCESS: Found via statement matching!");
                            System.out.println("[TryCatchFailAdder] ================================================");
                        }
                        return stmtMatch;
                    }
                } else if (isDirectTestFailure) {
                    // Case 2: 테스트 메서드 자체에서 예외 (또는 helper method에서 예외)
                    // → Stack trace에서 실제 호출 라인 찾기
                    if (DEBUG_ORACLE_TRANSFORM) {
                        System.out.println("[TryCatchFailAdder] [STMT-MATCH] Direct test failure detected");
                        System.out.println("[TryCatchFailAdder] [STMT-MATCH] Looking for calling statement in test method");
                    }
                    
                    // Stack trace에서 테스트 메서드 다음 프레임 찾기 (실제 호출 위치)
                    int testFrameIndex = -1;
                    for (int idx = 0; idx < stackTrace.length; idx++) {
                        if (stackTrace[idx] == testFrame) {
                            testFrameIndex = idx;
                            break;
                        }
                    }
                    
                    int callingLineNumber = testFrame.getLineNumber();
                    
                    // 이전 프레임이 있으면 (helper method 호출의 경우) 테스트 메서드 호출 라인 사용
                    if (testFrameIndex > 0 && testFrameIndex - 1 >= 0) {
                        StackTraceElement prevFrame = stackTrace[testFrameIndex - 1];
                        if (prevFrame.getClassName().equals(testFrame.getClassName()) && 
                            prevFrame.getMethodName().equals(testFrame.getMethodName())) {
                            // 같은 메서드라면 그 라인 사용
                            callingLineNumber = prevFrame.getLineNumber();
                            if (DEBUG_ORACLE_TRANSFORM) {
                                System.out.println("[TryCatchFailAdder] [STMT-MATCH] Using previous frame line: " + callingLineNumber);
                            }
                        }
                    }
                    
                    // Stack trace line에서 statement 추출 시도
                    String stmtFromLine = extractStatementFromExecutedFile(
                        executedFileContent, callingLineNumber, ctMethod);
                    
                    if (stmtFromLine != null && !stmtFromLine.trim().isEmpty()) {
                        if (DEBUG_ORACLE_TRANSFORM) {
                            System.out.println("[TryCatchFailAdder] [STMT-MATCH] ✓ Extracted failing statement from line " + callingLineNumber);
                            System.out.println("[TryCatchFailAdder] [STMT-MATCH] Statement: " + stmtFromLine);
                        }
                        
                        // Find equivalent statement in current method using string matching
                        List<CtStatement> allStmts = collectAllStatements(ctMethod.getBody());
                        String normalizedExtracted = normalizeStatementSignature(stmtFromLine);
                        
                        for (CtStatement stmt : allStmts) {
                            String currentStmtStr = stmt.toString().trim();
                            String normalizedCurrent = normalizeStatementSignature(currentStmtStr);
                            
                            // Exact match only for direct test failure
                            if (normalizedCurrent.equals(normalizedExtracted)) {
                                if (DEBUG_ORACLE_TRANSFORM) {
                                    System.out.println("[TryCatchFailAdder] [STMT-MATCH] ✓ Found exact matching statement via string comparison");
                                    System.out.println("[TryCatchFailAdder] [STMT-MATCH] Statement: " + currentStmtStr);
                                    System.out.println("[TryCatchFailAdder] ================================================");
                                }
                                return stmt;
                            }
                        }
                        
                        if (DEBUG_ORACLE_TRANSFORM) {
                            System.out.println("[TryCatchFailAdder] [STMT-MATCH] ✗ No exact match found, attempted partial match would be unreliable");
                        }
                    }
                    
                    // Fallback: 첫 번째 invocation 선택 (helper method 호출이 있을 수 있음)
                    if (DEBUG_ORACLE_TRANSFORM) {
                        System.out.println("[TryCatchFailAdder] [STMT-MATCH] String matching failed, falling back to first invocation");
                    }
                    
                    List<CtStatement> allStmts = collectAllStatements(ctMethod.getBody());
                    // 첫 번째 invocation을 포함하는 statement 찾기
                    for (CtStatement stmt : allStmts) {
                        List<CtInvocation<?>> invocations = stmt.getElements(new TypeFilter<>(CtInvocation.class));
                        if (!invocations.isEmpty()) {
                            if (DEBUG_ORACLE_TRANSFORM) {
                                String stmtStr = stmt.toString().replace("\n", " ");
                                if (stmtStr.length() > 80) stmtStr = stmtStr.substring(0, 80) + "...";
                                System.out.println("[TryCatchFailAdder] [STMT-MATCH] ✓ Found first invocation statement");
                                System.out.println("[TryCatchFailAdder] [STMT-MATCH] Statement: " + stmtStr);
                                System.out.println("[TryCatchFailAdder] ================================================");
                            }
                            return stmt;
                        }
                    }
                    
                    // 최후의 fallback: 첫 번째 statement
                    if (!allStmts.isEmpty()) {
                        if (DEBUG_ORACLE_TRANSFORM) {
                            String firstStmtStr = allStmts.get(0).toString().replace("\n", " ");
                            if (firstStmtStr.length() > 80) firstStmtStr = firstStmtStr.substring(0, 80) + "...";
                            System.out.println("[TryCatchFailAdder] [STMT-MATCH] ✓ Using first statement as last resort");
                            System.out.println("[TryCatchFailAdder] [STMT-MATCH] Statement: " + firstStmtStr);
                            System.out.println("[TryCatchFailAdder] ================================================");
                        }
                        return allStmts.get(0);
                    }
                }
                
                if (DEBUG_ORACLE_TRANSFORM) {
                    System.out.println("[TryCatchFailAdder] [STMT-MATCH] ✗ Statement matching failed, falling back to line-based matching");
                }
            }
        }
        
        if (DEBUG_ORACLE_TRANSFORM) {
            System.out.println("[TryCatchFailAdder] ================================================");
        }
        
        // ✅ Fallback: 기존의 라인 번호 기반 매칭
        List<CtInvocation<?>> allInvocations = ctMethod.getBody().getElements(new TypeFilter<>(CtInvocation.class));
        List<CtConstructorCall<?>> allConstructorCalls = ctMethod.getBody().getElements(new TypeFilter<>(CtConstructorCall.class));

        // 테스트 클래스 정보 수집
        CtClass testClass = null;
        String testClassName = null;
        try {
            testClass = ctMethod.getParent(CtClass.class);
            testClassName = (testClass != null) ? testClass.getQualifiedName() : null;
        } catch (Exception e) {
            // 무시
        }

        // 동적 생성된 테스트의 경우 stack trace에서 test class name 추출
        if (testClassName == null && stackTrace.length > 0) {
            for (StackTraceElement frame : stackTrace) {
                // _P_ 또는 _M_ 패턴을 포함하는 프레임 찾기 (동적 생성된 테스트)
                if (frame.getClassName().matches(".*_[PM]_.*")) {
                    testClassName = frame.getClassName();
                    // System.out.println("[TRY-CATCH-DEBUG] Extracted test class name from stack
                    // trace: " + testClassName);
                    break;
                }
            }
        }

        if (DEBUG_ORACLE_TRANSFORM) {
            System.out.println("[TryCatchFailAdder] testClassName extracted: " + testClassName);
            System.out.println("[TryCatchFailAdder] ctMethod.getSimpleName(): " + ctMethod.getSimpleName());
            System.out.println("[TryCatchFailAdder] Executed Content : " + executedFileContent);
            
            // ✅ NEW: Line Discrepancy 분석
            System.out.println("\n[TryCatchFailAdder] ========== LINE DISCREPANCY ANALYSIS ==========");
            analyzeLineDiscrepancy(stackTrace, executedFileContent, ctMethod.getSimpleName());
            System.out.println("[TryCatchFailAdder] ==============================================\n");
        }
        
        // ✅ 개선: 먼저 테스트 메서드 프레임을 찾아서 우선 처리
        // _P_, _M_, _C_ 패턴을 포함하는 프레임 = 동적 생성된 테스트 메서드
        StackTraceElement dynamicTestFrame = null;
        int dynamicTestFrameIndex = -1;
        
        for (int i = 0; i < stackTrace.length; i++) {
            StackTraceElement frame = stackTrace[i];
            // _P_, _M_, _C_ 패턴으로 동적 생성된 테스트 메서드 찾기
            if (frame.getClassName().matches(".*_[PMC]_.*") && frame.getLineNumber() > 0) {
                dynamicTestFrame = frame;
                dynamicTestFrameIndex = i;
                
                // System.out.println("[TryCatchFailAdder] Found test method frame at index " + i + ": " +
                //     frame.getClassName() + "." + frame.getMethodName() + ":" + frame.getLineNumber());
                break;
            }
        }
        
        // ✅ 테스트 메서드 프레임을 찾았으면 STEP 1으로 throwing method 찾기
        if (dynamicTestFrame != null && dynamicTestFrameIndex > 0) {
            StackTraceElement prevFrame = stackTrace[dynamicTestFrameIndex - 1];
            String throwingMethodName = prevFrame.getMethodName();
            String throwingClassName = prevFrame.getClassName();
            if (DEBUG_ORACLE_TRANSFORM) {
                System.out.println("[TryCatchFailAdder] [STEP 1] Searching for invocation: " + 
                    throwingClassName + "." + throwingMethodName + " at test line: " + dynamicTestFrame.getLineNumber());
                System.out.println("[TryCatchFailAdder] executedFileContent: " + 
                    (executedFileContent != null ? "provided (" + executedFileContent.length() + " chars)" : "null"));
            }
            CtStatement stmtFromInvocation = findStatementWithThrowingMethodInvocation(
                ctMethod, throwingMethodName, throwingClassName, 
                dynamicTestFrame.getLineNumber(), executedFileContent);
            
            if (stmtFromInvocation != null) {
                if (DEBUG_ORACLE_TRANSFORM) {
                    System.out.println("[TryCatchFailAdder] ✓ [STEP 1] Found statement via invocation: " +
                        stmtFromInvocation.getClass().getSimpleName());
                }
                return stmtFromInvocation;
            } else {
                if (DEBUG_ORACLE_TRANSFORM) {
                    System.out.println("[TryCatchFailAdder] ✗ [STEP 1] No invocation found - fallback to line number matching");
                }
            }
        }
        
        // ✅ STEP 1 실패 시 기존 로직으로 fallback
        for (int i = 0; i < stackTrace.length; i++) {
            StackTraceElement frame = stackTrace[i];
            
            if (DEBUG_ORACLE_TRANSFORM && i < 3) {
                System.out.println("[TryCatchFailAdder] Processing frame[" + i + "]: " +
                    frame.getClassName() + "." + frame.getMethodName() + ":" +
                    frame.getLineNumber());
            }

              // 첫 번째 프레임이 테스트 메서드 자체인 경우
              // ✅ _P_, _M_, _C_ 패턴으로 동적 생성된 테스트 메서드 확인
              boolean isTestMethodFrame = false;
              if (frame.getLineNumber() > 0) {
                  // _P_, _M_, _C_ 패턴을 포함하면 테스트 메서드
                  isTestMethodFrame = frame.getClassName().matches(".*_[PMC]_.*");
              }
              
              if (isTestMethodFrame) {
                  // ✅ 이미 위에서 처리했으므로 여기서는 STEP 2 (Line number matching)만 수행
                  if (DEBUG_ORACLE_TRANSFORM) {
                      System.out.println("[TryCatchFailAdder] [STEP 2 Fallback] Test method frame - trying line number matching");
                      System.out.println("[TryCatchFailAdder]   Frame: " + frame.getClassName() + "." + frame.getMethodName() + ":" + frame.getLineNumber());
                  }

                  // 2) Invocation으로 찾지 못하면 line number로 매칭
                  if (DEBUG_ORACLE_TRANSFORM) {
                      System.out.println("[TryCatchFailAdder]   [STEP 2] Searching by line number: " + frame.getLineNumber());
                  }
                  
                  // 정확한 line number로 찾기 시도
                  CtStatement stmt = findStmtCoveringLine(ctMethod, frame.getLineNumber());

                  // 동적 생성된 테스트는 소스 위치 정보가 없으므로 executedFileContent 사용
                  if (stmt == null && executedFileContent != null) {
                      if (DEBUG_ORACLE_TRANSFORM) {
                          System.out.println("[TryCatchFailAdder]   SourcePosition not available - using executedFileContent");
                      }
                      stmt = findStmtUsingExecutedFileContentWithNested(ctMethod, frame.getLineNumber(), executedFileContent);
                  }
                  
                  // 그래도 안 되면 aggressive heuristic 사용
                  if (stmt == null) {
                      if (DEBUG_ORACLE_TRANSFORM) {
                          System.out.println("[TryCatchFailAdder]   Fallback to aggressive heuristic");
                          System.out.println("[TryCatchFailAdder]   Method has " + ctMethod.getBody().getStatements().size() + " top-level statements");
                      }
                      stmt = findStmtCoveringLineAggressive(ctMethod, frame.getLineNumber());
                  }

                  if (stmt != null) {
                      // [CRITICAL] statement가 Try-Catch 블록 자체인 경우 → 이미 처리된 것이므로 스킵
                      if (stmt instanceof CtTry) {
                          if (DEBUG_ORACLE_TRANSFORM) {
                              System.out.println("[TryCatchFailAdder]   ✗ [STEP 2] Found statement is a Try-Catch block itself, skipping");
                          }
                          // 다음 crash point를 찾기 위해 계속 진행
                          continue;
                      }
                      
                      // 이미 try-catch로 감싸진 statement인지 확인
                      if (isAlreadyWrappedInTryCatch(stmt)) {
                          if (DEBUG_ORACLE_TRANSFORM) {
                              System.out.println("[TryCatchFailAdder]   ✗ [STEP 2] Statement already wrapped in try-catch, skipping");
                          }
                          // 다음 crash point를 찾기 위해 null 반환하지 않고 계속 진행
                          continue;
                      }
                      
                      if (DEBUG_ORACLE_TRANSFORM) {
                          System.out.println("[TryCatchFailAdder]   ✓ [STEP 2] Found statement: " + stmt.getClass().getSimpleName());
                      }
                      return stmt;
                  }
                  if (DEBUG_ORACLE_TRANSFORM) {
                      System.out.println("[TryCatchFailAdder]   ✗ [STEP 2] Could not find statement at line " + frame.getLineNumber());
                  }
              }

            // Framework 프레임이지만 테스트에서 직접 호출한 경우 (constructor) 처리
            boolean isFrameworkFrame = frame.getClassName().startsWith("org.junit.") ||
                                       frame.getClassName().startsWith("java.") ||
                                       frame.getClassName().startsWith("sun.") ||
                                       frame.getClassName().startsWith("jdk.internal.");

            if (isFrameworkFrame) {
                // Constructor 호출이고, 다음 프레임이 테스트 메서드인 경우 처리
                if ("<init>".equals(frame.getMethodName()) && i + 1 < stackTrace.length) {
                    StackTraceElement nextFrame = stackTrace[i + 1];
                    // System.out.println("[TRY-CATCH-DEBUG] Checking if constructor called from
                    // test:");
                    // System.out.println("[TRY-CATCH-DEBUG] testClassName = " + testClassName);
                    // System.out.println("[TRY-CATCH-DEBUG] nextFrame.getClassName() = " +
                    // nextFrame.getClassName());
                    // 다음 프레임이 테스트 클래스인지 확인
                    if (testClassName != null && nextFrame.getClassName().equals(testClassName)) {
                        // System.out.println("[TRY-CATCH-DEBUG] Framework constructor called directly
                        // from test - searching for: new " +
                        // frame.getClassName().substring(frame.getClassName().lastIndexOf('.') + 1) +
                        // "(...)");

                        // 이 클래스의 생성자 호출을 찾기
                        String constructorClassName = frame.getClassName();

                        for (CtConstructorCall<?> call : allConstructorCalls) {
                            if (call.getExecutable() != null && call.getExecutable().getDeclaringType() != null) {
                                String callClassName = call.getExecutable().getDeclaringType().getQualifiedName();
                                if (callClassName.equals(constructorClassName)) {
                                    // System.out.println("[TRY-CATCH-DEBUG] Found matching constructor call for " +
                                    // constructorClassName);
                                    CtStatement stmt = findContainingStatement(call);
                                    if (stmt != null) {
                                        return stmt;
                                    }
                                }
                            }
                        }
                    }
                }
                // System.out.println("[TRY-CATCH-DEBUG] Skipping framework frame: " +
                // frame.getClassName());
                continue;
            }

            // ✅ CRITICAL: 이 frame이 테스트 메서드 프레임이면 스킵 (위에서 이미 처리했음)
            // Frame이 CUT/Library 메서드인 경우에만 아래 로직 실행
            if (testClassName != null && 
                frame.getClassName().equals(testClassName) && 
                frame.getMethodName().equals(ctMethod.getSimpleName())) {
                // 이미 위에서 처리했으므로 continue
                continue;
            }
            
            // 1. 일반 메서드 호출 확인 - 다중 호출 감지 및 전체 래핑 로직
            List<CtInvocation<?>> matchingInvocations = new ArrayList<>();

            // 먼저 메서드 이름과 타입이 일치하는 모든 호출을 수집
            for (CtInvocation<?> invocation : allInvocations) {
                CtExecutableReference<?> executable = invocation.getExecutable();
                if (executable == null || executable.getDeclaringType() == null) {
                    continue;
                }

                // 메서드 이름이 일치하는 경우, 타입 검증 진행
                if (executable.getSimpleName().equals(frame.getMethodName())) {
                    try {
                        // 다형성 및 타입 일치 확인
                        Class<?> invocationClass = executable.getDeclaringType().getActualClass();
                        Class<?> stackTraceClass = Class.forName(frame.getClassName());

                        if (invocationClass.isAssignableFrom(stackTraceClass) ||
                            stackTraceClass.isAssignableFrom(invocationClass)) {
                            matchingInvocations.add(invocation);
                        }
                    } catch (Exception e) {
                        // 클래스 로딩 실패 시 기존 문자열 비교로 대체
                        if (executable.getDeclaringType().getQualifiedName().equals(frame.getClassName())) {
                            matchingInvocations.add(invocation);
                        }
                    }
                }
            }

            // 매칭되는 호출의 개수에 따라 처리 방식 결정
            if (matchingInvocations.size() > 1) {
                // System.out.println("[TRY-CATCH-DEBUG] ⚠️ MULTIPLE SAME INVOCATION DETECTED: "
                // + matchingInvocations.size() + " calls to " + frame.getMethodName());

                // Stack trace에서 테스트 메서드 frame을 찾기 (여러 라이브러리 frame을 건너뛸 수 있음)
                StackTraceElement testMethodFrame = null;
                for (int j = i + 1; j < stackTrace.length; j++) {
                    StackTraceElement candidateFrame = stackTrace[j];
                    if (testClassName != null && candidateFrame.getClassName().equals(testClassName)) {
                        testMethodFrame = candidateFrame;
                        // System.out.println("[TRY-CATCH-DEBUG] Found test method frame at stack index
                        // " + j + ": " + candidateFrame.getClassName() + ":" +
                        // candidateFrame.getLineNumber());
                        break;
                    }
                }

                if (testMethodFrame != null) {
                    // System.out.println("[TRY-CATCH-DEBUG] ✓ Using test method frame for exact
                    // matching");

                    // executedFileContent가 있으면 정확한 라인 매칭 시도
                    if (executedFileContent != null) {
                        CtStatement stmt = findStmtUsingExecutedFileContent(ctMethod, testMethodFrame.getLineNumber(),
                                executedFileContent, matchingInvocations, frame.getMethodName());
                        if (stmt != null) {
                            // System.out.println("[TRY-CATCH-DEBUG] Found statement using executed file
                            // content");
                            return stmt;
                        }
                    }

                    // Fallback: testMethod.toString() 기반 매칭
                    CtStatement stmt = findStmtCoveringLineAggressive(ctMethod, testMethodFrame.getLineNumber());
                    if (stmt != null) {
                        // System.out.println("[TRY-CATCH-DEBUG] Found statement using aggressive
                        // matching");
                        return stmt;
                    }
                    // System.out.println("[TRY-CATCH-DEBUG] Aggressive matching failed - falling
                    // back to execution order");
                }

                // Invocation position 기반 매칭은 SourcePosition이 valid한 경우에만 시도
                int targetLineNumber = frame.getLineNumber();

                // 메소드 시작 라인 추정 (동적 생성된 테스트를 위한 상대/절대 라인 변환)
                Integer methodStartLine = estimateMethodStartLine(ctMethod, matchingInvocations);

                // 각 invocation의 위치 출력 및 매칭
                CtInvocation<?> exactMatch = null;

                for (int idx = 0; idx < matchingInvocations.size(); idx++) {
                    CtInvocation<?> inv = matchingInvocations.get(idx);
                    SourcePosition pos = inv.getPosition();

                    if (pos != null && pos.isValidPosition()) {
                        int invAbsoluteLine = pos.getLine();
                        int invRelativeLine = invAbsoluteLine;

                        // 메소드 시작 라인을 알면 상대 라인 번호로 변환
                        int targetRelativeLine = targetLineNumber;
                        if (methodStartLine != null && methodStartLine > 0) {
                            invRelativeLine = invAbsoluteLine - methodStartLine;
                            targetRelativeLine = targetLineNumber - methodStartLine;
                            // System.out.println("[TRY-CATCH-DEBUG] Invocation #" + idx + " at absolute
                            // line " + invAbsoluteLine +
                            // " (relative " + invRelativeLine + "), searching for absolute " +
                            // targetLineNumber + " (relative " + targetRelativeLine + ")");
                        } else {
                            // System.out.println("[TRY-CATCH-DEBUG] Invocation #" + idx + " at absolute
                            // line " + invAbsoluteLine +
                            // ", searching for line " + targetLineNumber);
                        }

                        // 절대 라인과 상대 라인 둘 다 비교
                        boolean absoluteMatch = invAbsoluteLine == targetLineNumber ||
                                (pos.getLine() <= targetLineNumber && targetLineNumber <= pos.getEndLine());

                        boolean relativeMatch = methodStartLine != null &&
                                (invRelativeLine == targetRelativeLine ||
                                        (invRelativeLine <= targetRelativeLine && targetRelativeLine <= invRelativeLine
                                                + (pos.getEndLine() - pos.getLine())));

                        if (absoluteMatch || relativeMatch) {
                            exactMatch = inv;
                            // System.out.println("[TRY-CATCH-DEBUG] ✓ Matched invocation #" + idx +
                            // " (absolute: " + absoluteMatch + ", relative: " + relativeMatch + ")");
                        }
                    } else {
                        // System.out.println("[TRY-CATCH-DEBUG] Invocation #" + idx + " (no source
                        // position available)");
                    }
                }

                if (exactMatch != null) {
                    // System.out.println("[TRY-CATCH-DEBUG] ✓ Found exact invocation by line number
                    // matching");
                }

                // line number 매칭 실패시 첫 번째 것 선택
                if (exactMatch == null) {
                    // System.out.println("[TRY-CATCH-DEBUG] Line number matching failed - selecting
                    // first invocation in execution order");
                    exactMatch = findFirstInvocationInExecutionOrder(matchingInvocations, ctMethod);
                }

                if (exactMatch != null) {
                    CtStatement stmt = findContainingStatement(exactMatch);
                    if (stmt != null) {
                        return stmt;
                    }
                }

                // 그래도 찾지 못하면 전체 래핑
                // System.out.println("[TRY-CATCH-DEBUG] Could not find containing statement -
                // wrapping entire method");
                return new CtBlockImpl();

            } else if (matchingInvocations.size() == 1) {
                // System.out.println("[TRY-CATCH-DEBUG] Found single matching invocation of " +
                // frame.getMethodName());
                // 단일 호출이면 정확히 그것을 반환
                CtStatement stmt = findContainingStatement(matchingInvocations.get(0));
                if (stmt != null) {
                    return stmt;
                }
            }

            // 2. 생성자 호출 확인 - 다중 생성자 호출 감지
            if (frame.getMethodName().equals("<init>")) {
                List<CtConstructorCall<?>> matchingConstructorCalls = new ArrayList<>();
                
                for (CtConstructorCall<?> call : allConstructorCalls) {
                    if (call.getExecutable() != null && call.getExecutable().getDeclaringType() != null) {
                        try {
                            Class<?> constructorClass = call.getExecutable().getDeclaringType().getActualClass();
                            Class<?> stackTraceClass = Class.forName(frame.getClassName());

                            if (constructorClass.isAssignableFrom(stackTraceClass) || 
                                stackTraceClass.isAssignableFrom(constructorClass)) {
                                matchingConstructorCalls.add(call);
                            }
                        } catch (Exception e) {
                            // 클래스 로딩 실패 시 문자열 비교
                            if (call.getExecutable().getDeclaringType().getQualifiedName().equals(frame.getClassName())) {
                                matchingConstructorCalls.add(call);
                            }
                        }
                    }
                }
                
                // 매칭되는 생성자 호출 개수에 따라 처리
                if (matchingConstructorCalls.size() > 1) {
                    // System.out.println("[TRY-CATCH-DEBUG] ⚠️ MULTIPLE SAME CONSTRUCTOR DETECTED:
                    // " + matchingConstructorCalls.size() + " calls to new " +
                    // frame.getClassName());

                    // Stack trace에서 테스트 메서드 frame을 찾기
                    StackTraceElement testMethodFrame = null;
                    for (int j = i + 1; j < stackTrace.length; j++) {
                        StackTraceElement candidateFrame = stackTrace[j];
                        if (testClassName != null && candidateFrame.getClassName().equals(testClassName)) {
                            testMethodFrame = candidateFrame;
                            // System.out.println("[TRY-CATCH-DEBUG] Found test method frame at stack index
                            // " + j + ": " + candidateFrame.getClassName() + ":" +
                            // candidateFrame.getLineNumber());
                            break;
                        }
                    }

                    int targetLineNumber = frame.getLineNumber();

                    if (testMethodFrame != null) {
                        // System.out.println("[TRY-CATCH-DEBUG] ✓ Using test method frame for exact
                        // matching");

                        // executedFileContent가 있으면 정확한 라인 매칭 시도
                        if (executedFileContent != null) {
                            CtStatement stmt = findStmtUsingExecutedFileContentForConstructor(ctMethod,
                                    testMethodFrame.getLineNumber(), executedFileContent, matchingConstructorCalls);
                            if (stmt != null) {
                                // System.out.println("[TRY-CATCH-DEBUG] Found statement using executed file
                                // content");
                                return stmt;
                            }
                        }

                        targetLineNumber = testMethodFrame.getLineNumber();
                        // System.out.println("[TRY-CATCH-DEBUG] Using test method frame line number: "
                        // + targetLineNumber);
                    } else {
                        // System.out.println("[TRY-CATCH-DEBUG] Stack trace line number: " +
                        // targetLineNumber + " (no test method frame found)");
                    }

                    // 메소드 시작 라인 추정 (동적 생성된 테스트를 위한 상대/절대 라인 변환)
                    Integer methodStartLine = estimateMethodStartLineFromConstructors(ctMethod,
                            matchingConstructorCalls);

                    // 각 constructor call의 위치 출력 및 매칭
                    CtConstructorCall<?> exactMatch = null;

                    for (int idx = 0; idx < matchingConstructorCalls.size(); idx++) {
                        CtConstructorCall<?> call = matchingConstructorCalls.get(idx);
                        SourcePosition pos = call.getPosition();

                        if (pos != null && pos.isValidPosition()) {
                            int callAbsoluteLine = pos.getLine();
                            int callRelativeLine = callAbsoluteLine;

                            // 메소드 시작 라인을 알면 상대 라인 번호로 변환
                            int targetRelativeLine = targetLineNumber;
                            if (methodStartLine != null && methodStartLine > 0) {
                                callRelativeLine = callAbsoluteLine - methodStartLine;
                                targetRelativeLine = targetLineNumber - methodStartLine;
                                // System.out.println("[TRY-CATCH-DEBUG] Constructor #" + idx + " at absolute
                                // line " + callAbsoluteLine +
                                // " (relative " + callRelativeLine + "), searching for absolute " +
                                // targetLineNumber + " (relative " + targetRelativeLine + ")");
                            } else {
                                // System.out.println("[TRY-CATCH-DEBUG] Constructor #" + idx + " at absolute
                                // line " + callAbsoluteLine +
                                // ", searching for line " + targetLineNumber);
                            }

                            // 절대 라인과 상대 라인 둘 다 비교
                            boolean absoluteMatch = callAbsoluteLine == targetLineNumber ||
                                    (pos.getLine() <= targetLineNumber && targetLineNumber <= pos.getEndLine());

                            boolean relativeMatch = methodStartLine != null &&
                                    (callRelativeLine == targetRelativeLine ||
                                            (callRelativeLine <= targetRelativeLine
                                                    && targetRelativeLine <= callRelativeLine
                                                            + (pos.getEndLine() - pos.getLine())));

                            if (absoluteMatch || relativeMatch) {
                                exactMatch = call;
                                // System.out.println("[TRY-CATCH-DEBUG] ✓ Matched constructor #" + idx +
                                // " (absolute: " + absoluteMatch + ", relative: " + relativeMatch + ")");
                            }
                        } else {
                            // System.out.println("[TRY-CATCH-DEBUG] Constructor #" + idx + " (no source
                            // position available)");
                        }
                    }

                    if (exactMatch != null) {
                        // System.out.println("[TRY-CATCH-DEBUG] ✓ Found exact constructor call by line
                        // number matching");
                    }

                    // line number 매칭 실패시 첫 번째 것 선택
                    if (exactMatch == null) {
                        // System.out.println("[TRY-CATCH-DEBUG] Line number matching failed - selecting
                        // first constructor call in execution order");
                        exactMatch = findFirstConstructorCallInExecutionOrder(matchingConstructorCalls, ctMethod);
                    }

                    if (exactMatch != null) {
                        CtStatement stmt = findContainingStatement(exactMatch);
                        if (stmt != null) {
                            return stmt;
                        }
                    }

                    // 그래도 찾지 못하면 전체 래핑
                    // System.out.println("[TRY-CATCH-DEBUG] Could not find containing statement -
                    // wrapping entire method");
                    return new CtBlockImpl();

                } else if (matchingConstructorCalls.size() == 1) {
                    // System.out.println("[TRY-CATCH-DEBUG] Found single matching constructor call
                    // of " + frame.getClassName());
                    CtStatement stmt = findContainingStatement(matchingConstructorCalls.get(0));
                    if (stmt != null) {
                        return stmt;
                    }
                }
            }

            // 3. 헬퍼 메서드 호출 확인 (새로운 로직)
            if (testClass != null && testClassName != null && frame.getClassName().equals(testClassName)) {
                // System.out.println("[DEBUG] Checking for helper method: " + frame.getMethodName() + " in class " + testClassName);
                CtStatement helperCall = findHelperMethodCall(ctMethod, testClass, frame.getMethodName());
                if (helperCall != null) {
                    // System.out.println("[DEBUG] Found helper method call: " + helperCall.toString().split("\n")[0]);
                    return helperCall;
                }
            }
        }

        return null;
    }

    /**
     * 테스트 클래스 내의 헬퍼 메서드 호출을 찾기
     */
    private static CtStatement findHelperMethodCall(CtMethod testMethod, CtClass testClass, String helperMethodName) {
        if (testMethod == null || testMethod.getBody() == null) return null;

        // 테스트 메서드 내의 모든 메서드 호출 확인
        List<CtInvocation<?>> invocations = testMethod.getBody().getElements(new TypeFilter<>(CtInvocation.class));
        
        for (CtInvocation<?> invocation : invocations) {
            CtExecutableReference<?> executable = invocation.getExecutable();
            if (executable == null) continue;

            // 메서드 이름이 일치하는지 확인
            if (helperMethodName.equals(executable.getSimpleName())) {
                // 1. 같은 클래스의 메서드인지 확인 (this 호출)
                if (invocation.getTarget() == null || 
                    invocation.getTarget().toString().equals("this") ||
                    (executable.getDeclaringType() != null && 
                     testClass.getQualifiedName().equals(executable.getDeclaringType().getQualifiedName()))) {
                    
                    CtStatement stmt = findContainingStatement(invocation);
                    if (stmt != null) {
                        return stmt;
                    }
                }

                // 2. 상속된 메서드인지 확인
                try {
                    if (executable.getDeclaringType() != null) {
                        Class<?> declaringClass = executable.getDeclaringType().getActualClass();
                        Class<?> testActualClass = testClass.getReference().getActualClass();
                        
                        if (declaringClass.isAssignableFrom(testActualClass)) {
                            CtStatement stmt = findContainingStatement(invocation);
                            if (stmt != null) {
                                return stmt;
                            }
                        }
                    }
                } catch (Exception e) {
                    // 클래스 로딩 실패시 무시
                }
            }
        }

        return null;
    }

    /**
     * 주어진 expression을 포함하는 실제 statement 찾기
     */


      /**
       * 주어진 statement를 포함하는 top-level statement (메서드 body의 직접 자식)를 찾음
       * 예: 중첩 for 문 안의 statement → 가장 바깥쪽 for 문 반환
       * 
       * 중요: 이미 try-catch로 감싸진 블록을 발견하면, 그 블록 자체를 반환하지 않고
       * null을 반환해서 호출자가 다음 crash point를 찾을 수 있도록 함
       */
      private static CtStatement findTopLevelStatement(CtStatement stmt, CtMethod method) {
         if (stmt == null || method == null || method.getBody() == null) {
             return null;
         }
         
         CtElement current = stmt;
         CtStatement lastStatement = stmt;
         
         // 위로 올라가면서 메서드 body의 직접 자식을 찾음
         while (current != null) {
             CtElement parent = current.getParent();
             
             if (parent == null) {
                 break;
             }
             
             // 부모가 메서드 body인지 확인
             if (parent == method.getBody()) {
                 // current가 top-level statement
                 if (current instanceof CtStatement) {
                     CtStatement topLevelStmt = (CtStatement) current;
                     
                     // [IMPORTANT] 이미 try-catch로 감싸진 블록인지 확인
                     // fail() assertion이 있는 try-catch 블록이면 건너뜀
                     if (isAlreadyWrappedInTryCatch(topLevelStmt)) {
                         if (DEBUG_ORACLE_TRANSFORM) {
                             System.out.println("[TryCatchFailAdder] findTopLevelStatement: Found try-catch already wrapped, returning null to skip");
                         }
                         return null;  // null 반환 → 호출자가 다른 statement 찾도록
                     }
                     
                     return topLevelStmt;
                 }
                 
                 // lastStatement도 확인
                 if (lastStatement instanceof CtStatement) {
                     if (isAlreadyWrappedInTryCatch(lastStatement)) {
                         if (DEBUG_ORACLE_TRANSFORM) {
                             System.out.println("[TryCatchFailAdder] findTopLevelStatement: lastStatement already wrapped, returning null");
                         }
                         return null;
                     }
                 }
                 
                 return lastStatement;
             }
             
             // Statement를 기록
             if (current instanceof CtStatement) {
                 lastStatement = (CtStatement) current;
             }
             
             current = parent;
         }
         
         return lastStatement;
     }
    
    private static CtStatement findContainingStatement(CtElement element) {
        CtStatement stmt = element.getParent(CtStatement.class);
        
        // CtBlock인 경우 (메서드 body) 실제 statement를 찾아야 함
        if (stmt instanceof CtBlock) {
            // element를 포함하는 직접적인 statement 찾기
            CtElement current = element;
            while (current != null && current.getParent() != null) {
                CtElement parent = current.getParent();
                if (parent instanceof CtBlock && !(parent.getParent() instanceof CtMethod)) {
                    // nested block이면 계속 올라감
                    current = parent;
                    continue;
                }
                if (parent instanceof CtBlock && parent.getParent() instanceof CtMethod) {
                    // 메서드 body에 직접 포함된 statement
                    return (current instanceof CtStatement && !(current instanceof CtBlock)) ? 
                           (CtStatement) current : null;
                }
                current = parent;
            }
            return null;
        }
        
        return (stmt != null && !(stmt instanceof CtBlock)) ? stmt : null;
    }




            
    /**
     * Creates a try-catch block that wraps the entire method body
     * Used when forward reference issues are detected
     */
    /**
       * Checks if there exists multiple methodName calls existing in stmts
       *
       * @param stmts
       * @param crashPoint
       * @return
       */
     /**
      * Collects variable names that are declared/assigned in try-catch blocks
      * This helps track variables from previous oracle additions
      */
    private static void collectVariablesFromTryCatchBlocks(CtStatement stmt, Set<String> variables) {
        if (stmt instanceof CtTry) {
            CtTry tryStmt = (CtTry) stmt;
            // Collect from try body
            CtBlock<?> tryBody = tryStmt.getBody();
            if (tryBody != null) {
                collectDeclaredVariables(tryBody, variables);
            }
            // Collect from catchers
            for (CtCatch catcher : tryStmt.getCatchers()) {
                CtBlock<?> catchBody = catcher.getBody();
                if (catchBody != null) {
                    collectDeclaredVariables(catchBody, variables);
                }
            }
            // Collect from finally
            CtBlock<?> finallyBody = tryStmt.getFinalizer();
            if (finallyBody != null) {
                collectDeclaredVariables(finallyBody, variables);
            }
        }
    }
    
    /**
     * Collects all variable names used (read/written) in a statement
     * 로컬 변수만 수집 (필드, .class 리터럴 등은 제외)
     */
    private static void collectUsedVariables(CtStatement stmt, Set<String> usedVariables) {
        List<CtVariableAccess<?>> accesses = stmt.getElements(new TypeFilter<>(CtVariableAccess.class));
        for (CtVariableAccess<?> access : accesses) {
            if (access.getVariable() != null) {
                String varName = access.getVariable().getSimpleName();

                // .class 리터럴 제외
                if ("class".equals(varName)) {
                    continue;
                }

                // 필드 접근 제외 - 로컬 변수만 수집
                try {
                    CtElement declaration = access.getVariable().getDeclaration();
                    
                    // 1. 명확히 CtLocalVariable인 경우
                    if (declaration instanceof CtLocalVariable) {
                        usedVariables.add(varName);
                    }
                    // 2. declaration 찾기가 실패했지만 변수명이 유효해 보이는 경우
                    // (이전 try-catch 블록에서 선언된 변수일 수 있음)
                    else if (declaration != null && !isFieldOrStaticMember(varName)) {
                        usedVariables.add(varName);
                    }
                } catch (Exception e) {
                    // declaration이 없는 경우도 로컬 변수 이름으로 추가 시도
                    // (다른 블록에서 선언될 수 있음)
                    if (!isFieldOrStaticMember(varName)) {
                        usedVariables.add(varName);
                    }
                }
            }
        }
    }
    
     /**
      * 주어진 메서드에서 변수가 이미 선언되어 있는지 확인
      * 로컬 변수와 파라미터 모두 확인
      */
     private static boolean isVariableAlreadyDeclared(CtMethod<?> method, String varName) {
         if (method == null || method.getBody() == null || varName == null) {
             return false;
         }
         
         try {
             // 1. 메서드의 모든 로컬 변수 조회
             List<CtLocalVariable> allLocalVars = method.getBody().getElements(
                 new spoon.reflect.visitor.filter.TypeFilter<>(CtLocalVariable.class));
             
             if (DEBUG_ORACLE_TRANSFORM) {
                 System.out.println("[TryCatchFailAdder] Checking if variable '" + varName + "' is already declared");
                 System.out.println("[TryCatchFailAdder]   Found " + allLocalVars.size() + " local variables total");
             }
             
             for (CtLocalVariable var : allLocalVars) {
                 String declaredVarName = var.getSimpleName();
                 if (declaredVarName != null && declaredVarName.equals(varName)) {
                     if (DEBUG_ORACLE_TRANSFORM) {
                         System.out.println("[TryCatchFailAdder]   ✓ Variable '" + varName + "' found in local variables");
                     }
                     return true;
                 }
             }
             
             // 2. 파라미터도 확인
             List<?> params = method.getParameters();
             if (DEBUG_ORACLE_TRANSFORM && !params.isEmpty()) {
                 System.out.println("[TryCatchFailAdder]   Checking " + params.size() + " parameters");
             }
             
             for (Object param : params) {
                 if (param instanceof spoon.reflect.declaration.CtParameter) {
                     spoon.reflect.declaration.CtParameter ctParam = (spoon.reflect.declaration.CtParameter) param;
                     String paramName = ctParam.getSimpleName();
                     if (paramName != null && paramName.equals(varName)) {
                         if (DEBUG_ORACLE_TRANSFORM) {
                             System.out.println("[TryCatchFailAdder]   ✓ Variable '" + varName + "' found in parameters");
                         }
                         return true;
                     }
                 }
             }
             
             if (DEBUG_ORACLE_TRANSFORM) {
                 System.out.println("[TryCatchFailAdder]   ✗ Variable '" + varName + "' is NOT declared");
             }
         } catch (Exception e) {
             // 예외 발생 시 보수적으로 이미 선언된 것으로 가정
             if (DEBUG_ORACLE_TRANSFORM) {
                 System.out.println("[TryCatchFailAdder]   Exception checking variable: " + e.getMessage());
                 System.out.println("[TryCatchFailAdder]   Assuming variable is already declared (conservative approach)");
             }
             return true;  // 안전을 위해 true 반환 (중복 선언 방지)
         }
         
         return false;
     }
    
    /**
     * Check if a variable name looks like a field or static member
     * (e.g., uppercase, contains underscores, etc.)
     */
    private static boolean isFieldOrStaticMember(String varName) {
        // 명백한 필드나 상수인지 확인 (매우 보수적인 접근)
        // 대문자로 시작하거나 모두 대문자이고 언더스코어가 있으면 상수일 가능성 높음
        return varName.matches("[A-Z][A-Z0-9_]*") && varName.contains("_");
    }
    
    /**
     * Collects all variable names declared in a statement
     */
    private static void collectDeclaredVariables(CtStatement stmt, Set<String> declaredVariables) {
        List<CtLocalVariable> localVars = stmt.getElements(new TypeFilter<>(CtLocalVariable.class));
        for (CtLocalVariable localVar : localVars) {
            declaredVariables.add(localVar.getSimpleName());
        }
    }

    /**
     * Returns appropriate default value for a given type
     * @param typeName the type name (e.g., "int", "boolean", "String", "Object")
     * @return default value string for initialization
     */
    private static String getDefaultValueForType(String typeName) {
        // Handle primitive types
        switch (typeName) {
            case "int":
            case "short":
            case "byte":
                return "0";
            case "long":
                return "0L";
            case "float":
                return "0.0f";
            case "double":
                return "0.0";
            case "boolean":
                return "false";
            case "char":
                return "'\\0'";
            default:
                // For all reference types (String, Object, etc.)
                return "null";
        }
    }

    /**
     * Extracts all variable names and their inferred types from assignments in a statement
     * This is used to pre-declare variables that are used in try-catch blocks
     * but might not be explicitly declared in the anchor statement
     * 
     * @return Map of variable name -> inferred type name
     */
    /**
      * Same strategy used in Evosuite's TestCodeVisitor.java
      *
      * @param sourceClass
      * @return
      */
    private static boolean isValidSource(String sourceClass) {
        // Skip test class frames (containing _M_ or _P_ pattern indicating generated test methods)
        if (sourceClass.matches(".*_[MP]_.*")) {
            return false;
        }
        
        return (!sourceClass.startsWith(PackageInfo.getEvoSuitePackage() + ".") ||
                sourceClass.startsWith(PackageInfo.getEvoSuitePackage() + ".runtime.")) &&
                !sourceClass.equals(URLClassLoader.class.getName()) && // Classloaders may differ, e.g. when running
                                                                       // with ant
                !sourceClass.startsWith(RegExp.class.getPackage().getName()) &&
                !sourceClass.startsWith("java.lang.System") &&
                !sourceClass.startsWith("java.lang.String") &&
                !sourceClass.startsWith("java.lang.Class") &&
                !sourceClass.startsWith("sun.") &&
                !sourceClass.startsWith("com.sun.") &&
                !sourceClass.startsWith("jdk.internal.") &&
                !sourceClass.startsWith("<evosuite>");
    }

    /**
     * Analyzes a try block to determine what checked exceptions can actually be thrown
     * @param tryBody The try block to analyze
     * @return Set of exception class names that can be thrown
     */

    /**
     * 여러 개의 invocation 중 실행 순서상 가장 먼저 나오는 것을 찾기
     * Statement를 순서대로 순회하면서 첫 번째로 발견되는 invocation 반환
     */
    private static CtInvocation<?> findFirstInvocationInExecutionOrder(List<CtInvocation<?>> invocations, CtMethod method) {
        if (method == null || method.getBody() == null || invocations.isEmpty()) {
            return null;
        }

        // System.out.println("[TRY-CATCH-DEBUG] Finding first invocation in execution
        // order among " + invocations.size() + " candidates");

        // 메서드 body의 모든 statement를 순서대로 순회
        int stmtIndex = 0;
        for (CtStatement stmt : method.getBody().getStatements()) {
            // 이 statement와 그 하위에 있는 모든 invocation 체크
            for (CtInvocation<?> candidate : invocations) {
                if (isElementContainedIn(candidate, stmt)) {
                    // System.out.println("[TRY-CATCH-DEBUG] Found first invocation at statement
                    // index " + stmtIndex);
                    return candidate;
                }
            }
            stmtIndex++;
        }

        // 찾지 못하면 리스트의 첫 번째 반환
        // System.out.println("[TRY-CATCH-DEBUG] Could not find invocation in statements
        // - returning first from list");
        return invocations.get(0);
    }

    /**
     * 여러 개의 constructor call 중 실행 순서상 가장 먼저 나오는 것을 찾기
     */
    private static CtConstructorCall<?> findFirstConstructorCallInExecutionOrder(List<CtConstructorCall<?>> constructorCalls, CtMethod method) {
        if (method == null || method.getBody() == null || constructorCalls.isEmpty()) {
            return null;
        }

        // System.out.println("[TRY-CATCH-DEBUG] Finding first constructor call in
        // execution order among " + constructorCalls.size() + " candidates");

        // 메서드 body의 모든 statement를 순서대로 순회
        int stmtIndex = 0;
        for (CtStatement stmt : method.getBody().getStatements()) {
            // 이 statement와 그 하위에 있는 모든 constructor call 체크
            for (CtConstructorCall<?> candidate : constructorCalls) {
                if (isElementContainedIn(candidate, stmt)) {
                    // System.out.println("[TRY-CATCH-DEBUG] Found first constructor call at
                    // statement index " + stmtIndex);
                    return candidate;
                }
            }
            stmtIndex++;
        }

        // 찾지 못하면 리스트의 첫 번째 반환
        // System.out.println("[TRY-CATCH-DEBUG] Could not find constructor call in
        // statements - returning first from list");
        return constructorCalls.get(0);
    }

    /**
     * element가 container 내부에 포함되어 있는지 확인
     */
    private static boolean isElementContainedIn(CtElement element, CtElement container) {
        if (element == container) {
            return true;
        }

        // element의 모든 부모를 순회하면서 container와 일치하는지 확인
        CtElement current = element;
        try {
            while (current != null) {
                if (current == container || current.equals(container)) {
                    return true;
                }
                current = current.getParent();
            }
        } catch (Exception e) {
            // parent 순회 중 문제 발생 시 false 반환
        }

        return false;
    }

    /**
     * 테스트 메소드의 시작 라인 번호를 추정
     * 동적 생성된 테스트의 경우 SourcePosition이 없을 수 있으므로
     * invocation들의 위치를 기반으로 역추정
     */
    private static Integer estimateMethodStartLine(CtMethod method, List<CtInvocation<?>> invocations) {
        // 1. 메소드 자체의 SourcePosition이 유효하면 사용
        if (method.getPosition() != null && method.getPosition().isValidPosition()) {
            int startLine = method.getPosition().getLine();
            // System.out.println("[TRY-CATCH-DEBUG] Method start line from SourcePosition:
            // " + startLine);
            return startLine;
        }

        // 2. 메소드 body의 첫 번째 statement 위치 사용
        if (method.getBody() != null && !method.getBody().getStatements().isEmpty()) {
            CtStatement firstStmt = method.getBody().getStatements().get(0);
            if (firstStmt.getPosition() != null && firstStmt.getPosition().isValidPosition()) {
                // 첫 statement 앞에 메소드 선언부가 있을 것으로 추정 (보통 1-2줄)
                int estimatedStart = firstStmt.getPosition().getLine() - 2;
                // System.out.println("[TRY-CATCH-DEBUG] Estimated method start line from first
                // statement: " + estimatedStart);
                return estimatedStart;
            }
        }

        // 3. invocation들의 최소 라인 번호에서 역산
        if (invocations != null && !invocations.isEmpty()) {
            int minLine = Integer.MAX_VALUE;
            for (CtInvocation<?> inv : invocations) {
                if (inv.getPosition() != null && inv.getPosition().isValidPosition()) {
                    minLine = Math.min(minLine, inv.getPosition().getLine());
                }
            }
            if (minLine != Integer.MAX_VALUE) {
                // method.toString()에서 이 invocation의 상대 위치를 찾아 역산
                try {
                    String methodSource = method.toString();
                    String[] methodLines = methodSource.split("\n");

                    // 첫 invocation을 메소드 소스에서 찾기
                    CtInvocation<?> firstInv = null;
                    int firstInvAbsoluteLine = minLine;
                    for (CtInvocation<?> inv : invocations) {
                        if (inv.getPosition() != null && inv.getPosition().isValidPosition() &&
                                inv.getPosition().getLine() == minLine) {
                            firstInv = inv;
                            break;
                        }
                    }

                    if (firstInv != null) {
                        String invSource = firstInv.toString().split("\n")[0].trim();

                        // 메소드 소스에서 이 invocation이 몇 번째 라인인지 찾기
                        for (int li = 0; li < methodLines.length; li++) {
                            String line = methodLines[li].trim();
                            if (line.contains(invSource.substring(0, Math.min(20, invSource.length())))) {
                                int estimatedStart = firstInvAbsoluteLine - li;
                                // System.out.println("[TRY-CATCH-DEBUG] Estimated method start line from
                                // invocation position: " +
                                // estimatedStart + " (first inv at line " + firstInvAbsoluteLine + ", relative
                                // offset " + li + ")");
                                return estimatedStart;
                            }
                        }
                    }
                } catch (Exception e) {
                    // System.out.println("[TRY-CATCH-DEBUG] Failed to estimate method start line
                    // from invocations: " + e.getMessage());
                }
            }
        }

        // System.out.println("[TRY-CATCH-DEBUG] Could not estimate method start line");
        return null;
    }

    /**
     * 테스트 메소드의 시작 라인 번호를 추정 (constructor call 버전)
     */
    private static Integer estimateMethodStartLineFromConstructors(CtMethod method,
            List<CtConstructorCall<?>> constructorCalls) {
        // 1. 메소드 자체의 SourcePosition이 유효하면 사용
        if (method.getPosition() != null && method.getPosition().isValidPosition()) {
            int startLine = method.getPosition().getLine();
            // System.out.println("[TRY-CATCH-DEBUG] Method start line from SourcePosition:
            // " + startLine);
            return startLine;
        }

        // 2. 메소드 body의 첫 번째 statement 위치 사용
        if (method.getBody() != null && !method.getBody().getStatements().isEmpty()) {
            CtStatement firstStmt = method.getBody().getStatements().get(0);
            if (firstStmt.getPosition() != null && firstStmt.getPosition().isValidPosition()) {
                int estimatedStart = firstStmt.getPosition().getLine() - 2;
                // System.out.println("[TRY-CATCH-DEBUG] Estimated method start line from first
                // statement: " + estimatedStart);
                return estimatedStart;
            }
        }

        // 3. constructor call들의 최소 라인 번호에서 역산
        if (constructorCalls != null && !constructorCalls.isEmpty()) {
            int minLine = Integer.MAX_VALUE;
            for (CtConstructorCall<?> call : constructorCalls) {
                if (call.getPosition() != null && call.getPosition().isValidPosition()) {
                    minLine = Math.min(minLine, call.getPosition().getLine());
                }
            }
            if (minLine != Integer.MAX_VALUE) {
                try {
                    String methodSource = method.toString();
                    String[] methodLines = methodSource.split("\n");

                    CtConstructorCall<?> firstCall = null;
                    int firstCallAbsoluteLine = minLine;
                    for (CtConstructorCall<?> call : constructorCalls) {
                        if (call.getPosition() != null && call.getPosition().isValidPosition() &&
                                call.getPosition().getLine() == minLine) {
                            firstCall = call;
                            break;
                        }
                    }

                    if (firstCall != null) {
                        String callSource = firstCall.toString().split("\n")[0].trim();

                        for (int li = 0; li < methodLines.length; li++) {
                            String line = methodLines[li].trim();
                            if (line.contains(callSource.substring(0, Math.min(20, callSource.length())))) {
                                int estimatedStart = firstCallAbsoluteLine - li;
                                // System.out.println("[TRY-CATCH-DEBUG] Estimated method start line from
                                // constructor position: " +
                                // estimatedStart + " (first call at line " + firstCallAbsoluteLine + ",
                                // relative offset " + li + ")");
                                return estimatedStart;
                            }
                        }
                    }
                } catch (Exception e) {
                    // System.out.println("[TRY-CATCH-DEBUG] Failed to estimate method start line
                    // from constructors: " + e.getMessage());
                }
            }
        }

        // System.out.println("[TRY-CATCH-DEBUG] Could not estimate method start line");
        return null;
    }

    /**
      * [모드 2] WHOLE_WRAP: Crashing point 이후 전체 메서드를 try-catch로 wrap
      * ENABLE_WHOLE_WRAP_ORACLE_GEN = true일 때 호출됨
      */
    /**
     * Wraps from the crashing point to the end of the method body
     * This is used when ENABLE_WHOLE_WRAP_ORACLE_GEN is true
     * 
     * Unlike DEFAULT mode which wraps only at the crash point,
     * this mode wraps from crash point through all subsequent statements
     */
     private static Pair<CtMethod, String> addTryCatchFailWithWholeWrap(CtMethod testMethod, Failure failure, 
             Launcher launcher, String executedFileContent) {
          
          if (DEBUG_ORACLE_TRANSFORM) {
              System.out.println("[TryCatchFailAdder-WholeWrap] ========================================");
              System.out.println("[TryCatchFailAdder-WholeWrap] Wrapping from crash point to end");
              System.out.println("[TryCatchFailAdder-WholeWrap] Test: " + testMethod.getSimpleName());
          }
          
          try {
              CtMethod ctMethod = testMethod.clone();
              Factory factory = launcher.getFactory();
              
              // Get exception information from failure
              Throwable exception = failure.getException();
              if (exception == null) {
                  return addTryCatchFailDefault(testMethod, failure, launcher, executedFileContent);
              }
              
              StackTraceElement[] stackTrace = exception.getStackTrace();
              if (stackTrace.length == 0) {
                  return addTryCatchFailDefault(testMethod, failure, launcher, executedFileContent);
              }
              
              // Print stack trace for debugging
              if (DEBUG_ORACLE_TRANSFORM) {
                  String exceptionMsg = exception.getMessage();
                  System.out.println("[TryCatchFailAdder-WholeWrap] Exception: " + exception.getClass().getName());
                  if (exceptionMsg != null && exceptionMsg.length() > 80) {
                      System.out.println("[TryCatchFailAdder-WholeWrap] Message: " + exceptionMsg.substring(0, 80) + "...");
                  } else {
                      System.out.println("[TryCatchFailAdder-WholeWrap] Message: " + exceptionMsg);
                  }
                  System.out.println("[TryCatchFailAdder-WholeWrap] Stack trace details:");
                  for (int idx = 0; idx < Math.min(stackTrace.length, 15); idx++) {
                      StackTraceElement elem = stackTrace[idx];
                      String fileName = elem.getFileName() != null ? elem.getFileName() : "Unknown";
                      boolean isNative = elem.isNativeMethod();
                      String nativeTag = isNative ? " (native)" : "";
                      System.out.println("[TryCatchFailAdder-WholeWrap]   [" + idx + "] " + 
                          elem.getClassName() + "." + 
                          elem.getMethodName() + "(" + fileName + ":" + 
                          elem.getLineNumber() + ")" + nativeTag);
                  }
                  if (stackTrace.length > 15) {
                      System.out.println("[TryCatchFailAdder-WholeWrap]   ... (" + (stackTrace.length - 15) + " more frames)");
                  }
                  System.out.println("[TryCatchFailAdder-WholeWrap] Total stack frames: " + stackTrace.length);
              }
              
              String errorType = exception.getClass().getName();
              String originalErrorType = errorType;
             
             if (!errorType.matches("^[a-zA-Z_$][a-zA-Z\\d_$]*(\\$[a-zA-Z_$][a-zA-Z\\d_$]*)*(\\.[a-zA-Z_$][a-zA-Z\\d_$]*(\\$[a-zA-Z_$][a-zA-Z\\d_$]*)*)*$")) {
                 errorType = "java.lang.RuntimeException";
             }
             
             // Find the crashing statement
             CtStatement crashingStmt = findFailingStmtSmart(ctMethod, stackTrace, executedFileContent);
             
             if (crashingStmt == null) {
                 // If we can't find crash point, fall back to wrapping entire method
                 if (DEBUG_ORACLE_TRANSFORM) {
                     System.out.println("[TryCatchFailAdder-WholeWrap] Could not find crash point, wrapping entire method");
                 }
                 return wrapEntireMethod(ctMethod, factory, errorType, originalErrorType, stackTrace, testMethod.getSimpleName());
             }
             
             // Get the parent block (usually method body)
             CtBlock<?> parentBlock = null;
             try {
                 parentBlock = crashingStmt.getParent(CtBlock.class);
             } catch (Exception e) {
                 // If parent block not found, wrap entire method
                 return wrapEntireMethod(ctMethod, factory, errorType, originalErrorType, stackTrace, testMethod.getSimpleName());
             }
             
             if (parentBlock == null) {
                 return wrapEntireMethod(ctMethod, factory, errorType, originalErrorType, stackTrace, testMethod.getSimpleName());
             }
             
             // Get all statements in the parent block
             List<CtStatement> allStatements = parentBlock.getStatements();
             
             // Find the index of the crashing statement
             int crashIndex = -1;
             for (int i = 0; i < allStatements.size(); i++) {
                 if (allStatements.get(i) == crashingStmt) {
                     crashIndex = i;
                     break;
                 }
             }
             
             if (crashIndex == -1) {
                 // Statement not found in direct children, try to locate it differently
                 if (DEBUG_ORACLE_TRANSFORM) {
                     System.out.println("[TryCatchFailAdder-WholeWrap] Crash statement not found in parent, wrapping entire method");
                 }
                 return wrapEntireMethod(ctMethod, factory, errorType, originalErrorType, stackTrace, testMethod.getSimpleName());
             }
             
             if (DEBUG_ORACLE_TRANSFORM) {
                 System.out.println("[TryCatchFailAdder-WholeWrap] Found crash statement at index: " + crashIndex);
                 System.out.println("[TryCatchFailAdder-WholeWrap] Total statements: " + allStatements.size());
                 System.out.println("[TryCatchFailAdder-WholeWrap] Will wrap statements from " + crashIndex + " to " + (allStatements.size() - 1));
             }
             
             // Create try block with statements from crash point to end
             CtTry tryBlock = factory.Core().createTry();
             CtBlock<?> tryBody = factory.Core().createBlock();
             
             // Add all statements from crash point to end to try body
             for (int i = crashIndex; i < allStatements.size(); i++) {
                 tryBody.addStatement(allStatements.get(i).clone());
             }
             
             // Add fail() assertion
             tryBody.addStatement(factory.Code().createCodeSnippetStatement(
                     "org.junit.Assert.fail(\"Expecting exception: " + errorType + "\")"));
             
             tryBlock.setBody(tryBody);
             
             // Create catch block
             StackTraceElement cutFrame = findCUTFrame(stackTrace);
             tryBlock.addCatcher(createCatcher(factory, errorType, originalErrorType, cutFrame, true, testMethod.getSimpleName()));
             
             // Replace from crash point with try block
             // Remove statements from crash point to end
             for (int i = allStatements.size() - 1; i >= crashIndex; i--) {
                 allStatements.remove(i);
             }
             
             // Add try-catch block
             allStatements.add(tryBlock);
             
             if (DEBUG_ORACLE_TRANSFORM) {
                 System.out.println("[TryCatchFailAdder-WholeWrap] ✓ Wrapped from crash point successfully");
             }
             
             return new Pair<>(ctMethod, ctMethod.toString());
             
         } catch (Exception e) {
             if (DEBUG_ORACLE_TRANSFORM) {
                 System.out.println("[TryCatchFailAdder-WholeWrap] ✗ Error during wrap: " + e.getMessage());
                 e.printStackTrace();
             }
             // Fallback to default behavior
             return addTryCatchFailDefault(testMethod, failure, launcher, executedFileContent);
         }
     }
     
     /**
      * Helper method to wrap the entire method body
      */
     private static Pair<CtMethod, String> wrapEntireMethod(CtMethod ctMethod, Factory factory,
             String errorType, String originalErrorType, StackTraceElement[] stackTrace, String testMethodName) {
         
         if (DEBUG_ORACLE_TRANSFORM) {
             System.out.println("[TryCatchFailAdder-WholeWrap] Wrapping entire method body");
         }
         
         // Get current method body statements
         CtBlock<?> methodBody = ctMethod.getBody();
         List<CtStatement> originalStatements = new ArrayList<>(methodBody.getStatements());
         
         // Clear the method body
         methodBody.getStatements().clear();
         
         // Create try block
         CtTry tryBlock = factory.Core().createTry();
         CtBlock<?> tryBody = factory.Core().createBlock();
         
         // Add all original statements to try body
         for (CtStatement stmt : originalStatements) {
             tryBody.addStatement(stmt.clone());
         }
         
         // Add fail() assertion
         tryBody.addStatement(factory.Code().createCodeSnippetStatement(
                 "org.junit.Assert.fail(\"Expecting exception: " + errorType + "\")"));
         
         tryBlock.setBody(tryBody);
         
         // Create catch block
         StackTraceElement cutFrame = findCUTFrame(stackTrace);
         tryBlock.addCatcher(createCatcher(factory, errorType, originalErrorType, cutFrame, true, testMethodName));
         
         // Add try-catch to method body
         methodBody.addStatement(tryBlock);
         
         return new Pair<>(ctMethod, ctMethod.toString());
     }
    
    /**
     * [모드 3] MULTIPLE_GENERATION: 반복 실행 및 Oracle 재생성
     * ENABLE_MULTIPLE_ORACLE_GEN = true일 때 호출됨
     * 
     * 참고: 실제 반복 실행은 Compiler에서 처리하므로 이 메서드는 단일 Oracle만 추가
     */
    private static Pair<CtMethod, String> addTryCatchFailWithMultipleGeneration(CtMethod testMethod, Failure failure,
            Launcher launcher, String executedFileContent) {
        
        if (DEBUG_ORACLE_TRANSFORM) {
            System.out.println("[TryCatchFailAdder-MultipleGen] ========================================");
            System.out.println("[TryCatchFailAdder-MultipleGen] Adding single oracle (iteration handled by Compiler)");
            System.out.println("[TryCatchFailAdder-MultipleGen] Test: " + testMethod.getSimpleName());
        }
        
        // MULTIPLE_ORACLE_GEN 모드에서도 단일 Oracle 추가는 기본 로직 사용
        // 반복 실행은 Compiler.addTryCatchFailWithMultipleAttempts()에서 처리
        return addTryCatchFailDefault(testMethod, failure, launcher, executedFileContent);
    }
    
    /**
     * 주어진 CtElement(invocation, statement 등)가 이미 try-catch 블록 안에 감싸져 있는지 확인
     * fail() assertion이 있는 try-catch 블록인 경우에만 "이미 처리됨"으로 간주
     * 
     * [FIX] parent가 초기화되지 않은 경우를 처리
     */
    private static boolean isAlreadyWrappedInTryCatch(CtElement element) {
        if (element == null) {
            return false;
        }
        
        CtElement current = element;
        
        // 부모를 따라 올라가면서 try-catch 블록 찾기
        while (current != null) {
            try {
                current = current.getParent();
            } catch (Exception e) {
                // parent가 초기화되지 않은 경우
                if (DEBUG_ORACLE_TRANSFORM) {
                    System.out.println("[TryCatchFailAdder]       Warning: parent not initialized, stopping search: " + e.getMessage());
                }
                return false;
            }
            
            if (current instanceof CtTry) {
                CtTry tryBlock = (CtTry) current;
                
                try {
                    // try 블록 안에 fail() assertion이 있는지 확인
                    // fail() assertion이 있으면 이미 oracle이 추가된 것
                    List<CtInvocation<?>> invocations = tryBlock.getBody()
                        .getElements(new TypeFilter<>(CtInvocation.class));
                    
                    for (CtInvocation<?> inv : invocations) {
                        if (inv.getExecutable() != null) {
                            String methodName = inv.getExecutable().getSimpleName();
                            String className = inv.getExecutable().getDeclaringType() != null ?
                                inv.getExecutable().getDeclaringType().getQualifiedName() : "";
                            
                            // org.junit.Assert.fail()이나 Assert.fail() 호출 확인
                            if ("fail".equals(methodName) && 
                                (className.contains("junit.Assert") || className.contains("Assert"))) {
                                if (DEBUG_ORACLE_TRANSFORM) {
                                    System.out.println("[TryCatchFailAdder]       Found existing try-catch with fail() assertion");
                                }
                                return true;
                            }
                        }
                    }
                } catch (Exception e) {
                    // 내용 검색 중 오류 발생
                    if (DEBUG_ORACLE_TRANSFORM) {
                        System.out.println("[TryCatchFailAdder]       Warning: error checking try-catch content: " + e.getMessage());
                    }
                    // 오류가 발생했으면 이미 감싸진 것으로 간주하지 않음
                    continue;
                }
            }
        }
        
        return false;
    }

}