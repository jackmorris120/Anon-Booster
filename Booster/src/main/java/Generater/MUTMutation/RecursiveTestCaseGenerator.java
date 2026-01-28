package Generater.MUTMutation;

import spoon.reflect.code.*;
import spoon.reflect.declaration.*;
import spoon.reflect.factory.Factory;
import spoon.reflect.reference.CtTypeReference;
import spoon.reflect.reference.CtVariableReference;
import spoon.reflect.reference.CtExecutableReference;
import spoon.support.reflect.code.*;
import utils.Pair;
import spoon.Launcher;
import spoon.reflect.visitor.DefaultJavaPrettyPrinter;
import Generater.MUTMutation.ASTParser;
import RegressionOracles.Analyzer;
import RegressionOracles.ObserverInstrumenter;
import utils.Config;

import java.lang.annotation.Annotation;
import java.util.*;

public class RecursiveTestCaseGenerator {
    private String testClassName;
    private String packageAndImport;
    private Map<String, Integer> mutCountMap;
    private Random random;
    private Factory factory;
    private static final int MAX_RECURSION_DEPTH = 5;
    public int duplicateCount = 0;
    private final Analyzer analyzer;
    private final ObserverInstrumenter collector;
    
    // Track which objects have been used for each MUT to avoid reusing same objects
    // Key: MUT signature, Value: Map of type -> used object names
    private Map<String, Map<String, Set<String>>> mutUsedObjectsMap = new HashMap<>();
    
    // Track objects used in first N arguments for T-way like behavior (avoiding duplicates)
    // Key: MUT signature, Value: Set of (type_position -> object_name) patterns used
    private static final int NUM_FIRST_ARGS_FOR_DIVERSITY = 2;  // First N arguments to ensure diversity
    private Map<String, Set<String>> mutFirstArgDiversityMap = new HashMap<>();
    
    // Combinatorial testing support - manages combination generators per MUT
    private Map<MUTInput, CombinationGenerator> combinationGenerators = new HashMap<>();
    
    // Debug flags - set to true to enable verbose logging
    private static final boolean DEBUG_RECURSIVE_GEN = false;  // For resolveType, processStatementDependencies, etc.
    private static final boolean DEBUG_ORACLE = false;          // For oracle instrumentation process
    private static final boolean DEBUG_COMBINATORIAL = false;   // For combinatorial testing details

    public RecursiveTestCaseGenerator(String testClassName, String packageAndImport) {
        this.testClassName = testClassName;
        this.packageAndImport = packageAndImport;
        this.mutCountMap = new HashMap<>();
        this.random = new Random();
        Launcher launcher = new Launcher();
        this.factory = launcher.getFactory();
        this.analyzer = new Analyzer();
        this.collector = new ObserverInstrumenter(this.factory);
    }
    
     private static void debugLog(String message) {
         if (DEBUG_RECURSIVE_GEN) {
             System.out.println(message);
         }
     }

     
     private static void debugOracleLog(String message) {
         if (DEBUG_ORACLE) {
             System.out.println(message);
         }
     }
     
     private static void debugCombiLog(String message) {
         if (DEBUG_COMBINATORIAL) {
             System.out.println(message);
         }
     }

    public Pair<CtClass, String> generateTest(MUTInput mutInput, int index, boolean allStacked) {
          // System.out.println("\n[generateTest] Attempting to generate test for MUT: " + mutInput.getMUTInvocation());
          // System.out.println("[generateTest] MUT signature: " + mutInput.getMethodSignature());
          // System.out.println("[generateTest] Input pools: " + (mutInput.getInputs() != null ? mutInput.getInputs().size() : 0));
          
          if(DEBUG_RECURSIVE_GEN){
              System.out.println("\n##################################################");
              System.out.println("##  New Test Gen for  : "+mutInput.getMUTInvocation());
              System.out.println("##################################################");
              }
          
          CtAbstractInvocation mut = mutInput.getMUTInvocation();
          String mutSignature = mut.getExecutable().getSignature();
          
          // Initialize tracking for this MUT if not present
          mutUsedObjectsMap.putIfAbsent(mutSignature, new HashMap<>());
          
          List<CtStatement> stmts = new ArrayList<>();
          Map<String, Integer> varNameCounter = new HashMap<>();
          Set<String> usedStmtPatterns = new HashSet<>();
          
          try {
              CtAbstractInvocation clonedMut = (CtAbstractInvocation) mut.clone();
              CtAbstractInvocation filledMUT = fillMUTArguments(clonedMut, mutInput, stmts, varNameCounter, usedStmtPatterns, 0, mutSignature);
            
             if (filledMUT != null) {
                // In REGRESSION_MODE, wrap non-void MUT result in a variable assignment
                CtStatement mutStatement = (CtStatement) filledMUT;
                if (Config.REGRESSION_MODE && filledMUT instanceof CtInvocation) {
                    CtInvocation invocation = (CtInvocation) filledMUT;
                    CtTypeReference<?> returnType = invocation.getType();
                    
                    if (returnType != null && 
                        !returnType.getSimpleName().equals("void") &&
                        !invocation.getExecutable().getSimpleName().equals("hashCode")) {
                        
                        debugOracleLog("[Oracle] MUT has non-void return type: " + returnType.getQualifiedName() + ", wrapping in variable");
                        
                        String name = returnType.getSimpleName().toLowerCase().replace("[", "").replace("]", "");
                        String qualifiedName = returnType.getQualifiedName();
                        
                        // Check if this is a generic type variable
                        if (qualifiedName.length() == 1 && Character.isUpperCase(qualifiedName.charAt(0))) {
                            qualifiedName = "java.lang.Object";
                        }
                        
                        CtTypeReference<?> fqnTypeRef = factory.createReference(qualifiedName);
                        fqnTypeRef.setImplicit(false);
                        
                        CtLocalVariable mutVariable = factory.createLocalVariable(
                            fqnTypeRef,
                            name + "_mut",
                            invocation
                        );
                        mutStatement = mutVariable;
                        debugOracleLog("[Oracle] Created MUT variable: " + name + "_mut");
                    } else {
                        debugOracleLog("[Oracle] MUT has void return or is hashCode, not wrapping in variable");
                    }
                } else if (Config.REGRESSION_MODE && filledMUT instanceof CtConstructorCall) {
                    CtConstructorCall ctorCall = (CtConstructorCall) filledMUT;
                    CtTypeReference<?> returnType = ctorCall.getType();
                    
                    if (returnType != null) {
                        debugOracleLog("[Oracle] MUT is constructor call, return type: " + returnType.getQualifiedName() + ", wrapping in variable");
                        
                        String name = returnType.getSimpleName().toLowerCase().replace("[", "").replace("]", "");
                        String qualifiedName = returnType.getQualifiedName();
                        
                        CtTypeReference<?> fqnTypeRef = factory.createReference(qualifiedName);
                        fqnTypeRef.setImplicit(false);
                        
                        CtLocalVariable mutVariable = factory.createLocalVariable(
                            fqnTypeRef,
                            name + "_mut",
                            ctorCall
                        );
                        mutStatement = mutVariable;
                        debugOracleLog("[Oracle] Created MUT variable: " + name + "_mut");
                    }
                }
                
                stmts.add(mutStatement);
                
                // Use method simple name (like TestCaseGenerator does)
                String mutName = mut.getExecutable() != null ? mut.getExecutable().getSimpleName() : "unknown";
                if (mutName.contains("<init>")) { // <> cannot be used in class name
                    mutName = "init";
                }
                // Use index parameter to ensure unique method names across both generators
                // This prevents duplicate method names when multiple tests are merged into MegaClass
                String testNameId = mutName + "_" + index;
                String generatedClassName = testClassName + "_M_" + testNameId;
                
                 CtClass<Object> testClass = factory.Core().createClass();
                 testClass.setSimpleName(generatedClassName);
                 
                 // Make class PUBLIC (required for JUnit)
                 Set<ModifierKind> classModifiers = new HashSet<>();
                 classModifiers.add(ModifierKind.PUBLIC);
                 testClass.setModifiers(classModifiers);
                 
                 CtMethod<Object> testMethod = factory.createMethod();
                testMethod.setSimpleName("test");
                Set<ModifierKind> methodModifiers = new HashSet<>();
                methodModifiers.add(ModifierKind.PUBLIC);
                testMethod.setModifiers(methodModifiers);
                
                CtTypeReference<Object> returnValue = factory.createTypeReference();
                returnValue.setSimpleName("void");
                testMethod.setType(returnValue);
                
                CtTypeReference<? extends Throwable> throwable = factory.createTypeReference();
                throwable.setSimpleName("Throwable");
                Set<CtTypeReference<? extends Throwable>> throwsExp = new HashSet<>();
                throwsExp.add(throwable);
                testMethod.setThrownTypes(throwsExp);
                
                CtAnnotationType testRefer = factory.createAnnotationType("Test");
                CtAnnotation<Annotation> testAnno = factory.createAnnotation();
                testAnno.setAnnotationType(testRefer.getReference());
                testAnno.addValue("timeout", 1000);
                List<CtAnnotation<? extends Annotation>> annotation = new LinkedList<>();
                annotation.add(testAnno);
                testMethod.setAnnotations(annotation);
                
                 CtBlock<Object> methodBody = factory.createBlock();
                 
                 // Use original statements directly for oracle analysis (like TestCaseGenerator)
                 // Do NOT convert to CtCodeSnippetStatement, otherwise Analyzer cannot find variables
                 methodBody.setStatements(stmts);
                 testMethod.setBody(methodBody);
                
                // Add regression oracle if in REGRESSION_MODE
                debugOracleLog("[Oracle] Config.REGRESSION_MODE = " + Config.REGRESSION_MODE);
                if (Config.REGRESSION_MODE) {
                    // debugOracleLog("[Oracle] Entering REGRESSION_MODE block - adding oracle instrumentation");
                    // Generate class and method strings BEFORE adding method to class
                    Launcher tempLauncher = new Launcher();
                    spoon.compiler.Environment tempEnv = tempLauncher.getEnvironment();
                    tempEnv.setAutoImports(true);
                    tempEnv.setNoClasspath(true);
                    DefaultJavaPrettyPrinter printer = new DefaultJavaPrettyPrinter(tempEnv);
                    String classStr = printer.prettyprint(testClass);
                    String methodStr = printer.prettyprint(testMethod);
                    
                    debugOracleLog("[Oracle] Generated class and method strings, adding method to class");
                    // Now add method to class for oracle analysis
                    testClass.addMethod(testMethod);
                    
                    // Fix undefined variables before oracle analysis
                    fixUndefinedVariablesInMethod(testMethod);
                    
                    debugOracleLog("[Oracle] Calling addRegressionOracleToTest()");
                    Pair<CtClass, List<String>> observerAddedTestAndStringPair = addRegressionOracleToTest(testClass);
                    
                    debugOracleLog("[Oracle] addRegressionOracleToTest returned: " + (observerAddedTestAndStringPair != null ? "non-null" : "null"));
                    if (observerAddedTestAndStringPair != null) {
                        debugOracleLog("[Oracle] Oracle value list: " + (observerAddedTestAndStringPair.getValue() != null ? observerAddedTestAndStringPair.getValue().size() + " oracles" : "null"));
                    }
                    
                    if (observerAddedTestAndStringPair != null && observerAddedTestAndStringPair.getValue() != null) {
                        debugOracleLog("[Oracle] Processing " + observerAddedTestAndStringPair.getValue().size() + " oracle statements");
                        // Combine strings just like TestCaseGenerator
                        int oracleCount = 0;
                        for (String oracle : observerAddedTestAndStringPair.getValue()) {
                            oracleCount++;
                            debugOracleLog("[Oracle] Adding oracle #" + oracleCount + ": " + (oracle.length() > 50 ? oracle.substring(0, 50) + "..." : oracle));
                            if (!oracle.contains("RegressionOracles.RegressionUtil.Logger.observe")) {
                                oracle = oracle.trim() + " // if statement for MUT null check";
                                methodStr = methodStr.substring(0, methodStr.lastIndexOf("}"));
                                methodStr = methodStr + "\t" + oracle + "\n}";
                            } else {
                                methodStr = methodStr.substring(0, methodStr.lastIndexOf("}"));
                                methodStr = methodStr + "\t\t" + oracle.trim() + "\n}";
                            }
                        }
                        methodStr = "\t" + methodStr.replaceAll("\n", "\n\t");
                        String finalStr = classStr.substring(0, classStr.lastIndexOf("}")) + "\n" + methodStr + "\n}";
                        finalStr = fixSpecialConstants(finalStr);
                        debugOracleLog("[Oracle] Successfully created test with " + oracleCount + " oracles");
                        
                 // Print individual test to verify it doesn't have the class variable issue
                 // System.out.println("\n========== INDIVIDUAL TEST GENERATED (WITH ORACLE) ==========");
                 // System.out.println("Test Method: " + testMethod.getSimpleName());
                 // System.out.println("Full Test Class:\n" + finalStr);
                 // System.out.println("=============================================================\n");
                        
                        return new Pair<>(observerAddedTestAndStringPair.getKey(), finalStr);
                    } else {
                        debugOracleLog("[Oracle] WARNING: observerAddedTestAndStringPair or its value is null, falling back to non-oracle mode");
                    }
                } else {
                    debugOracleLog("[Oracle] REGRESSION_MODE is false, skipping oracle instrumentation");
                }
                
                // Non-regression mode: just add method and return
                testClass.addMethod(testMethod);
                
                // Fix undefined variables before converting to string
                fixUndefinedVariablesInMethod(testMethod);
                
                debugOracleLog("[Oracle] Returning test WITHOUT oracle (non-regression mode)");
                String classStr = fixSpecialConstants(testClass.toString());
                
                 // Print individual test to verify it doesn't have the class variable issue
                 // System.out.println("\n========== INDIVIDUAL TEST GENERATED ==========");
                 // System.out.println("Test Method: " + testMethod.getSimpleName());
                 // System.out.println("Full Test Class:\n" + classStr);
                 // System.out.println("===============================================\n");
                
                return new Pair<>(testClass, classStr);
            }
            
            return null;
         } catch (Exception e) {
             // System.err.println("[RecursiveGen] ✗ Exception during test generation");
             // e.printStackTrace();
             return null;
         }
    }

    private CtAbstractInvocation fillMUTArguments(CtAbstractInvocation mut, MUTInput mutInput, 
                                                   List<CtStatement> stmts, Map<String, Integer> varNameCounter, 
                                                   Set<String> usedStmtPatterns, int depth, String mutSignature) {
         List<CtTypeReference> argTypes = mutInput.getArgTypes();
         List<CtExpression> newArgs = new ArrayList<>();
         
         // Get Input pools from MUTInput (position -> List<Input>)
         LinkedHashMap<Integer, List<Input>> inputPools = mutInput.getInputs();
        
        // Get or create CombinationGenerator for this MUT (TestCaseGenerator style)
        CombinationGenerator combiGenerator = combinationGenerators.get(mutInput);
        if (combiGenerator == null && inputPools != null && !inputPools.isEmpty()) {
            // Initialize sorted pools and t-way candidates
            if (mutInput.getSortedInputPools() == null) {
                mutInput.initSortedInputPools(inputPools);
            }
            mutInput.initTwayCandidates();
            mutInput.setCurrentPositions(0);
            
            // Build selected pools based on current t-way positions
            LinkedHashMap<Integer, List<Input>> selectedPools = new LinkedHashMap<>();
            for (Integer pos : mutInput.getCurrentPositions()) {
                if (mutInput.isStatic() && pos == 0) {
                    continue;
                }
                List<Input> pool = inputPools.get(pos);
                if (pool != null && !pool.isEmpty()) {
                    selectedPools.put(pos, pool);
                }
            }
            
            if (!selectedPools.isEmpty()) {
                int adjustedTWay = Math.min(mutInput.getTWay(), selectedPools.size());
                combiGenerator = new CombinationGenerator(selectedPools, adjustedTWay);
                combinationGenerators.put(mutInput, combiGenerator);
            }
        }
        
        // Get next combination from generator
        Map<Integer, Integer> combiMap = null;
        if (combiGenerator != null && combiGenerator.hasNext()) {
            combiMap = combiGenerator.nextCombination();
            if (combiMap != null) {
                // Print combination in simple format: "pos,idx pos,idx ..."
                StringBuilder combiStr = new StringBuilder();
                for (Map.Entry<Integer, Integer> entry : combiMap.entrySet()) {
                    if (combiStr.length() > 0) combiStr.append(" ");
                    combiStr.append(entry.getKey()).append(",").append(entry.getValue());
                }
                debugCombiLog("[Combi] " + mutSignature + " | " + combiStr.toString());
            }
        }
        
        // Process each argument position
        for (int i = 0; i < argTypes.size(); i++) {
            CtTypeReference requiredType = argTypes.get(i);
            
            // Handle receiver (position 0 for non-static methods)
            if (i == 0 && !mutInput.isStatic() && !(mut instanceof CtConstructorCall)) {
                CtExpression receiverExpr = null;
                
                 // Try to get receiver from Input pool first
                 if (combiMap != null && combiMap.containsKey(0)) {
                     List<Input> receiverPool = inputPools.get(0);
                     if (receiverPool != null && !receiverPool.isEmpty()) {
                         int selectedIdx = combiMap.get(0);
                         if (selectedIdx < receiverPool.size()) {
                             Input receiverInput = receiverPool.get(selectedIdx);
                             debugLog("[Combinatorial] Using receiver from pool at index " + selectedIdx);
                             receiverExpr = processInputLastStmtOnly(receiverInput, stmts, varNameCounter, usedStmtPatterns, depth);
                             // [중요] Receiver가 null literal이면 다른 input 시도
                             if (receiverExpr instanceof CtLiteral && ((CtLiteral) receiverExpr).getValue() == null) {
                                 debugLog("[fillMUTArguments] Receiver from pool is null literal, trying other inputs");
                                 receiverExpr = null;
                             }
                         }
                     }
                 }
                
                // Fallback to receiverInputMap if combiMap didn't provide one
                if (receiverExpr == null && requiredType == null) {
                    Map<String, Input> receiverMap = mutInput.getReceiverInputMap();
                    if (receiverMap != null && !receiverMap.isEmpty()) {
                        Input receiverInput = receiverMap.values().iterator().next();
                        if (receiverInput != null && receiverInput.getVarName() != null) {
                            String varName = ((CtElement) receiverInput.getVarName()).toString();
                            receiverExpr = createVariableRead(varName, null);
                        }
                    }
                }
                
                  // Fallback to resolveType
                  if (receiverExpr == null && requiredType != null) {
                      // System.out.println("[fillMUTArguments] Attempting to resolve receiver type: " + requiredType.getQualifiedName());
                      receiverExpr = resolveType(requiredType, stmts, varNameCounter, usedStmtPatterns, depth);
                      
                      // [중요] resolveType이 null literal을 반환한 경우 Pool에서 찾기
                      if (receiverExpr instanceof CtLiteral && ((CtLiteral) receiverExpr).getValue() == null) {
                          debugLog("[fillMUTArguments] resolveType returned null literal for receiver, searching pool");
                          CtExpression fromPool = findValueFromPool(requiredType);
                          if (fromPool != null) {
                              debugLog("[fillMUTArguments] Found receiver from pool");
                              receiverExpr = fromPool;
                          } else {
                              CtExpression anyValue = findAnyValueFromPool();
                              if (anyValue != null) {
                                  debugLog("[fillMUTArguments] Found any value from pool as receiver");
                                  receiverExpr = anyValue;
                              }
                          }
                      }
                  }
                  
                  if (receiverExpr == null) {
                      // System.out.println("[fillMUTArguments] ERROR: Could not resolve receiver");
                      return null;
                  }
                  
                  // System.out.println("[fillMUTArguments] Successfully resolved receiver");
                 
                  if (mut instanceof CtInvocation) {
                      if (receiverExpr instanceof CtLiteral && ((CtLiteral) receiverExpr).getValue() == null) {
                          debugLog("[fillMUTArguments] ERROR: receiver is still null literal after all attempts, rejecting test");
                          // System.out.println("[fillMUTArguments] ERROR: receiver is null literal");
                          return null;
                      }
                     if (receiverExpr instanceof CtVariableRead) {
                         ((CtInvocation) mut).setTarget(receiverExpr);
                     } else {
                         // System.out.println("[fillMUTArguments] ERROR: receiver is not CtVariableRead: " + receiverExpr.getClass().getSimpleName());
                         return null;
                     }
                 }
            } 
            // Handle regular arguments
            else if (i > 0 || mutInput.isStatic() || mut instanceof CtConstructorCall) {
                if (requiredType == null) {
                    continue;
                }
                
                CtExpression argExpr = null;
                
                // Try to use Input from combinatorial selection first
                if (combiMap != null && combiMap.containsKey(i)) {
                    List<Input> pool = inputPools.get(i);
                    if (pool != null && !pool.isEmpty()) {
                        int selectedIdx = combiMap.get(i);
                        if (selectedIdx < pool.size()) {
                            Input selectedInput = pool.get(selectedIdx);
                            debugCombiLog("[Combinatorial] Position " + i + ": using Input at index " + selectedIdx + "/" + pool.size() + " (from combiMap)");
                            argExpr = processInputLastStmtOnly(selectedInput, stmts, varNameCounter, usedStmtPatterns, depth);
                            
                            // [핵심] 타입 일치 확인: 필요한 타입과 실제 Input 타입이 다르면 사용 불가
                            if (argExpr != null && !isArgumentTypeCompatible(argExpr, requiredType)) {
                                debugCombiLog("[Combinatorial] Position " + i + ": Input type mismatch (expected " + requiredType.getQualifiedName() + "), falling back to resolveType");
                                argExpr = null;  // 타입 불일치이므로 reset
                            }
                        }
                    }
                }
                
                // If not in combiMap, try random selection from Input pool
                if (argExpr == null && inputPools != null) {
                    List<Input> pool = inputPools.get(i);
                    if (pool != null && !pool.isEmpty()) {
                        int randomIdx = random.nextInt(pool.size());
                        Input randomInput = pool.get(randomIdx);
                        debugCombiLog("[Combinatorial] Position " + i + ": using random Input at index " + randomIdx + "/" + pool.size());
                        argExpr = processInputLastStmtOnly(randomInput, stmts, varNameCounter, usedStmtPatterns, depth);
                        
                        // [핵심] 타입 일치 확인
                        if (argExpr != null && !isArgumentTypeCompatible(argExpr, requiredType)) {
                            debugCombiLog("[Combinatorial] Position " + i + ": Input type mismatch (expected " + requiredType.getQualifiedName() + "), falling back to resolveType");
                            argExpr = null;  // 타입 불일치이므로 reset
                        }
                    }
                }
                
                // Final fallback to resolveType if Input processing failed or type mismatch
                if (argExpr == null) {
                    debugCombiLog("[Combinatorial] Position " + i + ": falling back to resolveType (no valid Input or type mismatch)");
                    argExpr = resolveType(requiredType, stmts, varNameCounter, usedStmtPatterns, depth);
                    if (argExpr == null) {
                        return null;
                    }
                }
                
                newArgs.add(argExpr);
            }
        }
        
        mut.setArguments((List) newArgs);
        return mut;
    }

    private CtExpression resolveType(CtTypeReference<?> type, List<CtStatement> stmts, 
                                      Map<String, Integer> varNameCounter, Set<String> usedStmtPatterns, int depth) {
         debugLog("\n[resolveType][Depth:" + depth + "] ===== START resolveType =====");
         debugLog("[resolveType][Depth:" + depth + "] Type: " + (type != null ? type.getQualifiedName() : "null"));
         
         if (type == null) {
             debugLog("[resolveType][Depth:" + depth + "] Type is null, returning null literal");
             return factory.createLiteral(null);
         }

         debugLog("[resolveType][Depth:" + depth + "] Resolving type: " + type.getQualifiedName());

         if (isPrimitiveOrString(type)) {
             debugLog("[resolveType][Depth:" + depth + "] Type is primitive/String, getting direct value");
             return getDirectValue(type);
         }
         
         // Special handling for Class type - return directly without wrapping in variable
         if ("java.lang.Class".equals(type.getQualifiedName())) {
             debugLog("[resolveType][Depth:" + depth + "] Type is Class, returning direct expression");
             return factory.createCodeSnippetExpression("Object.class");
         }
         
         if (depth >= MAX_RECURSION_DEPTH) {
             debugLog("[RecursiveGen][Depth:" + depth + "] ⚠ MAX_DEPTH reached for type: " + type.getQualifiedName() + "! Using full sequence without recursion");
             return resolveTypeWithFullSequence(type, stmts, varNameCounter);
         }
         
           // Keep trying different candidates until we find a valid sequence
           Set<Pair<CtTypeReference, CtElement>> triedCandidates = new HashSet<>();
           int candidateAttemptCount = 0;
           int maxCandidateAttempts = 10;
           
           while (candidateAttemptCount < maxCandidateAttempts) {
               debugLog("[resolveType][Depth:" + depth + "] === Candidate attempt " + (candidateAttemptCount + 1) + " ===");
               debugLog("[resolveType][Depth:" + depth + "] Calling selectBestCandidateFromPool...");
               // ★ 통합 메소드: 정확한 타입 + 구현체 모두 검색
               Pair<CtTypeReference, CtElement> candidate = selectBestCandidateFromPool(type, triedCandidates);
               CtElement candidateElement = null;
               CtTypeReference candidateType = null;
               debugLog("[resolveType][Depth:" + depth + "] selectBestCandidateFromPool returned: " + (candidate != null ? "FOUND" : "null"));
                
               if (candidate == null) {
                   debugLog("[resolveType][Depth:" + depth + "] No candidate found, returning direct value");
                   return getDirectValue(type);
               }
              
              // Skip if already tried
              if (triedCandidates.contains(candidate)) {
                  debugLog("[resolveType][Depth:" + depth + "] Already tried this candidate, trying another...");
                  candidateAttemptCount++;
                  continue;
              }

              candidateElement = candidate.getValue();
              candidateType = candidate.getKey();
              triedCandidates.add(candidate);
             
              debugLog("[resolveType][Depth:" + depth + "] Found candidate!");
               
               // ★ 더 자세한 candidate 정보 출력
               String candName = getCandidateName(candidate);
               CtTypeReference candType = candidate.getKey();
               debugLog("[resolveType][Depth:" + depth + "] ================== CANDIDATE DETAILS ==================");
               debugLog("[resolveType][Depth:" + depth + "] Candidate Name: " + candName);
               debugLog("[resolveType][Depth:" + depth + "] Candidate Type: " + candType.getQualifiedName());
               debugLog("[resolveType][Depth:" + depth + "] Requested Type: " + type.getQualifiedName());
               debugLog("[resolveType][Depth:" + depth + "] Type Match: " + (typeMatches(candType, type) ? "✓ YES" : "✗ NO"));
               debugLog("[resolveType][Depth:" + depth + "] Candidate Element: " + candidate.getValue().getClass().getSimpleName());
               debugLog("[resolveType][Depth:" + depth + "] =====================================================");
               
               Set<List<CtElement>> sequences = CandidatePool.getVartypeToInputPool().get(candidate);
               debugLog("[resolveType][Depth:" + depth + "] Sequences found: " + (sequences != null ? sequences.size() : "null"));
               
               if (sequences == null || sequences.isEmpty()) {
                   debugLog("[resolveType][Depth:" + depth + "] No sequences found for candidate, trying next candidate...");
                   candidateAttemptCount++;
                   continue;
               }
              
               debugLog("[resolveType][Depth:" + depth + "] Found " + sequences.size() + " sequences for candidate");
              
               // Keep trying sequences until we find a valid one
               CtElement lastElement = null;
               List<CtElement> chosenSequence = null;
               int attemptCount = 0;
               int maxAttempts = sequences.size() + 5;
          
           while (attemptCount < maxAttempts) {
               chosenSequence = selectRandomSequenceAvoidingUsed(sequences, usedStmtPatterns);
               debugLog("[resolveType][Depth:" + depth + "] ========== SEQUENCE SELECTION ==========");
               debugLog("[resolveType][Depth:" + depth + "] Attempt " + (attemptCount + 1) + " / " + maxAttempts);
               debugLog("[resolveType][Depth:" + depth + "] Chosen sequence size: " + (chosenSequence != null ? chosenSequence.size() + " elements" : "null"));
               if (chosenSequence != null && !chosenSequence.isEmpty()) {
                   CtElement lastElem = chosenSequence.get(chosenSequence.size() - 1);
                   debugLog("[resolveType][Depth:" + depth + "] Last element in sequence: " + lastElem.getClass().getSimpleName());
                   if (lastElem instanceof CtLocalVariable) {
                       CtLocalVariable lastVar = (CtLocalVariable) lastElem;
                       debugLog("[resolveType][Depth:" + depth + "] Variable name: " + lastVar.getSimpleName());
                       debugLog("[resolveType][Depth:" + depth + "] Variable type: " + (lastVar.getType() != null ? lastVar.getType().getQualifiedName() : "null"));
                   }
               }
               debugLog("[resolveType][Depth:" + depth + "] ========================================");
              
              if (chosenSequence == null || chosenSequence.isEmpty()) {
                  debugLog("[resolveType][Depth:" + depth + "] Chosen sequence is empty or all used, returning direct value");
                  return getDirectValue(type);
              }
              
               lastElement = chosenSequence.get(chosenSequence.size() - 1);
               debugLog("[resolveType][Depth:" + depth + "] Last element type: " + lastElement.getClass().getSimpleName());
               
                // Check if last statement is problematic (bare CtInvocation that may reference undefined variables)
                if (lastElement instanceof CtInvocation && !(lastElement instanceof CtLocalVariable)) {
                    debugLog("[resolveType][Depth:" + depth + "] WARNING: Last statement is bare CtInvocation (not wrapped in CtLocalVariable), trying next sequence...");
                    attemptCount++;
                    continue;
                }
                
                // Check if last statement actually declares the type we want
                if (!(lastElement instanceof CtLocalVariable)) {
                    debugLog("[resolveType][Depth:" + depth + "] WARNING: Last element is not CtLocalVariable, trying next sequence...");
                    attemptCount++;
                    continue;
                }
                
                CtLocalVariable lastVar = (CtLocalVariable) lastElement;
                CtTypeReference declaredType = lastVar.getType();
                
                // [핵심 수정] typeMatches 대신 isTypeCompatible 사용 (subtype 허용)
                // Check if declared type is compatible with the requested type (allows subtypes)
                if (declaredType == null || !isTypeCompatible(declaredType, type)) {
                    debugLog("[resolveType][Depth:" + depth + "] WARNING: Last statement declares " + 
                        (declaredType != null ? declaredType.getQualifiedName() : "null") + 
                        " but we need " + type.getQualifiedName() + ", trying next sequence...");
                    attemptCount++;
                    continue;
                }
                
                // Special check for java.lang.Class type - reject null assignments
                if ("java.lang.Class".equals(type.getQualifiedName())) {
                    CtExpression defaultExpr = lastVar.getDefaultExpression();
                    if (defaultExpr instanceof CtLiteral && ((CtLiteral) defaultExpr).getValue() == null) {
                        debugLog("[resolveType][Depth:" + depth + "] WARNING: Class type with null value, trying next sequence...");
                        attemptCount++;
                        continue;
                    }
                }
                
                // Check if default expression type is compatible with requested type
                CtExpression defaultExpr = lastVar.getDefaultExpression();
                if (defaultExpr != null) {
                    CtTypeReference exprType = null;
                    
                    // Handle VariableRead
                    if (defaultExpr instanceof CtVariableRead) {
                        exprType = defaultExpr.getType();
                    } 
                    // Handle casting (CtUnaryOperator)
                    else if (defaultExpr instanceof spoon.reflect.code.CtUnaryOperator) {
                        spoon.reflect.code.CtUnaryOperator unaryOp = (spoon.reflect.code.CtUnaryOperator) defaultExpr;
                        CtExpression operand = unaryOp.getOperand();
                        if (operand instanceof CtVariableRead) {
                            exprType = operand.getType();
                        }
                    }
                    
                    if (exprType != null && !typeMatches(exprType, type)) {
                        // Check if it's at least a valid subtype relationship
                        boolean isValidCast = false;
                        try {
                            // MapType is subtype of JavaType, so JavaType cannot be cast to MapType
                            if (type.isSubtypeOf(exprType)) {
                                // Requested type is subtype of expression type - invalid upcast!
                                debugLog("[resolveType][Depth:" + depth + "] WARNING: Invalid upcast detected - cannot cast " + 
                                    exprType.getQualifiedName() + " to its subtype " + type.getQualifiedName() + ", trying next sequence...");
                                attemptCount++;
                                continue;
                            } else if (exprType.isSubtypeOf(type)) {
                                // Expression type is subtype - valid downcast
                                isValidCast = true;
                            }
                        } catch (Exception e) {
                            // Ignore subtype check errors
                        }
                        
                        if (!isValidCast) {
                            debugLog("[resolveType][Depth:" + depth + "] WARNING: Default expression type " + 
                                exprType.getQualifiedName() + " is not compatible with requested type " + 
                                type.getQualifiedName() + ", trying next sequence...");
                            attemptCount++;
                            continue;
                        }
                     }
                     
                     if (defaultExpr instanceof CtConstructorCall) {
                         CtConstructorCall ctorCall = (CtConstructorCall) defaultExpr;
                         if (hasNestedSameTypeConstructor(ctorCall)) {
                             debugLog("[resolveType][Depth:" + depth + "] WARNING: Detected nested same-type constructor pattern, trying next sequence...");
                             attemptCount++;
                             continue;
                         }
                         
                         if (hasInvalidAnnotatedParameterPattern(ctorCall)) {
                             debugLog("[resolveType][Depth:" + depth + "] WARNING: Detected invalid AnnotatedParameter pattern, trying next sequence...");
                             attemptCount++;
                             continue;
                         }
                     }
                 }
                 
                 // Check if last statement's dependencies can be resolved
                // Valid sequence found
                debugLog("[resolveType][Depth:" + depth + "] Valid sequence found!");
                break;
          }
          
          if (attemptCount >= maxAttempts) {
              debugLog("[resolveType][Depth:" + depth + "] Could not find valid sequence after " + maxAttempts + " attempts, trying next candidate...");
              candidateAttemptCount++;
              continue; // Try next candidate
          }
          
          // If we reach here, we found a valid sequence, break out of candidate loop
          debugLog("[resolveType][Depth:" + depth + "] Chosen sequence has " + chosenSequence.size() + " elements");
          debugLog("[resolveType][Depth:" + depth + "] Processing last STMT from sequence, type class: " + lastElement.getClass().getSimpleName());
         
         CtStatement lastStmt = null;
         if (lastElement instanceof CtStatement) {
             lastStmt = ((CtStatement) lastElement).clone();
             if(!isLastStmtDefValid(lastElement, candidateElement)){
                debugLog("[John ADD] Last STMT is NOT VALID Last STMT "+ lastElement + " Candidate Element: " + candidateElement);
             }
             debugLog("[resolveType][Depth:" + depth + "] lastStmt cloned successfully");
             debugLog("[resolveType][Depth:" + depth + "] lastStmt details:");
             debugLog("[resolveType][Depth:" + depth + "]   - Class: " + lastStmt.getClass().getSimpleName());
             debugLog("[resolveType][Depth:" + depth + "]   - toString(): " + lastStmt.toString());
             debugLog("[resolveType][Depth:" + depth + "]   - Requested Type: " + type.getQualifiedName());
             if (lastStmt instanceof CtLocalVariable) {
                 CtLocalVariable localVar = (CtLocalVariable) lastStmt;
                 CtTypeReference stmtType = localVar.getType();
                 debugLog("[resolveType][Depth:" + depth + "]   - Declared Type: " + (stmtType != null ? stmtType.getQualifiedName() : "null"));
                 
                 CtExpression defaultExpr = localVar.getDefaultExpression();
                 if (defaultExpr instanceof CtInvocation) {
                     CtInvocation inv = (CtInvocation) defaultExpr;
                     debugLog("[resolveType][Depth:" + depth + "]   - Invocation Method: " + inv.getExecutable().getSimpleName());
                     List<?> invArgs = inv.getArguments();
                     for (int i = 0; i < invArgs.size(); i++) {
                         CtExpression arg = (CtExpression) invArgs.get(i);
                         debugLog("[resolveType][Depth:" + depth + "]     - Arg " + i + ": " + arg.toString() + " (Type: " + (arg.getType() != null ? arg.getType().getQualifiedName() : "null") + ")");
                     }
                 }
             }
         } else {
             debugLog("[resolveType][Depth:" + depth + "] Last element is not a Statement, it's: " + lastElement.getClass().getSimpleName());
             return getDirectValue(type);
         }
          
          if (lastStmt instanceof CtLocalVariable) {
              debugLog("[resolveType][Depth:" + depth + "] lastStmt is CtLocalVariable");
               CtLocalVariable localVar = (CtLocalVariable) lastStmt;
               CtTypeReference varType = localVar.getType();
               
               // [핵심 수정] typeMatches 대신 isTypeCompatible 사용 (subtype 허용)
               // Check if variable type is compatible with requested type (allows subtypes)
               if (varType != null && !isTypeCompatible(varType, type)) {
                   debugLog("[resolveType][Depth:" + depth + "] Type incompatible, returning default value");
                   return getDirectValue(type);
               }
              
              // Check if defaultExpression is void BEFORE processing dependencies
              CtExpression defaultExpr = localVar.getDefaultExpression();
              if (defaultExpr instanceof CtInvocation) {
                  CtInvocation invocation = (CtInvocation) defaultExpr;
                  CtTypeReference returnType = invocation.getType();
                  if (returnType != null && "void".equals(returnType.getSimpleName())) {
                      return getDirectValue(type);
                  }
              }
          } else if (lastStmt instanceof CtInvocation) {
              CtInvocation invocation = (CtInvocation) lastStmt;
              CtTypeReference returnType = invocation.getType();
              if (returnType != null && "void".equals(returnType.getSimpleName())) {
                  return getDirectValue(type);
              }
              
              CtExpression target = invocation.getTarget();
              if (target == null || (target instanceof CtLiteral && ((CtLiteral) target).getValue() == null)) {
                  return getDirectValue(type);
              }
           }
           
           debugLog("[resolveType][Depth:" + depth + "] === Calling processStatementDependencies for depth " + (depth+1) + " ===");
           processStatementDependencies(lastStmt, stmts, varNameCounter, depth + 1);
           debugLog("[resolveType][Depth:" + depth + "] === Returned from processStatementDependencies ===");
          
            if (lastStmt instanceof CtLocalVariable) {
                debugLog("[resolveType][Depth:" + depth + "] Handling CtLocalVariable result");
               CtLocalVariable localVar = (CtLocalVariable) lastStmt;
               CtTypeReference actualType = localVar.getType();
               
               debugLog("[resolveType][Depth:" + depth + "] Actual type: " + (actualType != null ? actualType.getQualifiedName() : "null"));
               debugLog("[resolveType][Depth:" + depth + "] Requested type: " + type.getQualifiedName());
               
               if (actualType != null) {
                   String qname = actualType.getQualifiedName();
                   if (qname.startsWith("java.lang.reflect.Constructor") || 
                       qname.startsWith("java.lang.reflect.Method") ||
                       qname.startsWith("java.lang.reflect.Field")) {
                       CtTypeReference rawType = factory.Type().createReference(qname.replaceAll("<.*>", ""));
                       localVar.setType(rawType);
                       actualType = rawType;
                       debugLog("[resolveType][Depth:" + depth + "] Stripped generics from reflection type: " + rawType.getQualifiedName());
                   }
               }
               
               String varName = localVar.getSimpleName();
               if (isAlreadyDeclared(varName, stmts)) {
                   varName = generateUniqueNameFromStmts(varName, stmts, varNameCounter);
                   localVar.setSimpleName(varName);
               }
                stmts.add(lastStmt);
                
                CtVariableRead varRead = createVariableRead(varName, actualType);
                debugLog("[resolveType][Depth:" + depth + "] Created CtVariableRead: " + (varRead != null ? varRead.toString() : "null"));
                
                if (!isTypeCompatible(actualType, type)) {
                    debugLog("[resolveType][Depth:" + depth + "] Type mismatch! Creating cast expression");
                    CtExpression castedExpr = createCastedExpression(varRead, type);
                    debugLog("[resolveType][Depth:" + depth + "] Cast expression result: " + (castedExpr != null ? castedExpr.toString() : "null"));
                    return castedExpr;
                }
                debugLog("[resolveType][Depth:" + depth + "] Returning CtVariableRead: " + (varRead != null ? varRead.toString() : "null"));
                return varRead;
          } else if (lastStmt instanceof CtInvocation) {
              CtInvocation invocation = (CtInvocation) lastStmt;
              CtExpression target = invocation.getTarget();
              
              if (target == null || (target instanceof CtLiteral && ((CtLiteral) target).getValue() == null)) {
                  return getDirectValue(type);
              }
              
              String varName = generateUniqueName(type.getSimpleName(), varNameCounter);
              CtTypeReference actualReturnType = invocation.getType();
              debugLog("[resolveType][Depth:" + depth + "] CtInvocation return type: " + 
                  (actualReturnType != null ? actualReturnType.getQualifiedName() : "null"));
              
              CtTypeReference varType = actualReturnType != null ? actualReturnType : type;
              CtLocalVariable newVar = factory.createLocalVariable(
                  varType, 
                  varName, 
                  invocation
              );
              stmts.add(newVar);
              
              CtVariableRead varRead = createVariableRead(varName, varType);
              if (!isTypeCompatible(varType, type)) {
                  debugLog("[resolveType][Depth:" + depth + "] Type mismatch in invocation! Creating cast expression");
                  return createCastedExpression(varRead, type);
              }
              return varRead;
          } else if (lastStmt instanceof CtConstructorCall) {
              String varName = generateUniqueName(type.getSimpleName(), varNameCounter);
              CtConstructorCall ctorCall = (CtConstructorCall) lastStmt;
              CtTypeReference actualType = ctorCall.getType();
              debugLog("[resolveType][Depth:" + depth + "] CtConstructorCall type: " + 
                  (actualType != null ? actualType.getQualifiedName() : "null"));
              
              CtTypeReference varType = actualType != null ? actualType : type;
              CtLocalVariable newVar = factory.createLocalVariable(
                  varType, 
                  varName, 
                  ctorCall
              );
              stmts.add(newVar);
              
              CtVariableRead varRead = createVariableRead(varName, varType);
              if (!isTypeCompatible(varType, type)) {
                  debugLog("[resolveType][Depth:" + depth + "] Type mismatch in constructor call! Creating cast expression");
                  return createCastedExpression(varRead, type);
              }
              return varRead;
          }
          
          // For any other statement type, try to wrap it in a variable assignment
          // debugLog("[RecursiveGen][Depth:" + depth + "] Last statement type not recognized: " + lastStmt.getClass().getSimpleName());
          return getDirectValue(type);
          
          } // End of candidate loop
          
          // If we exhausted all candidates, return default value
          debugLog("[resolveType][Depth:" + depth + "] Exhausted all candidate attempts, returning direct value");
          return getDirectValue(type);
     }

    private CtExpression resolveTypeWithFullSequence(CtTypeReference<?> type, List<CtStatement> stmts, 
                                                     Map<String, Integer> varNameCounter) {
        // debugLog("[RecursiveGen][FullSeq] Resolving with full sequence for type: " + type.getQualifiedName());
        
        Pair<CtTypeReference, CtElement> candidate = selectCandidateFromPool(type, new HashSet<>());
        
        if (candidate == null) {
            // debugLog("[RecursiveGen][FullSeq] No candidate found, using default value");
            return getDirectValue(type);
        }
        
        Set<List<CtElement>> sequences = CandidatePool.getVartypeToInputPool().get(candidate);
        if (sequences == null || sequences.isEmpty()) {
            // debugLog("[RecursiveGen][FullSeq] No sequences found, using default value");
            return getDirectValue(type);
        }
        
        List<CtElement> chosenSequence = selectRandomSequence(sequences);
        if (chosenSequence.isEmpty()) {
            // debugLog("[RecursiveGen][FullSeq] Chosen sequence is empty, using default value");
            return getDirectValue(type);
        }
        
        // debugLog("[RecursiveGen][FullSeq] Adding full sequence of " + chosenSequence.size() + " statements without recursion");
        
        // Check if we need to rename variables in the entire sequence
        Map<String, String> renameMap = new HashMap<>();
        boolean needsRename = false;
        
        for (CtElement elem : chosenSequence) {
            if (elem instanceof CtStatement) {
                String existingVarName = getVarNameIfExists((CtStatement) elem);
                if (existingVarName != null && isAlreadyDeclared(existingVarName, stmts)) {
                    needsRename = true;
                    break;
                }
            }
        }
        
        // If renaming is needed, create a unique suffix for this entire sequence
        String sequenceSuffix = "";
        if (needsRename) {
            int sequenceId = varNameCounter.getOrDefault("__sequence_id", 0);
            varNameCounter.put("__sequence_id", sequenceId + 1);
            sequenceSuffix = "_seq" + sequenceId;
            
            // Build rename map for all variables in this sequence
            for (CtElement elem : chosenSequence) {
                if (elem instanceof CtStatement) {
                    String existingVarName = getVarNameIfExists((CtStatement) elem);
                    if (existingVarName != null) {
                        renameMap.put(existingVarName, existingVarName + sequenceSuffix);
                    }
                }
            }
        }
        
        // Add all statements with renaming and dependency processing
        for (int i = 0; i < chosenSequence.size(); i++) {
            CtElement elem = chosenSequence.get(i);
            if (elem instanceof CtStatement) {
                CtStatement stmt = ((CtStatement) elem).clone();
                
                // Apply renaming if needed - rename variable declarations
                if (needsRename && stmt instanceof CtLocalVariable) {
                    CtLocalVariable localVar = (CtLocalVariable) stmt;
                    String oldName = localVar.getSimpleName();
                    String newName = renameMap.get(oldName);
                    if (newName != null) {
                        localVar.setSimpleName(newName);
                    }
                }
                
                // Rename ALL variable references in ALL statements (not just CtLocalVariable)
                if (needsRename) {
                    renameVariableReferences(stmt, renameMap);
                }
                
                // Process nested constructor call arguments BEFORE adding to stmts
                if (stmt instanceof CtLocalVariable) {
                    CtLocalVariable localVar = (CtLocalVariable) stmt;
                    CtExpression defaultExpr = localVar.getDefaultExpression();
                    if (defaultExpr instanceof CtConstructorCall) {
                        processConstructorCallArguments((CtConstructorCall) defaultExpr, stmts, varNameCounter, 0);
                    }
                }
                
                stmts.add(stmt);
            }
        }
        
        CtElement lastElement = chosenSequence.get(chosenSequence.size() - 1);
        
        if (lastElement instanceof CtLocalVariable) {
            CtLocalVariable lastVar = (CtLocalVariable) lastElement;
            String varName = lastVar.getSimpleName();
            if (needsRename && renameMap.containsKey(varName)) {
                varName = renameMap.get(varName);
            }
            return createVariableRead(varName, type);
        } else {
            String varName = generateUniqueName(type.getSimpleName(), varNameCounter);
            return createVariableRead(varName, type);
        }
    }

      private void processStatementDependencies(CtStatement stmt, List<CtStatement> stmts, 
                                                 Map<String, Integer> varNameCounter, int depth) {
           debugLog("\n[processStatementDependencies][Depth:" + depth + "] ===== ENTER processStatementDependencies =====");
           debugLog("[processStatementDependencies][Depth:" + depth + "] Statement type: " + (stmt != null ? stmt.getClass().getSimpleName() : "null"));
           
           if (stmt instanceof CtInvocation) {
               debugLog("[processStatementDependencies][Depth:" + depth + "] Statement is CtInvocation");
              CtInvocation invocation = (CtInvocation) stmt;
              
                CtExpression target = invocation.getTarget();
                 if (target instanceof CtVariableRead) {
                     String varName = ((CtVariableRead) target).getVariable().getSimpleName();
                     CtTypeReference targetType = ((CtVariableRead) target).getType();
                     
                      // ★ 변경: receiver도 항상 새로운 객체 생성
                      // 이유: 같은 타입이지만 다른 구현체(예: ArrayNode, TextNode)가 필요할 수 있음
                      debugLog("[processStatementDependencies][Depth:" + depth + "] Resolving receiver: " + varName + " (" + (targetType != null ? targetType.getQualifiedName() : "null") + ")");
                      
                       CtExpression resolved = resolveType(targetType, stmts, varNameCounter, new HashSet<>(), depth);
                       // [수정] Receiver Object 자리에는 null 리터럴이 절대 들어가면 안됨
                       boolean isNullLiteral = resolved != null && (resolved instanceof CtLiteral && ((CtLiteral) resolved).getValue() == null);
                       
                       if (resolved == null || isNullLiteral) {
                           debugLog("[processStatementDependencies][Depth:" + depth + "] WARNING: null received for receiver, trying to find alternative from pool");
                           // Pool에서 대체제 찾기
                           CtExpression fromPool = findValueFromPool(targetType);
                           if (fromPool != null) {
                               debugLog("[processStatementDependencies][Depth:" + depth + "] Found alternative receiver from pool");
                               invocation.setTarget(fromPool);
                           } else {
                               // Pool에도 없으면 아무 객체나 찾기
                               CtExpression anyValue = findAnyValueFromPool();
                               if (anyValue != null) {
                                   debugLog("[processStatementDependencies][Depth:" + depth + "] Found any value from pool as receiver");
                                   invocation.setTarget(anyValue);
                               } else {
                                   // 마지막 수단: alternative implementation 찾기
                                   CtTypeReference<?> alternativeType = findAlternativeImplementation(targetType);
                                   if (alternativeType != null) {
                                       debugLog("[processStatementDependencies][Depth:" + depth + "] Trying alternative implementation: " + alternativeType.getQualifiedName());
                                       CtExpression altResolved = resolveType(alternativeType, stmts, varNameCounter, new HashSet<>(), depth);
                                       boolean isAltNullLiteral = altResolved != null && (altResolved instanceof CtLiteral && ((CtLiteral) altResolved).getValue() == null);
                                       if (altResolved != null && !isAltNullLiteral) {
                                           invocation.setTarget(altResolved);
                                       } else {
                                           // full sequence 시도
                                           boolean fullSeqAdded = addFullSequenceForVariable(target, targetType, stmts, varNameCounter);
                                           if (!fullSeqAdded) {
                                               debugLog("[processStatementDependencies][Depth:" + depth + "] ERROR: Could not resolve receiver at all");
                                           }
                                       }
                                   } else {
                                       // No alternative found, try full sequence as before
                                       boolean fullSeqAdded = addFullSequenceForVariable(target, targetType, stmts, varNameCounter);
                                       if (!fullSeqAdded) {
                                           debugLog("[processStatementDependencies][Depth:" + depth + "] ERROR: Could not resolve receiver - no alternative implementation available");
                                       }
                                   }
                               }
                           }
                       } else {
                           // 정상적인 non-null 객체
                           invocation.setTarget(resolved);
                       }
              } else if (target instanceof CtConstructorCall) {
                 // Target is a constructor call - need to resolve its arguments
                 CtConstructorCall ctorCall = (CtConstructorCall) target;
            debugLog("\n[processStatementDependencies][Depth:" + depth + "] ========== Processing CtInvocation arguments ==========");
            debugLog("[processStatementDependencies][Depth:" + depth + "] Total arguments: " + invocation.getArguments().size());
            List<CtExpression> processedArgs = new ArrayList<>();
             List<?> args = invocation.getArguments();
             for (int argIdx = 0; argIdx < args.size(); argIdx++) {
                 Object argObj = args.get(argIdx);
                 CtExpression arg = (CtExpression) argObj;
                 debugLog("\n[processStatementDependencies][Depth:" + depth + "] --- Argument " + argIdx + " ---");
                 debugLog("[processStatementDependencies][Depth:" + depth + "] Argument type (class): " + arg.getClass().getSimpleName());
                 
                 if (arg instanceof CtVariableRead) {
                     String varName = ((CtVariableRead) arg).getVariable().getSimpleName();
                     CtTypeReference argType = arg.getType();
                     debugLog("[processStatementDependencies][Depth:" + depth + "] Variable name: " + varName);
                     debugLog("[processStatementDependencies][Depth:" + depth + "] Variable type from arg.getType(): " + (argType != null ? argType.getQualifiedName() : "NULL"));
                       if (!isAlreadyDeclared(varName, stmts)) {
                           debugLog("[RecursiveGen][Depth:" + depth + "] Variable not declared yet, resolving type...");
                           CtExpression resolved = resolveType(argType, stmts, varNameCounter, new HashSet<>(), depth);
                           if (resolved != null) {
                               debugLog("[RecursiveGen][Depth:" + depth + "] Successfully resolved to expression");
                               processedArgs.add(resolved);
                           } else {
                               processedArgs.add(arg);
                           }
                       } else {
                           debugLog("[RecursiveGen][Depth:" + depth + "] Variable already declared");
                           processedArgs.add(arg);
                       }
                     } else {
                         processedArgs.add(arg);
                     }
                 }
                 ctorCall.setArguments((List) processedArgs);
              } else if (target instanceof CtInvocation) {
                  // Target is an invocation - recursively process it
                  processStatementDependencies((CtStatement) target, stmts, varNameCounter, depth);
              }
             
              List<CtExpression> processedArgs = processArgumentsWithLiteralReplacement(
                  invocation.getArguments(), stmts, varNameCounter, depth);
               invocation.setArguments((List) processedArgs);
              
              // [DISABLED] 반환값이 Primitive/String이면 변수에 저장하고 Logger.observe() 추가
              // captureStatementInvocationReturnValue(invocation, stmts, varNameCounter);
          } else if (stmt instanceof CtConstructorCall) {
             CtConstructorCall ctorCall = (CtConstructorCall) stmt;
             List<CtExpression> processedArgs = processArgumentsWithLiteralReplacement(
                 ctorCall.getArguments(), stmts, varNameCounter, depth);
             ctorCall.setArguments((List) processedArgs);
          } else if (stmt instanceof CtLocalVariable) {
              CtLocalVariable localVar = (CtLocalVariable) stmt;
              CtExpression defaultExpr = localVar.getDefaultExpression();
              
               // [DEBUG] Log the expression type
               if (defaultExpr != null) {
                   debugLog("[processStatementDependencies][Depth:" + depth + "] defaultExpr class: " + defaultExpr.getClass().getName());
               }
              
               // First, check if defaultExpr is a variable read that needs resolution
               if (defaultExpr instanceof CtVariableRead) {
                  String varName = ((CtVariableRead) defaultExpr).getVariable().getSimpleName();
                  if (!isAlreadyDeclared(varName, stmts)) {
                      CtTypeReference exprType = ((CtVariableRead) defaultExpr).getType();
                      CtExpression resolved = resolveType(exprType, stmts, varNameCounter, new HashSet<>(), depth);
                      if (resolved != null) {
                          localVar.setDefaultExpression(resolved);
                      }
                  }
              } else if (defaultExpr instanceof spoon.reflect.code.CtUnaryOperator) {
                  spoon.reflect.code.CtUnaryOperator unaryOp = (spoon.reflect.code.CtUnaryOperator) defaultExpr;
                  CtExpression operand = unaryOp.getOperand();
                  if (operand instanceof CtVariableRead) {
                      String varName = ((CtVariableRead) operand).getVariable().getSimpleName();
                      if (!isAlreadyDeclared(varName, stmts)) {
                          CtTypeReference operandType = ((CtVariableRead) operand).getType();
                          CtExpression resolved = resolveType(operandType, stmts, varNameCounter, new HashSet<>(), depth);
                          if (resolved != null) {
                              unaryOp.setOperand(resolved);
                          }
                      }
                  }
              } else if (defaultExpr.getClass().getSimpleName().contains("Cast")) {
                  // [핵심 수정] Handle cast expressions like ((Type) (invocation))
                  // Use reflection to access the casted expression since CtTypeCast might not be in imports
                  debugLog("[processStatementDependencies][Depth:" + depth + "] Detected Cast expression");
                  try {
                      java.lang.reflect.Method getExprMethod = defaultExpr.getClass().getMethod("getExpression");
                      CtExpression castedExpr = (CtExpression) getExprMethod.invoke(defaultExpr);
                      debugLog("[processStatementDependencies][Depth:" + depth + "] Cast expression inner type: " + (castedExpr != null ? castedExpr.getClass().getSimpleName() : "null"));
                      
                      // Process the casted expression recursively
                      if (castedExpr instanceof CtInvocation) {
                          debugLog("[processStatementDependencies][Depth:" + depth + "] Cast contains invocation, processing...");
                          CtInvocation invocation = (CtInvocation) castedExpr;
                          CtExpression target = invocation.getTarget();
                          debugLog("[processStatementDependencies][Depth:" + depth + "] Invocation target: " + (target != null ? target.toString() : "null"));
                          
                          if (target instanceof CtVariableRead) {
                              String varName = ((CtVariableRead) target).getVariable().getSimpleName();
                              debugLog("[processStatementDependencies][Depth:" + depth + "] Target is CtVariableRead: " + varName);
                              if (!isAlreadyDeclared(varName, stmts)) {
                                  debugLog("[processStatementDependencies][Depth:" + depth + "] Variable not declared, resolving...");
                                  CtTypeReference targetType = ((CtVariableRead) target).getType();
                                  CtExpression resolved = resolveType(targetType, stmts, varNameCounter, new HashSet<>(), depth);
                                  if (resolved != null) {
                                      debugLog("[processStatementDependencies][Depth:" + depth + "] Successfully resolved, setting target to: " + resolved.toString());
                                      invocation.setTarget(resolved);
                                  } else {
                                      debugLog("[processStatementDependencies][Depth:" + depth + "] WARNING: resolveType returned null");
                                  }
                              } else {
                                  debugLog("[processStatementDependencies][Depth:" + depth + "] Variable already declared");
                              }
                          } else {
                              debugLog("[processStatementDependencies][Depth:" + depth + "] Target is not CtVariableRead: " + (target != null ? target.getClass().getSimpleName() : "null"));
                          }
                          
                          // Process invocation arguments
                          List<CtExpression> processedArgs = new ArrayList<>();
                          List<?> args = invocation.getArguments();
                          debugLog("[processStatementDependencies][Depth:" + depth + "] Processing " + args.size() + " arguments");
                          for (Object argObj : args) {
                              CtExpression arg = (CtExpression) argObj;
                              if (arg instanceof CtVariableRead) {
                                  String varName = ((CtVariableRead) arg).getVariable().getSimpleName();
                                  CtTypeReference argType = arg.getType();
                                  if (!isAlreadyDeclared(varName, stmts)) {
                                      CtExpression resolved = resolveType(argType, stmts, varNameCounter, new HashSet<>(), depth);
                                      if (resolved != null) {
                                          processedArgs.add(resolved);
                                      } else {
                                          processedArgs.add(arg);
                                      }
                                  } else {
                                      processedArgs.add(arg);
                                  }
                              } else {
                                  processedArgs.add(arg);
                              }
                          }
                          invocation.setArguments((List) processedArgs);
                      } else {
                          debugLog("[processStatementDependencies][Depth:" + depth + "] Cast expression does not contain invocation");
                      }
                  } catch (Exception e) {
                      debugLog("[processStatementDependencies][Depth:" + depth + "] ERROR processing cast expression: " + e.getMessage());
                      e.printStackTrace();
                  }
               } else if (defaultExpr instanceof CtConstructorCall) {
                   // ⭐ CtConstructorCall (예: new StringReader(...))의 인수 처리
                   CtConstructorCall ctorCall = (CtConstructorCall) defaultExpr;
                   List<CtExpression> processedArgs = processArgumentsWithLiteralReplacement(
                       ctorCall.getArguments(), stmts, varNameCounter, depth);
                   ctorCall.setArguments((List) processedArgs);
               } else if (defaultExpr instanceof CtInvocation) {
                   CtInvocation invocation = (CtInvocation) defaultExpr;
                  
                   // Process target (receiver) recursively
                   CtExpression target = invocation.getTarget();
                   debugLog("[processStatementDependencies][Depth:" + depth + "] Processing invocation: " + invocation.toString());
                   debugLog("[processStatementDependencies][Depth:" + depth + "] Target: " + (target != null ? target.toString() : "null"));
                   debugLog("[processStatementDependencies][Depth:" + depth + "] Target class: " + (target != null ? target.getClass().getSimpleName() : "null"));
                   
                   // [핵심 수정] Handle null or literal null targets
                   if (target == null || (target instanceof CtLiteral && ((CtLiteral) target).getValue() == null)) {
                       debugLog("[processStatementDependencies][Depth:" + depth + "] WARNING: Invocation has null target! Attempting to infer from method signature...");
                       // Try to get expected receiver type from method signature
                       CtExecutableReference execRef = invocation.getExecutable();
                       if (execRef != null && execRef.getDeclaringType() != null) {
                           CtTypeReference expectedType = execRef.getDeclaringType();
                           debugLog("[processStatementDependencies][Depth:" + depth + "] Inferred receiver type: " + expectedType.getQualifiedName());
                           CtExpression resolved = resolveType(expectedType, stmts, varNameCounter, new HashSet<>(), depth);
                           if (resolved != null) {
                               debugLog("[processStatementDependencies][Depth:" + depth + "] Successfully resolved null target to: " + resolved.toString());
                               invocation.setTarget(resolved);
                           }
                       }
                   } else if (target instanceof CtVariableRead) {
                       debugLog("[processStatementDependencies][Depth:" + depth + "] Target is CtVariableRead, processing...");
                       String varName = ((CtVariableRead) target).getVariable().getSimpleName();
                       debugLog("[processStatementDependencies][Depth:" + depth + "] Variable name: " + varName);
                       debugLog("[processStatementDependencies][Depth:" + depth + "] isAlreadyDeclared: " + isAlreadyDeclared(varName, stmts));
                       if (!isAlreadyDeclared(varName, stmts)) {
                           CtTypeReference targetType = ((CtVariableRead) target).getType();
                           debugLog("[processStatementDependencies][Depth:" + depth + "] Resolving type: " + targetType.getQualifiedName());
                           CtExpression resolved = resolveType(targetType, stmts, varNameCounter, new HashSet<>(), depth);
                           if (resolved != null) {
                               debugLog("[processStatementDependencies][Depth:" + depth + "] Successfully resolved to: " + resolved.toString());
                               invocation.setTarget(resolved);
                           } else {
                               debugLog("[processStatementDependencies][Depth:" + depth + "] WARNING: resolveType returned null");
                           }
                       }
                    } else if (target instanceof CtInvocation) {
                       // Nested invocation - recursively process its dependencies without creating temp variable
                       CtInvocation nestedInvocation = (CtInvocation) target;
                       processNestedInvocationDependencies(nestedInvocation, stmts, varNameCounter, depth);
                   } else if (target instanceof CtConstructorCall) {
                       // Target is a constructor call - process its arguments
                       CtConstructorCall ctorCall = (CtConstructorCall) target;
                       List<CtExpression> processedArgs = new ArrayList<>();
                       List<?> ctorArgs = ctorCall.getArguments();
                       for (Object argObj : ctorArgs) {
                           CtExpression arg = (CtExpression) argObj;
                           if (arg instanceof CtVariableRead) {
                               String varName = ((CtVariableRead) arg).getVariable().getSimpleName();
                               CtTypeReference argType = arg.getType();
                               if (!isAlreadyDeclared(varName, stmts)) {
                                   CtExpression resolved = resolveType(argType, stmts, varNameCounter, new HashSet<>(), depth);
                                   if (resolved != null) {
                                       processedArgs.add(resolved);
                                   } else {
                                       processedArgs.add(arg);
                                   }
                               } else {
                                   processedArgs.add(arg);
                               }
                           } else {
                               processedArgs.add(arg);
                           }
                       }
                       ctorCall.setArguments((List) processedArgs);
                   }
                 
                  // Process arguments
                  List<CtExpression> processedArgs = new ArrayList<>();
                  List<?> args = invocation.getArguments();
                  for (Object argObj : args) {
                      CtExpression arg = (CtExpression) argObj;
                      if (arg instanceof CtVariableRead) {
                          String varName = ((CtVariableRead) arg).getVariable().getSimpleName();
                          CtTypeReference argType = arg.getType();
                     if (!isAlreadyDeclared(varName, stmts)) {
                         debugLog("[processStatementDependencies][Depth:" + depth + "] Variable NOT declared, calling resolveType...");
                         
                         // Special handling for Class type - use invocation's return type
                         if ("java.lang.Class".equals(argType.getQualifiedName())) {
                             CtTypeReference returnType = invocation.getType();
                             if (returnType != null && !returnType.getQualifiedName().equals("java.lang.Object")) {
                                 String returnTypeName = returnType.getQualifiedName();
                                 // Skip if return type contains generics or wildcards
                                 if (!returnTypeName.contains("<") && !returnTypeName.contains("?") && 
                                     !returnTypeName.equals("void") && !returnTypeName.equals("null")) {
                                     String classLiteral = returnTypeName + ".class";
                                     debugLog("[processStatementDependencies][Depth:" + depth + "] Class type detected, using return type class literal: " + classLiteral);
                                     CtExpression classExpr = factory.createCodeSnippetExpression(classLiteral);
                                     processedArgs.add(classExpr);
                                     continue;
                                 }
                             }
                         }
                         
                         CtExpression resolved = resolveType(argType, stmts, varNameCounter, new HashSet<>(), depth);
                         debugLog("[processStatementDependencies][Depth:" + depth + "] resolveType returned: " + (resolved != null ? resolved.getClass().getSimpleName() : "null"));
                         debugLog("[processStatementDependencies][Depth:" + depth + "] stmts.size() after resolveType: " + stmts.size());
                         if (resolved != null) {
                             debugLog("[processStatementDependencies][Depth:" + depth + "] Resolved successfully, using resolved expression");
                             processedArgs.add(resolved);
                         } else {
                             processedArgs.add(arg);
                         }
                      } else {
                          debugLog("[processStatementDependencies][Depth:" + depth + "] Variable already declared, using as-is");
                          processedArgs.add(arg);
                      }
                       } else if (arg instanceof CtInvocation) {
                           // Handle nested invocation (e.g., sw.toString())
                           CtInvocation nestedInvocation = (CtInvocation) arg;
                           CtExpression invTarget = nestedInvocation.getTarget();
                           if (invTarget instanceof CtVariableRead) {
                               String varName = ((CtVariableRead) invTarget).getVariable().getSimpleName();
                               if (!isAlreadyDeclared(varName, stmts)) {
                                   CtTypeReference targetType = invTarget.getType();
                                   CtExpression resolved = resolveType(targetType, stmts, varNameCounter, new HashSet<>(), depth);
                                   if (resolved != null) {
                                       nestedInvocation.setTarget(resolved);
                                   }
                               }
                           }
                           processedArgs.add(nestedInvocation);
                        } else if (arg instanceof CtConstructorCall) {
                            CtConstructorCall nestedCtor = (CtConstructorCall) arg;
                            List<CtExpression> nestedProcessedArgs = processArgumentsWithLiteralReplacement(
                                nestedCtor.getArguments(), stmts, varNameCounter, depth);
                            nestedCtor.setArguments((List) nestedProcessedArgs);
                            processedArgs.add(nestedCtor);
                       } else {
                           processedArgs.add(arg);
                       }
                   }
                   invocation.setArguments((List) processedArgs);
               } else if (defaultExpr instanceof CtConstructorCall) {
                   CtConstructorCall ctorCall = (CtConstructorCall) defaultExpr;
                   processConstructorCallArguments(ctorCall, stmts, varNameCounter, depth);
                } else if (defaultExpr instanceof CtNewArray) {
                    CtNewArray newArray = (CtNewArray) defaultExpr;
                    CtTypeReference arrayType = newArray.getType();
                    CtTypeReference componentType = null;
                    if (arrayType != null && arrayType instanceof spoon.reflect.reference.CtArrayTypeReference) {
                        componentType = ((spoon.reflect.reference.CtArrayTypeReference<?>) arrayType).getComponentType();
                    }
                    
                    List<CtExpression> processedElements = new ArrayList<>();
                    List<?> elements = newArray.getElements();
                    if (elements != null) {
                        for (Object elemObj : elements) {
                            CtExpression elem = (CtExpression) elemObj;
                            if (elem instanceof CtLiteral && ((CtLiteral) elem).getValue() == null) {
                                if (componentType != null) {
                                    CtExpression resolved = resolveType(componentType, stmts, varNameCounter, new HashSet<>(), depth);
                                    if (resolved != null) {
                                        processedElements.add(resolved);
                                    } else {
                                        processedElements.add(getDefaultValue(componentType));
                                    }
                                } else {
                                    processedElements.add(elem);
                                }
                            } else if (elem instanceof CtVariableRead) {
                                String varName = ((CtVariableRead) elem).getVariable().getSimpleName();
                                CtTypeReference elemType = elem.getType();
                                if (!isAlreadyDeclared(varName, stmts)) {
                                    CtExpression resolved = resolveType(elemType, stmts, varNameCounter, new HashSet<>(), depth);
                                    if (resolved != null) {
                                        processedElements.add(resolved);
                                    } else {
                                        processedElements.add(elem);
                                    }
                                } else {
                                    processedElements.add(elem);
                                }
                             } else if (elem instanceof CtLiteral) {
                                 // ⭐ 배열 요소의 리터럴도 입력 풀에서 대체
                                 CtTypeReference elemType = elem.getType();
                                 CtExpression replacementFromPool = findLiteralReplacement(elemType, stmts, varNameCounter);
                                 if (replacementFromPool != null) {
                                     processedElements.add(replacementFromPool);
                                 } else {
                                     processedElements.add(elem);
                                 }
                             } else if (elem instanceof CtInvocation) {
                                 CtInvocation arrayInvocation = (CtInvocation) elem;
                                 processNestedInvocationDependencies(arrayInvocation, stmts, varNameCounter, depth);
                                 processedElements.add(arrayInvocation);
                             } else {
                                 processedElements.add(elem);
                             }
                        }
                        newArray.setElements(processedElements);
                    }
                }
           }
      }

     private boolean isAlreadyDeclared(String varName, List<CtStatement> stmts) {
         for (CtStatement stmt : stmts) {
             if (stmt instanceof CtLocalVariable) {
                 if (((CtLocalVariable) stmt).getSimpleName().equals(varName)) {
                     return true;
                 }
             }
         }
         return false;
     }

     private boolean isPrimitiveOrString(CtTypeReference<?> type) {
          if (type == null) return false;
          String qName = type.getQualifiedName();
          return type.isPrimitive() ||
                "java.lang.String".equals(qName) ||
                "java.lang.Integer".equals(qName) ||
                "java.lang.Long".equals(qName) ||
                "java.lang.Double".equals(qName) ||
                "java.lang.Float".equals(qName) ||
                "java.lang.Boolean".equals(qName) ||
                "java.lang.Character".equals(qName) ||
                "java.lang.Byte".equals(qName) ||
                "java.lang.Short".equals(qName);
    }
    
    private boolean typeMatches(CtTypeReference<?> type1, CtTypeReference<?> type2) {
        if (type1 == null || type2 == null) {
            return type1 == type2;
        }
        String qName1 = type1.getQualifiedName();
        String qName2 = type2.getQualifiedName();
        return qName1.equals(qName2);
    }

    /**
     * 메서드 인자로 사용될 Expression의 타입이 필요한 타입과 호환되는지 확인
     * 예: char 타입 expression을 char[] 자리에 사용하면 false
     */
    private boolean isArgumentTypeCompatible(CtExpression argExpr, CtTypeReference<?> requiredType) {
        if (argExpr == null || requiredType == null) {
            return false;
        }
        
        CtTypeReference<?> argType = null;
        try {
            argType = argExpr.getType();
        } catch (Exception e) {
            return false;
        }
        
        if (argType == null) {
            return false;
        }
        
        // 정확한 타입 비교
        if (isTypeCompatible(argType, requiredType)) {
            return true;
        }
        
        // [핵심] 배열 타입 체크: 
        // char[] 가 필요한데 char를 전달하면 false
        // int[] 가 필요한데 int를 전달하면 false
        String argQName = argType.getQualifiedName();
        String reqQName = requiredType.getQualifiedName();
        
        // 필요한 타입이 배열이면
        if (requiredType.isArray()) {
            // 실제 타입도 배열이어야 함
            if (!argType.isArray()) {
                return false;  // 배열이 아니면 불호환
            }
        }
        
        return false;
    }

    private boolean isTypeCompatible(CtTypeReference<?> actualType, CtTypeReference<?> requestedType) {
        if (actualType == null || requestedType == null) {
            return actualType == requestedType;
        }
        
        String actualQName = actualType.getQualifiedName();
        String requestedQName = requestedType.getQualifiedName();
        
        if (actualQName.equals(requestedQName)) {
            return true;
        }
        
        try {
            if (actualType.isSubtypeOf(requestedType)) {
                return true;
            }
         } catch (Exception e) {
             // System.out.println("[isTypeCompatible] Exception during subtype check: " + e.getMessage());
         }
        
        return false;
    }

    private CtExpression createCastedExpression(CtExpression expr, CtTypeReference<?> targetType) {
        if (expr == null || targetType == null) {
            return expr;
        }
        
        CtTypeReference<?> exprType = expr.getType();
        if (isTypeCompatible(exprType, targetType)) {
            return expr;
        }
        
         // System.out.println("[createCastedExpression] Creating cast from " + 
         //     (exprType != null ? exprType.getQualifiedName() : "null") + 
         //     " to " + targetType.getQualifiedName());
         
         try {
             String castStr = "(" + targetType.getQualifiedName() + ") " + expr.toString();
             CtExpression castExpr = factory.createCodeSnippetExpression(castStr);
             return castExpr;
         } catch (Exception e) {
             // System.out.println("[createCastedExpression] Failed to create cast expression: " + e.getMessage());
             return expr;
         }
    }

    private CtExpression getDirectValue(CtTypeReference<?> type) {
         Set<CtElement> values = CandidatePool.getDirectToValues().get(type);
         if (values != null && !values.isEmpty()) {
             List<CtElement> valueList = new ArrayList<>(values);
             CtElement selected = valueList.get(random.nextInt(valueList.size()));
             return (CtExpression) selected.clone();
         }
         
         if ("java.lang.String".equals(type.getQualifiedName())) {
             // System.out.println("[getDirectValue] No String values in DirectToValues, trying to get diverse String values");
             CtExpression stringValue = getStringFromDirectValues(type);
             if (stringValue != null) {
                 // System.out.println("[getDirectValue] Successfully obtained diverse String value");
                 return stringValue;
             }
             // System.out.println("[getDirectValue] No String values found, using default empty string");
         }
        
         return getDefaultValue(type);
     }

       private CtExpression getStringFromDirectValues(CtTypeReference<?> type) {
           if (DEBUG_RECURSIVE_GEN) {
               System.out.println("[getStringFromDirectValues] 🔍 Starting String value collection for type: " + 
                   (type != null ? type.getQualifiedName() : "null"));
           }
           
           List<String> stringValues = new ArrayList<>();
           // 기본 String 값들
           stringValues.add("");
           stringValues.add("test");
           stringValues.add("value");
           stringValues.add("data");
           stringValues.add("input");
           stringValues.add("output");
           stringValues.add("key");
           stringValues.add("name");
           
           int initialSize = stringValues.size();
           
           // DirectValues에서 추가 String 값들 수집
           Set<CtElement> directValues = CandidatePool.getDirectToValues().get(type);
           int collectedFromPool = 0;
           
           if (directValues != null) {
               if (DEBUG_RECURSIVE_GEN) {
                   System.out.println("[getStringFromDirectValues]   📦 DirectValues pool contains " + directValues.size() + " elements");
               }
               
               for (CtElement elem : directValues) {
                   if (elem instanceof CtLiteral) {
                       CtLiteral lit = (CtLiteral) elem;
                       Object val = lit.getValue();
                       if (val instanceof String) {
                           String strVal = (String) val;
                           if (!stringValues.contains(strVal)) {
                               stringValues.add(strVal);
                               collectedFromPool++;
                               if (DEBUG_RECURSIVE_GEN) {
                                   System.out.println("[getStringFromDirectValues]   ✅ Added from pool: \"" + strVal + "\"");
                               }
                           }
                       }
                   }
               }
           } else {
               if (DEBUG_RECURSIVE_GEN) {
                   System.out.println("[getStringFromDirectValues]   ⚠️ No DirectValues pool found for type");
               }
           }
           
           if (!stringValues.isEmpty()) {
               int selectedIndex = random.nextInt(stringValues.size());
               String selected = stringValues.get(selectedIndex);
               
               if (DEBUG_RECURSIVE_GEN) {
                   System.out.println("[getStringFromDirectValues] 🎯 Total String values available: " + stringValues.size() + 
                       " (default: " + initialSize + ", from pool: " + collectedFromPool + ")");
                   System.out.println("[getStringFromDirectValues] 🎲 Randomly selected index: " + selectedIndex + "/" + stringValues.size() + 
                       " -> \"" + selected + "\"");
                   System.out.println("[getStringFromDirectValues]   📋 Available values: " + stringValues.toString());
               }
               
               return factory.createLiteral(selected);
           }
           
           if (DEBUG_RECURSIVE_GEN) {
               System.out.println("[getStringFromDirectValues] ❌ No String values available, returning null");
           }
           return null;
       }

       private CtExpression getDefaultValue(CtTypeReference<?> type) {
          if (type == null) {
              return factory.createLiteral(null);
          }
         
         // [배열 타입 처리]
         if (type.isArray()) {
             return createDefaultArray(type);
         }
         
         if (type.isPrimitive()) {
             if ("int".equals(type.getSimpleName())) return factory.createLiteral(0);
             if ("long".equals(type.getSimpleName())) return factory.createLiteral(0L);
             if ("double".equals(type.getSimpleName())) return factory.createLiteral(0.0);
             if ("float".equals(type.getSimpleName())) return factory.createLiteral(0.0f);
             if ("boolean".equals(type.getSimpleName())) return factory.createLiteral(false);
             if ("char".equals(type.getSimpleName())) return factory.createLiteral('\0');
             if ("byte".equals(type.getSimpleName())) return factory.createLiteral((byte)0);
             if ("short".equals(type.getSimpleName())) return factory.createLiteral((short)0);
         }
         
         String qName = type.getQualifiedName();
          if ("java.lang.String".equals(qName)) {
              return factory.createLiteral("");
          }
          
          if ("java.lang.Class".equals(qName)) {
               // System.out.println("[getDefaultValue] Creating Class literal: Object.class");
               return factory.createCodeSnippetExpression("Object.class");
           }
          
           // [핵심 수정] Object 타입이면 빈 String 반환 (null 대신)
           if ("java.lang.Object".equals(qName)) {
               return factory.createLiteral("");
           }
           
           // 파라미터용으로는 null 리터럴 허용 (Receiver용이 아니므로)
           return factory.createLiteral(null);
     }
     
     /**
      * 배열 타입에 대한 기본값 생성
      * char[] -> new char[0]
      * int[] -> new int[0]
      * String[] -> new String[0]
      */
     private CtExpression createDefaultArray(CtTypeReference<?> arrayType) {
         String arrayQName = arrayType.getQualifiedName();
         
         // 배열 타입 이름에서 [] 제거해서 컴포넌트 타입 추출
         // e.g., "char[]" -> "char", "java.lang.String[]" -> "java.lang.String"
         String componentTypeName = arrayQName.replaceAll("\\[\\]", "");
         
         // new Type[0] 형태로 코드 스니펫 생성
         // 예: new char[0], new int[0], new java.lang.String[0]
         String arrayCode = "new " + componentTypeName + "[0]";
         
         try {
             return factory.Code().createCodeSnippetExpression(arrayCode);
         } catch (Exception e) {
             // 코드 스니펫 생성 실패시 null 반환
             debugLog("[createDefaultArray] Failed to create array expression: " + arrayCode);
             return factory.createLiteral(null);
         }
     }

      /**
       * [수정] Pool에서 지정된 타입과 호환되는 값 찾기
       */
      private CtExpression findValueFromPool(CtTypeReference<?> type) {
          if (type == null) {
              return null;
          }
          
          // DirectToValues에서 정확한 타입 찾기
          Set<CtElement> values = CandidatePool.getDirectToValues().get(type);
          if (values != null && !values.isEmpty()) {
              List<CtElement> valueList = new ArrayList<>(values);
              CtElement selected = valueList.get(random.nextInt(valueList.size()));
              return (CtExpression) selected.clone();
          }
          
          // VartypeToInputPool에서 호환 타입 찾기
          for (Map.Entry<Pair<CtTypeReference, CtElement>, Set<List<CtElement>>> entry : CandidatePool.getVartypeToInputPool().entrySet()) {
              Pair<CtTypeReference, CtElement> keyPair = entry.getKey();
              CtTypeReference<?> keyType = keyPair.getKey();
              if (typeMatches(keyType, type)) {
                  Set<List<CtElement>> sequences = entry.getValue();
                  if (sequences != null && !sequences.isEmpty()) {
                      List<List<CtElement>> seqList = new ArrayList<>(sequences);
                      List<CtElement> chosenSeq = seqList.get(random.nextInt(seqList.size()));
                      if (!chosenSeq.isEmpty()) {
                          CtElement lastElem = chosenSeq.get(chosenSeq.size() - 1);
                          if (lastElem instanceof CtLocalVariable) {
                              CtLocalVariable var = (CtLocalVariable) lastElem;
                              return createVariableRead(var.getSimpleName(), var.getType());
                          }
                      }
                  }
              }
          }
          
          return null;
      }
      
      /**
       * [수정] Pool에서 아무 값이나 찾기 (모든 타입 대상)
       */
      private CtExpression findAnyValueFromPool() {
          // DirectToValues에서 아무거나 찾기
          Map<CtTypeReference, Set<CtElement>> directToValues = CandidatePool.getDirectToValues();
          if (directToValues != null && !directToValues.isEmpty()) {
              List<Set<CtElement>> allValues = new ArrayList<>(directToValues.values());
              if (!allValues.isEmpty()) {
                  Set<CtElement> selectedSet = allValues.get(random.nextInt(allValues.size()));
                  if (!selectedSet.isEmpty()) {
                      List<CtElement> valueList = new ArrayList<>(selectedSet);
                      CtElement selected = valueList.get(random.nextInt(valueList.size()));
                      return (CtExpression) selected.clone();
                  }
              }
          }
          
          // VartypeToInputPool에서 아무거나 찾기
          Map<Pair<CtTypeReference, CtElement>, Set<List<CtElement>>> vartypePool = CandidatePool.getVartypeToInputPool();
          if (vartypePool != null && !vartypePool.isEmpty()) {
              List<Map.Entry<Pair<CtTypeReference, CtElement>, Set<List<CtElement>>>> entries = new ArrayList<>(vartypePool.entrySet());
              Map.Entry<Pair<CtTypeReference, CtElement>, Set<List<CtElement>>> selectedEntry = entries.get(random.nextInt(entries.size()));
              Set<List<CtElement>> sequences = selectedEntry.getValue();
              if (sequences != null && !sequences.isEmpty()) {
                  List<List<CtElement>> seqList = new ArrayList<>(sequences);
                  List<CtElement> chosenSeq = seqList.get(random.nextInt(seqList.size()));
                  if (!chosenSeq.isEmpty()) {
                      CtElement lastElem = chosenSeq.get(chosenSeq.size() - 1);
                      if (lastElem instanceof CtLocalVariable) {
                          CtLocalVariable var = (CtLocalVariable) lastElem;
                          return createVariableRead(var.getSimpleName(), var.getType());
                      }
                  }
              }
          }
          
          return null;
      }

      /**
       * ★ 통합 메소드: 정확한 타입과 호환 타입(구현체)를 모두 한 번에 검색
       * 우선순위:
       * 1단계: 정확한 타입 검색 (exact match) - 최우선
       * 2단계: qualified name 검색 (same qualified name) - 2순위
       * 3단계: abstract/interface의 구현체 검색 (compatible types) - 3순위
       * 
       * 같은 우선순위 내에서는 모든 후보를 수집해서 함께 고려
       */
      private Pair<CtTypeReference, CtElement> selectBestCandidateFromPool(
              CtTypeReference<?> type,
             Set<Pair<CtTypeReference, CtElement>> excludeCandidates) {
         
         if (type == null) {
             return null;
         }
         
         String typeQName = type.getQualifiedName();
         List<Pair<CtTypeReference, CtElement>> tier1Candidates = new ArrayList<>();  // 1단계 결과
         List<Pair<CtTypeReference, CtElement>> tier2Candidates = new ArrayList<>();  // 2단계 결과
         List<Pair<CtTypeReference, CtElement>> tier3Candidates = new ArrayList<>();  // 3단계 결과
         
         debugLog("[selectBestCandidateFromPool] Looking for type: " + typeQName);
         
         // === 1단계: 정확한 타입 검색 (참조 동일성) ===
         debugLog("[selectBestCandidateFromPool] Step 1: Trying exact match by reference...");
         Set<Pair<CtTypeReference, CtElement>> exactCandidates = CandidatePool.getVarTypeNamePool().get(type);
         if (exactCandidates != null && !exactCandidates.isEmpty()) {
             debugLog("[selectBestCandidateFromPool] Found " + exactCandidates.size() + " exact matches");
             tier1Candidates.addAll(exactCandidates);
         }
         
         // === 2단계: qualified name으로 검색 ===
         debugLog("[selectBestCandidateFromPool] Step 2: Trying qualified name match...");
         for (Map.Entry<CtTypeReference, Set<Pair<CtTypeReference, CtElement>>> entry : 
              CandidatePool.getVarTypeNamePool().entrySet()) {
             if (entry.getKey().getQualifiedName().equals(typeQName) && 
                 !entry.getValue().equals(exactCandidates)) {  // 1단계에서 이미 찾은 것은 제외
                 debugLog("[selectBestCandidateFromPool] Found " + entry.getValue().size() + 
                         " matches by qualified name");
                 tier2Candidates.addAll(entry.getValue());
                 break;
             }
         }
         
         // === 3단계: abstract/interface의 구현체 검색 ===
         debugLog("[selectBestCandidateFromPool] Step 3: Trying to find implementations for abstract/interface...");
         List<CtTypeReference<?>> implementations = ASTParser.abstractToImplsMap.get(typeQName);
         
         if (implementations != null && !implementations.isEmpty()) {
             debugLog("[selectBestCandidateFromPool] Found " + implementations.size() + 
                     " implementation types for: " + typeQName);
             
             // 각 구현체별로 varTypeNamePool 검색
             for (CtTypeReference<?> implType : implementations) {
                 Set<Pair<CtTypeReference, CtElement>> implCandidates = 
                     CandidatePool.getVarTypeNamePool().get(implType);
                 if (implCandidates != null && !implCandidates.isEmpty()) {
                     debugLog("[selectBestCandidateFromPool]   - Found " + implCandidates.size() + 
                             " candidates for implementation: " + implType.getSimpleName());
                     tier3Candidates.addAll(implCandidates);
                 }
             }
         } else {
             debugLog("[selectBestCandidateFromPool] No implementations found for: " + typeQName);
         }
         
          // === 우선순위에 따라 선택 ===
          // 1단계가 있으면 1단계 + 3단계(구현체) 모두 포함
          List<Pair<CtTypeReference, CtElement>> selectedTier = new ArrayList<>();
          String selectedTierName = "";
          
          if (!tier1Candidates.isEmpty()) {
              // Tier 1이 있으면: Tier 1 + Tier 3 합치기 (다양한 구현체 포함)
              selectedTier.addAll(tier1Candidates);
              selectedTierName = "Tier 1 (exact match)";
              
              if (!tier3Candidates.isEmpty()) {
                  selectedTier.addAll(tier3Candidates);
                  selectedTierName += " + Tier 3 (implementations)";
              }
          } else if (!tier2Candidates.isEmpty()) {
              // Tier 1이 없으면 Tier 2 선택
              selectedTier.addAll(tier2Candidates);
              selectedTierName = "Tier 2 (qualified name)";
              
              if (!tier3Candidates.isEmpty()) {
                  selectedTier.addAll(tier3Candidates);
                  selectedTierName += " + Tier 3 (implementations)";
              }
          } else {
              // 1, 2 모두 없으면 Tier 3만 선택
              selectedTier.addAll(tier3Candidates);
              selectedTierName = "Tier 3 (implementations)";
          }
          
          // ★ 선택된 tier의 모든 후보 출력
          if (!selectedTier.isEmpty()) {
            //   debugLog("[selectBestCandidateFromPool] ========== ALL COMPATIBLE CANDIDATES ==========");
            //   debugLog("[selectBestCandidateFromPool] Type: " + typeQName);
            //   debugLog("[selectBestCandidateFromPool] Using " + selectedTierName);
            //   debugLog("[selectBestCandidateFromPool] Total candidates: " + selectedTier.size());
              int idx = 1;
              for (Pair<CtTypeReference, CtElement> cand : selectedTier) {
                  String candName = getCandidateName(cand);
                  String candType = cand.getKey().getQualifiedName();
                  String simpleType = candType.substring(candType.lastIndexOf('.') + 1);
                  
                  // lastStmt 정보도 출력
                  Set<List<CtElement>> candSequences = CandidatePool.getVartypeToInputPool().get(cand);
                  String seqInfo = "";
                  if (candSequences != null && !candSequences.isEmpty()) {
                      List<CtElement> firstSeq = candSequences.iterator().next();
                      if (!firstSeq.isEmpty()) {
                          CtElement lastElem = firstSeq.get(firstSeq.size() - 1);
                          String lastStmtStr = lastElem.toString();
                          seqInfo = "\n[selectBestCandidateFromPool]        LastStmt: " + lastStmtStr;
                      }
                  }
                  
                //   debugLog("[selectBestCandidateFromPool]   [" + idx + "] " + candName + " (" + simpleType + ")" + seqInfo);
                  idx++;
              }
            //   debugLog("[selectBestCandidateFromPool] =============================================");
          }
         
         // === 후보 선택 ===
         selectedTier.removeAll(excludeCandidates);
         
         if (selectedTier.isEmpty()) {
             debugLog("[selectBestCandidateFromPool] No candidates found after all steps");
             return null;
         }
         
         // null이 아닌 것 우선 선택
         List<Pair<CtTypeReference, CtElement>> nonNullCandidates = new ArrayList<>();
         List<Pair<CtTypeReference, CtElement>> nullCandidates = new ArrayList<>();
         
         for (Pair<CtTypeReference, CtElement> candidate : selectedTier) {
             String candidateName = getCandidateName(candidate);
             if (candidateName.startsWith("null_")) {
                 nullCandidates.add(candidate);
             } else {
                 nonNullCandidates.add(candidate);
             }
         }
         
         if (!nonNullCandidates.isEmpty()) {
             Pair<CtTypeReference, CtElement> selected = nonNullCandidates.get(random.nextInt(nonNullCandidates.size()));
             debugLog("[selectBestCandidateFromPool] Returning non-null candidate from " + 
                     nonNullCandidates.size() + " options");
             return selected;
         } else if (!nullCandidates.isEmpty()) {
             debugLog("[selectBestCandidateFromPool] All candidates are null, returning null candidate");
             return nullCandidates.get(random.nextInt(nullCandidates.size()));
         }
         
         return null;
     }
     
     private Pair<CtTypeReference, CtElement> selectCandidateFromPool(CtTypeReference<?> type, Set<Pair<CtTypeReference, CtElement>> excludeCandidates) {
          debugLog("[selectCandidateFromPool] Looking for exact type match: " + type.getQualifiedName());
          debugLog("[selectCandidateFromPool] Total types in pool: " + CandidatePool.getVarTypeNamePool().size());
          
          // Try exact match first (by reference equality)
          Set<Pair<CtTypeReference, CtElement>> candidates = CandidatePool.getVarTypeNamePool().get(type);
          debugLog("[selectCandidateFromPool] Exact match result: " + (candidates != null ? candidates.size() : "null"));
          
          if (candidates != null && !candidates.isEmpty()) {
              List<Pair<CtTypeReference, CtElement>> candidateList = new ArrayList<>(candidates);
              candidateList.removeAll(excludeCandidates);
              if (!candidateList.isEmpty()) {
                  // Separate null objects from non-null objects
                  List<Pair<CtTypeReference, CtElement>> nonNullCandidates = new ArrayList<>();
                  List<Pair<CtTypeReference, CtElement>> nullCandidates = new ArrayList<>();
                  
                  for (Pair<CtTypeReference, CtElement> candidate : candidateList) {
                      String candidateName = getCandidateName(candidate);
                      if (candidateName.startsWith("null_")) {
                          nullCandidates.add(candidate);
                      } else {
                          nonNullCandidates.add(candidate);
                      }
                  }
                  
                  // Prefer non-null candidates first
                  if (!nonNullCandidates.isEmpty()) {
                      debugLog("[selectCandidateFromPool] Returning non-null candidate from " + nonNullCandidates.size() + " options");
                      return nonNullCandidates.get(random.nextInt(nonNullCandidates.size()));
                  } else if (!nullCandidates.isEmpty()) {
                      debugLog("[selectCandidateFromPool] All candidates are null, returning null candidate");
                      return nullCandidates.get(random.nextInt(nullCandidates.size()));
                  }
              }
          }
          
          // If no exact match, try qualified name comparison
          debugLog("[selectCandidateFromPool] Trying qualified name match for: " + type.getQualifiedName());
          for (Map.Entry<CtTypeReference, Set<Pair<CtTypeReference, CtElement>>> entry : CandidatePool.getVarTypeNamePool().entrySet()) {
              if (entry.getKey().getQualifiedName().equals(type.getQualifiedName())) {
                  debugLog("[selectCandidateFromPool] Found match by qualified name!");
                  Set<Pair<CtTypeReference, CtElement>> matchedCandidates = entry.getValue();
                  if (!matchedCandidates.isEmpty()) {
                      List<Pair<CtTypeReference, CtElement>> candidateList = new ArrayList<>(matchedCandidates);
                      candidateList.removeAll(excludeCandidates);
                      if (!candidateList.isEmpty()) {
                          return candidateList.get(random.nextInt(candidateList.size()));
                      }
                  }
              }
          }
          
          debugLog("[selectCandidateFromPool] No match found");
          return null;
      }
    
     private Pair<CtTypeReference, CtElement> selectCompatibleCandidateFromPool(CtTypeReference<?> type, Set<Pair<CtTypeReference, CtElement>> excludeCandidates) {
         if (type == null) {
             return null;
         }
         
         String typeQName = type.getQualifiedName();
         List<Pair<CtTypeReference, CtElement>> compatibleCandidates = new ArrayList<>();
         
         List<CtTypeReference<?>> implementations = ASTParser.abstractToImplsMap.get(typeQName);
         
         if (implementations != null && !implementations.isEmpty()) {
             for (CtTypeReference<?> implType : implementations) {
                 Set<Pair<CtTypeReference, CtElement>> candidates = CandidatePool.getVarTypeNamePool().get(implType);
                 if (candidates != null && !candidates.isEmpty()) {
                     compatibleCandidates.addAll(candidates);
                 }
             }
         }
         
          compatibleCandidates.removeAll(excludeCandidates);
          if (!compatibleCandidates.isEmpty()) {
              // Separate null objects from non-null objects
              List<Pair<CtTypeReference, CtElement>> nonNullCandidates = new ArrayList<>();
              List<Pair<CtTypeReference, CtElement>> nullCandidates = new ArrayList<>();
              
              for (Pair<CtTypeReference, CtElement> candidate : compatibleCandidates) {
                  String candidateName = getCandidateName(candidate);
                  if (candidateName.startsWith("null_")) {
                      nullCandidates.add(candidate);
                  } else {
                      nonNullCandidates.add(candidate);
                  }
              }
              
              // Prefer non-null candidates from compatible types first
              if (!nonNullCandidates.isEmpty()) {
                  debugLog("[selectCompatibleCandidateFromPool] Returning non-null compatible candidate from " + nonNullCandidates.size() + " options");
                  return nonNullCandidates.get(random.nextInt(nonNullCandidates.size()));
              } else if (!nullCandidates.isEmpty()) {
                  debugLog("[selectCompatibleCandidateFromPool] All compatible candidates are null, returning null candidate");
                  return nullCandidates.get(random.nextInt(nullCandidates.size()));
              }
          }
         
         return null;
     }
    
    private Pair<CtTypeReference, CtElement> selectRandomCandidateFromPool() {
        java.util.Map<CtTypeReference, Set<Pair<CtTypeReference, CtElement>>> pool = CandidatePool.getVarTypeNamePool();
        if (pool == null || pool.isEmpty()) {
            return null;
        }
        
        List<Pair<CtTypeReference, CtElement>> allCandidates = new ArrayList<>();
        for (Set<Pair<CtTypeReference, CtElement>> candidates : pool.values()) {
            if (candidates != null && !candidates.isEmpty()) {
                allCandidates.addAll(candidates);
            }
        }
        
        if (allCandidates.isEmpty()) {
            return null;
        }
        
        return allCandidates.get(random.nextInt(allCandidates.size()));
    }

    private List<CtElement> selectRandomSequence(Set<List<CtElement>> sequences) {
         List<List<CtElement>> seqList = new ArrayList<>(sequences);
         return seqList.get(random.nextInt(seqList.size()));
     }
    
    private List<CtElement> selectRandomSequenceAvoidingUsed(Set<List<CtElement>> sequences, Set<String> usedPatterns) {
        List<List<CtElement>> availableSeqs = new ArrayList<>();
        
        for (List<CtElement> seq : sequences) {
            String pattern = normalizeStmtPattern(seq);
            if (!usedPatterns.contains(pattern)) {
                availableSeqs.add(seq);
            }
        }
        
        if (availableSeqs.isEmpty()) {
            // debugLog("[RecursiveGen] All sequence patterns already used, allowing reuse");
            availableSeqs = new ArrayList<>(sequences);
        }
        
        List<CtElement> chosen = availableSeqs.get(random.nextInt(availableSeqs.size()));
        usedPatterns.add(normalizeStmtPattern(chosen));
        return chosen;
    }
    
    private String normalizeStmtPattern(List<CtElement> sequence) {
        if (sequence == null || sequence.isEmpty()) {
            return "";
        }
        
        CtElement lastElem = sequence.get(sequence.size() - 1);
        if (lastElem instanceof CtLocalVariable) {
            CtLocalVariable var = (CtLocalVariable) lastElem;
            String typeStr = var.getType() != null ? var.getType().getQualifiedName() : "null";
            CtExpression defaultExpr = var.getDefaultExpression();
            String exprPattern = defaultExpr != null ? normalizeExpression(defaultExpr) : "null";
            return typeStr + " <VAR> = " + exprPattern;
        }
        
        return lastElem.toString();
    }
    
    private String normalizeExpression(CtExpression expr) {
        if (expr instanceof CtConstructorCall) {
            CtConstructorCall ctor = (CtConstructorCall) expr;
            return "new " + ctor.getType().getQualifiedName() + "(...)";
        } else if (expr instanceof CtInvocation) {
            CtInvocation inv = (CtInvocation) expr;
            String methodName = inv.getExecutable() != null ? inv.getExecutable().getSimpleName() : "unknown";
            return "<TARGET>." + methodName + "(...)";
        }
        return expr.toString();
    }

    // Java keywords that cannot be used as variable names
    private static final Set<String> JAVA_KEYWORDS = new HashSet<>(Arrays.asList(
        "abstract", "assert", "boolean", "break", "byte", "case", "catch", "char",
        "class", "const", "continue", "default", "do", "double", "else", "enum",
        "extends", "final", "finally", "float", "for", "goto", "if", "implements",
        "import", "instanceof", "int", "interface", "long", "native", "new", "package",
        "private", "protected", "public", "return", "short", "static", "strictfp",
        "super", "switch", "synchronized", "this", "throw", "throws", "transient",
        "try", "void", "volatile", "while"
    ));
    
    private String generateUniqueName(String baseName, Map<String, Integer> counter) {
        baseName = baseName.toLowerCase().replace("[]", "Array").replace(".", "_");
        
        // Avoid Java keywords by appending "_var" suffix
        if (JAVA_KEYWORDS.contains(baseName)) {
            baseName = baseName + "_var";
        }
        
        int count = counter.getOrDefault(baseName, 0);
        counter.put(baseName, count + 1);
        return baseName + "_" + count;
    }
    
    private String generateUniqueNameFromStmts(String baseName, List<CtStatement> stmts, Map<String, Integer> counter) {
        String candidateName;
        int attempt = 0;
        baseName = baseName.toLowerCase().replace("[]", "Array").replace(".", "_");
        
        // Avoid Java keywords by appending "_var" suffix
        if (JAVA_KEYWORDS.contains(baseName)) {
            baseName = baseName + "_var";
        }
        
        do {
            int count = counter.getOrDefault(baseName, 0);
            counter.put(baseName, count + 1);
            candidateName = baseName + "_" + count;
            attempt++;
            if (attempt > 1000) {
                // debugLog("[RecursiveGen] Warning: generateUniqueNameFromStmts exceeded 1000 attempts");
                break;
            }
        } while (isAlreadyDeclared(candidateName, stmts));
        
        return candidateName;
    }
    
    private String findDeclaredVariableOfType(CtTypeReference<?> type, List<CtStatement> stmts) {
        for (CtStatement stmt : stmts) {
            if (stmt instanceof CtLocalVariable) {
                CtLocalVariable var = (CtLocalVariable) stmt;
                if (typeMatches(var.getType(), type)) {
                    return var.getSimpleName();
                }
            }
        }
        return null;
    }
    
     private boolean needsCast(CtTypeReference<?> from, CtTypeReference<?> to) {
         if (from == null || to == null) return false;
         if (!from.isPrimitive() || !to.isPrimitive()) return false;
         
         String fromType = from.getSimpleName();
         String toType = to.getSimpleName();
         
         if (fromType.equals(toType)) return false;
         
         if (toType.equals("byte") && !fromType.equals("byte")) return true;
        if (toType.equals("short") && fromType.matches("int|long|float|double")) return true;
        if (toType.equals("char") && !fromType.equals("char")) return true;
         if (toType.equals("int") && fromType.matches("long|float|double")) return true;
         if (toType.equals("float") && fromType.matches("double")) return true;
         
         return false;
     }
    
    private CtExpression castExpressionIfNeeded(CtExpression expr, CtTypeReference<?> targetType) {
        if (expr == null || targetType == null) return expr;
        
        CtTypeReference<?> exprType = expr.getType();
        if (exprType == null) return expr;
        
        if (!needsCast(exprType, targetType)) {
            return expr;
        }
        
        String castStr = "((" + targetType.getSimpleName() + ")(" + expr.toString() + "))";
        CtCodeSnippetExpression castExpr = factory.createCodeSnippetExpression(castStr);
        
        return castExpr;
    }

    private CtVariableRead createVariableRead(String varName, CtTypeReference type) {
        CtVariableReference varRef = factory.createLocalVariableReference();
        varRef.setSimpleName(varName);
        varRef.setType(type);
        
        CtVariableRead varRead = factory.createVariableRead();
        varRead.setVariable(varRef);
        
        return varRead;
    }
    
    private String fixSpecialConstants(String code) {
        // Replace unqualified special float/double constants with qualified ones
        // But only if they are not already qualified (i.e., not preceded by .)
        
        // NaNF → java.lang.Float.NaN (only if not already qualified)
        code = code.replaceAll("(?<!\\.)\\bNaNF\\b", "java.lang.Float.NaN");
        
        // NaN → java.lang.Double.NaN (only if not already qualified and not followed by F)
        code = code.replaceAll("(?<!\\.)\\bNaN\\b(?!F)", "java.lang.Double.NaN");
        
        // POSITIVE_INFINITYF → java.lang.Float.POSITIVE_INFINITY (only if not already qualified)
        code = code.replaceAll("(?<!\\.)\\bPOSITIVE_INFINITYF\\b", "java.lang.Float.POSITIVE_INFINITY");
        
        // NEGATIVE_INFINITYF → java.lang.Float.NEGATIVE_INFINITY (only if not already qualified)
        code = code.replaceAll("(?<!\\.)\\bNEGATIVE_INFINITYF\\b", "java.lang.Float.NEGATIVE_INFINITY");
        
        // POSITIVE_INFINITY → java.lang.Double.POSITIVE_INFINITY (only if not already qualified and not followed by F)
        code = code.replaceAll("(?<!\\.)\\bPOSITIVE_INFINITY\\b(?!F)", "java.lang.Double.POSITIVE_INFINITY");
        
        // NEGATIVE_INFINITY → java.lang.Double.NEGATIVE_INFINITY (only if not already qualified and not followed by F)
        code = code.replaceAll("(?<!\\.)\\bNEGATIVE_INFINITY\\b(?!F)", "java.lang.Double.NEGATIVE_INFINITY");
        
        // Infinity → java.lang.Double.POSITIVE_INFINITY (only if not already qualified)
        code = code.replaceAll("(?<!\\.)\\bInfinity\\b", "java.lang.Double.POSITIVE_INFINITY");
        
        return code;
    }
    
    private boolean addFullSequenceForVariable(CtExpression varExpr, CtTypeReference varType, 
                                                List<CtStatement> stmts, Map<String, Integer> varNameCounter) {
        debugLog("[RecursiveGen] === addFullSequenceForVariable called ===");
        debugLog("[RecursiveGen] varType: " + (varType != null ? varType.getQualifiedName() : "null"));
        
        if (varType == null) {
            debugLog("[RecursiveGen] ERROR: varType is null, returning false");
            return false;
        }
        
        debugLog("[RecursiveGen] Searching for candidate in pool for type: " + varType.getQualifiedName());
        Pair<CtTypeReference, CtElement> candidate = selectCandidateFromPool(varType, new HashSet<>());
        debugLog("[RecursiveGen] selectCandidateFromPool result: " + (candidate != null ? "FOUND" : "NULL"));
        
        if (candidate == null) {
            debugLog("[RecursiveGen] Trying selectCompatibleCandidateFromPool...");
            candidate = selectCompatibleCandidateFromPool(varType, new HashSet<>());
            debugLog("[RecursiveGen] selectCompatibleCandidateFromPool result: " + (candidate != null ? "FOUND" : "NULL"));
        }
        
        if (candidate == null) {
         debugLog("[RecursiveGen] ✗ Cannot find any candidate sequence for type: " + varType.getQualifiedName());
             debugLog("[RecursiveGen] Available types in pool:");
             // CandidatePool.getVarTypeNamePool().keySet().forEach(t -> System.out.println("  - " + t.getQualifiedName()));
             return false;
        }
        
        debugLog("[RecursiveGen] Using candidate: " + candidate.getValue().toString());
        Set<List<CtElement>> sequences = CandidatePool.getVartypeToInputPool().get(candidate);
        debugLog("[RecursiveGen] Sequences found: " + (sequences != null ? sequences.size() : "null/0"));
        
        if (sequences == null || sequences.isEmpty()) {
            debugLog("[RecursiveGen] ✗ No sequences found for type: " + varType.getQualifiedName());
            return false;
        }
        
        List<CtElement> chosenSequence = selectRandomSequence(sequences);
        debugLog("[RecursiveGen] ✓ Adding " + chosenSequence.size() + " statements for type: " + varType.getQualifiedName());
        
        for (CtElement elem : chosenSequence) {
            if (elem instanceof CtStatement) {
                CtStatement stmt = ((CtStatement) elem).clone();
                String existingVarName = getVarNameIfExists(stmt);
                
                if (existingVarName != null) {
                    if (isAlreadyDeclared(existingVarName, stmts)) {
                        String newVarName = generateUniqueName(existingVarName, varNameCounter);
                        if (stmt instanceof CtLocalVariable) {
                            ((CtLocalVariable) stmt).setSimpleName(newVarName);
                        }
                    }
                }
                stmts.add(stmt);
            }
        }
        
        return true;
    }
    
    private String getVarNameIfExists(CtStatement stmt) {
         if (stmt instanceof CtLocalVariable) {
             return ((CtLocalVariable) stmt).getSimpleName();
         }
         return null;
    }
    
    private CtExpression processInputFromPool(Input input, List<CtStatement> stmts, 
                                               Map<String, Integer> varNameCounter, 
                                               Set<String> usedStmtPatterns, int depth) {
        if (input == null) {
            return null;
        }
        
        try {
            // Add input's preparation statements to stmts
            if (input.isVar() && input.getInput() != null) {
                for (CtElement elem : input.getInput()) {
                    if (elem instanceof CtStatement) {
                        CtStatement stmt = ((CtStatement) elem).clone();
                        stmts.add(stmt);
                    }
                }
            }
            
            // Get the variable reference
            CtElement varName = input.getVarName();
            if (varName != null) {
                if (varName instanceof CtExpression) {
                    return (CtExpression) varName;
                } else if (varName instanceof CtVariableReference) {
                    CtTypeReference type = input.getType();
                    return createVariableRead(((CtVariableReference) varName).getSimpleName(), type);
                }
            }
            
            return null;
        } catch (Exception e) {
            debugLog("[processInputFromPool] Failed to process Input: " + e.getMessage());
            return null;
        }
    }
    
    /**
     * Process Input by taking ONLY the last statement and resolving its dependencies recursively.
     * This is used for combinatorial testing where we want to use MUTInput pool objects
     * but resolve their dependencies through the recursive type resolution mechanism.
     */
    private CtExpression processInputLastStmtOnly(Input input, List<CtStatement> stmts, 
                                                   Map<String, Integer> varNameCounter, 
                                                   Set<String> usedStmtPatterns, int depth) {
        if (input == null) {
            return null;
        }
        
        try {
            // For non-variable inputs (direct values/literals), return them directly
            if (!input.isVar()) {
                CtElement directValue = input.getDirectValue();
                if (directValue instanceof CtExpression) {
                    return (CtExpression) directValue;
                }
                return null;
            }
            
            // For variable inputs, get the last statement only
            List<CtElement> inputSequence = input.getInput();
            if (inputSequence == null || inputSequence.isEmpty()) {
                debugLog("[processInputLastStmtOnly] Input sequence is null or empty");
                return null;
            }
            
            // Get the last statement (the one that creates the variable we need)
            CtElement lastElement = inputSequence.get(inputSequence.size() - 1);
            if (!(lastElement instanceof CtStatement)) {
                debugLog("[processInputLastStmtOnly] Last element is not a CtStatement");
                return null;
            }
            
            CtStatement lastStmt = ((CtStatement) lastElement).clone();
            debugLog("[processInputLastStmtOnly] Processing lastStmt: " + lastStmt.toString());
            
            // Validate the last statement
            if (lastStmt instanceof CtLocalVariable) {
                CtLocalVariable localVar = (CtLocalVariable) lastStmt;
                CtTypeReference varType = localVar.getType();
                CtExpression defaultExpr = localVar.getDefaultExpression();
                
                // Check for void invocations
                if (defaultExpr instanceof CtInvocation) {
                    CtInvocation invocation = (CtInvocation) defaultExpr;
                    CtTypeReference returnType = invocation.getType();
                    if (returnType != null && "void".equals(returnType.getSimpleName())) {
                        debugLog("[processInputLastStmtOnly] Skipping void invocation");
                        return null;
                    }
                }
                
                // Recursively resolve dependencies of this statement
                debugLog("[processInputLastStmtOnly] Resolving dependencies for lastStmt at depth " + (depth + 1));
                processStatementDependencies(lastStmt, stmts, varNameCounter, depth + 1);
                
                // Handle variable name conflicts
                String varName = localVar.getSimpleName();
                if (isAlreadyDeclared(varName, stmts)) {
                    varName = generateUniqueNameFromStmts(varName, stmts, varNameCounter);
                    localVar.setSimpleName(varName);
                }
                
                // Add the statement
                stmts.add(lastStmt);
                
                // Return variable read
                return createVariableRead(varName, varType);
                
            } else if (lastStmt instanceof CtInvocation) {
                CtInvocation invocation = (CtInvocation) lastStmt;
                CtTypeReference returnType = invocation.getType();
                
                if (returnType != null && "void".equals(returnType.getSimpleName())) {
                    debugLog("[processInputLastStmtOnly] Skipping void invocation");
                    return null;
                }
                
                CtExpression target = invocation.getTarget();
                if (target == null || (target instanceof CtLiteral && ((CtLiteral) target).getValue() == null)) {
                    debugLog("[processInputLastStmtOnly] Invocation has null target");
                    return null;
                }
                
                // Recursively resolve dependencies
                processStatementDependencies(lastStmt, stmts, varNameCounter, depth + 1);
                
                // Wrap in variable
                String varName = generateUniqueName(returnType != null ? returnType.getSimpleName() : "var", varNameCounter);
                CtLocalVariable newVar = factory.createLocalVariable(
                    returnType != null ? returnType : factory.createReference("java.lang.Object"),
                    varName,
                    invocation
                );
                stmts.add(newVar);
                
                return createVariableRead(varName, returnType);
                
            } else if (lastStmt instanceof CtConstructorCall) {
                CtConstructorCall ctorCall = (CtConstructorCall) lastStmt;
                CtTypeReference actualType = ctorCall.getType();
                
                // Recursively resolve dependencies
                processStatementDependencies(lastStmt, stmts, varNameCounter, depth + 1);
                
                // Wrap in variable
                String varName = generateUniqueName(actualType != null ? actualType.getSimpleName() : "obj", varNameCounter);
                CtLocalVariable newVar = factory.createLocalVariable(
                    actualType != null ? actualType : factory.createReference("java.lang.Object"),
                    varName,
                    ctorCall
                );
                stmts.add(newVar);
                
                return createVariableRead(varName, actualType);
            }
            
            debugLog("[processInputLastStmtOnly] Unsupported statement type: " + lastStmt.getClass().getSimpleName());
            return null;
            
        } catch (Exception e) {
            debugLog("[processInputLastStmtOnly] Exception: " + e.getMessage());
            e.printStackTrace();
            return null;
        }
    }
    
    private String getCandidateName(Pair<CtTypeReference, CtElement> candidate) {
        if (candidate == null || candidate.getValue() == null) {
            return "";
        }
        CtElement element = candidate.getValue();
        if (element instanceof CtLocalVariable) {
            return ((CtLocalVariable) element).getSimpleName();
        } else if (element instanceof CtVariableReference) {
            return ((CtVariableReference) element).getSimpleName();
        }
        return element.toString();
    }
    
    private void renameVariableReferences(CtStatement stmt, Map<String, String> renameMap) {
        if (renameMap.isEmpty()) {
            return;
        }
        
        // Find all CtVariableRead in the statement and rename them
        List<CtVariableRead> varReads = stmt.getElements(new spoon.reflect.visitor.filter.TypeFilter<>(CtVariableRead.class));
        for (CtVariableRead varRead : varReads) {
            String oldName = varRead.getVariable().getSimpleName();
            String newName = renameMap.get(oldName);
            if (newName != null) {
                varRead.getVariable().setSimpleName(newName);
            }
        }
        
        // Also find all CtVariableWrite (assignment left-hand side) and rename them
        List<spoon.reflect.code.CtVariableWrite> varWrites = stmt.getElements(
            new spoon.reflect.visitor.filter.TypeFilter<>(spoon.reflect.code.CtVariableWrite.class));
        for (spoon.reflect.code.CtVariableWrite varWrite : varWrites) {
            String oldName = varWrite.getVariable().getSimpleName();
            String newName = renameMap.get(oldName);
            if (newName != null) {
                varWrite.getVariable().setSimpleName(newName);
            }
        }
    }
    
    private void processConstructorCallArguments(CtConstructorCall ctorCall, List<CtStatement> stmts, 
                                                  Map<String, Integer> varNameCounter, int depth) {
        List<CtExpression> processedArgs = new ArrayList<>();
        List<?> args = ctorCall.getArguments();
        
        List<CtTypeReference<?>> parameterTypes = null;
        try {
            CtExecutableReference<?> executable = ctorCall.getExecutable();
            if (executable != null) {
                parameterTypes = executable.getParameters();
            }
        } catch (Exception e) {
        }
        
        for (int i = 0; i < args.size(); i++) {
            Object argObj = args.get(i);
            CtExpression arg = (CtExpression) argObj;
            
            if (arg instanceof CtVariableRead) {
                String varName = ((CtVariableRead) arg).getVariable().getSimpleName();
                CtTypeReference argType = arg.getType();
                
                CtTypeReference expectedType = (parameterTypes != null && i < parameterTypes.size()) 
                    ? parameterTypes.get(i) 
                    : argType;
                
                if (!isAlreadyDeclared(varName, stmts)) {
                    CtExpression resolved = resolveType(expectedType, stmts, varNameCounter, new HashSet<>(), depth);
                    if (resolved != null) {
                        processedArgs.add(resolved);
                    } else {
                        processedArgs.add(arg);
                    }
                } else {
                    processedArgs.add(arg);
                }
            } else if (arg instanceof CtConstructorCall) {
                // Recursively process nested constructor call
                CtConstructorCall nestedCtor = (CtConstructorCall) arg;
                processConstructorCallArguments(nestedCtor, stmts, varNameCounter, depth);
                processedArgs.add(nestedCtor);
            } else if (arg instanceof CtInvocation) {
                // Process invocation (e.g., new Foo().getBar() or foo.getBar().getBaz())
                CtInvocation invocation = (CtInvocation) arg;
                CtExpression target = invocation.getTarget();
                if (target instanceof CtConstructorCall) {
                    processConstructorCallArguments((CtConstructorCall) target, stmts, varNameCounter, depth);
                } else if (target instanceof CtInvocation) {
                    // Nested invocation - recursively process it
                    processNestedInvocationDependencies((CtInvocation) target, stmts, varNameCounter, depth);
                } else if (target instanceof CtVariableRead) {
                    String varName = ((CtVariableRead) target).getVariable().getSimpleName();
                    if (!isAlreadyDeclared(varName, stmts)) {
                        CtTypeReference targetType = ((CtVariableRead) target).getType();
                        CtExpression resolved = resolveType(targetType, stmts, varNameCounter, new HashSet<>(), depth);
                        if (resolved != null) {
                            invocation.setTarget(resolved);
                        }
                    }
                }
                // Also process invocation arguments
                List<CtExpression> invProcessedArgs = new ArrayList<>();
                List<?> invArgs = invocation.getArguments();
                for (Object invArgObj : invArgs) {
                    CtExpression invArg = (CtExpression) invArgObj;
                    if (invArg instanceof CtVariableRead) {
                        String varName = ((CtVariableRead) invArg).getVariable().getSimpleName();
                        CtTypeReference argType = invArg.getType();
                        if (!isAlreadyDeclared(varName, stmts)) {
                            CtExpression resolved = resolveType(argType, stmts, varNameCounter, new HashSet<>(), depth);
                            if (resolved != null) {
                                invProcessedArgs.add(resolved);
                            } else {
                                invProcessedArgs.add(invArg);
                            }
                        } else {
                            invProcessedArgs.add(invArg);
                        }
                    } else if (invArg instanceof CtConstructorCall) {
                        processConstructorCallArguments((CtConstructorCall) invArg, stmts, varNameCounter, depth);
                        invProcessedArgs.add(invArg);
                    } else if (invArg instanceof CtInvocation) {
                        // Nested invocation as argument - recursively process it
                        CtInvocation nestedInv = (CtInvocation) invArg;
                        CtExpression nestedTarget = nestedInv.getTarget();
                        if (nestedTarget instanceof CtVariableRead) {
                            String nestedVarName = ((CtVariableRead) nestedTarget).getVariable().getSimpleName();
                            if (!isAlreadyDeclared(nestedVarName, stmts)) {
                                CtTypeReference nestedTargetType = ((CtVariableRead) nestedTarget).getType();
                                CtExpression resolved = resolveType(nestedTargetType, stmts, varNameCounter, new HashSet<>(), depth);
                                if (resolved != null) {
                                    nestedInv.setTarget(resolved);
                                }
                            }
                        } else if (nestedTarget instanceof CtInvocation) {
                            processNestedInvocationDependencies((CtInvocation) nestedTarget, stmts, varNameCounter, depth);
                        }
                        invProcessedArgs.add(nestedInv);
                    } else {
                        invProcessedArgs.add(invArg);
                    }
                }
                invocation.setArguments((List) invProcessedArgs);
                processedArgs.add(invocation);
            } else {
                processedArgs.add(arg);
            }
        }
        ctorCall.setArguments((List) processedArgs);
    }


    private boolean isLastStmtDefValid(CtElement lastStmt, CtElement target){
        if (!(lastStmt instanceof CtLocalVariable)) {
            return false;
        }
        
        if (target == null) {
            return false;
        }
        
        CtLocalVariable lastVar = (CtLocalVariable) lastStmt;
        String declaredVarName = lastVar.getSimpleName();
        
        String targetVarName = null;
        if (target instanceof CtVariableRead) {
            targetVarName = ((CtVariableRead) target).getVariable().getSimpleName();
        } else if (target instanceof CtLocalVariable) {
            targetVarName = ((CtLocalVariable) target).getSimpleName();
        } else {
            targetVarName = target.toString().trim();
        }
        
        return declaredVarName != null && declaredVarName.equals(targetVarName);
    }



     private void processNestedInvocationDependencies(CtInvocation invocation, List<CtStatement> stmts,
                                                     Map<String, Integer> varNameCounter, int depth) {
        CtExpression target = invocation.getTarget();
        if (target instanceof CtVariableRead) {
            String varName = ((CtVariableRead) target).getVariable().getSimpleName();
            if (!isAlreadyDeclared(varName, stmts)) {
                CtTypeReference targetType = ((CtVariableRead) target).getType();
                CtExpression resolved = resolveType(targetType, stmts, varNameCounter, new HashSet<>(), depth);
                if (resolved != null) {
                    invocation.setTarget(resolved);
                }
            }
        } else if (target instanceof CtInvocation) {
            processNestedInvocationDependencies((CtInvocation) target, stmts, varNameCounter, depth);
        }
        
        List<CtExpression> processedArgs = new ArrayList<>();
        List<?> args = invocation.getArguments();
        for (Object argObj : args) {
            CtExpression arg = (CtExpression) argObj;
            if (arg instanceof CtVariableRead) {
                String varName = ((CtVariableRead) arg).getVariable().getSimpleName();
                CtTypeReference argType = arg.getType();
                if (!isAlreadyDeclared(varName, stmts)) {
                    CtExpression resolved = resolveType(argType, stmts, varNameCounter, new HashSet<>(), depth);
                    if (resolved != null) {
                        processedArgs.add(resolved);
                    } else {
                        processedArgs.add(arg);
                    }
                } else {
                    processedArgs.add(arg);
                }
            } else {
                processedArgs.add(arg);
            }
        }
        invocation.setArguments((List) processedArgs);
    }

    public String getPackageAndImport() {
        return packageAndImport;
    }

    public void setPackageAndImport(String packageAndImport) {
        this.packageAndImport = packageAndImport;
    }
    
    public long getOverhead() {
        return 0L;
    }
    
    private boolean hasNestedSameTypeConstructor(CtConstructorCall ctorCall) {
        if (ctorCall == null) {
            return false;
        }
        
        CtTypeReference ctorType = ctorCall.getType();
        if (ctorType == null) {
            return false;
        }
        
        String ctorTypeName = ctorType.getQualifiedName();
        
        List<?> args = ctorCall.getArguments();
        for (Object argObj : args) {
            if (!(argObj instanceof CtExpression)) {
                continue;
            }
            
            CtExpression arg = (CtExpression) argObj;
            
            if (arg instanceof CtInvocation) {
                CtInvocation invocation = (CtInvocation) arg;
                CtExpression target = invocation.getTarget();
                
                if (target instanceof CtConstructorCall) {
                    CtConstructorCall nestedCtor = (CtConstructorCall) target;
                    CtTypeReference nestedType = nestedCtor.getType();
                    
                    if (nestedType != null && ctorTypeName.equals(nestedType.getQualifiedName())) {
                        return true;
                    }
                }
            } else if (arg instanceof CtConstructorCall) {
                CtConstructorCall nestedCtor = (CtConstructorCall) arg;
                CtTypeReference nestedType = nestedCtor.getType();
                
                if (nestedType != null && ctorTypeName.equals(nestedType.getQualifiedName())) {
                    return true;
                }
                
                if (hasNestedSameTypeConstructor(nestedCtor)) {
                    return true;
                }
            }
        }
        
        return false;
    }
    
    private boolean hasInvalidAnnotatedParameterPattern(CtConstructorCall ctorCall) {
        if (ctorCall == null) {
            return false;
        }
        
        CtTypeReference ctorType = ctorCall.getType();
        if (ctorType == null) {
            return false;
        }
        
        String ctorTypeName = ctorType.getQualifiedName();
        
        if ("com.fasterxml.jackson.databind.introspect.AnnotatedParameter".equals(ctorTypeName)) {
            List<?> args = ctorCall.getArguments();
            if (args.isEmpty()) {
                return false;
            }
            
            Object firstArgObj = args.get(0);
            if (!(firstArgObj instanceof CtExpression)) {
                return false;
            }
            
            CtExpression firstArg = (CtExpression) firstArgObj;
            
            if (firstArg instanceof CtVariableRead) {
                CtTypeReference argType = firstArg.getType();
                if (argType != null) {
                    String argTypeName = argType.getQualifiedName();
                    if ("java.lang.reflect.Constructor".equals(argTypeName) ||
                        "java.lang.reflect.Method".equals(argTypeName) ||
                        "java.lang.reflect.Field".equals(argTypeName)) {
                        return true;
                    }
                }
            }
        }
        
        List<?> args = ctorCall.getArguments();
        for (Object argObj : args) {
            if (!(argObj instanceof CtExpression)) {
                continue;
            }
            
            CtExpression arg = (CtExpression) argObj;
            
            if (arg instanceof CtConstructorCall) {
                CtConstructorCall nestedCtor = (CtConstructorCall) arg;
                if (hasInvalidAnnotatedParameterPattern(nestedCtor)) {
                    return true;
                }
            }
        }
        
        return false;
    }
    
    private Pair<CtClass, List<String>> addRegressionOracleToTest(CtClass<Object> generatedTest) {
        debugOracleLog("[addRegressionOracleToTest] Starting oracle instrumentation");
        // Analyze
        debugOracleLog("[addRegressionOracleToTest] Analyzing local variables (non-primitive)");
        Map<CtMethod, List<CtLocalVariable>> localVariablesPerTestMethod = analyzer.analyze(generatedTest, false);
        debugOracleLog("[addRegressionOracleToTest] Analyzing local variables (primitive)");
        Map<CtMethod, List<CtLocalVariable>> localVariablesPrimitive = analyzer.analyze(generatedTest, true);
        // Collect
        Set<CtMethod<?>> methods = generatedTest.getMethods();
         debugOracleLog("[addRegressionOracleToTest] Number of methods in test class: " + methods.size());
         if (methods.size() != 1) {
             // System.out.println("[addRegressionOracleToTest] WARNING: The number of methods in class is not 1: " + methods.size());
             return null;
         }
        for (CtMethod<?> ctMethod : methods) {
            debugOracleLog("[addRegressionOracleToTest] Instrumenting observer for method: " + ctMethod.getSimpleName());
            debugOracleLog("[addRegressionOracleToTest] Non-primitive variables to observe: " + (localVariablesPerTestMethod.get(ctMethod) != null ? localVariablesPerTestMethod.get(ctMethod).size() : 0));
            debugOracleLog("[addRegressionOracleToTest] Primitive variables to observe: " + (localVariablesPrimitive.get(ctMethod) != null ? localVariablesPrimitive.get(ctMethod).size() : 0));
            Pair<CtClass, List<String>> observerAddedClassAndStringPair = collector.instrumentObserver(ctMethod,
                    localVariablesPerTestMethod, localVariablesPrimitive);
            debugOracleLog("[addRegressionOracleToTest] Observer instrumentation completed, returning result");
            return observerAddedClassAndStringPair;
        }
        debugOracleLog("[addRegressionOracleToTest] No methods found to instrument");
        return null;
    }
    
    private void fixUndefinedVariablesInMethod(CtMethod<?> method) {
        if (method == null || method.getBody() == null) {
            return;
        }
        
        // Use Spoon to find DEF-USE analysis
        // DEF: All variable declarations in the method
        Set<String> declaredVars = new HashSet<>();
        List<CtLocalVariable<?>> localVarDecls = method.getElements(new spoon.reflect.visitor.filter.TypeFilter<>(CtLocalVariable.class));
        for (CtLocalVariable<?> varDecl : localVarDecls) {
            declaredVars.add(varDecl.getSimpleName());
        }
        
        // USE: All variable reads in the method
        Map<String, CtTypeReference<?>> undefinedVars = new LinkedHashMap<>();
        List<spoon.reflect.code.CtVariableRead<?>> varReads = method.getElements(
            new spoon.reflect.visitor.filter.TypeFilter<>(spoon.reflect.code.CtVariableRead.class)
        );
        
        for (spoon.reflect.code.CtVariableRead<?> varRead : varReads) {
             String varName = varRead.getVariable().getSimpleName();
             
             // Skip "class" - it's a Java keyword used in type literals (e.g., Object.class)
             // Spoon sometimes parses ".class" as a CtVariableRead incorrectly
             if ("class".equals(varName)) {
                 continue;
             }
             
             // [수정] 특수 상수들은 스킵 (NaN, Infinity 등은 나중에 fixSpecialConstants()에서 처리됨)
             // 이들을 undefined variable로 선언하면 컴파일 에러 발생
             if (isSpecialConstant(varName)) {
                 debugLog("[fixUndefinedVariablesInMethod] Skipping special constant: " + varName);
                 continue;
             }
             
             // Check if this variable is used but not declared in this method
             if (!declaredVars.contains(varName)) {
                 // Skip method parameters and class fields
                 if (isMethodParameter(method, varName) || isClassField(method, varName)) {
                     continue;
                 }
                 
                 // Get the type from the variable reference
                 CtTypeReference<?> varType = varRead.getVariable().getType();
                 if (varType == null) {
                     varType = factory.createReference("java.lang.Object");
                 }
                 
                 undefinedVars.put(varName, varType);
             }
         }
        
        // ADDITIONAL: Find chained assignments with regex (these are not captured by CtVariableRead)
        // Pattern: Type var1 = lastXXX = ... or var1 = lastXXX = ...
        List<CtStatement> statements = method.getBody().getStatements();
        for (CtStatement stmt : statements) {
            String stmtStr = stmt.toString();
            
            // Pattern for chained assignment: var1 = var2 = expression
            java.util.regex.Pattern chainPattern = java.util.regex.Pattern.compile(
                "([a-zA-Z_][a-zA-Z0-9_]*)\\s*=\\s*([a-zA-Z_][a-zA-Z0-9_]*)\\s*="
            );
            java.util.regex.Matcher matcher = chainPattern.matcher(stmtStr);
            
            while (matcher.find()) {
                 String middleVar = matcher.group(2);
                 
                 // [수정] 특수 상수들은 스킵
                 if (isSpecialConstant(middleVar)) {
                     debugLog("[fixUndefinedVariablesInMethod] Skipping special constant in chain: " + middleVar);
                     continue;
                 }
                 
                 // Check if middle variable is undeclared
                 if (!declaredVars.contains(middleVar) && !undefinedVars.containsKey(middleVar)) {
                     // Try to infer type from the statement
                     CtTypeReference<?> inferredType = null;
                     
                     if (stmt instanceof CtLocalVariable) {
                         inferredType = ((CtLocalVariable<?>) stmt).getType();
                     }
                     
                     if (inferredType == null) {
                         inferredType = factory.createReference("java.lang.Object");
                     }
                     
                     undefinedVars.put(middleVar, inferredType);
                 }
             }
        }
        
         if (undefinedVars.isEmpty()) {
             return;
         }
         
         // System.out.println("[FixUndefinedVars] Found " + undefinedVars.size() + " undefined variables in method " + method.getSimpleName());
         
          // Add variable declarations at the beginning of the method
          List<CtStatement> newStatements = new ArrayList<>();
          for (Map.Entry<String, CtTypeReference<?>> entry : undefinedVars.entrySet()) {
               String varName = entry.getKey();
               CtTypeReference<?> varType = entry.getValue();
               
               // [수정] _mut이 포함된 변수는 스킵 (MUT 결과 변수이므로 선언하면 안됨)
               if (varName.contains("_mut")) {
                   debugLog("[fixUndefinedVariablesInMethod] Skipping _mut variable: " + varName);
                   continue;
               }
               
               // [수정] FQN 형식(qualified name)이면 스킵 (예: java.lang.Double.NaN)
               // FQN은 이미 사용 가능한 형태이므로 변수 선언할 필요 없음
               if (varName.contains(".")) {
                   debugLog("[fixUndefinedVariablesInMethod] Skipping FQN variable: " + varName);
                   continue;
               }
               
               // Get default value expression based on type
              CtExpression defaultValue = getDefaultValue(varType);
              
              // System.out.println("  Adding declaration: " + varType.getQualifiedName() + " " + varName + " = " + defaultValue + ";");
             
             CtLocalVariable varDecl = factory.createLocalVariable(
                 varType,
                 varName,
                 defaultValue
             );
             newStatements.add(varDecl);
        }
        
        // Add original statements
        newStatements.addAll(method.getBody().getStatements());
        
        // Update method body
        method.getBody().setStatements(newStatements);
    }
    
    private boolean isMethodParameter(CtMethod<?> method, String varName) {
        if (method.getParameters() == null) {
            return false;
        }
        for (spoon.reflect.declaration.CtParameter<?> param : method.getParameters()) {
            if (param.getSimpleName().equals(varName)) {
                return true;
            }
        }
        return false;
    }
    
     private boolean isClassField(CtMethod<?> method, String varName) {
         CtClass<?> parentClass = method.getParent(CtClass.class);
         if (parentClass == null) {
             return false;
         }
         for (spoon.reflect.declaration.CtField<?> field : parentClass.getFields()) {
             if (field.getSimpleName().equals(varName)) {
                 return true;
             }
         }
         return false;
     }
     
     /**
      * Check if a variable name is a special constant (NaN, Infinity, etc.)
      * These are converted to qualified names later by fixSpecialConstants()
      * so they should not be treated as undefined variables
      */
     private boolean isSpecialConstant(String varName) {
         return varName.equals("NaN") || 
                varName.equals("NaNF") ||
                varName.equals("Infinity") ||
                varName.equals("InfinityF") ||
                varName.equals("POSITIVE_INFINITY") ||
                varName.equals("POSITIVE_INFINITYF") ||
                varName.equals("NEGATIVE_INFINITY") ||
                varName.equals("NEGATIVE_INFINITYF");
     }
     
     /**
      * Find an alternative implementation for a given type from the inheritance hierarchy
     * This is useful when the exact type cannot be resolved but a related implementation exists
     * 
     * @param type The type to find an alternative for
     * @return An alternative implementation type, or null if none found
     */
    private CtTypeReference<?> findAlternativeImplementation(CtTypeReference<?> type) {
        if (type == null) {
            return null;
        }
        
        String typeName = type.getQualifiedName();
        
        // Check if this type has known implementations in abstractToImplsMap
        List<CtTypeReference<?>> implementations = ASTParser.abstractToImplsMap.get(typeName);
        
        if (implementations != null && !implementations.isEmpty()) {
            // Return the first available implementation
            // Prefer non-abstract implementations
            for (CtTypeReference<?> impl : implementations) {
                try {
                    CtType<?> implDecl = impl.getTypeDeclaration();
                    if (implDecl != null && !implDecl.isAbstract()) {
                        debugLog("[findAlternativeImplementation] Found concrete implementation for " + typeName + ": " + impl.getQualifiedName());
                        return impl;
                    }
                } catch (Exception e) {
                    // Continue searching
                    continue;
                }
            }
            
            // If no concrete implementation, return the first one anyway
            debugLog("[findAlternativeImplementation] Found abstract implementation for " + typeName + ": " + implementations.get(0).getQualifiedName());
            return implementations.get(0);
        }
        
        debugLog("[findAlternativeImplementation] No alternative implementation found for " + typeName);
        return null;
    }
    
    /**
     * Primitive 또는 String 반환값을 추적할지 확인
     * void, null, 객체는 제외하고 primitive/String만 추적
     */
    private boolean shouldCaptureReturnValue(CtTypeReference<?> returnType) {
        if (returnType == null) {
            return false;
        }
        
        // void 제외
        if ("void".equals(returnType.getSimpleName())) {
            return false;
        }
        
        // Primitive 타입 포함
        if (returnType.isPrimitive()) {
            return true;
        }
        
        // String 포함
        if ("java.lang.String".equals(returnType.getQualifiedName())) {
            return true;
        }
        
        // 그 외 객체타입 제외
        return false;
    }
    
    /**
     * 독립 구문 메서드 호출의 반환값을 변수에 저장하고 Logger.observe() 추가
     * 예: sw.toString() → String result_0_mut = sw.toString();
     *           Logger.observe(..., "local$result_0_mut", result_0_mut);
     */
    private void captureStatementInvocationReturnValue(CtInvocation invocation, 
                                                       List<CtStatement> stmts, 
                                                       Map<String, Integer> varNameCounter) {
        try {
            CtTypeReference<?> returnType = invocation.getExecutable().getType();
            
            // Primitive/String 반환값만 추적
            if (!shouldCaptureReturnValue(returnType)) {
                if (DEBUG_ORACLE) {
                    System.out.println("[captureStatementInvocationReturnValue] Skipping capture for return type: " + 
                        (returnType != null ? returnType.getQualifiedName() : "null"));
                }
                return;
            }
            
            // 반환값을 저장할 변수 생성
            int counter = varNameCounter.getOrDefault("result", 0);
            String resultVarName = "result_" + counter + "_mut";
            varNameCounter.put("result", counter + 1);
            
            if (DEBUG_ORACLE) {
                System.out.println("[captureStatementInvocationReturnValue] Capturing return value: " + 
                    resultVarName + " (" + (returnType != null ? returnType.getQualifiedName() : "null") + ")");
            }
            
            // result_X_mut = invocation; 형태의 변수 선언 생성
            Factory factory = invocation.getFactory();
            
            // 코드 스니펫으로 변수 선언 생성
            String returnTypeStr = returnType != null ? returnType.getQualifiedName() : "Object";
            String varDeclCode = returnTypeStr + " " + resultVarName + " = " + invocation.toString();
            
            CtLocalVariable<?> resultVar = factory.createCodeSnippetStatement(varDeclCode).getParent(CtLocalVariable.class);
            
            if (resultVar == null) {
                // 코드 스니펫으로 직접 생성
                CtLocalVariable<?> localVar = factory.createLocalVariable(returnType, resultVarName, invocation.clone());
                stmts.add(localVar);
            } else {
                stmts.add(resultVar);
            }
            
            // Logger.observe() 추가
            addLoggerObserveStatement(stmts, resultVarName, resultVarName, factory);
            
        } catch (Exception e) {
            if (DEBUG_ORACLE) {
                System.out.println("[captureStatementInvocationReturnValue] Error capturing return value: " + e.getMessage());
                e.printStackTrace();
            }
        }
    }
    
    /**
     * Logger.observe() 호출 statement 추가
     * Logger.observe(testName, key, value);
     */
    private void addLoggerObserveStatement(List<CtStatement> stmts, String resultVarName, 
                                          String key, Factory factory) {
        try {
            // Logger.observe(testName, key, resultVarName) 코드 스니펫으로 생성
            String observeCode = String.format(
                "RegressionOracles.RegressionUtil.Logger.observe(\"%s\", \"local$%s\", %s);",
                testClassName,
                key,
                resultVarName
            );
            
            CtStatement observeStmt = factory.createCodeSnippetStatement(observeCode);
            stmts.add(observeStmt);
            
        } catch (Exception e) {
            if (DEBUG_ORACLE) {
                System.out.println("[addLoggerObserveStatement] Error adding Logger.observe: " + e.getMessage());
            }
        }
    }

    /**
     * CtInvocation/CtConstructorCall의 arguments를 처리하는 공통 헬퍼 메서드
     * CtVariableRead, CtLiteral 등을 각각 처리
     * @param args 처리할 arguments 리스트
     * @param stmts statement 리스트
     * @param varNameCounter 변수 이름 카운터
     * @param depth 재귀 깊이
     * @return 처리된 arguments
     */
    private List<CtExpression> processArgumentsWithLiteralReplacement(
            List<?> args, List<CtStatement> stmts, 
            Map<String, Integer> varNameCounter, int depth) {
        
        List<CtExpression> processedArgs = new ArrayList<>();
        
        for (Object argObj : args) {
            CtExpression arg = (CtExpression) argObj;
            
            if (arg instanceof CtVariableRead) {
                String varName = ((CtVariableRead) arg).getVariable().getSimpleName();
                CtTypeReference argType = arg.getType();
                if (!isAlreadyDeclared(varName, stmts)) {
                    CtExpression resolved = resolveType(argType, stmts, varNameCounter, new HashSet<>(), depth);
                    if (resolved != null) {
                        processedArgs.add(resolved);
                    } else {
                        processedArgs.add(arg);
                    }
                } else {
                    processedArgs.add(arg);
                }
            } else if (arg instanceof CtLiteral) {
                // ⭐ 리터럴의 경우, 입력 풀에서 같은 타입의 다른 값으로 대체 시도
                CtTypeReference argType = arg.getType();
                if (DEBUG_RECURSIVE_GEN) {
                    System.out.println("[processArgumentsWithLiteralReplacement] Original literal: " + arg.toString() + 
                        " (type: " + (argType != null ? argType.getQualifiedName() : "null") + ")");
                }
                CtExpression replacementFromPool = findLiteralReplacement(argType, stmts, varNameCounter);
                if (replacementFromPool != null) {
                    if (DEBUG_RECURSIVE_GEN) {
                        System.out.println("[processArgumentsWithLiteralReplacement] ✓ Replaced with: " + replacementFromPool.toString());
                    }
                    processedArgs.add(replacementFromPool);
                } else {
                    if (DEBUG_RECURSIVE_GEN) {
                        System.out.println("[processArgumentsWithLiteralReplacement] ✗ No replacement found, keeping original: " + arg.toString());
                    }
                    processedArgs.add(arg);  // 대체제 없으면 원래 값 유지
                }
            } else {
                processedArgs.add(arg);
            }
        }
        
        return processedArgs;
    }

    /**
     * 리터럴 값을 입력 풀에서 같은 타입의 다른 값으로 교체하는 헬퍼 메서드
     * Primitive Type과 String의 경우 우선적으로 다음을 활용:
     * 1. CandidatePool.getDirectToValues() (리터럴)
     * 2. CandidatePool.varTypeNamePool + vartypeToInputPool (변수)
     * 3. InputCombinations.processInputPool() (fallback)
     * @param literalType 리터럴의 타입
     * @param stmts statement 리스트 (변수 선언 추가용)
     * @param varNameCounter 변수 이름 카운터
     * @return 풀에서 찾은 같은 타입의 값, 없으면 null
     */
    private CtExpression findLiteralReplacement(CtTypeReference literalType, 
                                                 List<CtStatement> stmts, 
                                                 Map<String, Integer> varNameCounter) {
        if (literalType == null) {
            return null;
        }

        try {
            String typeName = literalType.getQualifiedName();
            
            if (DEBUG_RECURSIVE_GEN) {
                System.out.println("\n[findLiteralReplacement] Starting replacement search for type: " + typeName);
            }
            
             // ⭐ Primitive Type + String인 경우, directToValues와 varTypeNamePool에서 모두 수집
             if (isPrimitiveOrStringType(typeName)) {
                 if (DEBUG_RECURSIVE_GEN) {
                     System.out.println("[findLiteralReplacement] Type is Primitive/String, collecting from both pools...");
                 }
                 
                 List<Object> allCandidates = new ArrayList<>();  // 리터럴과 변수를 섞어서 저장
                 
                 // directToValues에서 리터럴 값 모두 수집
                 if (DEBUG_RECURSIVE_GEN) {
                     System.out.println("[findLiteralReplacement] Collecting literals from directToValues...");
                 }
                 HashMap<CtTypeReference, Set<CtElement>> directToValues = 
                     Generater.MUTMutation.CandidatePool.getDirectToValues();
                 int literalCount = 0;
                 for (Map.Entry<CtTypeReference, Set<CtElement>> entry : directToValues.entrySet()) {
                     if (areTypesCompatible(entry.getKey(), literalType)) {
                         Set<CtElement> values = entry.getValue();
                         if (values != null && !values.isEmpty()) {
                             for (CtElement value : values) {
                                 if (value instanceof CtExpression) {
                                     allCandidates.add(value);
                                     literalCount++;
                                 }
                             }
                         }
                     }
                 }
                 if (DEBUG_RECURSIVE_GEN) {
                     System.out.println("[findLiteralReplacement] Collected " + literalCount + " literals");
                 }
                 
                 // varTypeNamePool에서 변수 모두 수집
                 if (DEBUG_RECURSIVE_GEN) {
                     System.out.println("[findLiteralReplacement] Collecting variables from varTypeNamePool...");
                 }
                 HashMap<CtTypeReference, Set<Pair<CtTypeReference, CtElement>>> varTypeNamePool = 
                     Generater.MUTMutation.CandidatePool.getVarTypeNamePool();
                 HashMap<Pair<CtTypeReference, CtElement>, Set<List<CtElement>>> vartypeToInputPool = 
                     Generater.MUTMutation.CandidatePool.getVartypeToInputPool();
                 int variableCount = 0;
                 for (Map.Entry<CtTypeReference, Set<Pair<CtTypeReference, CtElement>>> entry : varTypeNamePool.entrySet()) {
                     if (areTypesCompatible(entry.getKey(), literalType)) {
                         Set<Pair<CtTypeReference, CtElement>> pairs = entry.getValue();
                         if (pairs != null && !pairs.isEmpty()) {
                             for (Pair<CtTypeReference, CtElement> pair : pairs) {
                                 Set<List<CtElement>> inputSequences = vartypeToInputPool.get(pair);
                                 if (inputSequences != null && !inputSequences.isEmpty()) {
                                     allCandidates.add(pair);
                                     variableCount++;
                                 }
                             }
                         }
                     }
                 }
                 if (DEBUG_RECURSIVE_GEN) {
                     System.out.println("[findLiteralReplacement] Collected " + variableCount + " variables");
                 }
                 
                 // 수집된 후보에서 랜덤으로 선택
                 if (!allCandidates.isEmpty()) {
                     if (DEBUG_RECURSIVE_GEN) {
                         System.out.println("[findLiteralReplacement] Total candidates: " + allCandidates.size() + 
                             " (" + literalCount + " literals + " + variableCount + " variables)");
                     }
                     
                      int randomIdx = random.nextInt(allCandidates.size());
                      Object selectedCandidate = allCandidates.get(randomIdx);
                      
                      if (DEBUG_RECURSIVE_GEN) {
                          System.out.println("[findLiteralReplacement] 🎲 Randomly selected index " + randomIdx + "/" + allCandidates.size());
                      }
                      
                      // 리터럴인 경우
                      if (selectedCandidate instanceof CtExpression) {
                          CtExpression literal = (CtExpression) selectedCandidate;
                          if (DEBUG_RECURSIVE_GEN) {
                              System.out.println("[findLiteralReplacement] ✓ Selected LITERAL: " + literal.toString());
                          }
                          return literal;
                      }
                      
                      // 변수 Pair인 경우
                      if (selectedCandidate instanceof Pair) {
                          @SuppressWarnings("unchecked")
                          Pair<CtTypeReference, CtElement> pair = (Pair<CtTypeReference, CtElement>) selectedCandidate;
                          CtTypeReference pairType = pair.getKey();
                          CtElement pairElement = pair.getValue();
                          
                          if (DEBUG_RECURSIVE_GEN) {
                              System.out.println("[findLiteralReplacement] ✓ Selected VARIABLE from pair:");
                              System.out.println("[findLiteralReplacement]   🔹 Pair type: " + (pairType != null ? pairType.getQualifiedName() : "null"));
                              System.out.println("[findLiteralReplacement]   🔹 Pair element: " + (pairElement != null ? pairElement.toString() : "null"));
                          }
                          
                          Set<List<CtElement>> inputSequences = vartypeToInputPool.get(pair);
                          
                          if (DEBUG_RECURSIVE_GEN) {
                              System.out.println("[findLiteralReplacement]   📝 Input sequences count: " + 
                                  (inputSequences != null ? inputSequences.size() : 0));
                          }
                          
                          if (inputSequences != null && !inputSequences.isEmpty()) {
                              List<CtElement> sequence = inputSequences.iterator().next();
                              
                              if (DEBUG_RECURSIVE_GEN) {
                                  System.out.println("[findLiteralReplacement]   📋 Selected sequence has " + 
                                      (sequence != null ? sequence.size() : 0) + " elements");
                              }
                              
                              if (sequence != null && !sequence.isEmpty()) {
                                  CtElement lastElement = sequence.get(sequence.size() - 1);
                                  
                                  if (DEBUG_RECURSIVE_GEN) {
                                      System.out.println("[findLiteralReplacement]   📌 Last element type: " + 
                                          (lastElement != null ? lastElement.getClass().getSimpleName() : "null"));
                                  }
                                  
                                  if (lastElement instanceof CtStatement) {
                                      CtStatement lastStmt = ((CtStatement) lastElement).clone();
                                      
                                      if (lastStmt instanceof CtLocalVariable) {
                                          CtLocalVariable<?> localVar = (CtLocalVariable<?>) lastStmt;
                                          String originalVarName = localVar.getSimpleName();
                                          String varName = originalVarName;
                                          
                                          if (DEBUG_RECURSIVE_GEN) {
                                              System.out.println("[findLiteralReplacement]   📦 Original variable: " + originalVarName + 
                                                  " (type: " + localVar.getType().getQualifiedName() + ")");
                                          }
                                          
                                          if (isAlreadyDeclared(varName, stmts)) {
                                              String newVarName = generateUniqueNameFromStmts(varName, stmts, varNameCounter);
                                              localVar.setSimpleName(newVarName);
                                              
                                              if (DEBUG_RECURSIVE_GEN) {
                                                  System.out.println("[findLiteralReplacement]   🔄 Variable renamed: " + originalVarName + 
                                                      " -> " + newVarName + " (already declared)");
                                              }
                                              varName = newVarName;
                                          }
                                          
                                          stmts.add(lastStmt);
                                          
                                          if (DEBUG_RECURSIVE_GEN) {
                                              System.out.println("[findLiteralReplacement] ✅ Final variable: " + varName + 
                                                  " | Statement added to list | Creating VariableRead");
                                          }
                                          
                                          return createVariableRead(varName, literalType);
                                      }
                                  }
                              }
                          }
                      }
                 } else {
                     if (DEBUG_RECURSIVE_GEN) {
                         System.out.println("[findLiteralReplacement] No candidates found in CandidatePool");
                     }
                 }
             }
            
            // 3단계 Fallback: InputCombinations의 processInputPool을 활용
            if (DEBUG_RECURSIVE_GEN) {
                System.out.println("[findLiteralReplacement] Step 3: Fallback to InputCombinations.processInputPool...");
            }
            List<Input> inputPool = InputCombinations.getInputPoolForType(literalType);
            
            if (inputPool == null || inputPool.isEmpty()) {
                if (DEBUG_RECURSIVE_GEN) {
                    System.out.println("[findLiteralReplacement] ✗ No inputs found in any pool");
                }
                return null;
            }

            // 풀에서 랜덤하게 하나 선택
            int randomIdx = random.nextInt(inputPool.size());
            Input selectedInput = inputPool.get(randomIdx);
            
            if (DEBUG_RECURSIVE_GEN) {
                System.out.println("[findLiteralReplacement] Selected input at index " + randomIdx + "/" + inputPool.size());
            }
            
            if (selectedInput == null) {
                return null;
            }

            CtExpression result = convertInputToExpression(selectedInput);
            if (DEBUG_RECURSIVE_GEN && result != null) {
                System.out.println("[findLiteralReplacement] ✓ Converted to expression: " + result.toString());
            }
            return result;
        } catch (Exception e) {
            if (DEBUG_RECURSIVE_GEN) {
                System.out.println("[findLiteralReplacement] ✗ Error finding replacement: " + e.getMessage());
                e.printStackTrace();
            }
            debugLog("[findLiteralReplacement] Error finding replacement: " + e.getMessage());
        }

        return null;
    }

    /**
     * Input 객체를 CtExpression으로 변환
     * 직접 값이면 리터럴 반환, 변수면 변수 read 반환
     */
    private CtExpression convertInputToExpression(Input input) {
        if (input == null) {
            return null;
        }

        // 직접 값인 경우
        if (!input.isVar()) {
            CtElement directValue = input.getDirectValue();
            if (directValue instanceof CtExpression) {
                return (CtExpression) directValue;
            }
        } else {
            // 변수인 경우, 마지막 statement에서 변수 read를 반환
            List<CtElement> inputSequence = input.getInput();
            if (inputSequence != null && !inputSequence.isEmpty()) {
                CtElement lastElement = inputSequence.get(inputSequence.size() - 1);
                if (lastElement instanceof CtLocalVariable) {
                    CtLocalVariable<?> localVar = (CtLocalVariable<?>) lastElement;
                    return createVariableRead(localVar.getSimpleName(), localVar.getType());
                }
            }
        }
        
        return null;
    }

    /**
     * CandidatePool의 varTypeNamePool + vartypeToInputPool에서 변수 찾기
     * 변수를 찾으면 해당 변수의 선언 statement를 stmts에 추가하고 변수 read 반환
     * @param literalType 타입
     * @param stmts statement 리스트
     * @param varNameCounter 변수 이름 카운터
     * @return 변수 read 표현식
     */
    private CtExpression findVariableReplacement(CtTypeReference literalType,
                                                  List<CtStatement> stmts,
                                                  Map<String, Integer> varNameCounter) {
        try {
            HashMap<CtTypeReference, Set<Pair<CtTypeReference, CtElement>>> varTypeNamePool = 
                Generater.MUTMutation.CandidatePool.getVarTypeNamePool();
            HashMap<Pair<CtTypeReference, CtElement>, Set<List<CtElement>>> vartypeToInputPool = 
                Generater.MUTMutation.CandidatePool.getVartypeToInputPool();
            
            if (DEBUG_RECURSIVE_GEN) {
                System.out.println("  [findVariableReplacement] Searching varTypeNamePool (size: " + varTypeNamePool.size() + ")");
            }
            
            for (Map.Entry<CtTypeReference, Set<Pair<CtTypeReference, CtElement>>> entry : varTypeNamePool.entrySet()) {
                if (areTypesCompatible(entry.getKey(), literalType)) {
                    Set<Pair<CtTypeReference, CtElement>> pairs = entry.getValue();
                    if (DEBUG_RECURSIVE_GEN) {
                        System.out.println("  [findVariableReplacement] Found compatible type with " + 
                            (pairs != null ? pairs.size() : 0) + " variable pairs");
                    }
                    
                    if (pairs != null && !pairs.isEmpty()) {
                        // 랜덤하게 하나 선택
                        int randomIdx = random.nextInt(pairs.size());
                        Pair<CtTypeReference, CtElement> selectedPair = pairs.stream()
                            .skip(randomIdx)
                            .findFirst()
                            .orElse(null);
                        
                        if (selectedPair != null) {
                            if (DEBUG_RECURSIVE_GEN) {
                                System.out.println("  [findVariableReplacement] Selected pair at index " + randomIdx);
                            }
                            
                            // vartypeToInputPool에서 해당 변수의 생성 sequence 가져오기
                            Set<List<CtElement>> inputSequences = vartypeToInputPool.get(selectedPair);
                            if (inputSequences != null && !inputSequences.isEmpty()) {
                                // 첫 번째 sequence 사용
                                List<CtElement> sequence = inputSequences.iterator().next();
                                if (sequence != null && !sequence.isEmpty()) {
                                    if (DEBUG_RECURSIVE_GEN) {
                                        System.out.println("  [findVariableReplacement] Sequence found with " + sequence.size() + " statements");
                                    }
                                    
                                    // 마지막 statement가 변수 선언
                                    CtElement lastElement = sequence.get(sequence.size() - 1);
                                    if (lastElement instanceof CtStatement) {
                                        CtStatement lastStmt = ((CtStatement) lastElement).clone();
                                        
                                        // 변수 이름 추출
                                        String varName = null;
                                        if (lastStmt instanceof CtLocalVariable) {
                                            CtLocalVariable<?> localVar = (CtLocalVariable<?>) lastStmt;
                                            varName = localVar.getSimpleName();
                                            
                                            if (DEBUG_RECURSIVE_GEN) {
                                                System.out.println("  [findVariableReplacement] Original variable name: " + varName);
                                            }
                                            
                                            // 이름 충돌 방지
                                            if (isAlreadyDeclared(varName, stmts)) {
                                                String newName = generateUniqueNameFromStmts(varName, stmts, varNameCounter);
                                                if (DEBUG_RECURSIVE_GEN) {
                                                    System.out.println("  [findVariableReplacement] Name conflict, renamed to: " + newName);
                                                }
                                                varName = newName;
                                                localVar.setSimpleName(varName);
                                            }
                                            
                                            // statement 추가
                                            stmts.add(lastStmt);
                                            
                                            if (DEBUG_RECURSIVE_GEN) {
                                                System.out.println("  [findVariableReplacement] ✓ Added variable declaration: " + lastStmt.toString());
                                            }
                                            
                                            // 변수 read 반환
                                            return createVariableRead(varName, literalType);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            
            if (DEBUG_RECURSIVE_GEN) {
                System.out.println("  [findVariableReplacement] No compatible type found in varTypeNamePool");
            }
        } catch (Exception e) {
            if (DEBUG_RECURSIVE_GEN) {
                System.out.println("  [findVariableReplacement] Exception: " + e.getMessage());
                e.printStackTrace();
            }
            debugLog("[findVariableReplacement] Error finding variable: " + e.getMessage());
        }
        
        return null;
    }

    /**
     * CandidatePool의 directToValues에서 Primitive/String 리터럴 값 찾기
     * @param literalType 타입
     * @return 같은 타입의 리터럴 값
     */
    private CtExpression findDirectValueReplacement(CtTypeReference literalType) {
        try {
            // directToValues에서 리터럴 값만 찾기
            HashMap<CtTypeReference, Set<CtElement>> directToValues = 
                Generater.MUTMutation.CandidatePool.getDirectToValues();
            
            if (DEBUG_RECURSIVE_GEN) {
                System.out.println("  [findDirectValueReplacement] Searching directToValues (size: " + directToValues.size() + ")");
            }
            
            for (Map.Entry<CtTypeReference, Set<CtElement>> entry : directToValues.entrySet()) {
                if (areTypesCompatible(entry.getKey(), literalType)) {
                    Set<CtElement> values = entry.getValue();
                    if (DEBUG_RECURSIVE_GEN) {
                        System.out.println("  [findDirectValueReplacement] Found compatible type with " + 
                            (values != null ? values.size() : 0) + " values");
                    }
                    
                    if (values != null && !values.isEmpty()) {
                        // 랜덤하게 하나 선택
                        int randomIdx = random.nextInt(values.size());
                        CtElement selectedValue = values.stream()
                            .skip(randomIdx)
                            .findFirst()
                            .orElse(null);
                        
                        if (selectedValue instanceof CtExpression) {
                            if (DEBUG_RECURSIVE_GEN) {
                                System.out.println("  [findDirectValueReplacement] Selected literal at index " + randomIdx + 
                                    ": " + selectedValue.toString());
                            }
                            return (CtExpression) selectedValue;
                        }
                    }
                }
            }
            
            if (DEBUG_RECURSIVE_GEN) {
                System.out.println("  [findDirectValueReplacement] No compatible type found in directToValues");
            }
        } catch (Exception e) {
            if (DEBUG_RECURSIVE_GEN) {
                System.out.println("  [findDirectValueReplacement] Exception: " + e.getMessage());
            }
            debugLog("[findDirectValueReplacement] Error finding direct value: " + e.getMessage());
        }
        
        return null;
    }

    /**
     * Primitive Type 또는 String 타입인지 확인
     */
    private boolean isPrimitiveOrStringType(String typeName) {
        return typeName.equals("int") || typeName.equals("long") || 
               typeName.equals("double") || typeName.equals("float") ||
               typeName.equals("boolean") || typeName.equals("char") ||
               typeName.equals("byte") || typeName.equals("short") ||
               typeName.equals("java.lang.String") ||
               typeName.equals("java.lang.Integer") || typeName.equals("java.lang.Long") ||
               typeName.equals("java.lang.Double") || typeName.equals("java.lang.Float") ||
               typeName.equals("java.lang.Boolean") || typeName.equals("java.lang.Character") ||
               typeName.equals("java.lang.Byte") || typeName.equals("java.lang.Short");
    }

    /**
     * 두 타입이 호환 가능한지 확인 (InputCombinations에서 가져온 로직)
     */
    private boolean areTypesCompatible(CtTypeReference<?> type1, CtTypeReference<?> type2) {
        if (type1 == null || type2 == null) return false;
        String name1 = type1.getQualifiedName();
        String name2 = type2.getQualifiedName();
        return name1.equals(name2) || 
               (isPrimitiveOrStringType(name1) && isPrimitiveOrStringType(name2) && 
                name1.replace("java.lang.", "").equals(name2.replace("java.lang.", "")));
    }
}
