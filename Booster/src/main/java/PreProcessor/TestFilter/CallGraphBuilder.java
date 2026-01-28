package PreProcessor.TestFilter;

import spoon.reflect.CtModel;
import spoon.reflect.declaration.*;
import spoon.reflect.code.*;
import spoon.reflect.reference.*;
import spoon.reflect.visitor.filter.TypeFilter;
import java.util.*;
import java.util.stream.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.*;

public class CallGraphBuilder {
    
    private Map<String, Set<String>> callGraph;
    private Map<String, CtMethod<?>> methodMap;
    private CtModel model;
    private Map<String, Set<String>> overrideCache;
    private boolean trackFields;
    private List<CtType<?>> allTypes;
    private int numThreads;
    
    public CallGraphBuilder(CtModel model) {
        this(model, false);
    }
    
    public CallGraphBuilder(CtModel model, boolean trackFields) {
        this.model = model;
        this.callGraph = new ConcurrentHashMap<>();
        this.methodMap = new ConcurrentHashMap<>();
        this.overrideCache = new ConcurrentHashMap<>();
        this.trackFields = trackFields;
        this.allTypes = new ArrayList<>();
        for (CtType<?> type : model.getAllTypes()) {
            this.allTypes.add(type);
        }
        this.numThreads = Math.min(Runtime.getRuntime().availableProcessors(), 8);
    }
    
    public void buildCallGraph() {
        System.out.println("Building call graph... (using " + numThreads + " threads)");
        buildStartTime = System.currentTimeMillis();
        long startTime = buildStartTime;
        
        AtomicInteger typeCount = new AtomicInteger(0);
        AtomicInteger methodCount = new AtomicInteger(0);
        AtomicInteger constructorCount = new AtomicInteger(0);
        
        System.out.print("  Processing types: ");
        
        ExecutorService executor = Executors.newFixedThreadPool(numThreads);
        List<Future<?>> futures = new ArrayList<>();
        
        for (CtType<?> type : allTypes) {
            futures.add(executor.submit(() -> {
                try {
                    int count = typeCount.incrementAndGet();
                    if (count % 20 == 0) {
                        System.out.print(count + "...");
                    }
                    
                    if (type == null) {
                        return;
                    }
                    
                    for (CtMethod<?> method : type.getMethods()) {
                        if (method != null) {
                            String sig = getMethodSignature(method);
                            if (sig != null) {
                                processExecutable(method, sig);
                                methodCount.incrementAndGet();
                            }
                        }
                    }
                    
                    if (type instanceof CtClass) {
                        CtClass<?> clazz = (CtClass<?>) type;
                        for (CtConstructor<?> constructor : clazz.getConstructors()) {
                            if (constructor != null) {
                                String sig = getConstructorSignature(constructor);
                                if (sig != null) {
                                    processExecutable(constructor, sig);
                                    constructorCount.incrementAndGet();
                                }
                            }
                        }
                    }
                } catch (Exception e) {
                    System.err.println("Error in thread processing type " + 
                        (type != null ? type.getQualifiedName() : "null") + ": " + e.getMessage());
                    e.printStackTrace();
                }
            }));
        }
        
        for (Future<?> future : futures) {
            try {
                future.get();
            } catch (Exception e) {
                System.err.println("Error processing type: " + e.getMessage());
                e.printStackTrace();
            }
        }
        
        executor.shutdown();
        
        System.out.println(typeCount.get());
        System.out.print("  Finding override methods: ");
        
        long duration = System.currentTimeMillis() - startTime;
        System.out.println("\nCall graph built:");
        System.out.println("  - " + typeCount.get() + " types processed");
        System.out.println("  - " + methodCount.get() + " methods");
        System.out.println("  - " + constructorCount.get() + " constructors");
        System.out.println("  - " + callGraph.size() + " total executables");
        System.out.println("  - " + overrideCheckCount.get() + " override checks performed");
        System.out.println("  - " + duration + "ms elapsed");
    }
    
    private void processExecutable(CtExecutable<?> executable, String signature) {
        if (executable == null || signature == null || signature.isEmpty()) {
            return;
        }
        
        CtMethod<?> methodValue = executable instanceof CtMethod ? (CtMethod<?>) executable : null;
        if (methodValue != null) {
            methodMap.put(signature, methodValue);
        }
        
        if (executable.getBody() == null) {
            callGraph.put(signature, ConcurrentHashMap.newKeySet());
            return;
        }
        
        Set<String> calledExecutables = ConcurrentHashMap.newKeySet();
        
        List<CtInvocation<?>> invocations = executable.getBody().getElements(new TypeFilter<>(CtInvocation.class));
        for (CtInvocation<?> invocation : invocations) {
            CtExecutableReference<?> execRef = invocation.getExecutable();
            String calledSignature = getExecutableSignature(execRef);
            if (calledSignature != null) {
                calledExecutables.add(calledSignature);
                
                Set<String> overriddenSignatures = findOverriddenMethods(execRef);
                calledExecutables.addAll(overriddenSignatures);
            }
        }
        
        List<CtConstructorCall<?>> constructorCalls = executable.getBody().getElements(new TypeFilter<>(CtConstructorCall.class));
        for (CtConstructorCall<?> ctorCall : constructorCalls) {
            CtExecutableReference<?> ctorRef = ctorCall.getExecutable();
            String ctorSignature = getExecutableSignature(ctorRef);
            if (ctorSignature != null) {
                calledExecutables.add(ctorSignature);
            }
        }
        
        List<CtLambda<?>> lambdas = executable.getBody().getElements(new TypeFilter<>(CtLambda.class));
        for (CtLambda<?> lambda : lambdas) {
            if (lambda.getBody() != null) {
                List<CtInvocation<?>> lambdaInvocations = lambda.getBody().getElements(new TypeFilter<>(CtInvocation.class));
                for (CtInvocation<?> invocation : lambdaInvocations) {
                    CtExecutableReference<?> execRef = invocation.getExecutable();
                    String calledSig = getExecutableSignature(execRef);
                    if (calledSig != null) {
                        calledExecutables.add(calledSig);
                    }
                }
            }
        }
        
        List<CtNewClass<?>> anonymousClasses = executable.getBody().getElements(new TypeFilter<>(CtNewClass.class));
        for (CtNewClass<?> newClass : anonymousClasses) {
            CtClass<?> anonymousClass = newClass.getAnonymousClass();
            if (anonymousClass != null) {
                for (CtMethod<?> method : anonymousClass.getMethods()) {
                    if (method.getBody() != null) {
                        List<CtInvocation<?>> anonInvocations = method.getBody().getElements(new TypeFilter<>(CtInvocation.class));
                        for (CtInvocation<?> invocation : anonInvocations) {
                            CtExecutableReference<?> execRef = invocation.getExecutable();
                            String calledSig = getExecutableSignature(execRef);
                            if (calledSig != null) {
                                calledExecutables.add(calledSig);
                            }
                        }
                    }
                }
            }
        }
        
        if (trackFields) {
            List<CtFieldRead<?>> fieldReads = executable.getBody().getElements(new TypeFilter<>(CtFieldRead.class));
            for (CtFieldRead<?> fieldRead : fieldReads) {
                CtFieldReference<?> fieldRef = fieldRead.getVariable();
                if (fieldRef != null && fieldRef.getDeclaringType() != null) {
                    String fieldSignature = fieldRef.getDeclaringType().getQualifiedName() + "." + fieldRef.getSimpleName();
                    calledExecutables.add(fieldSignature);
                }
            }
            
            List<CtFieldWrite<?>> fieldWrites = executable.getBody().getElements(new TypeFilter<>(CtFieldWrite.class));
            for (CtFieldWrite<?> fieldWrite : fieldWrites) {
                CtFieldReference<?> fieldRef = fieldWrite.getVariable();
                if (fieldRef != null && fieldRef.getDeclaringType() != null) {
                    String fieldSignature = fieldRef.getDeclaringType().getQualifiedName() + "." + fieldRef.getSimpleName();
                    calledExecutables.add(fieldSignature);
                }
            }
        }
        
        callGraph.put(signature, calledExecutables);
    }
    
    public boolean isReachable(CtMethod<?> startMethod, Set<String> targetClasses) {
        String startSignature = getMethodSignature(startMethod);
        Set<String> visited = new HashSet<>();
        Queue<String> queue = new LinkedList<>();
        
        if (!callGraph.containsKey(startSignature)) {
            // Debug: Print why method is not in call graph
            if (startSignature.contains("testParseLocalDate_weekyear")) {
                System.out.println("[DEBUG] Method not in call graph: " + startSignature);
            }
            return false;
        }
        
        queue.add(startSignature);
        visited.add(startSignature);
        
        int maxDepth = 100;
        int depth = 0;
        
        while (!queue.isEmpty() && depth < maxDepth) {
            int levelSize = queue.size();
            
            for (int i = 0; i < levelSize; i++) {
                String currentSignature = queue.poll();
                
                String currentClass = extractClassName(currentSignature);
                
                if (targetClasses.contains(currentClass)) {
                    return true;
                }
                
                if (currentSignature.contains(".") && !currentSignature.contains("(")) {
                    String fieldClass = currentSignature.substring(0, currentSignature.lastIndexOf('.'));
                    if (targetClasses.contains(fieldClass)) {
                        return true;
                    }
                }
                
                Set<String> callees = callGraph.get(currentSignature);
                if (callees == null) {
                    continue;
                }
                
                for (String callee : callees) {
                    if (!visited.contains(callee)) {
                        visited.add(callee);
                        queue.add(callee);
                    }
                }
            }
            
            depth++;
        }
        
        // Debug: if reached max depth
        if (depth >= maxDepth && startSignature.contains("testParseLocalDate_weekyear")) {
            System.out.println("[DEBUG] Reached max depth (" + maxDepth + ") for: " + startSignature);
            System.out.println("[DEBUG]   Target classes: " + targetClasses);
            System.out.println("[DEBUG]   Visited " + visited.size() + " methods");
        }
        
        return false;
    }
    
    public Set<String> getReachablePath(CtMethod<?> startMethod, Set<String> targetClasses) {
        String startSignature = getMethodSignature(startMethod);
        Set<String> visited = new HashSet<>();
        Queue<String> queue = new LinkedList<>();
        Map<String, String> parentMap = new HashMap<>();
        
        queue.add(startSignature);
        visited.add(startSignature);
        parentMap.put(startSignature, null);
        
        String foundTarget = null;
        
        while (!queue.isEmpty() && foundTarget == null) {
            String currentSignature = queue.poll();
            
            String currentClass = extractClassName(currentSignature);
            if (targetClasses.contains(currentClass)) {
                foundTarget = currentSignature;
                break;
            }
            
            Set<String> callees = callGraph.get(currentSignature);
            if (callees == null) {
                continue;
            }
            
            for (String callee : callees) {
                if (!visited.contains(callee)) {
                    visited.add(callee);
                    queue.add(callee);
                    parentMap.put(callee, currentSignature);
                }
            }
        }
        
        Set<String> path = new LinkedHashSet<>();
        if (foundTarget != null) {
            String current = foundTarget;
            while (current != null) {
                path.add(current);
                current = parentMap.get(current);
            }
        }
        
        return path;
    }
    
    private String getMethodSignature(CtMethod<?> method) {
        if (method == null) {
            return null;
        }
        
        try {
            CtType<?> declaringType = method.getDeclaringType();
            if (declaringType == null) {
                String simpleName = method.getSimpleName();
                return simpleName != null ? simpleName : null;
            }
            
            String className = declaringType.getQualifiedName();
            String methodName = method.getSimpleName();
            
            if (className == null || methodName == null) {
                return null;
            }
            
            StringBuilder sig = new StringBuilder(256);
            sig.append(className);
            sig.append(".");
            sig.append(methodName);
            sig.append("(");
            
            List<CtParameter<?>> params = method.getParameters();
            if (params != null) {
                for (int i = 0; i < params.size(); i++) {
                    if (i > 0) sig.append(",");
                    CtParameter<?> param = params.get(i);
                    if (param != null) {
                        CtTypeReference<?> typeRef = param.getType();
                        if (typeRef != null) {
                            String typeName = typeRef.getSimpleName();
                            if (typeName != null) {
                                sig.append(typeName);
                            }
                        }
                    }
                }
            }
            
            sig.append(")");
            return sig.toString();
        } catch (Exception e) {
            return null;
        }
    }
    
    private String getExecutableSignature(CtExecutableReference<?> execRef) {
        if (execRef.getDeclaringType() == null) {
            return null;
        }
        
        StringBuilder sig = new StringBuilder(256);
        sig.append(execRef.getDeclaringType().getQualifiedName());
        sig.append(".");
        sig.append(execRef.getSimpleName());
        sig.append("(");
        
        List<CtTypeReference<?>> params = execRef.getParameters();
        for (int i = 0; i < params.size(); i++) {
            if (i > 0) sig.append(",");
            sig.append(params.get(i).getSimpleName());
        }
        
        sig.append(")");
        return sig.toString();
    }
    
    private String getConstructorSignature(CtConstructor<?> constructor) {
        if (constructor == null) {
            return null;
        }
        
        try {
            CtType<?> declaringType = constructor.getDeclaringType();
            if (declaringType == null) {
                return null;
            }
            
            String className = declaringType.getQualifiedName();
            if (className == null) {
                return null;
            }
            
            StringBuilder sig = new StringBuilder(256);
            sig.append(className);
            sig.append(".<init>(");
            
            List<CtParameter<?>> params = constructor.getParameters();
            if (params != null) {
                for (int i = 0; i < params.size(); i++) {
                    if (i > 0) sig.append(",");
                    CtParameter<?> param = params.get(i);
                    if (param != null) {
                        CtTypeReference<?> typeRef = param.getType();
                        if (typeRef != null) {
                            String typeName = typeRef.getSimpleName();
                            if (typeName != null) {
                                sig.append(typeName);
                            }
                        }
                    }
                }
            }
            
            sig.append(")");
            return sig.toString();
        } catch (Exception e) {
            return null;
        }
    }
    
    private AtomicInteger overrideCheckCount = new AtomicInteger(0);
    private AtomicLong lastLogTime = new AtomicLong(System.currentTimeMillis());
    private long buildStartTime = 0;
    
    private Set<String> findOverriddenMethods(CtExecutableReference<?> execRef) {
        if (execRef.getDeclaringType() == null) {
            return Collections.emptySet();
        }
        
        String cacheKey = execRef.getDeclaringType().getQualifiedName() + "." + execRef.getSimpleName();
        Set<String> cached = overrideCache.get(cacheKey);
        if (cached != null) {
            return cached;
        }
        
        Set<String> overriddenMethods = ConcurrentHashMap.newKeySet();
        
        int count = overrideCheckCount.incrementAndGet();
        long currentTime = System.currentTimeMillis();
        long lastLog = lastLogTime.get();
        if (count % 200 == 0 && currentTime - lastLog > 1000 && lastLogTime.compareAndSet(lastLog, currentTime)) {
            long elapsed = (currentTime - buildStartTime) / 1000;
            System.out.print(".");
            if (count % 2000 == 0) {
                System.out.print(" [" + count + " checked, " + elapsed + "s]");
            }
        }
        
        CtTypeReference<?> declaringType = execRef.getDeclaringType();
        
        for (CtType<?> type : allTypes) {
            if (isSubtypeOf(type, declaringType)) {
                for (CtMethod<?> method : type.getMethods()) {
                    if (methodOverrides(method, execRef)) {
                        String overriddenSig = getMethodSignature(method);
                        overriddenMethods.add(overriddenSig);
                    }
                }
            }
        }
        
        overrideCache.put(cacheKey, overriddenMethods);
        return overriddenMethods;
    }
    
    private boolean isSubtypeOf(CtType<?> type, CtTypeReference<?> superType) {
        if (type.getQualifiedName().equals(superType.getQualifiedName())) {
            return false;
        }
        
        CtTypeReference<?> superClass = type.getSuperclass();
        if (superClass != null && superClass.getQualifiedName().equals(superType.getQualifiedName())) {
            return true;
        }
        
        for (CtTypeReference<?> iface : type.getSuperInterfaces()) {
            if (iface.getQualifiedName().equals(superType.getQualifiedName())) {
                return true;
            }
            
            CtType<?> ifaceDecl = iface.getTypeDeclaration();
            if (ifaceDecl != null && isSubtypeOf(type, iface)) {
                return true;
            }
        }
        
        if (superClass != null) {
            CtType<?> superClassDecl = superClass.getTypeDeclaration();
            if (superClassDecl != null && isSubtypeOf(superClassDecl, superType)) {
                return true;
            }
        }
        
        return false;
    }
    
    private boolean methodOverrides(CtMethod<?> method, CtExecutableReference<?> superMethodRef) {
        if (!method.getSimpleName().equals(superMethodRef.getSimpleName())) {
            return false;
        }
        
        List<CtParameter<?>> params = method.getParameters();
        List<CtTypeReference<?>> superParams = superMethodRef.getParameters();
        
        if (params.size() != superParams.size()) {
            return false;
        }
        
        for (int i = 0; i < params.size(); i++) {
            CtTypeReference<?> paramType = params.get(i).getType();
            CtTypeReference<?> superParamType = superParams.get(i);
            
            if (paramType == null || superParamType == null) {
                continue;
            }
            
            if (!paramType.getQualifiedName().equals(superParamType.getQualifiedName())) {
                return false;
            }
        }
        
        return true;
    }
    
    private String extractClassName(String signature) {
        int lastDot = signature.lastIndexOf('.');
        
        if (lastDot == -1) {
            return "";
        }
        
        int openParen = signature.indexOf('(');
        if (openParen != -1 && openParen < lastDot) {
            return "";
        }
        
        String beforeMethod = signature.substring(0, lastDot);
        
        if (beforeMethod.endsWith(".<init>")) {
            return beforeMethod.substring(0, beforeMethod.length() - 7);
        }
        
        return beforeMethod;
    }
    
    public Map<String, Set<String>> getCallGraph() {
        return callGraph;
    }
    
    public void printStatistics() {
        System.out.println("=== Call Graph Statistics ===");
        System.out.println("Total methods: " + callGraph.size());
        
        int totalEdges = 0;
        for (Set<String> callees : callGraph.values()) {
            totalEdges += callees.size();
        }
        System.out.println("Total call edges: " + totalEdges);
        
        if (!callGraph.isEmpty()) {
            double avgCalls = (double) totalEdges / callGraph.size();
            System.out.println("Average calls per method: " + String.format("%.2f", avgCalls));
        }
    }
}
