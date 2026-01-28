package PreProcessor.TestFilter;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class TestMethodRemover {
    
    public static boolean removeMethodFromFile(String filePath, String methodSignature) {
        String className = extractClassName(methodSignature);
        String methodName = extractMethodName(methodSignature);
        List<String> paramTypes = extractParameterTypes(methodSignature);
        
        System.out.println("  Attempting to remove: " + methodName + " from " + filePath);
        
        try {
            String content = new String(Files.readAllBytes(Paths.get(filePath)), StandardCharsets.UTF_8);
            String modified = removeMethod(content, methodName, paramTypes);
            
            if (modified == null) {
                System.err.println("  → Failed to find method: " + methodName);
                return false;
            }
            
            Files.write(Paths.get(filePath), modified.getBytes(StandardCharsets.UTF_8));
            System.out.println("  → Successfully removed method: " + methodName);
            return true;
            
        } catch (IOException e) {
            System.err.println("  → File I/O error: " + e.getMessage());
            return false;
        }
    }
    
    public static class RemovalResult {
        public final String filePath;
        public final int successCount;
        public final int failCount;
        public final List<String> failedMethods;
        
        public RemovalResult(String filePath, int successCount, int failCount, List<String> failedMethods) {
            this.filePath = filePath;
            this.successCount = successCount;
            this.failCount = failCount;
            this.failedMethods = failedMethods;
        }
    }
    
    public static RemovalResult removeMultipleMethodsFromFile(String filePath, List<String> methodSignatures) {
        int successCount = 0;
        int failCount = 0;
        List<String> failedMethods = new ArrayList<>();
        
        System.out.println("[Processing] " + filePath + " (" + methodSignatures.size() + " methods)");
        
        try {
            String content = new String(Files.readAllBytes(Paths.get(filePath)), StandardCharsets.UTF_8);
            
            for (String methodSignature : methodSignatures) {
                String methodName = extractMethodName(methodSignature);
                List<String> paramTypes = extractParameterTypes(methodSignature);
                
                String modified = removeMethod(content, methodName, paramTypes);
                
                if (modified != null) {
                    content = modified;
                    successCount++;
                } else {
                    failCount++;
                    failedMethods.add(methodName);
                }
            }
            
            if (successCount > 0) {
                Files.write(Paths.get(filePath), content.getBytes(StandardCharsets.UTF_8));
                System.out.println("[Success] " + filePath + ": " + successCount + "/" + methodSignatures.size() + " methods removed");
            }
            
        } catch (IOException e) {
            System.err.println("[Error] File I/O error for " + filePath + ": " + e.getMessage());
            failCount = methodSignatures.size();
            for (String sig : methodSignatures) {
                failedMethods.add(extractMethodName(sig));
            }
        }
        
        return new RemovalResult(filePath, successCount, failCount, failedMethods);
    }
    
    public static Map<String, RemovalResult> removeMethodsInParallel(Map<String, List<String>> fileMethodMap, int numThreads) {
        System.out.println("[Parallel] Starting with " + numThreads + " threads for " + fileMethodMap.size() + " files");
        
        ExecutorService executor = Executors.newFixedThreadPool(numThreads);
        Map<String, RemovalResult> results = new ConcurrentHashMap<>();
        List<Future<?>> futures = new ArrayList<>();
        
        int totalMethods = 0;
        for (List<String> methods : fileMethodMap.values()) {
            totalMethods += methods.size();
        }
        System.out.println("[Parallel] Total methods to remove: " + totalMethods);
        
        for (Map.Entry<String, List<String>> entry : fileMethodMap.entrySet()) {
            String filePath = entry.getKey();
            List<String> methods = entry.getValue();
            
            Future<?> future = executor.submit(() -> {
                RemovalResult result = removeMultipleMethodsFromFile(filePath, methods);
                results.put(filePath, result);
            });
            
            futures.add(future);
        }
        
        int completed = 0;
        for (Future<?> future : futures) {
            try {
                future.get();
                completed++;
                if (completed % 10 == 0 || completed == futures.size()) {
                    System.out.println("[Progress] " + completed + "/" + futures.size() + " files completed");
                }
            } catch (InterruptedException | ExecutionException e) {
                System.err.println("[Error] Thread execution error: " + e.getMessage());
            }
        }
        
        executor.shutdown();
        try {
            if (!executor.awaitTermination(60, TimeUnit.MINUTES)) {
                executor.shutdownNow();
            }
        } catch (InterruptedException e) {
            executor.shutdownNow();
        }
        
        return results;
    }
    
    private static String removeMethod(String content, String methodName, List<String> paramTypes) {
        int methodStart = findMethodStart(content, methodName, paramTypes);
        if (methodStart < 0) {
            return null;
        }
        
        int annotationStart = findAnnotationStart(content, methodStart);
        
        int bodyStart = findMethodBodyStart(content, methodStart);
        if (bodyStart < 0) {
            return null;
        }
        
        int bodyEnd = findMatchingBrace(content, bodyStart);
        if (bodyEnd < 0) {
            return null;
        }
        
        String before = content.substring(0, annotationStart);
        String after = content.substring(bodyEnd + 1);
        
        return before + after;
    }
    
    private static int findMethodStart(String content, String methodName, List<String> paramTypes) {
        String escapedMethodName = Pattern.quote(methodName);
        String regex = "\\b(public|protected|private|static|final|abstract|synchronized|native|strictfp|\\s)+\\s+"
                     + "(?:<[^>]+>\\s+)?"
                     + "(?:[\\w<>\\[\\]\\., ]+\\s+)?"
                     + escapedMethodName + "\\s*\\(";
        
        Pattern pattern = Pattern.compile(regex);
        Matcher matcher = pattern.matcher(content);
        
        List<Integer> candidates = new ArrayList<>();
        while (matcher.find()) {
            candidates.add(matcher.start());
        }
        
        if (candidates.isEmpty()) {
            return -1;
        }
        
        if (paramTypes.isEmpty()) {
            return candidates.get(0);
        }
        
        for (int start : candidates) {
            if (matchesParameters(content, start, methodName, paramTypes)) {
                return start;
            }
        }
        
        return candidates.get(0);
    }
    
    private static boolean matchesParameters(String content, int methodStart, String methodName, List<String> expectedParamTypes) {
        int parenStart = content.indexOf('(', methodStart);
        if (parenStart < 0) return false;
        
        int parenEnd = findMatchingParen(content, parenStart);
        if (parenEnd < 0) return false;
        
        String paramsStr = content.substring(parenStart + 1, parenEnd).trim();
        
        if (paramsStr.isEmpty()) {
            return expectedParamTypes.isEmpty();
        }
        
        String[] params = splitParameters(paramsStr);
        
        if (params.length != expectedParamTypes.size()) {
            return false;
        }
        
        for (int i = 0; i < params.length; i++) {
            String paramType = extractTypeFromParameter(params[i]);
            String expectedType = expectedParamTypes.get(i);
            
            String simpleExpected = getSimpleName(expectedType);
            String simpleActual = getSimpleName(paramType);
            
            if (!simpleActual.equals(simpleExpected) && !paramType.equals(expectedType)) {
                return false;
            }
        }
        
        return true;
    }
    
    private static String[] splitParameters(String paramsStr) {
        List<String> params = new ArrayList<>();
        int depth = 0;
        int start = 0;
        
        for (int i = 0; i < paramsStr.length(); i++) {
            char c = paramsStr.charAt(i);
            
            if (c == '<') depth++;
            else if (c == '>') depth--;
            else if (c == ',' && depth == 0) {
                params.add(paramsStr.substring(start, i).trim());
                start = i + 1;
            }
        }
        
        if (start < paramsStr.length()) {
            params.add(paramsStr.substring(start).trim());
        }
        
        return params.toArray(new String[0]);
    }
    
    private static String extractTypeFromParameter(String param) {
        param = param.trim();
        
        int lastSpace = param.lastIndexOf(' ');
        if (lastSpace > 0) {
            return param.substring(0, lastSpace).trim();
        }
        
        return param;
    }
    
    private static String getSimpleName(String fullType) {
        fullType = fullType.replaceAll("\\s+", "");
        
        if (fullType.contains("<")) {
            fullType = fullType.substring(0, fullType.indexOf('<'));
        }
        
        int lastDot = fullType.lastIndexOf('.');
        if (lastDot >= 0) {
            return fullType.substring(lastDot + 1);
        }
        
        return fullType;
    }
    
    private static int findAnnotationStart(String content, int methodStart) {
        int currentLineStart = content.lastIndexOf('\n', methodStart - 1) + 1;
        if (currentLineStart < 0) currentLineStart = 0;
        
        int deleteStart = methodStart;
        
        while (true) {
            int prevLineEnd = currentLineStart - 1;
            if (prevLineEnd <= 0) break;
            
            int prevLineStart = content.lastIndexOf('\n', prevLineEnd - 1) + 1;
            if (prevLineStart < 0) prevLineStart = 0;
            
            String line = content.substring(prevLineStart, prevLineEnd).trim();
            
            if (line.startsWith("@") || line.startsWith("//") || line.isEmpty()) {
                deleteStart = prevLineStart;
                currentLineStart = prevLineStart;
            } else {
                break;
            }
        }
        
        return deleteStart;
    }
    
    private static int findMethodBodyStart(String content, int methodStart) {
        int parenStart = content.indexOf('(', methodStart);
        if (parenStart < 0) return -1;
        
        int parenEnd = findMatchingParen(content, parenStart);
        if (parenEnd < 0) return -1;
        
        for (int i = parenEnd + 1; i < content.length(); i++) {
            char c = content.charAt(i);
            if (c == '{') {
                return i;
            } else if (c == ';') {
                return -1;
            }
        }
        
        return -1;
    }
    
    private static int findMatchingParen(String content, int openIndex) {
        int depth = 0;
        boolean inString = false;
        boolean inChar = false;
        boolean escape = false;
        
        for (int i = openIndex; i < content.length(); i++) {
            char c = content.charAt(i);
            
            if (escape) {
                escape = false;
                continue;
            }
            
            if (c == '\\') {
                escape = true;
                continue;
            }
            
            if (c == '"' && !inChar) {
                inString = !inString;
            } else if (c == '\'' && !inString) {
                inChar = !inChar;
            }
            
            if (!inString && !inChar) {
                if (c == '(') depth++;
                else if (c == ')') {
                    depth--;
                    if (depth == 0) return i;
                }
            }
        }
        
        return -1;
    }
    
    private static int findMatchingBrace(String content, int openIndex) {
        int depth = 0;
        boolean inString = false;
        boolean inChar = false;
        boolean inLineComment = false;
        boolean inBlockComment = false;
        boolean escape = false;
        
        for (int i = openIndex; i < content.length(); i++) {
            char c = content.charAt(i);
            char next = (i + 1 < content.length()) ? content.charAt(i + 1) : '\0';
            
            if (inLineComment) {
                if (c == '\n') inLineComment = false;
                continue;
            }
            
            if (inBlockComment) {
                if (c == '*' && next == '/') {
                    inBlockComment = false;
                    i++;
                }
                continue;
            }
            
            if (!inString && !inChar) {
                if (c == '/' && next == '/') {
                    inLineComment = true;
                    i++;
                    continue;
                }
                if (c == '/' && next == '*') {
                    inBlockComment = true;
                    i++;
                    continue;
                }
            }
            
            if (escape) {
                escape = false;
                continue;
            }
            
            if (c == '\\') {
                escape = true;
                continue;
            }
            
            if (c == '"' && !inChar) {
                inString = !inString;
            } else if (c == '\'' && !inString) {
                inChar = !inChar;
            }
            
            if (!inString && !inChar) {
                if (c == '{') depth++;
                else if (c == '}') {
                    depth--;
                    if (depth == 0) return i;
                }
            }
        }
        
        return -1;
    }
    
    private static String extractClassName(String signature) {
        int lastDot = signature.lastIndexOf('.');
        if (lastDot < 0) return "";
        return signature.substring(0, lastDot);
    }
    
    private static String extractMethodName(String signature) {
        int lastDot = signature.lastIndexOf('.');
        int parenStart = signature.indexOf('(');
        
        if (lastDot < 0 || parenStart < 0) return signature;
        
        return signature.substring(lastDot + 1, parenStart);
    }
    
    private static List<String> extractParameterTypes(String signature) {
        List<String> types = new ArrayList<>();
        
        int parenStart = signature.indexOf('(');
        int parenEnd = signature.lastIndexOf(')');
        
        if (parenStart < 0 || parenEnd < 0 || parenStart >= parenEnd) {
            return types;
        }
        
        String paramsStr = signature.substring(parenStart + 1, parenEnd).trim();
        
        if (paramsStr.isEmpty()) {
            return types;
        }
        
        String[] params = splitParameters(paramsStr);
        for (String param : params) {
            types.add(param.trim());
        }
        
        return types;
    }
    
    public static void main(String[] args) {
        if (args.length < 1) {
            System.err.println("Usage:");
            System.err.println("  Single mode:    TestMethodRemover <filePath> <methodSignature>");
            System.err.println("  Batch mode:     TestMethodRemover --batch <numThreads>");
            System.err.println("  (In batch mode, input format: filePath|method1,method2,method3)");
            System.exit(1);
        }
        
        if ("--batch".equals(args[0])) {
            int numThreads = args.length > 1 ? Integer.parseInt(args[1]) : Runtime.getRuntime().availableProcessors();
            runBatchMode(numThreads);
        } else {
            if (args.length < 2) {
                System.err.println("Single mode requires 2 arguments: <filePath> <methodSignature>");
                System.exit(1);
            }
            String filePath = args[0];
            String methodSignature = args[1];
            boolean success = removeMethodFromFile(filePath, methodSignature);
            System.exit(success ? 0 : 1);
        }
    }
    
    private static void runBatchMode(int numThreads) {
        System.out.println("[Batch] Running in batch mode with " + numThreads + " threads");
        System.out.println("[Batch] Reading from stdin (format: filePath|method1,method2,...)");
        
        Map<String, List<String>> fileMethodMap = new HashMap<>();
        
        try (java.util.Scanner scanner = new java.util.Scanner(System.in)) {
            while (scanner.hasNextLine()) {
                String line = scanner.nextLine().trim();
                if (line.isEmpty()) continue;
                
                int pipeIndex = line.indexOf('|');
                if (pipeIndex < 0) continue;
                
                String filePath = line.substring(0, pipeIndex);
                String methodsStr = line.substring(pipeIndex + 1);
                
                List<String> methods = new ArrayList<>();
                for (String method : methodsStr.split(",")) {
                    String trimmed = method.trim();
                    if (!trimmed.isEmpty()) {
                        methods.add(trimmed);
                    }
                }
                
                if (!methods.isEmpty()) {
                    fileMethodMap.put(filePath, methods);
                }
            }
        }
        
        if (fileMethodMap.isEmpty()) {
            System.err.println("[Error] No valid input provided");
            System.exit(1);
        }
        
        System.out.println("[Batch] Loaded " + fileMethodMap.size() + " files from input");
        
        long startTime = System.currentTimeMillis();
        Map<String, RemovalResult> results = removeMethodsInParallel(fileMethodMap, numThreads);
        long endTime = System.currentTimeMillis();
        
        int totalSuccess = 0;
        int totalFail = 0;
        
        System.out.println("\n<<BATCH_RESULTS>>");
        for (RemovalResult result : results.values()) {
            System.out.println(result.filePath + "|" + result.successCount + "|" + result.failCount);
            totalSuccess += result.successCount;
            totalFail += result.failCount;
            
            if (!result.failedMethods.isEmpty()) {
                System.err.println("[Warning] Failed methods in " + result.filePath + ": " + 
                    String.join(", ", result.failedMethods));
            }
        }
        System.out.println("<<END_BATCH_RESULTS>>");
        
        System.out.println("\n[Summary] Batch processing completed");
        System.out.println("[Summary] Files processed: " + results.size());
        System.out.println("[Summary] Methods removed: " + totalSuccess);
        System.out.println("[Summary] Failed removals: " + totalFail);
        System.out.println("[Summary] Time elapsed: " + (endTime - startTime) + "ms (" + 
            String.format("%.2f", (endTime - startTime) / 1000.0) + "s)");
        
        System.exit(totalFail == 0 ? 0 : 1);
    }
}
