package PreProcessor.TestFilter;

import spoon.Launcher;
import spoon.reflect.*;
import spoon.reflect.declaration.*;
import spoon.compiler.Environment;
import java.util.*;

public class SpoonBuilder {

    private static Launcher launcher;
    private static Environment environment;

    public static void initModel() {
        launcher = new Launcher();
        environment = launcher.getEnvironment();
        
        environment.setAutoImports(false);
        environment.setNoClasspath(true);
        environment.setCommentEnabled(false);
        environment.setComplianceLevel(8);
        environment.setLevel("ERROR");
        environment.setShouldCompile(false);
        
        Set<String> filesToParse = new HashSet<>();
        
        if (!Config.baseTestFilePaths.isEmpty()) {
            filesToParse.addAll(Config.baseTestFilePaths);
            
            Set<String> parentClassFiles = findParentClassFiles(Config.baseTestFilePaths, Config.rootTestDir);
            filesToParse.addAll(parentClassFiles);
            System.out.println("Found " + parentClassFiles.size() + " parent/helper test classes");
            if (!parentClassFiles.isEmpty()) {
                System.out.println("Parent classes:");
                for (String parent : parentClassFiles) {
                    System.out.println("  - " + new java.io.File(parent).getName());
                }
            }
        }
        
        if (!Config.CUTFilePaths.isEmpty()) {
            filesToParse.addAll(Config.CUTFilePaths);
        }
        
        // Add all source files for complete call graph construction
        if (Config.rootSrcDir != null && !Config.rootSrcDir.isEmpty()) {
            launcher.addInputResource(Config.rootSrcDir);
            System.out.println("Added source directory for call graph: " + Config.rootSrcDir);
        }
        
        for (String filePath : filesToParse) {
            launcher.addInputResource(filePath);
        }
        
        if (Config.CLASS_PATH != null && !Config.CLASS_PATH.isEmpty()) {
            String[] classpath = Arrays.stream(Config.CLASS_PATH.split(java.io.File.pathSeparator))
                    .filter(p -> p != null && !p.trim().isEmpty())
                    .distinct()
                    .toArray(String[]::new);
            environment.setSourceClasspath(classpath);
        }
        
        try {
            launcher.buildModel();
        } catch (Exception e) {
            System.err.println("Error building Spoon model: " + e.getMessage());
            e.printStackTrace();
        }
    }
    
    private static Set<String> findParentClassFiles(ArrayList<String> testFiles, String rootTestDir) {
        Set<String> parentFiles = new HashSet<>();
        Set<String> visited = new HashSet<>(testFiles);
        Queue<String> toProcess = new LinkedList<>(testFiles);
        
        while (!toProcess.isEmpty()) {
            String currentFile = toProcess.poll();
            
            try {
                List<String> lines = java.nio.file.Files.readAllLines(java.nio.file.Paths.get(currentFile));
                
                for (String line : lines) {
                    line = line.trim();
                    
                    if (line.startsWith("public class") || line.startsWith("class") || 
                        line.startsWith("public abstract class") || line.startsWith("abstract class")) {
                        if (line.contains(" extends ")) {
                            String extendsClause = line.substring(line.indexOf(" extends ") + 9);
                            String parentClass = extendsClause.split("[\\s<{]")[0].trim();
                            
                            if (!parentClass.isEmpty() && !parentClass.equals("Object") && 
                                !parentClass.startsWith("java.") && !parentClass.startsWith("junit.") &&
                                !parentClass.startsWith("org.junit.")) {
                                
                                String parentFile = findClassFile(parentClass, currentFile, rootTestDir);
                                if (parentFile != null && !visited.contains(parentFile)) {
                                    parentFiles.add(parentFile);
                                    visited.add(parentFile);
                                    toProcess.add(parentFile);
                                }
                            }
                        }
                        break;
                    }
                }
            } catch (Exception e) {
                System.err.println("Warning: Could not read file " + currentFile + ": " + e.getMessage());
            }
        }
        
        return parentFiles;
    }
    
    private static String findClassFile(String className, String contextFile, String rootTestDir) {
        try {
            java.io.File contextFileObj = new java.io.File(contextFile);
            String packagePath = contextFileObj.getParent();
            
            String simpleClassName = className.contains(".") ? 
                className.substring(className.lastIndexOf('.') + 1) : className;
            
            String candidatePath = packagePath + "/" + simpleClassName + ".java";
            if (new java.io.File(candidatePath).exists()) {
                return candidatePath;
            }
            
            if (rootTestDir != null) {
                java.nio.file.Path rootPath = java.nio.file.Paths.get(rootTestDir);
                try (java.util.stream.Stream<java.nio.file.Path> paths = 
                     java.nio.file.Files.walk(rootPath)) {
                    return paths
                        .filter(p -> p.toString().endsWith("/" + simpleClassName + ".java"))
                        .map(p -> p.toString())
                        .findFirst()
                        .orElse(null);
                }
            }
        } catch (Exception e) {
            System.err.println("Warning: Error finding parent class " + className + ": " + e.getMessage());
        }
        
        return null;
    }
    
    public static CtModel getModel() {
        if (launcher == null) {
            throw new IllegalStateException("Model not initialized. Call initModel() first.");
        }
        return launcher.getModel();
    }

}
