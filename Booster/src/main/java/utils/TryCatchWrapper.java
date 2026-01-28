package utils;

import spoon.Launcher;
import spoon.reflect.code.CtCatch;
import spoon.reflect.code.CtCatchVariable;
import spoon.reflect.code.CtTry;
import spoon.reflect.declaration.CtClass;
import spoon.reflect.declaration.CtMethod;
import spoon.reflect.declaration.CtType;
import spoon.reflect.factory.Factory;
import spoon.reflect.reference.CtTypeReference;
import spoon.reflect.visitor.filter.TypeFilter;
import spoon.support.compiler.VirtualFile;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public class TryCatchWrapper {

    public static String buildClass(String className, String mutatedClass) {
        Launcher launcher = new Launcher();
        launcher.addInputResource(new VirtualFile(mutatedClass));
        launcher.getEnvironment().setNoClasspath(true);
        launcher.getEnvironment().setAutoImports(false);
        Collection<CtType<?>> allTypes = launcher.buildModel().getAllTypes();
//        System.out.println("All types : " + allTypes);
//        System.out.println("All types size: " + allTypes.size());
        CtClass testSuite = (CtClass) allTypes.stream().findFirst().get(); //instead of using Launcher.parseClass to avoid crash due to ESTest_scaffolding.java
        testSuite.setSimpleName(className);
        List<CtMethod> methods = testSuite.getElements(new TypeFilter<>(CtMethod.class));
        for (CtMethod method : methods) {
            processMethod(method);
        }
        return testSuite.toString();
    }

    public static String buildClassForFullyQulified(String className, String mutatedClass) {
        Launcher launcher = new Launcher();
        launcher.addInputResource(new VirtualFile(mutatedClass));
        launcher.getEnvironment().setNoClasspath(true);
        launcher.getEnvironment().setAutoImports(true);
        Collection<CtType<?>> allTypes = launcher.buildModel().getAllTypes();
//        System.out.println("All types : " + allTypes);
//        System.out.println("All types size: " + allTypes.size());
        CtClass testSuite = (CtClass) allTypes.stream().findFirst().get(); //instead of using Launcher.parseClass to avoid crash due to ESTest_scaffolding.java
        testSuite.setSimpleName(className);
        List<CtMethod> methods = testSuite.getElements(new TypeFilter<>(CtMethod.class));
        for (CtMethod method : methods) {
            processMethod(method);
        }
        return testSuite.toString();
    }

    private static void processMethod(CtMethod method) {
        Factory factory = new Launcher().getFactory();
        CtTry tryBlock = factory.Core().createTry();
        CtCatch catcher = factory.Core().createCatch();
        CtCatchVariable<? extends Throwable> catchVaribale = factory.Core().createCatchVariable();
        catcher.setParameter(catchVaribale);
        tryBlock.setBody(method.getBody());
        List<CtCatch> catches = new ArrayList<>();
        catches.add(catcher);
        CtCatchVariable<? extends Throwable> throwable = factory.Core().createCatchVariable();
        CtTypeReference<? extends Throwable> type = factory.Core().createTypeReference();
        throwable.setSimpleName("Throwable verySpecialNameNeverDuplicate");
        catcher.setParameter(throwable);
        catcher.setBody(factory.Core().createCodeSnippetStatement());
        tryBlock.setCatchers(catches);
        method.setBody(tryBlock);
    }
}