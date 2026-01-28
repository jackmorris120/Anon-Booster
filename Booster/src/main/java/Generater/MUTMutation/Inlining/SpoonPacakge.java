package Generater.MUTMutation.Inlining;

import spoon.Launcher;
import spoon.compiler.Environment;
import spoon.reflect.CtModel;
import spoon.reflect.declaration.CtCompilationUnit;
import spoon.reflect.declaration.CtType;
import spoon.reflect.visitor.filter.TypeFilter;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.io.File; // <--- 오류 해결: File 클래스 임포트
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import Generater.MUTMutation.Inlining.MegaClassBuilder;

public class SpoonPacakge {

    private final Launcher launcher;
    private final Environment environment;
    private final CtModel ctModel; 
    private List<String> targetPkg = null; // 패키지 이름을 저장할 변수

    public Launcher getLauncher() {
        return launcher;
    }
    public Environment getEnvironment() {
        return environment;
    }
    public CtModel getCtModel() {
        return ctModel;
    }
    public List<String> getTargetPkg() {
        return targetPkg;
    }

    public SpoonPacakge(Launcher launcher, CtModel ctModel, Environment env, List<String> targetPkg) {
        this.launcher = launcher;
        this.ctModel = ctModel;
        this.environment = env; 
        this.targetPkg = targetPkg; // 생성자에서 패키지 이름을 초기화
    }

}
