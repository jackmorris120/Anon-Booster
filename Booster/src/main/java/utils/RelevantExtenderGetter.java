package utils;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.*;
import spoon.Launcher;
import spoon.SpoonException;
import spoon.reflect.CtModel;
import spoon.reflect.declaration.CtClass;
import spoon.reflect.reference.CtTypeReference;
import spoon.reflect.visitor.filter.TypeFilter;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class RelevantExtenderGetter {
    // 최종으로 남길 슈퍼클래스 FQN 모음
    private static Set<String> finalExtender = new HashSet<>();

    public static void main() {
        for (String baseTest : Config.BASE_TESTS) {
            CtModel model;
            try {
                model = init(baseTest);
            } catch (Exception e) {
                return;
            }

            if (model == null) {
                System.err.println("[BT-ERROR] 모델 생성 실패: " + baseTest);
                continue;
            }

            Map<String, String> extendString = extractAllExtenders(model);
            filterValidExtenders(extendString);
        }

        System.out.println("----------------------------------------------");
        System.out.println("Final Out Come : ");

        StringBuilder sb = new StringBuilder();
        for (String temp : finalExtender) {
            System.out.println(" - " + temp);
            sb.append(temp).append("\n");
        }

        String projectDir = Config.PROJECT_DIR;
        String regex = "(.*?/\\d+[fb])";
        Pattern pattern = Pattern.compile(regex);
        Matcher matcher = pattern.matcher(projectDir);

        if (matcher.find()) {
            String targetDir = matcher.group(1);
            String outputPath = Paths.get(targetDir).resolve("extended.txt").toString();
            try {
                Files.write(Paths.get(outputPath), sb.toString().getBytes(StandardCharsets.UTF_8));
                System.out.println("[INFO] extended.txt 파일 생성 완료: " + outputPath);
            } catch (IOException e) {
                System.err.println("[BT-ERROR] 파일 쓰기 실패: " + outputPath);
                e.printStackTrace();
            }
        } else {
            System.err.println("[BT-ERROR] 정규식 패턴에 맞는 경로를 찾지 못해 파일을 생성할 수 없습니다: " + projectDir);
        }
    }

    /**
     * Spoon을 사용해 주어진 경로(path)의 소스/바이트코드에서 CtModel을 생성
     */
    private static CtModel init(String path) {
        try {
            Launcher launcher = new Launcher();
            launcher.getEnvironment().setAutoImports(true);
            launcher.getEnvironment().setNoClasspath(true);
            launcher.addInputResource(path);
            launcher.buildModel();
            return launcher.getModel();
        } catch (SpoonException e) {
            System.err.println("[BT-ERROR] Spoon init error for " + path + ": " + e.getMessage());
            return null;
        }
    }

    /**
     * 모델 내 모든 CtClass<?>에 대해 “자식 클래스 FQN → 슈퍼클래스 FQN” 매핑을 생성
     */
    public static Map<String, String> extractAllExtenders(CtModel model) {
        Map<String, String> result = new LinkedHashMap<>();

        // CtClass<?>만 골라서 리스트로 얻기
        List<CtClass<?>> classes = model.getElements(new TypeFilter<>(CtClass.class));

        for (CtClass<?> ctClass : classes) {
            // 자식 클래스의 FQN
            String childClassFQN = ctClass.getQualifiedName();

            // 슈퍼클래스 참조 얻기
            CtTypeReference<?> superRef = ctClass.getSuperclass();

            // 슈퍼클래스가 없거나(Object만 상속) null 처리
            if (superRef == null) {
                continue;
            }

            // 슈퍼클래스의 FQN
            String superClassFQN = superRef.getQualifiedName();
            result.put(childClassFQN, superClassFQN);
        }

        return result;
    }

    /**
     * “자식 클래스”와 “슈퍼클래스”가 동일한 패키지에 속하는 경우에만 finalExtender에 추가한다.
     * 또한 java.lang.*, java.util.*, org.junit.*, junit.framework.* 로 시작하는 경우와
     * 단독 클래스명(“.”이 없는 경우)은 모두 제외한다.
     */
    private static void filterValidExtenders(Map<String, String> extendString) {
        for (Map.Entry<String, String> entry : extendString.entrySet()) {
            String childFQN = entry.getKey(); // 예: "com.example.MyTest"
            String superFQN = entry.getValue(); // 예: "com.example.BaseTest"

            // 1) superFQN이 null이거나 빈 문자열이면 제외
            if (superFQN == null || superFQN.isEmpty()) {
                continue;
            }

            // 2) java.lang.* 제외
            if (superFQN.startsWith("java.lang.")) {
                continue;
            }
            if (superFQN.contains("$")) {
                continue;
            }
            // 3) java.util.* 제외
            if (superFQN.startsWith("java.util.")) {
                continue;
            }
            // 4) org.junit.* 제외
            if (superFQN.startsWith("org.junit.")) {
                continue;
            }
            // 5) junit.framework.* 제외
            if (superFQN.startsWith("junit.framework.")) {
                continue;
            }

            // 6) 단독 클래스명(“.”이 없는 경우) 제외
            if (!superFQN.contains(".")) {
                continue;
            }

            // 7) “자식”과 “슈퍼”의 패키지 이름만 추출
            int childLastDot = childFQN.lastIndexOf('.');
            int superLastDot = superFQN.lastIndexOf('.');
            // 둘 중 하나라도 “.”이 없으면(패키지 정보가 없으면) 제외
            if (childLastDot == -1 || superLastDot == -1) {
                continue;
            }
            String childPkg = childFQN.substring(0, childLastDot);
            String superPkg = superFQN.substring(0, superLastDot);

            // // 8) 패키지가 다르면 제외
            // if (!childPkg.equals(superPkg)) {
            //     continue;
            // }

            // 9) 위 조건들을 모두 통과했을 때만 최종 결과에 추가
            // System.out.println(" - " + superFQN);
            finalExtender.add(superFQN);
        }
    }
}