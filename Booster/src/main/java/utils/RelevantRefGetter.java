package utils;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.*;

import spoon.Launcher;
import spoon.SpoonException;
import spoon.reflect.CtModel;
import spoon.reflect.declaration.CtClass;
import spoon.reflect.declaration.CtCompilationUnit;
import spoon.reflect.declaration.CtImport;
import spoon.reflect.declaration.CtImportKind;
import spoon.reflect.reference.CtExecutableReference;
import spoon.reflect.reference.CtFieldReference;
import spoon.reflect.reference.CtPackageReference;
import spoon.reflect.reference.CtReference;
import spoon.reflect.reference.CtTypeReference;
import spoon.reflect.visitor.filter.TypeFilter;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class RelevantRefGetter {

    /** 최종으로 남길 FQN 목록 (extends + 타입참조 + import 기반 전부 포함) */
    private static final Set<String> finalExtender = new HashSet<>();

    public static void main() {
        CtModel model = initAll();
        if (model == null) {
            System.err.println("[BT-ERROR] 모델 생성 실패");
            return;
        }

        Set<String> testDefinedFQNs = classesInTestDir(model);
        Set<String> baseTestFQNs = toBaseTestFqns(model);
        Set<String> baseTestSimpleNames = buildBaseTestSimpleNames();

        Map<String, String> extendString = extractAllExtenders(model);
        filterValidExtenders(extendString, testDefinedFQNs, baseTestFQNs, baseTestSimpleNames);

        filterAndAddReferencedTestClasses(model, testDefinedFQNs, baseTestFQNs, baseTestSimpleNames);

        filterAndAddImportedTestClasses(model, testDefinedFQNs, baseTestFQNs, baseTestSimpleNames);

        System.out.println("----------------------------------------------");
        System.out.println("Final Out Come : ");
        finalExtender.removeIf(RelevantRefGetter::isTestLikeName);
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
            String outputPath = Paths.get(targetDir).resolve("referenced.txt").toString();
            try {
                Files.write(Paths.get(outputPath), sb.toString().getBytes(StandardCharsets.UTF_8));
                System.out.println("[INFO] referenced.txt 파일 생성 완료: " + outputPath);
            } catch (IOException e) {
                System.err.println("[BT-ERROR] 파일 쓰기 실패: " + outputPath);
            }
        } else {
            System.err.println("[BT-ERROR] 정규식 패턴에 맞는 경로를 찾지 못해 파일을 생성할 수 없습니다: " + projectDir);
        }
    }

    /** 프로젝트 전체 루트(필요 최소: TEST_ROOT_DIR)로 모델 빌드 */
    private static CtModel initAll() {
        try {
            Launcher launcher = new Launcher();
            launcher.getEnvironment().setAutoImports(true);
            launcher.getEnvironment().setNoClasspath(true);
            // launcher.addInputResource(Config.TEST_ROOT_DIR);
  
            launcher.buildModel();
            return launcher.getModel();
        } catch (SpoonException e) {
            System.err.println("[BT-ERROR] Spoon init error: " + e.getMessage());
            return null;
        }
    }

    /** 자식FQN → 슈퍼FQN 매핑 */
    public static Map<String, String> extractAllExtenders(CtModel model) {
        Map<String, String> result = new LinkedHashMap<>();
        List<CtClass<?>> classes = model.getElements(new TypeFilter<CtClass<?>>(CtClass.class));
        for (CtClass<?> ctClass : classes) {
            String childClassFQN = safeQN(ctClass);
            if (childClassFQN == null) continue;

            CtTypeReference<?> superRef = ctClass.getSuperclass();
            if (superRef == null) continue;

            String superClassFQN = superRef.getQualifiedName();
            if (superClassFQN == null || superClassFQN.isEmpty()) continue;

            result.put(childClassFQN, superClassFQN);
        }
        return result;
    }

    private static void filterValidExtenders(Map<String, String> extendString,
                                             Set<String> testDefinedFQNs,
                                             Set<String> baseTestFQNs,
                                             Set<String> baseTestSimpleNames) {
        for (Map.Entry<String, String> entry : extendString.entrySet()) {
            String superFQN = entry.getValue();
            if (isFiltered(superFQN)) continue;                 // JDK/JUnit/내부클래스/무패키지 제외
            if (!testDefinedFQNs.contains(superFQN)) continue;  // 테스트 루트 내 정의된 클래스만

            // ★ BASE_TESTS 제외 (FQN 또는 simple name 매칭)
            String sn = simpleTopLevelName(superFQN);
            if (baseTestFQNs.contains(superFQN) || baseTestSimpleNames.contains(sn)) continue;
            if (isTestLikeName(superFQN)) continue;
            finalExtender.add(superFQN);
        }
    }

    /** FQN 직접참조 기반: 모델 내 타입참조 FQN ∩ "테스트 디렉터리에서 정의된 클래스" 수집 */
    private static void filterAndAddReferencedTestClasses(CtModel model,
                                                          Set<String> testDefinedFQNs,
                                                          Set<String> baseTestFQNs,
                                                          Set<String> baseTestSimpleNames) {
        Set<String> referencedFQNs = collectReferencedTypes(model);
        if (referencedFQNs.isEmpty()) return;

        for (String fqn : referencedFQNs) {
            if (isFiltered(fqn)) continue;
            if (!testDefinedFQNs.contains(fqn)) continue;

            // ★ BASE_TESTS 제외 (FQN 또는 simple name 매칭)
            String sn = simpleTopLevelName(fqn);
            if (baseTestFQNs.contains(fqn) || baseTestSimpleNames.contains(sn)) continue;
            if (isTestLikeName(fqn)) continue;
            finalExtender.add(fqn);
        }
    }

    /** 모델 내 모든 CtTypeReference의 FQN 수집 (import 여부와 무관) */
    private static Set<String> collectReferencedTypes(CtModel model) {
        Set<String> out = new HashSet<>();
        List<CtTypeReference<?>> refs = model.getElements(new TypeFilter<CtTypeReference<?>>(CtTypeReference.class));
        for (CtTypeReference<?> ref : refs) {
            if (ref == null) continue;
            String qn = ref.getQualifiedName();
            if (qn == null || qn.isEmpty()) continue;
            out.add(qn);
        }
        return out;
    }

    /** 테스트 디렉터리에서 정의된 클래스들의 FQN 집합 (파일 경로 기준) */
    private static Set<String> classesInTestDir(CtModel model) {
        Set<String> testRoots = new HashSet<>();
        // addIfNotBlank(testRoots, Config.TEST_ROOT_DIR);

        Set<String> normRoots = new HashSet<>();
        for (String r : testRoots) normRoots.add(norm(r));

        Set<String> out = new HashSet<>();
        List<CtClass<?>> classes = model.getElements(new TypeFilter<CtClass<?>>(CtClass.class));
        for (CtClass<?> c : classes) {
            if (c.getPosition() == null || !c.getPosition().isValidPosition()) continue;
            File f = c.getPosition().getFile();
            if (f == null) continue;

            String filePath = norm(f.getAbsolutePath());
            for (String root : normRoots) {
                if (filePath.startsWith(root)) {
                    String qn = safeQN(c);
                    if (qn != null) out.add(qn);
                    break;
                }
            }
        }
        return out;
    }

    /** import 및 와일드카드 import에서 테스트 정의 클래스들을 수집 */
    private static void filterAndAddImportedTestClasses(CtModel model,
                                                        Set<String> testDefinedFQNs,
                                                        Set<String> baseTestFQNs,
                                                        Set<String> baseTestSimpleNames) {
        Set<String> importedFQNs = collectImportedTypes(model);
        Set<String> wildcardPkgs = collectWildcardImportPackages(model);
        if (importedFQNs.isEmpty() && wildcardPkgs.isEmpty()) return;

        // 1) 정확 타입 import
        for (String fqn : importedFQNs) {
            if (isFiltered(fqn)) continue;
            if (!testDefinedFQNs.contains(fqn)) continue;

            String sn = simpleTopLevelName(fqn);
            if (baseTestFQNs.contains(fqn) || baseTestSimpleNames.contains(sn)) continue;
            if (isTestLikeName(fqn)) continue;
            finalExtender.add(fqn);
        }

        // 2) 와일드카드 import
        if (!wildcardPkgs.isEmpty()) {
            for (String td : testDefinedFQNs) {
                if (isFiltered(td)) continue;

                String sn = simpleTopLevelName(td);
                if (baseTestFQNs.contains(td) || baseTestSimpleNames.contains(sn)) continue;
                if (isTestLikeName(td)) continue;
                for (String pkg : wildcardPkgs) {
                    if (td.startsWith(pkg + ".")) {
                        finalExtender.add(td);
                        break;
                    }
                }
            }
        }
    }

    /** 모델 내 모든 import 구문에서 "정확한 타입 FQN"을 수집 (static import 포함) */
    private static Set<String> collectImportedTypes(CtModel model) {
        Set<String> out = new HashSet<>();
        List<CtCompilationUnit> units = model.getElements(new TypeFilter<CtCompilationUnit>(CtCompilationUnit.class));
        for (CtCompilationUnit cu : units) {
            java.util.Collection<CtImport> imports = cu.getImports();
            if (imports == null || imports.isEmpty()) continue;

            for (CtImport imp : imports) {
                CtImportKind kind = imp.getImportKind();
                CtReference ref = imp.getReference();
                if (ref == null) continue;

                switch (kind) {
                    case TYPE: {
                        if (ref instanceof CtTypeReference) {
                            CtTypeReference<?> tr = (CtTypeReference<?>) ref;
                            String qn = tr.getQualifiedName();
                            if (qn != null && !qn.isEmpty()) out.add(qn);
                        }
                        break;
                    }
                    case METHOD: {
                        if (ref instanceof CtExecutableReference) {
                            CtExecutableReference<?> er = (CtExecutableReference<?>) ref;
                            CtTypeReference<?> decl = er.getDeclaringType();
                            if (decl != null) {
                                String qn = decl.getQualifiedName();
                                if (qn != null && !qn.isEmpty()) out.add(qn);
                            }
                        }
                        break;
                    }
                    case FIELD: {
                        if (ref instanceof CtFieldReference) {
                            CtFieldReference<?> fr = (CtFieldReference<?>) ref;
                            CtTypeReference<?> decl = fr.getDeclaringType();
                            if (decl != null) {
                                String qn = decl.getQualifiedName();
                                if (qn != null && !qn.isEmpty()) out.add(qn);
                            }
                        }
                        break;
                    }
                    // 와일드카드는 collectWildcardImportPackages()에서 처리
                    case ALL_TYPES:
                    case ALL_STATIC_MEMBERS:
                    default:
                        break;
                }
            }
        }
        return out;
    }

    /** import a.b.*; / import static a.b.C.*; 에서 패키지/타입 패키지 프리픽스를 수집 */
    private static Set<String> collectWildcardImportPackages(CtModel model) {
        Set<String> pkgs = new HashSet<>();
        List<CtCompilationUnit> units = model.getElements(new TypeFilter<CtCompilationUnit>(CtCompilationUnit.class));
        for (CtCompilationUnit cu : units) {
            java.util.Collection<CtImport> imports = cu.getImports();
            if (imports == null || imports.isEmpty()) continue;

            for (CtImport imp : imports) {
                CtImportKind kind = imp.getImportKind();
                CtReference ref = imp.getReference();
                if (ref == null) continue;

                if (kind == CtImportKind.ALL_TYPES) {
                    // import a.b.*;
                    if (ref instanceof CtPackageReference) {
                        CtPackageReference pr = (CtPackageReference) ref;
                        String pkg = pr.getQualifiedName();
                        if (pkg != null && !pkg.isEmpty()) pkgs.add(pkg);
                    }
                } else if (kind == CtImportKind.ALL_STATIC_MEMBERS) {
                    // import static a.b.C.*;
                    if (ref instanceof CtTypeReference) {
                        CtTypeReference<?> tr = (CtTypeReference<?>) ref; // a.b.C
                        String qn = tr.getQualifiedName();
                        if (qn != null && qn.contains(".")) {
                            String pkg = qn.substring(0, qn.lastIndexOf('.')); // a.b
                            if (!pkg.isEmpty()) pkgs.add(pkg);
                        }
                    }
                }
            }
        }
        return pkgs;
    }

    /** 파일경로 → top-level FQN 인덱스 */
    private static Map<String, String> buildFileToFqnIndex(CtModel model) {
        Map<String, String> idx = new HashMap<>();
        List<CtCompilationUnit> units = model.getElements(new TypeFilter<CtCompilationUnit>(CtCompilationUnit.class));
        for (CtCompilationUnit cu : units) {
            if (cu.getFile() == null) continue;
            String filePath = norm(cu.getFile().getAbsolutePath());

            cu.getDeclaredTypes().forEach(t -> {
                if (t.getDeclaringType() != null) return; // 내부/중첩 제외
                String qn;
                try {
                    qn = t.getQualifiedName();
                } catch (Exception e) {
                    qn = null;
                }
                if (qn == null || qn.isEmpty()) return;
                int dollar = qn.indexOf('$');
                if (dollar >= 0) qn = qn.substring(0, dollar);
                idx.put(filePath, qn);
            });
        }
        return idx;
    }

    /** Config.BASE_TESTS(파일 경로들)를 해당 top-level FQN 들로 변환 */
    private static Set<String> toBaseTestFqns(CtModel model) {
        Set<String> out = new HashSet<>();
        if (Config.BASE_TESTS == null || Config.BASE_TESTS.isEmpty()) return out;

        Map<String, String> file2qn = buildFileToFqnIndex(model);

        for (String p : Config.BASE_TESTS) {
            String abs = norm(new File(p).getAbsolutePath());
            String qn = file2qn.get(abs);

            if (qn == null) {
                // 경로가 조금 달라도 파일명으로 후방 매칭 시도
                String name = new File(p).getName(); // e.g., TestAbstractPartial.java
                for (Map.Entry<String, String> e : file2qn.entrySet()) {
                    if (e.getKey().endsWith("/" + name)) {
                        qn = e.getValue();
                        break;
                    }
                }
            }

            if (qn != null) {
                int dollar = qn.indexOf('$');
                if (dollar >= 0) qn = qn.substring(0, dollar);
                out.add(qn);
            }
        }
        return out;
    }

    /** FQN → simple top-level 이름으로 */
    private static String simpleTopLevelName(String fqn) {
        if (fqn == null) return null;
        int dollar = fqn.indexOf('$');
        if (dollar >= 0) fqn = fqn.substring(0, dollar);
        int dot = fqn.lastIndexOf('.');
        return (dot >= 0) ? fqn.substring(dot + 1) : fqn;
    }

    /** BASE_TESTS의 파일명(확장자 제거) → simple name 집합 */
    private static Set<String> buildBaseTestSimpleNames() {
        Set<String> out = new HashSet<>();
        if (Config.BASE_TESTS == null) return out;
        for (String p : Config.BASE_TESTS) {
            if (p == null) continue;
            String name = new File(p).getName(); // TestAbstractPartial.java
            if (name.endsWith(".java")) name = name.substring(0, name.length() - 5);
            int dollar = name.indexOf('$');
            if (dollar >= 0) name = name.substring(0, dollar);
            if (!name.isEmpty()) out.add(name);
        }
        return out;
    }

    // ========= 공용 유틸 =========

    private static String safeQN(CtClass<?> ct) {
        try {
            String qn = ct.getQualifiedName();
            return (qn == null || qn.isEmpty()) ? null : qn;
        } catch (Exception e) {
            return null;
        }
    }

    private static void addIfNotBlank(Set<String> set, String v) {
        if (v != null && !v.trim().isEmpty()) set.add(v);
    }

    private static String norm(String p) {
        return p.replace('\\', '/');
    }

    /** simple name 에 'test' 가 포함되면 제외 (대소문자 무관) */
    private static boolean isTestLikeName(String fqn) {
        String sn = simpleTopLevelName(fqn);
        return sn != null && sn.toLowerCase(Locale.ROOT).contains("test");
    }


    /** 공통 필터: JDK/테스트 프레임워크/내부클래스/패키지 없는 이름 등 제외 */
    private static boolean isFiltered(String fqn) {
        if (fqn == null || fqn.isEmpty()) return true;
        if (fqn.contains("$")) return true;       // 내부클래스 제외(필요시 완화 가능)
        if (!fqn.contains(".")) return true;      // 패키지 없는 단독명 제외
        if (fqn.startsWith("java.lang.")
                || fqn.startsWith("java.util.")
                || fqn.startsWith("org.junit.")
                || fqn.startsWith("junit.framework.")) {
            return true;
        }
        return false;
    }
}