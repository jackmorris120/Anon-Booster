package utils;

import java.util.List;
import java.util.*;
import spoon.reflect.declaration.*;

public class Config {
    /* package name */
    public static String PACKAGE = "";
    /* this can be class path dependency needed */
    public static String CLASS_PATH = "";
    /* .java output path */
    public static String OUTPUT_PATH = "";
    /* .class output path */
    public static String BUILD_PATH = "";

    public static String MEGAFILE_PATH = "";

    public static String PROJECT_NAME = "";

    public static List<String> BASE_TESTS = null;

    public static List<String> EXTENDED_TESTS = null;

    public static List<String> REFERENCE_LISTS = new ArrayList<>();

    public static String PROJECT_DIR = "";

    public static int NUM_COMPILE_FAIL = 0;
    /**
     * path to testcase file
     */
    public static String TEST_FILE = "";
    /**
     * full class name org.class.xxx
     */

    public static String BUGTRIGGERRING_TESTS = null;


    public static String FULL_CLASS_NAME = "";

    public static List<String> CUT_FILES = null;

    public static long START_TIME = 0;

    public static List<CtMethod> MEGA_TEST_CASES = new ArrayList<>();

    public static HashSet<String> SOURCE_CODE_FILES = null;

    public static boolean recursiveMethodCalls = true;

    public static boolean SEED_AUGMENTATION = true;

    public static boolean COMBINATORIAL = true;

    public static String ASSEMBLE_MODE = "";

    public static int MAX_DEPTH = 10;

    public static boolean Tway_TOPT = false;

    /**
     * In regression mode, we generate regression oracles
     */
    public static boolean REGRESSION_MODE = false;

    public static String STRING_IDENTIFIER = "String___";

    public static long COLLECTING_TIME_BUDGET = 0;
    
    /**
     * Enable/disable combination explosion analysis reporting
     */
    public static boolean ENABLE_COMBINATION_ANALYSIS = false;

    public static boolean DEBUG_COMPILE_FAIL_TESTS = false;
    
    /**
     * Maximum number of unique sequences allowed per type to prevent combination explosion
     */
    public static int MAX_SEQUENCES_PER_TYPE = 2000;
    
    /**
     * Enable/disable automatic addition of extreme values for primitive types
     */
    public static boolean ENABLE_PRIMITIVE_EXTREME_VALUES = true;
    
    
    /**
     * Two-level filtering system for test inlining scope:
     * 
     * LIMIT_TO_BUG_TRIGGERING_TESTS (file-level filtering):
     * - When true: Only inline tests from the exact files that contain bug triggering tests
     * - When false: No file-level filtering applied
     * 
     * LIMIT_TO_BUG_TRIGGERING_PACKAGES (package-level filtering):
     * - When true: Only inline tests from packages that contain bug triggering tests
     * - When false: No package-level filtering applied
     * 
     * Behavior combinations:
     * - Both false: Inline all tests from all provided test files
     * - Only PACKAGES=true: Inline all tests from bug triggering packages
     * - Only TESTS=true: Inline all tests from bug triggering files (+ all packages due to no package filter)
     * - Both true: Inline tests from bug triggering files within bug triggering packages (most restrictive)
     */
    public static boolean LIMIT_TO_BUG_TRIGGERING_TESTS = false;
    public static boolean LIMIT_TO_BUG_TRIGGERING_PACKAGES = false;

    /*
     * Configs for TryCatch Oracle 
     * When ENABLE_MULTIPLE_ORACLE_GEN is True
     * repeat run - Oracle Gen - Compile - run - Oracle Gen Until that Test Does not fail 
     * 
     * When ENABLE_WHOLE_WRAP_ORACLE_GEN is Ture
     * Wrap whole Test body since the crashing point in to the try block
     * 
     * When both are off generate Try Catch oracle for the initial Crashing point and pass
     */

    public static boolean ENABLE_MULTIPLE_ORACLE_GEN = false;

    public static boolean ENABLE_WHOLE_WRAP_ORACLE_GEN = true;
    
    /**
     * ENABLE_MULTIPLE_ORACLE_GEN이 true일 때 최대 시도 횟수
     * null이면 기본값 5
     */
    public static Integer MULTIPLE_ORACLE_MAX_ITERATIONS = 5;

    public static boolean ENABLE_HYBRID_GEN = false;

    public static boolean BUILD_UP_GEN = true;

    /**
     * OPTIONS FOR MINIMIZATION
     */

    public static boolean ENABLE_TEST_MINIMIZATION = true;
    public static boolean DEBUG_TEST_MINIMIZATION = false;
    // Option for removing Passing Test 
    public static boolean REMOVE_PASSING_TESTS = true;
    // Option for using same signature as the bucket
    public static boolean ENABLE_ERROR_MSG_EXTRACTION_IN_SIGNATURE = false;

    /**
     * OPTIONS FOR MUT EXTRACTION IN SIGNATURES
     * When enabled, MUT information (extracted from _P_, _C_, _M_ patterns) is included in
     * the signature used for test minimization and bucketing.
     * When disabled, signatures are based purely on exception type and StackTrace.
     */
    public static boolean ENABLE_MUT_EXTRACTION_IN_SIGNATURE = false; // Default: disabled for pure signatures

    /**
     * OPTIONS FOR BUCKETING
     * When enabled, tests with the same StackTrace signature are grouped together
     * instead of being filtered out. Each exception bucket is organized with a
     * comment header.
     * Note: TestMinimizer is always run when ENABLE_TEST_BUCKETING = true
     */
    public static boolean ENABLE_TEST_BUCKETING = true; // Enable bucketing to organize tests by exception
    public static boolean DEBUG_TEST_BUCKETING = false;
    
    

}
// 