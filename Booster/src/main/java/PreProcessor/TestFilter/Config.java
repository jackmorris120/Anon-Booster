package PreProcessor.TestFilter;

import java.util.*;

public class Config {

    public static ArrayList<String> baseTestFilePaths = new ArrayList<>();

    public static String CLASS_PATH = "";

    public static String rootTestDir = "";

    public static String rootSrcDir = "";

    public static ArrayList<String> CUTFilePaths = new ArrayList<>();

    public static ArrayList<String> bugTriggeringTests = new ArrayList<>();
    
    public static boolean useRelevantTestsOnly = true;

    public static boolean keepReachablePruneOthers = true;

    public static String datasetManifest = "";
    
    public static String datasetOutputDir = "";
    
    /**
     * Control how bug-triggering tests are handled:
     * - true: Keep bug-triggering tests (exclude from removal)
     * - false: Exclude bug-triggering tests (add to removal list)
     * Default is false (exclude bug-triggering tests)
     */
    public static boolean keepBugTriggeringTests = false;
    

}
