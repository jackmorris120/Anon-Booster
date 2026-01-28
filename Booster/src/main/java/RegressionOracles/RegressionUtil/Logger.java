package RegressionOracles.RegressionUtil;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Created by Benjamin DANGLOT
 * benjamin.danglot@inria.fr
 * on 21/06/17
 */
public class Logger {

    public static Map<String, List<Assertion>> observations = new HashMap<String, List<Assertion>>(); //<Test name, Assertion>

    public static void observe(String testName, String key, Object object) {
         Assertion assertion = new Assertion(key, object);
        
         if (!observations.containsKey(testName))
             observations.put(testName, new ArrayList<>());
         observations.get(testName).add(assertion);
     }
    
    /**
     * Clear all observations to prevent memory leak during long-running test generation.
     * Should be called periodically (e.g., after each test is processed) to prevent
     * the observations map from growing unbounded.
     */
    public static void clearObservations() {
        observations.clear();
    }
    
    /**
     * Get current number of observations for monitoring memory usage
     */
    public static int getObservationsSize() {
        return observations.size();
    }
}
