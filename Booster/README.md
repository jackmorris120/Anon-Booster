# Booster - Intelligent Test Case Generation Tool

Booster automatically generates new test sets by recomposing existing developer tests using two different strategies.

## Features

- **Sequence Chaining (seqc)**: Identifies required objects and arranges code sequences for object creation
- **Sequence Preserving (seqp)**: Masks primitive/literal values and assigns new values of matching types
- **JUnit 3 → JUnit 4 Conversion**: Automatically upgrades legacy test code
- **Regression & Non-regression Testing**: Generates regression oracles to verify changes don't break existing functionality
- **Incremental File Output**: Splits generated tests across multiple files

## Requirements

- **Java 8+**, **Gradle 7.0+**
- **JUnit 4.12+**, **Spoon 9.0+**, **EvoSuite 1.1.0+**
- **Apache Commons Lang 3.0+**, **Apache Commons IO 2.0+**
- **RAM**: 8GB minimum (32GB+ recommended)

## Build

```bash
cd ~/Booster
./gradlew build shadowJar
```

Generated JAR: `build/libs/Booster-shadow.jar`

## Arguments

| # | Argument | Type | Description |
|------|--------|------|------|
| 0 | `CLASSPATH` | String | JAR files from `${BOOSTER_HOME}/Booster/libs/*` and `build/libs/Booster-shadow.jar` |
| 1 | `OUTPUT_DIR` | String | Output directory for generated tests |
| 2 | `TIME_BUDGET` | Long | Time limit in milliseconds (e.g., 150000 = 150s) |
| 3 | `NUM_SPLIT_TESTS` | Integer | Number of output files to split into |
| 4 | `MODE` | String | `seqc` or `seqp` |
| 5 | `CUT_FILE` | String | Target class source file path |
| 6 | `REGRESSION_MODE` | String | `regression` or `non_regression` |
| 7 | `PROJECT_DIR` | String | Project source root directory |
| 8+ | `BASE_TESTS` | String | Base test file paths (space-separated) |
| ... | `<sep>` | Separator | Divides BASE_TESTS from CUT_TEST |
| ...+1 | `CUT_TEST` | String | Class name or file path (single test) |

## Example

```bash
java -Xmx64g -XX:-OmitStackTraceInFastThrow \
  -classpath ${CLASSPATH} \
  Main_standalone \
  ${CLASSPATH} \
  ${OUTPUT_DIR} \
  150000 \
  4 \
  seqp \
  ${PROJECT_HOME}/src/main/java/org/example/NumberUtils.java \
  regression \
  ${PROJECT_HOME}/src/main/java \
  ${OUTPUT_DIR}/org/example/NumberUtilsTest.java \
  <sep> \
  org.example.NumberUtilsTest
```

## Configuration

Edit `src/main/java/utils/Config.java` to adjust:

- `ENABLE_TEST_MINIMIZATION`: Filter duplicate tests (default: true)
- `REMOVE_PASSING_TESTS`: Exclude passing tests (default: true)
- `ENABLE_TEST_BUCKETING`: Group tests by exception (default: true)

After changes, rebuild:
```bash
gradle build shadowJar
```

## Output

Generated test files follow the pattern:
- `*_P_1.java`, `*_P_2.java`, ... (seqp output)
- `*_C_1.java`, `*_C_2.java`, ... (seqc output)

## Notes

- **seqc**: Slower, more thorough (use for comprehensive testing)
- **seqp**: Faster, efficient (use for quick coverage)
- Recommended: Run seqc first, then seqp
