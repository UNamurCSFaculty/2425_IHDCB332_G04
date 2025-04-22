package be.unamur.info.b314.compiler.main;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.junit.rules.TestRule;
import org.junit.rules.TestWatcher;
import org.junit.runner.Description;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Test class for semantic validation of boolean operations
 * @author EMJ Team
 */
public class EMJTestSemanticBooleanoperations {
    private static final Logger LOG = LoggerFactory.getLogger(EMJTestSemanticBooleanoperations.class);

    @Rule
    // Create a temporary folder for outputs deleted after tests
    public TemporaryFolder testFolder = new TemporaryFolder();

    @Rule
    // Print message on logger before each test
    public TestRule watcher = new TestWatcher() {
        @Override
        protected void starting(Description description) {
            LOG.info(String.format("Starting test: %s()...",
                    description.getMethodName()));
        }
    };

    /* OK tests: should pass */

    @Test
    public void test_ok_booleanoperation_with_valid_comparison() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/semantic/booleanoperations/ok/ok_booleanoperation_with_valid_comparison.moj",
                testFolder.newFile(),
                true,
                "Boolean operations: Valid comparison types"
        );
    }

    /* KO tests: should not pass */

    @Test
    public void test_ko_booleanoperation_with_invalid_comparison() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/semantic/booleanoperations/ko/ko_booleanoperation_with_invalid_comparison.moj",
                testFolder.newFile(),
                false, // false car le test doit échouer (KO attendu)
                "Boolean operations: Invalid comparison types"
        );
    }
}
