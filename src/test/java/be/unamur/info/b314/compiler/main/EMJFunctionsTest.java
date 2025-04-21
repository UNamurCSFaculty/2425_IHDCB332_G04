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
 * Test class for EMJ function syntax validation.
 * Tests explicit return statements in functions as required by the project specifications.
 */
public class EMJFunctionsTest {
    private static final Logger LOG = LoggerFactory.getLogger(EMJFunctionsTest.class);

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
    public void function_with_explicit_return_v1_test() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/09_functions/ok/function_inline_v1.moj",
                testFolder.newFile(),
                true,
                "Functions: Function with explicit return using RETURN keyword"
        );
    }

    @Test
    public void function_with_explicit_return_v2_test() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/09_functions/ok/function_inline_v2.moj",
                testFolder.newFile(),
                true,
                "Functions: Function with explicit return using VOID_TYPE"
        );
    }

    @Test
    public void function_with_explicit_return_v3_test() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/09_functions/ok/function_inline_v3.moj",
                testFolder.newFile(),
                true,
                "Functions: Function with explicit return using RETURN_VOID"
        );
    }

    @Test
    public void test_ok_parameter_call_exact_match() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/09_functions/ok/exact_params.moj",
                testFolder.newFile(),
                true,
                "Should succeed: function call with correct number of parameters"
        );
    }

    /* KO tests: should fail */

    @Test
    public void function_without_return_test() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/09_functions/ko/function_without_return.moj",
                testFolder.newFile(),
                false,
                "Functions: Function without explicit return should fail"
        );
    }

    @Test
    public void test_ko_parameter_call_less_than_declared() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/09_functions/ko/less_params.moj",
                testFolder.newFile(),
                false,
                "Should fail: function call with too few parameters"
        );
    }

    @Test
    public void test_ko_parameter_call_more_than_declared() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/09_functions/ko/more_params.moj",
                testFolder.newFile(),
                false,
                "Should fail: function call with too many parameters"
        );
    }
}
