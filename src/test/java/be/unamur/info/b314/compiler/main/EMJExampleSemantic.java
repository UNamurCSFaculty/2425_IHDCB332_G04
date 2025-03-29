package be.unamur.info.b314.compiler.main;

import org.junit.Test;
import org.junit.Rule;
import org.junit.rules.TemporaryFolder;
import org.junit.rules.TestRule;
import org.junit.rules.TestWatcher;
import org.junit.runner.Description;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class EMJExampleSemantic {

    private static final Logger LOG = LoggerFactory.getLogger(EMJExampleSemantic.class);

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
        ;
    };

    /* OK tests: should pass */

    @Test
    public void test_ok_var_id_ok() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/example_semantic/ok/var_id_ok.moj",
                testFolder.newFile(),
                true, // true to indicate that the test should pass
                "OK TEST: the test file should be accepted by the compiler"
        );
    }

    /* KO tests: should fail */

    @Test
    public void test_ko_var_id_already_decl() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/example_semantic/ko/var_id_already_decl.moj",
                testFolder.newFile(),
                false, // false to indicate that the test should fail
                "KO TEST: the test file should NOT be accepted by the compiler"
        );
    }

    @Test
    public void test_ko_var_id_not_decl() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/example_semantic/ko/var_id_not_decl.moj",
                testFolder.newFile(),
                false, // false to indicate that the test should fail
                "KO TEST: the test file should NOT be accepted by the compiler"
        );
    }
}