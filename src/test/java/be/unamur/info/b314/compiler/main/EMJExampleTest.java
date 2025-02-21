package be.unamur.info.b314.compiler.main;

import org.junit.Test;
import org.junit.Rule;
import org.junit.rules.TemporaryFolder;
import org.junit.rules.TestRule;
import org.junit.rules.TestWatcher;
import org.junit.runner.Description;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class EMJExampleTest {

    private static final Logger LOG = LoggerFactory.getLogger(EMJExampleTest.class);

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
    public void example_test_ok() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/example/ok/example_ok.moj",
                testFolder.newFile(), 
                true, // true to indicate that the test should pass
                "example : OK test that should pass"
        );
    }

    /* KO tests: should fail */

    @Test
    public void example_test_ko() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/example/ko/example_ko.moj",
                testFolder.newFile(), 
                false, // false to indicate that the test should fail
                "example : KO test that should fail"
        );
    }
}