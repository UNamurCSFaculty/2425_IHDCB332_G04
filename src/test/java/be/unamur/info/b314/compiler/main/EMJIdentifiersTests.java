package be.unamur.info.b314.compiler.main;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.junit.rules.TestRule;
import org.junit.rules.TestWatcher;
import org.junit.runner.Description;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class EMJIdentifiersTests {
    private static final Logger LOG = LoggerFactory.getLogger(EMJIdentifiersTests.class);

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
    public void function_identifiers_test() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/04_identifiers/ok/function_ids.moj",
                testFolder.newFile(),
                true,
                "Identifiers: Function identifiers test"
        );
    }

    @Test
    public void variable_identifiers_test() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/04_identifiers/ok/variable_ids.moj",
                testFolder.newFile(),
                true,
                "Identifiers: Variable identifiers test"
        );
    }
}
