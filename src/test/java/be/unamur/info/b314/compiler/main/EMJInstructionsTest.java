package be.unamur.info.b314.compiler.main;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.junit.rules.TestRule;
import org.junit.rules.TestWatcher;
import org.junit.runner.Description;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class EMJInstructionsTest {
    private static final Logger LOG = LoggerFactory.getLogger(EMJInstructionsTest.class);

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
    public void assignments_test() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/06_instructions/ok/assignements.moj",
                testFolder.newFile(),
                true,
                "Instructions: Assignments test"
        );
    }

    @Test
    public void conditionals_test() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/06_instructions/ok/conditionnals.moj",
                testFolder.newFile(),
                true,
                "Instructions: Conditionals test"
        );
    }

    @Test
    public void declarations_test() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/06_instructions/ok/declarations.moj",
                testFolder.newFile(),
                true,
                "Instructions: Declarations test"
        );
    }

    @Test
    public void function_calls_test() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/06_instructions/ok/function_calls.moj",
                testFolder.newFile(),
                true,
                "Instructions: Function calls test"
        );
    }

    @Test
    public void loops_test() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/06_instructions/ok/loops.moj",
                testFolder.newFile(),
                true,
                "Instructions: Loops test"
        );
    }

    @Test
    public void returns_test() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/06_instructions/ok/returns.moj",
                testFolder.newFile(),
                true,
                "Instructions: Returns test"
        );
    }
}
