package be.unamur.info.b314.compiler.main;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.junit.rules.TestRule;
import org.junit.rules.TestWatcher;
import org.junit.runner.Description;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class EMJProgramStructureTest {
    private static final Logger LOG = LoggerFactory.getLogger(EMJProgramStructureTest.class);

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
    public void basic_program_test() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/01_program_structure/ok/basic_program.moj",
                testFolder.newFile(),
                true,
                "Program Structure: Basic program structure test"
        );
    }

    @Test
    public void basic_with_function_test() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/01_program_structure/ok/basic_with_function.moj",
                testFolder.newFile(),
                true,
                "Program Structure: Basic program with function test"
        );
    }

    /* KO tests: should fail */

    @Test
    public void invalid_missing_main_test() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/01_program_structure/ok/invalid_missing_main.moj",
                testFolder.newFile(),
                false,
                "Program Structure: Invalid program missing main function"
        );
    }
}
