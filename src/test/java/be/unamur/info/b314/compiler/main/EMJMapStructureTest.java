package be.unamur.info.b314.compiler.main;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.junit.rules.TestRule;
import org.junit.rules.TestWatcher;
import org.junit.runner.Description;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class EMJMapStructureTest {
    private static final Logger LOG = LoggerFactory.getLogger(EMJMapStructureTest.class);

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
    public void complex_map_test() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/08_map_structure/ok/complex_map.moj",
                testFolder.newFile(),
                true,
                "Map Structure: Complex map test"
        );
    }

    @Test
    public void basic_map_test() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/08_map_structure/ok/map.moj",
                testFolder.newFile(),
                true,
                "Map Structure: Basic map test"
        );
    }
}