package be.unamur.info.b314.compiler.main;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.junit.rules.TestRule;
import org.junit.rules.TestWatcher;
import org.junit.runner.Description;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class EMJCommentsTest {
    private static final Logger LOG = LoggerFactory.getLogger(EMJCommentsTest.class);

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
    public void multi_line_comment_test() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/02_comments/ok/multi_line.moj",
                testFolder.newFile(),
                true,
                "Comments: Multi-line comments test"
        );
    }

    @Test
    public void single_line_comment_test() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/02_comments/ok/single_line.moj",
                testFolder.newFile(),
                true,
                "Comments: Single-line comments test"
        );
    }

    /* KO tests: should fail */

    @Test
    public void invalid_nested_comment_test() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/02_comments/ko/invalid_nested.moj",
                testFolder.newFile(),
                false,
                "Comments: Invalid nested comments test that should fail"
        );
    }
}