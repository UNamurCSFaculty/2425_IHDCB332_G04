package be.unamur.info.b314.compiler.main;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.junit.rules.TestRule;
import org.junit.rules.TestWatcher;
import org.junit.runner.Description;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class EMJJenkinsTests {
    private static final Logger LOG = LoggerFactory.getLogger(EMJJenkinsTests.class);

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
    public void functions_ko_function_without_return() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/06_instructions/ko/no_return_function.moj",
                testFolder.newFile(),
                false,
                "Comments: No return functions"
        );
    }

//    @Test
//    public void boolexpr_ok_boolexpr_complex() throws Exception { //TODO: identifier le souci exact
//        CompilerTestHelper.launchCompilation(
//                "/02_comments/ok/single_line.moj",
//                testFolder.newFile(),
//                true,
//                "Comments: Single-line comments test"
//        );
//    }

    @Test
    public void comments_ko_comment_block_not_closed() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/06_instructions/ko/unclosed_comment.moj",
                testFolder.newFile(),
                false,
                "Comments: Unclosed block comment should fail"
        );
    }

    @Test
    public void emptyprogram_ko_empty_file() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/01_program_structure/ko/empty_file.moj",
                testFolder.newFile(),
                false,
                "Comments: Empty file should fail"
        );
    }

    @Test
    public void emptyprogram_ko_no_instruction() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/01_program_structure/ko/empty_program.moj",
                testFolder.newFile(),
                false,
                "Comments: Empty program should fail"
        );
    }
}