package be.unamur.info.b314.compiler.main;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.junit.rules.TestRule;
import org.junit.rules.TestWatcher;
import org.junit.runner.Description;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class EMJExpressionsTest {
    private static final Logger LOG = LoggerFactory.getLogger(EMJExpressionsTest.class);

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
    public void arithmetic_expressions_test() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/05_expressions/ok/arithmetic.moj",
                testFolder.newFile(),
                true,
                "Expressions: Arithmetic expressions test"
        );
    }

    @Test
    public void boolean_expressions_test() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/05_expressions/ok/bool_expr.moj",
                testFolder.newFile(),
                true,
                "Expressions: Boolean expressions test"
        );
    }

    @Test
    public void complex_expressions_test() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/05_expressions/ok/complex_expr.moj",
                testFolder.newFile(),
                true,
                "Expressions: Complex expressions test"
        );
    }
}