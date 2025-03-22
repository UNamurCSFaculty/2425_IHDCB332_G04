package be.unamur.info.b314.compiler.main;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.junit.rules.TestRule;
import org.junit.rules.TestWatcher;
import org.junit.runner.Description;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class EMJDataTypesTest {
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
    public void boolean_type_test() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/03_data_types/ok/boolean.moj",
                testFolder.newFile(),
                true,
                "Data Types: Boolean type declaration and usage test"
        );
    }

    @Test
    public void character_type_test() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/03_data_types/ok/character.moj",
                testFolder.newFile(),
                true,
                "Data Types: Character type declaration and usage test"
        );
    }

    @Test
    public void integer_type_test() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/03_data_types/ok/integer.moj",
                testFolder.newFile(),
                true,
                "Data Types: Integer type declaration and usage test"
        );
    }

    @Test
    public void string_type_test() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/03_data_types/ok/string.moj",
                testFolder.newFile(),
                true,
                "Data Types: String type declaration and usage test"
        );
    }

    @Test
    public void tuple_type_test() throws Exception {
        CompilerTestHelper.launchCompilation(
                "/03_data_types/ok/tuple.moj",
                testFolder.newFile(),
                true,
                "Data Types: Tuple type declaration and usage test"
        );
    }
}
