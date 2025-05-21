package be.unamur.info.b314.compiler.main;

// grammar
import be.unamur.info.b314.compiler.EMJLexer;
import be.unamur.info.b314.compiler.EMJParser;

import static com.google.common.base.Preconditions.checkArgument;
import java.io.*;

import be.unamur.info.b314.compiler.emj.Adapter.EMJVisitorAdapter;
import be.unamur.info.b314.compiler.emj.CodeGeneration.EMJCodeGenVisitorImpl;
import be.unamur.info.b314.compiler.emj.EMJErrorLogger;
import be.unamur.info.b314.compiler.emj.Result.ContextResult;
import be.unamur.info.b314.compiler.emj.Semantic.EMJSemanticVisitorImpl;
import be.unamur.info.b314.compiler.exception.EMJErrorException;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.RecognitionException;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


@SuppressWarnings("deprecation")

public class Main {
    private static final Logger LOG = LoggerFactory.getLogger(Main.class);
    private static final String NAME = "EMJ-compiler";
    private static final String HELP = "h";
    private static final String INPUT = "i";
    private static final String OUTPUT = "o";

    private EMJParser.RootContext rootTree;


    /**
     * Main method launched when starting compiler jar file.
     *
     * @param args Command line arguments.
     */
    public static void main(String[] args) {
        Main main = new Main();
        CommandLineParser parser = new DefaultParser();
        CommandLine line = null;

        try {
            line = parser.parse(main.options, args);
        }
        catch (ParseException ex) {
            LOG.error("Error while parsing command line!", ex);
            main.printHelpMessage();
        }

        // If help is requested, print help message and exit.
        if (line != null) {
            if (line.hasOption(HELP)) {
                main.printHelpMessage();
            }
            else {
                // Else start compilation
                try {
                    main.initialise(line);
                    main.compile(); // Call compile method (to be completed)
                    System.err.println("OK"); // Print OK on stderr
                    main.generateMicroPython(line);
                }
                catch (Exception e) {
                    LOG.error("Exception occurred during compilation!", e);
                    System.err.println("KO"); // Print KO on stderr if a problem occurred
                }
            }
        }
    }

    /**
     * The command line options.
     */
    private final Options options;

    /**
     * The input B314 file.
     */
    private File inputFile;

    /**
     * The output PCode file.
     */
    private File outputFile;

    private EMJParser parser;

    private Main() {
        // Create command line options
        options = new Options();

        options.addOption(Option.builder(HELP)
                .desc("Prints this help message.")
                .build());

        options.addOption(Option.builder(INPUT)
                .desc("The B314 input file.")
                .hasArg(true)
                .build());

        options.addOption(Option.builder(OUTPUT)
                .desc("The PCOde output file.")
                .hasArg(true)
                .build());
    }

    /**
     * Prints help message with these options.
     */
    private void printHelpMessage() {
        HelpFormatter formatter = new HelpFormatter();
        formatter.setWidth(128);
        formatter.printHelp(String.format("java -jar %s.jar -%s | %s %s",
                NAME, HELP, INPUT, OUTPUT), options);
    }

    /**
     * Initialise the input compiler using the given input line.
     *
     * @throws Exception If one of the three required arguments is not provided.
     */
    private void initialise(CommandLine line) throws Exception {
        LOG.debug("Initialisation");

        // Check that the arguments are there
        if (!line.hasOption(INPUT)) {
            throw new ParseException(String.format("Option %s is mandatory!", INPUT));
        }

        else if (!line.hasOption(OUTPUT)) {
            throw new ParseException(String.format("Option %s is mandatory!", OUTPUT));
        }

        // Get given files and check they exist
        inputFile = new File(line.getOptionValue(INPUT));
        checkArgument(inputFile.exists() && inputFile.isFile(), "File %s not found!", inputFile.getName());
        LOG.debug("Input file set to {}", inputFile.getPath());

        outputFile = new File(line.getOptionValue(OUTPUT));

        if (!outputFile.exists()) {
            outputFile.createNewFile();
        }

        checkArgument(outputFile.exists() && outputFile.isFile(), "File %s not created!", outputFile.getName());

        LOG.debug("Output file set to {}", outputFile.getPath());
        LOG.debug("Initialisation: done");
    }


    /**
     * Compiler methods, this is where the magic happens
     */
    private void compile() throws IOException, EMJErrorException {
        this.parseInput();           //Appelle unique au parser ici
        this.visitTree(rootTree);   //Utilise le root déjà parsé
    }


    //Pour ne pas Parser 2x (une fois dans compile et une fois dans generateMicroPython
    private void parseInput() throws IOException {
        LOG.debug("Parsing input");
        try {
            EMJLexer lexer = new EMJLexer(CharStreams.fromPath(inputFile.toPath()));
            EMJParser parser = new EMJParser(new CommonTokenStream(lexer));

            parser.removeErrorListeners();
            MyConsoleErrorListener errListener = new MyConsoleErrorListener();
            parser.addErrorListener(errListener);

            rootTree = parser.root();

            if (errListener.errorHasBeenReported()) {
                throw new IllegalArgumentException("Error while parsing input!");
            }

            LOG.debug("Parsing input: done");
            LOG.debug("AST is {}", rootTree.toStringTree(parser));
        } catch (Exception e) {
            LOG.error("Error while parsing", e);
            throw new IOException("Parsing failed", e);
        }
    }

    private void generateMicroPython(CommandLine line) throws IOException {
        LOG.info("GENERATE MICRO PYTHON CODE:");

        //Utilise rootTree déjà généré
        EMJCodeGenVisitorImpl codeGenVisitor = new EMJCodeGenVisitorImpl();
        codeGenVisitor.loadTemplates("micropython.stg");

        ContextResult programResult = (ContextResult) codeGenVisitor.visit(rootTree);

        String generatedCode = codeGenVisitor.generateCode(programResult);

        try (PrintWriter out = new PrintWriter(outputFile)) {
            out.println(generatedCode);
        }

        System.out.printf("Code généré :\n```python\n%s\n```%n", generatedCode);
    }


    private void visitTree(EMJParser.RootContext tree) throws EMJErrorException {
    // Visit tree
    EMJSemanticVisitorImpl visitor = new EMJSemanticVisitorImpl();
    
    // Passer le chemin du fichier source au visiteur pour la résolution des chemins relatifs

    EMJVisitorAdapter<Object> adapter = new EMJVisitorAdapter<>(visitor);
        LOG.debug("Visiting");
        adapter.visit(tree);
        LOG.debug("Visiting: done");

        // If an error occurred during the tree visit, throw it
        EMJErrorLogger errorLogger = visitor.getErrorLogger();
        if(errorLogger.containsErrors()) {
            System.out.println(errorLogger.getErrorsString());
            throw new EMJErrorException(errorLogger.getErrorsString());
        }
    }


}