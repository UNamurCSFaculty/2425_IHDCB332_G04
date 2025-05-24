package be.unamur.info.b314.compiler.emj.CodeGeneration;

import be.unamur.info.b314.compiler.EMJParser;
import be.unamur.info.b314.compiler.EMJParserBaseVisitor;
import be.unamur.info.b314.compiler.emj.EMJVarType;
// Utilisation du chemin complet pour éviter les problèmes de résolution de package
import be.unamur.info.b314.compiler.emj.Result.ContextResult;
import com.vdurmont.emoji.EmojiParser;
import org.stringtemplate.v4.ST;
import org.stringtemplate.v4.STGroup;
import org.stringtemplate.v4.STGroupFile;

import java.util.*;
import java.util.logging.FileHandler;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.logging.SimpleFormatter;
import java.io.IOException;

public class EMJCodeGenVisitorImpl extends EMJParserBaseVisitor<Object> implements EMJCodeGenVisitor {

    private STGroup templates;
    private int indentLevel = 0;
    private int loopCounter = 0;

    // Logger configuration
    private static final Logger logger = Logger.getLogger(EMJCodeGenVisitorImpl.class.getName());
    private static FileHandler fileHandler;

    static {
        try {
            // Configure logger with file output
            fileHandler = new FileHandler("emj_codegen.log", true);
            fileHandler.setFormatter(new SimpleFormatter());
            logger.addHandler(fileHandler);
            logger.setLevel(Level.INFO);
            // Remove console handlers if you want logs only in file
            Logger rootLogger = Logger.getLogger("");
            rootLogger.removeHandler(rootLogger.getHandlers()[0]);

            logger.info("Logger initialized successfully");
        } catch (IOException e) {
            System.err.println("Failed to initialize logger: " + e.getMessage());
            e.printStackTrace();
        }
    }

    public EMJCodeGenVisitorImpl() {
        logger.info("EMJCodeGenVisitorImpl instantiated");
    }

    private static final Map<String, String> emojiShortNames = new HashMap<>();

    static {
        emojiShortNames.put("🚗", "car");
        emojiShortNames.put("🦹", "thief");
        emojiShortNames.put("⬆️", "up");
        emojiShortNames.put("⬇️", "down");
        emojiShortNames.put("➡️", "right");
        emojiShortNames.put("⬅️", "left");
        emojiShortNames.put("🛑", "stop");
        emojiShortNames.put("🔢", "int");
        emojiShortNames.put("🔟", "bool");
        emojiShortNames.put("🔣", "char");
        emojiShortNames.put("🔡", "str");
        emojiShortNames.put("🌀", "void");
        emojiShortNames.put("↩️", "return");
        emojiShortNames.put("❓", "or");
        emojiShortNames.put("🤝", "and");
        emojiShortNames.put("⛔", "not");
        emojiShortNames.put("📦", "package");
        emojiShortNames.put("🏠", "main");
        emojiShortNames.put("🚔", "cop");
        emojiShortNames.put("🛣️", "road");
        emojiShortNames.put("🌋", "volcano");
        emojiShortNames.put("🏘️", "house");
        emojiShortNames.put("🚧", "barrier");
        emojiShortNames.put("🚜", "tractor");
        emojiShortNames.put("🌊", "water");
        emojiShortNames.put("✋", "stop_thief");
        emojiShortNames.put("📻", "toggle_sound");
        emojiShortNames.put("🚨", "toggle_light");
        //emojiShortNames.put("🐜", "ant"); // si utilisé
        // Ajoute d'autres emojis si nécessaire
    }

    @Override
    public ContextResult visitRoot(EMJParser.RootContext ctx) {
        if (ctx.programFile() != null) {
            logger.info("Visiting program file");
            return visitProgramFile(ctx.programFile());
        }
        else if (ctx.mapFile() != null) {
            logger.info("Visiting map file");
            return visitMapFile(ctx.mapFile());
        }
        logger.warning("Root context doesn't contain program or map file");
        return null;
    }

    @Override
    public ContextResult visitProgramFile(EMJParser.ProgramFileContext ctx) {
        Map<String, Object> attributes = new HashMap<>();

        // Génère les instructions principales (ex-main)
        logger.info("Generating main function");
        ContextResult mainResult = (ContextResult) visit(ctx.mainFunction());

        if (mainResult == null) {
            logger.severe("Error: mainResult is null. Cannot generate program body.");
            return ContextResult.invalid();
        }

        if (!mainResult.isValid()) {
            logger.warning("Warning: mainResult is not valid.");
        }

        // Vérification et ajout de l'attribut 'body'
        if (mainResult.getAttributes().containsKey("body")) {
            Object bodyObj = mainResult.getAttributes().get("body");
            if (bodyObj instanceof List) {
                List<?> bodyList = (List<?>) bodyObj;
                logger.info("Main body found with " + bodyList.size() + " instructions.");
                List<String> wrappedMain = new ArrayList<>();
                for (Object line : bodyList) {
                    wrappedMain.add(line.toString());
                }
                attributes.put("body", wrappedMain);

            } else {
                logger.severe("Error: 'body' attribute is not a list as expected. Type: " +
                        (bodyObj != null ? bodyObj.getClass().getName() : "null"));
                // Créer une liste vide plutôt que de générer une erreur
                attributes.put("body", new ArrayList<String>());
            }
        } else {
            logger.severe("Error: 'body' attribute is missing in mainResult.");
            // Créer une liste vide plutôt que de générer une erreur
            attributes.put("body", new ArrayList<String>());
        }

        // Génère les fonctions utilisateur
        List<String> renderedFunctions = new ArrayList<>();
        if (ctx.functionDecl() != null && !ctx.functionDecl().isEmpty()) {
            logger.info("Generating " + ctx.functionDecl().size() + " user functions.");

            for (EMJParser.FunctionDeclContext funcCtx : ctx.functionDecl()) {
                try {
                    incrIndent();
                    ContextResult funcResult = (ContextResult) visit(funcCtx);
                    decrIndent();

                    if (funcResult == null || !funcResult.isValid()) {
                        logger.warning("Error generating function: " +
                                (funcCtx.EMOJI_ID() != null ? funcCtx.EMOJI_ID().getText() : "<unnamed>"));
                        continue;
                    }

                    ST funcTemplate = templates.getInstanceOf(funcResult.getTemplateName());
                    if (funcTemplate == null) {
                        logger.warning("Function template not found: " + funcResult.getTemplateName());
                        continue;
                    }

                    for (Map.Entry<String, Object> entry : funcResult.getAttributes().entrySet()) {
                        try {
                            funcTemplate.add(entry.getKey(), entry.getValue());
                        } catch (Exception e) {
                            logger.warning("Error adding attribute '" +
                                    entry.getKey() + "' to function template: " + e.getMessage());
                        }
                    }

                    String renderedFunction = funcTemplate.render();
                    renderedFunctions.add(renderedFunction);
                    logger.info("Function rendered successfully: " +
                            (funcCtx.EMOJI_ID() != null ? funcCtx.EMOJI_ID().getText() : "<unnamed>"));
                } catch (Exception e) {
                    logger.log(Level.SEVERE, "Exception while generating function", e);
                }
            }
        } else {
            logger.info("No user functions to generate.");
        }

        attributes.put("functions", renderedFunctions);
        logger.info("Program generation completed with " + renderedFunctions.size() +
                " user functions.");

        return ContextResult.valid(attributes, "program");
    }

    @Override
    public ContextResult visitMapFile(EMJParser.MapFileContext ctx) {
        Map<String, Object> attributes = new HashMap<>();

        int width = Integer.parseInt(ctx.INT_VALUE(0).getText());
        int height = Integer.parseInt(ctx.INT_VALUE(1).getText());

        String orientation = sanitizeEmoji(ctx.orientation().getText());
        logger.info("Map dimensions: " + width + "x" + height + ", orientation: " + orientation);

        List<String> mapRows = new ArrayList<>();
        int index = 0;
        for (int i = 0; i < height; i++) {
            List<String> cells = new ArrayList<>();
            for (int j = 0; j < width; j++) {
                EMJParser.MapCellContext cellCtx = ctx.mapCell(index++);
                String emoji = cellCtx.getText();
                String cleaned = emojiShortNames.getOrDefault(emoji, "unknown");
                cells.add("\"" + cleaned + "\"");
            }
            String row = "[" + String.join(", ", cells) + "]";
            mapRows.add(row);
        }

        attributes.put("width", width);
        attributes.put("height", height);
        attributes.put("orientation", orientation);
        attributes.put("map", mapRows);

        logger.info("Map file processed successfully (full names)");
        return ContextResult.valid(attributes, "mapProgram");
    }


    @Override
    public ContextResult visitMainFunction(EMJParser.MainFunctionContext ctx) {
        Map<String, Object> attributes = new HashMap<>();

        // Visit all statements and render them
        List<String> renderedStatements = new ArrayList<>();
        for (EMJParser.StatementContext stmtCtx : ctx.statement()) {
            ContextResult stmtResult = (ContextResult) visit(stmtCtx);
            if (stmtResult == null) {
                logger.warning("Error: stmtResult is null for statement: " + stmtCtx.getText());
                continue;
            }

            if (!stmtResult.isValid()) {
                logger.warning("Warning: stmtResult is not valid for statement: " + stmtCtx.getText());
            }

            String renderedStatement = renderResult(stmtResult);
            if (renderedStatement != null && !renderedStatement.isEmpty()) {
                renderedStatements.add(renderedStatement);
            }
        }

        // Vérifier si le template existe réellement et quels sont ses attributs
        if (templates != null) {
            ST mainFunctionTemplate = templates.getInstanceOf("mainFunction");
            if (mainFunctionTemplate != null) {
                logger.info("mainFunction template found!");
                // Test du template avec l'attribut 'body'
                ST testTemplate = new ST(mainFunctionTemplate);
                try {
                    testTemplate.add("body", renderedStatements);
                    logger.fine("Test rendering of mainFunction template: \n" + testTemplate.render());
                } catch (Exception e) {
                    logger.log(Level.WARNING, "Error testing mainFunction template with 'body' attribute", e);
                }
            } else {
                logger.warning("mainFunction template not found!");
            }
        }

        // Debug: afficher le nombre d'instructions renderisées
        logger.info("Number of rendered instructions for main: " + renderedStatements.size());
        if (!renderedStatements.isEmpty()) {
            logger.fine("Example of rendered instruction: " + renderedStatements.get(0));
        }

        attributes.put("body", renderedStatements);
        return ContextResult.valid(attributes, "mainFunction");
    }

    private String renderResult(ContextResult result) {
        if (!result.isValid()) {
            return "";
        }

        // Vérifier que les templates sont chargés
        if (templates == null) {
            logger.severe("Templates not loaded. Check initialization.");
            return "# Templates not loaded";
        }

        // Obtenir le template
        String templateName = result.getTemplateName();
        ST template = templates.getInstanceOf(templateName);
        if (template == null) {
            logger.warning("Template not found: " + templateName);
            return "# Template not found: " + templateName;
        }

        // Ajouter les attributs de manière sécurisée
        for (Map.Entry<String, Object> entry : result.getAttributes().entrySet()) {
            String key = entry.getKey();
            Object value = entry.getValue();

            try {
                template.add(key, value);
            } catch (IllegalArgumentException e) {
                logger.warning("Error adding attribute '" + key + "' to template '" + templateName + "': " + e.getMessage());
                // Continuer avec les autres attributs plutôt que d'échouer complètement
            }
        }

        return template.render();
    }

    @Override
    public ContextResult visitStatement(EMJParser.StatementContext ctx) {
        if (ctx.varDecl() != null) {
            return (ContextResult) visit(ctx.varDecl());
        } else if (ctx.assignment() != null) {
            return (ContextResult) visit(ctx.assignment());
        } else if (ctx.functionCallStmt() != null) {
            return (ContextResult) visit(ctx.functionCallStmt());
        } else if (ctx.ifStatement() != null) {
            return (ContextResult) visit(ctx.ifStatement());
        } else if (ctx.loopStatement() != null) {
            return (ContextResult) visit(ctx.loopStatement());
        } else if (ctx.predefinedStmt() != null) {
            return (ContextResult) visit(ctx.predefinedStmt());
        } else if (ctx.getChildCount() == 2                     //  🌀  ;
                && "🌀".equals(ctx.getChild(0).getText())) {

            // Ici on ne veut rien générer (comme Skip), on signale juste que
            // l'instruction est valide pour éviter l'avertissement.
            return ContextResult.valid(Collections.emptyMap(), "skipStatement");
        }

        logger.warning("Unrecognized statement type: " + ctx.getText());
        return ContextResult.invalid();
    }

    @Override
    public ContextResult visitFunctionDecl(EMJParser.FunctionDeclContext ctx) {
        Map<String, Object> attributes = new HashMap<>();
        List<String> parameters = new ArrayList<>();
        List<String> bodyLines = new ArrayList<>();

        String varName = sanitizeEmoji(ctx.EMOJI_ID().getText());
        attributes.put("name", varName);
        logger.info("Processing function declaration: " + varName);

        if (ctx.optionalParamList() != null && ctx.optionalParamList().paramList() != null) {
            List<EMJParser.ParamContext> parametersContext = ctx.optionalParamList().paramList().param();
            for (EMJParser.ParamContext paramCtx : parametersContext) {
                ContextResult result = (ContextResult) visit(paramCtx);
                if (result.isValid()) {
                    ST subTemplate = templates.getInstanceOf(result.getTemplateName());
                    for (Map.Entry<String, Object> entry : result.getAttributes().entrySet()) {
                        subTemplate.add(entry.getKey(), entry.getValue());
                    }
                    parameters.add(subTemplate.render());
                }
            }
        }
        attributes.put("parameters", parameters);
        logger.fine("Function has " + parameters.size() + " parameters");

        for (EMJParser.StatementContext stmtCtx : ctx.statement()) {
            ContextResult result = (ContextResult) visit(stmtCtx);
            if (result.isValid()) {
                ST subTemplate = templates.getInstanceOf(result.getTemplateName());
                for (Map.Entry<String, Object> entry : result.getAttributes().entrySet()) {
                    subTemplate.add(entry.getKey(), entry.getValue());
                }
                bodyLines.add(subTemplate.render());
            }
        }
        attributes.put("body", bodyLines);
        logger.fine("Function has " + bodyLines.size() + " body lines");

        ContextResult returnStmtResult = (ContextResult) visit(ctx.returnStatement());
        attributes.put("return", returnStmtResult.getAttributes().values());

        return ContextResult.valid(attributes, "functionDecl");
    }

    @Override
    public ContextResult visitReturnStatement(EMJParser.ReturnStatementContext ctx) {
        Map<String, Object> attributes = new HashMap<>();

        if (ctx.getParent() != null && ctx.getParent().getParent() instanceof EMJParser.MainFunctionContext) {
            logger.fine("Return statement in main function - skipping");
            return ContextResult.valid(Collections.emptyMap(), "returnStatement");
        }

        // Check if it's a void return
        if (ctx.VOID_TYPE() != null || ctx.RETURN_VOID() != null || ctx.expression() == null) {
            attributes.put("value", "None");
            logger.fine("Processing void return statement");
        } else {
            // Visit the expression
            ContextResult exprResult = (ContextResult) visit(ctx.expression());
            attributes.put("value", exprResult.getAttributes().get("code"));
            logger.fine("Processing return statement with value: " + exprResult.getAttributes().get("code"));
        }

        return ContextResult.valid(attributes, "return");
    }

    @Override
    public ContextResult visitParam(EMJParser.ParamContext ctx) {
        Map<String, Object> attributes = new HashMap<>();

        String varName = sanitizeEmoji(ctx.EMOJI_ID().getText());
        attributes.put("name", varName);
        logger.fine("Processing parameter: " + varName);
        return ContextResult.valid(attributes, "parameter");
    }

    @Override
    public ContextResult visitTupleValue(EMJParser.TupleValueContext ctx) {
        Map<String, Object> attributes = new HashMap<>();

        // First value
        ContextResult val1Result = (ContextResult) visit(ctx.expression(0));
        // Second value
        ContextResult val2Result = (ContextResult) visit(ctx.expression(1));

        String tupleCode = "(" + val1Result.getAttributes().get("code") + ", " +
                val2Result.getAttributes().get("code") + ")";
        attributes.put("code", tupleCode);
        logger.fine("Processing tuple value: " + tupleCode);

        return ContextResult.valid(attributes, "primaryExpression");
    }

    @Override
    public ContextResult visitVarDecl(EMJParser.VarDeclContext ctx) {
        Map<String, Object> attributes = new HashMap<>();

        String varName = sanitizeEmoji(ctx.EMOJI_ID().getText());
        attributes.put("name", varName);

        // Obtenir le type
        String typeResult = getTypeFromContext(ctx.type());
        attributes.put("type", typeResult);

        logger.info("Processing variable declaration: " + varName + " of type " + typeResult);

        // Gérer la valeur initiale
        if (ctx.expression() != null) {
            ContextResult exprResult = (ContextResult) visit(ctx.expression());
            attributes.put("value", exprResult.getAttributes().get("code"));
            logger.fine("Variable initialized with value: " + exprResult.getAttributes().get("code"));
        } else {
            // Valeur par défaut selon le type
            switch (typeResult) {
                case "int":
                    attributes.put("value", "0");
                    break;
                case "bool":
                    attributes.put("value", "False");
                    break;
                case "str":
                case "char":
                    attributes.put("value", "\"\"");
                    break;
                default:
                    if (typeResult.startsWith("tuple")) {
                        attributes.put("value", "(None, None)");
                    } else {
                        attributes.put("value", "None");
                    }
            }
            logger.fine("Variable using default value for type " + typeResult);
        }

        attributes.put("indent", getIndent());
        return ContextResult.valid(attributes, "varDecl");
    }

    @Override
    public ContextResult visitBlock(EMJParser.BlockContext ctx) {
        Map<String, Object> attributes = new HashMap<>();

        // Visit all statements and render them
        List<String> renderedStatements = new ArrayList<>();
        for (EMJParser.StatementContext stmtCtx : ctx.statement()) {
            ContextResult stmtResult = (ContextResult) visit(stmtCtx);
            renderedStatements.add(renderResult(stmtResult));
        }

        // Put the rendered statements in attributes - use consistent naming with templates
        attributes.put("statements", renderedStatements); // For block template
        logger.fine("Processed block with " + renderedStatements.size() + " statements");

        return ContextResult.valid(attributes, "block");
    }

    @Override
    public ContextResult visitIfStatement(EMJParser.IfStatementContext ctx) {
        Map<String, Object> attributes = new HashMap<>();
        attributes.put("indent",getIndent());
        String emptyBlock = "pass #empty block";

        logger.info("Processing if statement");
        ContextResult conditionResult = (ContextResult) visit(ctx.expression());
        attributes.put("condition", renderResult(conditionResult));

        incrIndent();
        String renderedIfBlock = String.format("%s%s", getIndent(), emptyBlock);
        if (!ctx.block().isEmpty()) {
            if (!ctx.block(0).isEmpty()) {
                renderedIfBlock = renderResult((ContextResult) visit(ctx.block(0)));
                logger.fine("If block has content");
            } else {
                logger.fine("If block is empty");
            }
        }
        decrIndent();
        attributes.put("bodyIf", renderedIfBlock);

        // Bloc else si présent
        if (ctx.block().size() > 1) {
            incrIndent();
            String renderedElseBlock = String.format("%s%s", getIndent(), emptyBlock);
            if (!ctx.block().isEmpty() && !ctx.block(1).isEmpty()) {
                renderedElseBlock = renderResult((ContextResult) visit(ctx.block(1)));
                logger.fine("Else block has content");
            } else {
                logger.fine("Else block is empty");
            }
            decrIndent();
            attributes.put("bodyElse", renderedElseBlock);
        }else if (ctx.SKIPPING()!=null){
            incrIndent();
            attributes.put("bodyElse", String.format("%spass  # skip", getIndent()));
            logger.fine("Processing skip statement in else branch");
            decrIndent();
        }
        return ContextResult.valid(attributes, "ifStatement");
    }

    @Override
    public ContextResult visitLoopStatement(EMJParser.LoopStatementContext ctx) {
        Map<String, Object> attributes = new HashMap<>();
        attributes.put("indent",getIndent());
        String emptyBlock="pass #empty block";

        // Vérifier si c'est une boucle while (identifiée par l'emoji ♾️)
        if (ctx.WHILE() != null) {
            logger.info("Processing while loop");
            // Condition
            ContextResult conditionResult = (ContextResult) visit(ctx.expression());
            attributes.put("condition", renderResult(conditionResult));

            incrIndent();
            String renderedBlock = String.format("%s%s", getIndent(), emptyBlock);
            if (!ctx.block().statement().isEmpty()) {
                renderedBlock = renderResult((ContextResult) visit(ctx.block()));
                logger.fine("While loop block has content");
            } else {
                logger.fine("While loop block is empty");
            }
            decrIndent();
            // Ensure attribute name matches template parameter name
            attributes.put("body", renderedBlock);
            return ContextResult.valid(attributes, "whileStatement");
        } else if (ctx.FOR() != null) {// Cas pour la boucle for (identifiée par l'emoji 🔁)
            logger.info("Processing for loop");
            // Nombre d'itérations
            ContextResult exprResult = (ContextResult) visit(ctx.expression());
            attributes.put("range", renderResult(exprResult));
            attributes.put("counter", loopCounter++);
            logger.fine("For loop counter: " + (loopCounter-1));

            incrIndent();
            String renderedBlock = String.format("%s%s", getIndent(), emptyBlock);
            if (!ctx.block().statement().isEmpty()) {
                renderedBlock = renderResult((ContextResult) visit(ctx.block()));
                logger.fine("For loop block has content");
            } else {
                logger.fine("For loop block is empty");
            }
            decrIndent();

            // Ensure attribute name matches template parameter name
            attributes.put("body", renderedBlock);
            return ContextResult.valid(attributes, "forStatement");
        }
        logger.warning("Unrecognized loop type");
        return null;
    }

    @Override
    public ContextResult visitLeftExpression(EMJParser.LeftExpressionContext ctx) {
        Map<String, Object> attributes = new HashMap<>();

        // Get variable name
        String varName = sanitizeEmoji(ctx.EMOJI_ID().getText());

        // Check if it's a tuple access
        if (ctx.TUPLE_FIRST() != null) {
            attributes.put("code", varName + "[0]");
            logger.fine("Processing tuple first element access: " + varName + "[0]");
        } else if (ctx.TUPLE_SECOND() != null) {
            attributes.put("code", varName + "[1]");
            logger.fine("Processing tuple second element access: " + varName + "[1]");
        } else {
            attributes.put("code", varName);
            logger.fine("Processing variable reference: " + varName);
        }

        return ContextResult.valid(attributes, "leftExpression");
    }

    @Override
    public ContextResult visitAssignment(EMJParser.AssignmentContext ctx) {
        Map<String, Object> attributes = new HashMap<>();

        // Left expression
        ContextResult leftResult = (ContextResult) visit(ctx.leftExpression());
        String leftCode = leftResult.getAttributes().get("code").toString();
        attributes.put("left", leftCode);

        // Right expression
        ContextResult rightResult = (ContextResult) visit(ctx.expression());
        String rightCode = rightResult.getAttributes().get("code").toString();
        attributes.put("right", rightCode);

        logger.info("Processing assignment: " + leftCode + " = " + rightCode);
        attributes.put("indent", getIndent());
        return ContextResult.valid(attributes,"assignment");
    }

    @Override
    public ContextResult visitExpression(EMJParser.ExpressionContext ctx) {
        logger.fine("Processing expression");
        return (ContextResult) visit(ctx.orExpression());
    }

    @Override
    public ContextResult visitOrExpression(EMJParser.OrExpressionContext ctx) {
        if (!ctx.OR().isEmpty()) {
            Map<String, Object> attributes = new HashMap<>();
            StringBuilder code = new StringBuilder();

            for (int i = 0; i < ctx.andExpression().size(); i++) {
                ContextResult exprResult = (ContextResult) visit(ctx.andExpression(i));
                code.append(exprResult.getAttributes().get("code"));

                if (i < ctx.andExpression().size() - 1) {
                    code.append(" or ");
                }
            }

            String orExpr = code.toString();
            logger.fine("Processing OR expression: " + orExpr);
            attributes.put("code", orExpr);
            return ContextResult.valid(attributes, "primaryExpression");
        } else if (!ctx.andExpression().isEmpty()) {
            return (ContextResult) visit(ctx.andExpression(0));
        }

        logger.warning("Empty OR expression");
        return null;
    }

    @Override
    public ContextResult visitAndExpression(EMJParser.AndExpressionContext ctx) {
        if (!ctx.AND().isEmpty()) {
            Map<String, Object> attributes = new HashMap<>();
            StringBuilder code = new StringBuilder();

            for (int i = 0; i < ctx.notExpression().size(); i++) {
                ContextResult exprResult = (ContextResult) visit(ctx.notExpression(i));
                code.append(exprResult.getAttributes().get("code"));

                if (i < ctx.notExpression().size() - 1) {
                    code.append(" and ");
                }
            }

            String andExpr = code.toString();
            logger.fine("Processing AND expression: " + andExpr);
            attributes.put("code", andExpr);
            return ContextResult.valid(attributes, "primaryExpression");
        } else if (!ctx.notExpression().isEmpty()) {
            return (ContextResult) visit(ctx.notExpression(0));
        }

        logger.warning("Empty AND expression");
        return null;
    }

    @Override
    public ContextResult visitNotExpression(EMJParser.NotExpressionContext ctx) {
        if (ctx.NOT() != null) {
            Map<String, Object> attributes = new HashMap<>();
            ContextResult exprResult = (ContextResult) visit(ctx.comparisonExpression());
            String notExpr = "not " + exprResult.getAttributes().get("code");

            logger.fine("Processing NOT expression: " + notExpr);
            attributes.put("code", notExpr);
            return ContextResult.valid(attributes, "notExpression");
        } else if (!ctx.comparisonExpression().isEmpty()) {
            return (ContextResult) visit(ctx.comparisonExpression());
        }

        logger.warning("Empty NOT expression");
        return null;
    }

    @Override
    public ContextResult visitComparisonExpression(EMJParser.ComparisonExpressionContext ctx) {
        if (ctx.DOUBLE_EQUAL() != null || ctx.NOTEQUAL() != null ||
                ctx.LESS() != null || ctx.LEQ() != null ||
                ctx.GREATER() != null || ctx.GEQ() != null) {
            Map<String, Object> attributes = new HashMap<>();
            StringBuilder code = new StringBuilder();

            // Left operand
            ContextResult leftResult = (ContextResult) visit(ctx.additiveExpression(0));
            code.append(leftResult.getAttributes().get("code"));

            // Operator
            String op;
            if (ctx.DOUBLE_EQUAL() != null) op = " == ";
            else if (ctx.NOTEQUAL() != null) op = " != ";
            else if (ctx.LESS() != null) op = " < ";
            else if (ctx.LEQ() != null) op = " <= ";
            else if (ctx.GREATER() != null) op = " > ";
            else if (ctx.GEQ() != null) op = " >= ";
            else op = " ? "; // Should never happen

            code.append(op);

            // Right operand
            ContextResult rightResult = (ContextResult) visit(ctx.additiveExpression(1));
            code.append(rightResult.getAttributes().get("code"));

            String compExpr = code.toString();
            logger.fine("Processing comparison expression: " + compExpr);
            attributes.put("code", compExpr);
            return ContextResult.valid(attributes, "primaryExpression");
        } else if (!ctx.additiveExpression().isEmpty()) {
            return (ContextResult) visit(ctx.additiveExpression(0));
        }

        logger.warning("Empty comparison expression");
        return null;
    }

    @Override
    public ContextResult visitAdditiveExpression(EMJParser.AdditiveExpressionContext ctx) {
        if (!ctx.PLUS().isEmpty() || !ctx.MINUS().isEmpty()) {
            Map<String, Object> attributes = new HashMap<>();
            StringBuilder code = new StringBuilder();

            for (int i = 0; i < ctx.multiplicativeExpression().size(); i++) {
                ContextResult exprResult = (ContextResult) visit(ctx.multiplicativeExpression(i));
                code.append(exprResult.getAttributes().get("code"));

                if (i < ctx.multiplicativeExpression().size() - 1) {
                    if (ctx.PLUS(i) != null) {
                        code.append(" + ");
                    } else {
                        code.append(" - ");
                    }
                }
            }

            String addExpr = code.toString();
            logger.fine("Processing additive expression: " + addExpr);
            attributes.put("code", addExpr);
            return ContextResult.valid(attributes, "additiveExpression");
        } else if (!ctx.multiplicativeExpression().isEmpty()) {
            return (ContextResult) visit(ctx.multiplicativeExpression(0));
        }

        logger.warning("Empty additive expression");
        return null;
    }

    @Override
    public ContextResult visitMultiplicativeExpression(EMJParser.MultiplicativeExpressionContext ctx) {
        if (!ctx.MULTIPLY().isEmpty() || !ctx.DIVIDE().isEmpty()) {
            Map<String, Object> attributes = new HashMap<>();
            StringBuilder code = new StringBuilder();

            for (int i = 0; i < ctx.unaryExpression().size(); i++) {
                ContextResult exprResult = (ContextResult) visit(ctx.unaryExpression(i));
                code.append(exprResult.getAttributes().get("code"));

                if (i < ctx.unaryExpression().size() - 1) {
                    if (ctx.MULTIPLY(i) != null) {
                        code.append(" * ");
                    } else {
                        code.append(" / ");
                    }
                }
            }

            String multExpr = code.toString();
            logger.fine("Processing multiplicative expression: " + multExpr);
            attributes.put("code", multExpr);
            return ContextResult.valid(attributes, "multiplicativeExpression");
        } else if (!ctx.unaryExpression().isEmpty()) {
            return (ContextResult) visit(ctx.unaryExpression(0));
        }

        logger.warning("Empty multiplicative expression");
        return null;
    }

    @Override
    public ContextResult visitUnaryExpression(EMJParser.UnaryExpressionContext ctx) {
        if (ctx.MINUS() != null) {
            Map<String, Object> attributes = new HashMap<>();
            ContextResult exprResult = (ContextResult) visit(ctx.primaryExpression());
            String unaryExpr = "-" + exprResult.getAttributes().get("code");

            logger.fine("Processing unary expression: " + unaryExpr);
            attributes.put("code", unaryExpr);
            return ContextResult.valid(attributes, "unaryExpression");
        } else {
            return (ContextResult) visit(ctx.primaryExpression());
        }
    }

    @Override
    public ContextResult visitPrimaryExpression(EMJParser.PrimaryExpressionContext ctx) {
        Map<String, Object> attributes = new HashMap<>();
        String code = "";

        if (ctx.INT_VALUE() != null) {
            code = ctx.INT_VALUE().getText();
            logger.fine("Processing integer literal: " + code);
        } else if (ctx.STRING_VALUE() != null) {
            code = ctx.STRING_VALUE().getText();
            logger.fine("Processing string literal: " + code);
        } else if (ctx.CHAR_VALUE() != null) {
            code = ctx.CHAR_VALUE().getText();
            logger.fine("Processing character literal: " + code);
        } else if (ctx.TRUE() != null) {
            code = "True";
            logger.fine("Processing boolean true literal");
        } else if (ctx.FALSE() != null) {
            code = "False";
            logger.fine("Processing boolean false literal");
        } else if (ctx.NOT() != null) {
            ContextResult exprResult = (ContextResult) visit(ctx.primaryExpression());
            code = "not " + exprResult.getAttributes().get("code");
            logger.fine("Processing NOT expression: " + code);
        } else if (ctx.tupleValue() != null) {
            ContextResult tupleResult = (ContextResult) visit(ctx.tupleValue());
            code = tupleResult.getAttributes().get("code").toString();
            logger.fine("Processing tuple value: " + code);
        } else if (ctx.EMOJI_ID() != null) {
            code = sanitizeEmoji(ctx.EMOJI_ID().getText());
            logger.fine("Processing emoji identifier: " + code);
        } else if (ctx.functionCall() != null) {
            ContextResult callResult = (ContextResult) visit(ctx.functionCall());
            code = callResult.getAttributes().get("code").toString();
            logger.fine("Processing function call: " + code);
        } else if (ctx.leftExpression() != null) {
            ContextResult leftResult = (ContextResult) visit(ctx.leftExpression());
            code = leftResult.getAttributes().get("code").toString();
            logger.fine("Processing left expression: " + code);
        } else if (ctx.expression() != null) {
            ContextResult exprResult = (ContextResult) visit(ctx.expression());
            code = "(" + exprResult.getAttributes().get("code") + ")";
            logger.fine("Processing parenthesized expression: " + code);
        }

        attributes.put("code", code);
        return ContextResult.valid(attributes, "primaryExpression");
    }

    @Override
    public ContextResult visitFunctionCall(EMJParser.FunctionCallContext ctx) {
        Map<String, Object> attributes = new HashMap<>();
        String indent = getIndent();

        // Function name
        String funcName = sanitizeEmoji(ctx.EMOJI_ID().getText());

        // Arguments
        StringBuilder args = new StringBuilder();
        if (ctx.argumentList() != null) {
            List<EMJParser.ExpressionContext> argCtxs = ctx.argumentList().expression();
            for (int i = 0; i < argCtxs.size(); i++) {
                ContextResult argResult = (ContextResult) visit(argCtxs.get(i));
                args.append(argResult.getAttributes().get("code"));
                if (i < argCtxs.size() - 1) {
                    args.append(", ");
                }
            }
        }

        String functionCall = String.format("%s%s(%s)", indent, funcName, args);
        logger.info("Processing function call: " + functionCall);
        attributes.put("code", functionCall);
        return ContextResult.valid(attributes, "primaryExpression");
    }

    @Override
    public ContextResult visitPredefinedStmt(EMJParser.PredefinedStmtContext ctx) {
        String indent = getIndent();
        String code  = "";
        String arg   = ctx.INT_VALUE() != null ? ctx.INT_VALUE().getText() : "";
        String stmtType = "";

        if (ctx.STOP_THIEF() != null) {                 // ✋()
            code = indent + "cuteBot.stopcar()";
            stmtType = "stop_thief";
        } else if (ctx.SOUND_TOGGLE() != null) {        // 📻()
            code = indent + "toggle_sound()";
            stmtType = "sound_toggle";
        } else if (ctx.LIGHT_TOGGLE() != null) {        // 🚨()
            code = indent + "toggle_light()";
            stmtType = "light_toggle";
        } else if (ctx.UP_ARROW() != null) {            // ⬆️(n)
            code = indent + "move_up(" + arg + ")";
            stmtType = "move_up";
        } else if (ctx.DOWN_ARROW() != null) {          // ⬇️(n)
            code = indent + "move_down(" + arg + ")";
            stmtType = "move_down";
        } else if (ctx.RIGHT_ARROW() != null) {         // ➡️(n)
            code = indent + "turn_right(" + arg + ")";
            stmtType = "turn_right";
        } else if (ctx.LEFT_ARROW() != null) {          // ⬅️(n)
            code = indent + "turn_left(" + arg + ")";
            stmtType = "turn_left";
        }

        logger.info("Processing predefined statement: " + stmtType + (arg.isEmpty() ? "" : " with arg " + arg));
        Map<String, Object> attributes = new HashMap<>();
        attributes.put("code", code);

        return ContextResult.valid(attributes, "predefinedStmt");
    }

    /**
     * Generate indentation for the current level
     */
    private String getIndent() {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < indentLevel; i++) {
            sb.append("    ");
        }
        return sb.toString();
    }

    @Override
    public String renderTemplate(ContextResult context) {
        logger.warning("renderTemplate method called but not implemented");
        return "";
    }

    @Override
    public void loadTemplates(String templateDir) {
        try {
            logger.info("Attempting to load templates from: " + templateDir);

            // Essai 1: Chemins relatifs par rapport au classpath
            this.templates = new STGroupFile(templateDir);
            if (this.templates == null || !this.templates.isDefined("mainFunction")) {
                // Essai 2: Avec slash au début pour ressources dans le classpath
                logger.fine("Try loading templates with leading slash: /" + templateDir);
                this.templates = new STGroupFile("/" + templateDir);
            }

            // Essai 3: Dossier templates dans les ressources
            if (this.templates == null || !this.templates.isDefined("mainFunction")) {
                logger.fine("Try loading templates from /templates/ directory: /templates/" + templateDir);
                this.templates = new STGroupFile("/templates/" + templateDir);
            }

            // Essai 4: Chemin absolu avec resources
            if (this.templates == null || !this.templates.isDefined("mainFunction")) {
                String resourcePath = "src/main/resources/" + templateDir;
                logger.fine("Try loading templates from resources directory: " + resourcePath);
                this.templates = new STGroupFile(resourcePath);
            }

            // Si toujours pas de templates valides, c'est une erreur
            if (this.templates == null || !this.templates.isDefined("mainFunction")) {
                logger.severe("Valid templates not found for path: " + templateDir);
                logger.severe("Available templates: " + (this.templates != null ? String.join(", ", this.templates.getTemplateNames()) : "none"));
                throw new IllegalStateException("Unable to load template: " + templateDir);
            }

            // Si on arrive ici, c'est que les templates sont chargés avec succès
            logger.info("Templates loaded successfully from: " + templateDir);
            logger.info("Available templates: " + String.join(", ", this.templates.getTemplateNames()));
        } catch (Exception e) {
            logger.log(Level.SEVERE, "Error loading templates: " + e.getMessage(), e);
            throw new IllegalStateException("Unable to load template: " + templateDir, e);
        }
    }

    @Override
    public String generateCode(ContextResult program) {
        if (!program.isValid()) {
            logger.severe("Error: Program is not valid.");
            return "# Code generation failed: invalid program";
        }

        String templateName = program.getTemplateName();
        logger.info("Generating code with template: " + templateName);

        // Vérifier que les templates sont chargés
        if (templates == null) {
            logger.severe("Error: Templates are not loaded.");
            return "# Code generation failed: templates not loaded";
        }

        ST template = templates.getInstanceOf(templateName);
        if (template == null) {
            logger.severe("Error: Template '" + templateName + "' not found.");
            logger.severe("Available templates: " + String.join(", ", templates.getTemplateNames()));
            return "# Template not found: " + templateName;
        }

        // Afficher les attributs pour débogage
        logger.fine("Program attributes:");
        for (Map.Entry<String, Object> entry : program.getAttributes().entrySet()) {
            String key = entry.getKey();
            Object value = entry.getValue();
            logger.fine("  - " + key + ": " + (value instanceof Collection ? "Collection of size " + ((Collection<?>) value).size() : value));

            try {
                template.add(key, value);
            } catch (Exception e) {
                logger.warning("Error adding attribute '" + key + "': " + e.getMessage());
            }
        }

        // S'assurer spécifiquement que l'attribut 'body' existe si nécessaire
        if (templateName.equals("program") && !program.getAttributes().containsKey("body")) {
            logger.warning("Warning: 'body' attribute is missing for 'program' template.");
        }

        try {
            String renderedCode = template.render();
            logger.info("Code generation successful!");
            return renderedCode;
        } catch (Exception e) {
            logger.log(Level.SEVERE, "Error rendering template '" + templateName + "'", e);
            return "# Code generation failed: " + e.getMessage();
        }
    }

    private String getTypeFromContext(EMJParser.TypeContext typeCtx) {
        if (typeCtx == null) return EMJVarType.UNKNOWN.pyLabel();
        if (typeCtx.INT_TYPE() != null) {
            return EMJVarType.INT.pyLabel();
        }
        if (typeCtx.BOOL_TYPE() != null) {
            return EMJVarType.BOOL.pyLabel();
        }
        if (typeCtx.CHAR_TYPE() != null) {
            return EMJVarType.CHAR.pyLabel();
        }
        if (typeCtx.STRING_TYPE() != null) {
            return EMJVarType.STRING.pyLabel();
        }
        if (typeCtx.tupleType() != null) {
            EMJParser.TupleTypeContext tupleCtx = typeCtx.tupleType();
            String innerType = getTypeFromContext(tupleCtx.type());
            if (innerType.equals(EMJVarType.UNKNOWN.pyLabel())) {
                return EMJVarType.UNKNOWN.pyLabel();//TODO : on autorise "Tuple(UNKNOWN)" ? si oui, enlever ce if
            }
            return String.format("%s(%s)", EMJVarType.TUPLE.pyLabel(), innerType);
        }
        return EMJVarType.UNKNOWN.pyLabel();
    }

    private String sanitizeEmoji(String emoji) {
        // Nettoyer l'emoji pour créer un nom de variable Python valide
        String rawName = emoji.replaceAll("[\\[\\]]", "");

        // Supprime les variation selectors (comme U+FE0F)
        String normalized = rawName.replaceAll("\\p{M}|\\uFE0F", "");

        if (emojiShortNames.containsKey(normalized)) {
            return emojiShortNames.get(normalized);
        }
        String parsedEmoji = EmojiParser.parseToAliases(emoji);
        parsedEmoji = parsedEmoji.replaceAll("\\W", "");
        return "emoji_" + parsedEmoji;
    }

    private void incrIndent() {
        this.indentLevel += 1;
        logger.fine("Incremented indent level to " + this.indentLevel);
    }

    private void decrIndent() throws IllegalStateException {
        if (this.indentLevel <= 0) {
            logger.severe("Attempted to decrement indent level below 0 (current: " + this.indentLevel + ")");
            throw new IllegalStateException(String.format("YOU SHALL NOT DECREMENT INDENT (indentLvl :%d)", this.indentLevel));
        }
        this.indentLevel -= 1;
        logger.fine("Decremented indent level to " + this.indentLevel);
    }
}