package be.unamur.info.b314.compiler.emj.CodeGeneration;

import be.unamur.info.b314.compiler.EMJParser;
import be.unamur.info.b314.compiler.EMJParserBaseVisitor;
import be.unamur.info.b314.compiler.emj.EMJVarType;
import be.unamur.info.b314.compiler.emj.Result.ContextResult;
import org.stringtemplate.v4.ST;
import org.stringtemplate.v4.STGroup;
import org.stringtemplate.v4.STGroupFile;

import java.util.*;

public class EMJCodeGenVisitorImpl extends EMJParserBaseVisitor<Object> implements EMJCodeGenVisitor {
    private STGroup templates;
    private Map<String, String> emojiToIdentifier;
    private int indentLevel = 0;
    private int loopCounter = 0;


    public EMJCodeGenVisitorImpl() {
    }


    private static final Map<String, String> emojiShortNames = new HashMap<>();

    static {
        emojiShortNames.put("🚗", "car");
        emojiShortNames.put("🦹", "thief");
        emojiShortNames.put("📻", "radio");
        emojiShortNames.put("🚨", "light");
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
        //emojiShortNames.put("🐜", "ant"); // si utilisé
        // Ajoute d'autres emojis si nécessaire
    }

    @Override
    public ContextResult visitProgramFile(EMJParser.ProgramFileContext ctx) {
        Map<String, Object> attributes = new HashMap<>();

        // Génère les instructions principales (ex-main)
        ContextResult mainResult = (ContextResult) visit(ctx.mainFunction());
        attributes.put("body", mainResult.getAttributes().get("body")); // note : body est une List<String>

        // Génère les fonctions utilisateur
        List<String> renderedFunctions = new ArrayList<>();
        if (ctx.functionDecl() != null) {
            for (EMJParser.FunctionDeclContext funcCtx : ctx.functionDecl()) {

                incrIndent();
                ContextResult funcResult = (ContextResult) visit(funcCtx);
                decrIndent();

                ST funcTemplate = templates.getInstanceOf(funcResult.getTemplateName());
                for (Map.Entry<String, Object> entry : funcResult.getAttributes().entrySet()) {
                    funcTemplate.add(entry.getKey(), entry.getValue());
                }
                renderedFunctions.add(funcTemplate.render());
            }
        }
        attributes.put("functions", renderedFunctions);

        return ContextResult.valid(attributes, "program");
    }

    @Override
    public ContextResult visitMapFile(EMJParser.MapFileContext ctx) {
        Map<String, Object> attributes = new HashMap<>();

        int width = Integer.parseInt(ctx.INT_VALUE(0).getText());
        int height = Integer.parseInt(ctx.INT_VALUE(1).getText());

        // Nettoie l'orientation (⬆️ -> up, etc.)
        String orientation = sanitizeEmoji(ctx.orientation().getText());

        // Construction des lignes de la carte
        List<String> mapLines = new ArrayList<>();
        int index = 0;
        for (int i = 0; i < height; i++) {
            StringBuilder row = new StringBuilder();
            for (int j = 0; j < width; j++) {
                EMJParser.MapCellContext cellCtx = ctx.mapCell(index++);
                String emoji = cellCtx.getText();
                String cleaned = emojiShortNames.getOrDefault(emoji, "unknown");
                row.append(cleaned);
            }
            mapLines.add("\"" + row.toString() + "\"");
        }

        attributes.put("width", width);
        attributes.put("height", height);
        attributes.put("orientation", orientation);
        attributes.put("map", mapLines); // List<String>, dans le template avec wrap="\""

        return ContextResult.valid(attributes, "map_program");
    }

    @Override
    public ContextResult visitMainFunction(EMJParser.MainFunctionContext ctx) {
        Map<String, Object> attributes = new HashMap<>();

        // Visit all statements and render them
        List<String> renderedStatements = new ArrayList<>();
        for (EMJParser.StatementContext stmtCtx : ctx.statement()) {
            ContextResult stmtResult = (ContextResult) visit(stmtCtx);

            System.out.println("Statement type: " + stmtResult.getTemplateName());
            System.out.println("Attributes: " + stmtResult.getAttributes().keySet());

            renderedStatements.add(renderResult(stmtResult));
        }

        attributes.put("body", renderedStatements);
        return ContextResult.valid(attributes, "main_function");

    }

    private String renderResult(ContextResult result) {
        if (!result.isValid()) {
            return "";
        }

        ST template = templates.getInstanceOf(result.getTemplateName());
        if (template == null) {
            return "# Template not found: " + result.getTemplateName();
        }

        for (Map.Entry<String, Object> entry : result.getAttributes().entrySet()) {
            template.add(entry.getKey(), entry.getValue());
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
        } else if (ctx.returnStatement() != null) {
            // tu peux gérer plus tard si tu veux générer du code Python avec return
            return ContextResult.invalid(); // ou visite réelle si tu veux
        } else if (ctx.predefinedStmt() != null) {
            return (ContextResult) visit(ctx.predefinedStmt()); // à implémenter si nécessaire
        }

        return ContextResult.invalid();
    }

    @Override
    public ContextResult visitFunctionDecl(EMJParser.FunctionDeclContext ctx) {
        Map<String, Object> attributes = new HashMap<>();
        List<String> parameters = new ArrayList<>();
        List<String> bodyLines = new ArrayList<>();

        String varName = sanitizeEmoji(ctx.EMOJI_ID().getText());
        attributes.put("name", varName);

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

        ContextResult returnStmtResult = (ContextResult) visit(ctx.returnStatement());
        attributes.put("return", returnStmtResult.getAttributes().values());

        return ContextResult.valid(attributes, "functionDecl");
    }

    @Override
    public ContextResult visitReturnStatement(EMJParser.ReturnStatementContext ctx) {
        Map<String, Object> attributes = new HashMap<>();

        // Check if it's a void return
        if (ctx.VOID_TYPE() != null || ctx.RETURN_VOID() != null || ctx.expression() == null) {
            attributes.put("value", "None");
        } else {
            // Visit the expression
            ContextResult exprResult = (ContextResult) visit(ctx.expression());
            attributes.put("value", exprResult.getAttributes().get("code"));
        }

        return ContextResult.valid(attributes, "return");
    }

    @Override
    public ContextResult visitParam(EMJParser.ParamContext ctx) {
        Map<String, Object> attributes = new HashMap<>();

        String varName = sanitizeEmoji(ctx.EMOJI_ID().getText());
        attributes.put("name", varName);
        return ContextResult.valid(attributes, "parameter");
    }

    @Override
    public ContextResult visitVarDecl(EMJParser.VarDeclContext ctx) {
        Map<String, Object> attributes = new HashMap<>();

        String varName = sanitizeEmoji(ctx.EMOJI_ID().getText());
        attributes.put("name", varName);

        // Obtenir le type
        String typeResult = getTypeFromContext(ctx.type());
        attributes.put("type", typeResult);

        // Gérer la valeur initiale
        if (ctx.expression() != null) {
            ContextResult exprResult = (ContextResult) visit(ctx.expression());
            attributes.put("value", exprResult.getAttributes().get("code"));
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
        }

        attributes.put("indent", getIndent());
        return ContextResult.valid(attributes, "varDecl");
    }

    @Override
    public ContextResult visitBlock(EMJParser.BlockContext ctx) {
//        ContextResult blockSttTemplate = templateGroup.getInstanceOf("block");
//        blockSttTemplate.add("body", getStatementsAsStr(ctx.statement()));
//        return blockSttTemplate;
        return null;
    }

    @Override
    public ContextResult visitIfStatement(EMJParser.IfStatementContext ctx) {
//        ST ifSttTemplate = templateGroup.getInstanceOf("ifStatement");
//        ifSttTemplate.add("condition", visit(ctx.expression()).render());
//        ifSttTemplate.add("thenBlock", visit(ctx.block(0)).render());
//        if (ctx.block().size() == 2) {
//            ifSttTemplate.add("elseBlock", visit(ctx.block(1)).render());
//        }
//        return ifSttTemplate;
        return null;
    }

    @Override
    public ContextResult visitLoopStatement(EMJParser.LoopStatementContext ctx) {
//        ST loopSttTemplate = templateGroup.getInstanceOf("loopStatement");
//        loopSttTemplate.add("condition", visit(ctx.expression()).render());
//        loopSttTemplate.add("block", visit(ctx.block()).render());
//        return loopSttTemplate;
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
        } else if (ctx.TUPLE_SECOND() != null) {
            attributes.put("code", varName + "[1]");
        } else {
            attributes.put("code", varName);
        }

        return ContextResult.valid(attributes, "left_expression");
    }


    @Override
    public ContextResult visitAssignment(EMJParser.AssignmentContext ctx) {
        Map<String, Object> attributes = new HashMap<>();

        // Left expression
        ContextResult leftResult = (ContextResult) visit(ctx.leftExpression());
        attributes.put("left", leftResult.getAttributes().get("code"));

        // Right expression
        ContextResult rightResult = (ContextResult) visit(ctx.expression());
        attributes.put("right", rightResult.getAttributes().get("code"));

        attributes.put("indent", getIndent());
        return ContextResult.valid(attributes,"assignment");
    }

    @Override
    public ContextResult visitExpression(EMJParser.ExpressionContext ctx) {
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

            attributes.put("code", code.toString());
            return ContextResult.valid(attributes, "primary_expression");
        } else if (!ctx.andExpression().isEmpty()) {
            return (ContextResult) visit(ctx.andExpression(0));
        }

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

            attributes.put("code", code.toString());
            return ContextResult.valid(attributes, "primary_expression");
        } else if (!ctx.notExpression().isEmpty()) {
            return (ContextResult) visit(ctx.notExpression(0));
        }

        return null;
    }

    @Override
    public ContextResult visitNotExpression(EMJParser.NotExpressionContext ctx) {
        if (ctx.NOT() != null) {
            Map<String, Object> attributes = new HashMap<>();
            ContextResult exprResult = (ContextResult) visit(ctx.comparisonExpression());
            attributes.put("code", "not " + exprResult.getAttributes().get("code"));

            return ContextResult.valid(attributes, "not_expression");
        } else if (!ctx.comparisonExpression().isEmpty()) {
            return (ContextResult) visit(ctx.comparisonExpression());
        }

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

            attributes.put("code", code.toString());
            return ContextResult.valid(attributes, "primaryExpression");
        } else if (!ctx.additiveExpression().isEmpty()) {
            return (ContextResult) visit(ctx.additiveExpression(0));
        }
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
            attributes.put("code", code.toString());
            return ContextResult.valid(attributes, "additiveExpression");
        } else if (!ctx.multiplicativeExpression().isEmpty()) {
            return (ContextResult) visit(ctx.multiplicativeExpression(0));
        }
        return null;
    }

    @Override
    public ContextResult visitMultiplicativeExpression(EMJParser.MultiplicativeExpressionContext ctx) {
        if (!ctx.MULTIPLY().isEmpty() || !ctx.DIVIDE().isEmpty()) {
            Map<String, Object> attributes = new HashMap<>();
            ContextResult leftExprResult = (ContextResult) visit(ctx.unaryExpression(0));
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

            attributes.put("code", code.toString());
            return ContextResult.valid(attributes, "multiplicativeExpression");
        } else if (ctx.unaryExpression().size() == 1) {
            return (ContextResult) visit(ctx.unaryExpression(0));
        }
        return null;
    }

    @Override
    public ContextResult visitUnaryExpression(EMJParser.UnaryExpressionContext ctx) {
        if (ctx.MINUS() != null) {
            Map<String, Object> attributes = new HashMap<>();
            ContextResult exprResult = (ContextResult) visit(ctx.primaryExpression());
            attributes.put("code", "-" + exprResult.getAttributes().get("code"));
            return ContextResult.valid(attributes, "unaryExpression");
        } else {
            return (ContextResult) visit(ctx.primaryExpression());
        }
    }

    @Override
    public ContextResult visitPrimaryExpression(EMJParser.PrimaryExpressionContext ctx) {
        Map<String, Object> attributes = new HashMap<>();
        if (ctx.INT_VALUE() != null) {
            attributes.put("code", ctx.INT_VALUE().getText());
        } else if (ctx.STRING_VALUE() != null) {
            attributes.put("code", ctx.STRING_VALUE().getText());
        } else if (ctx.CHAR_VALUE() != null) {
            attributes.put("code", ctx.CHAR_VALUE().getText());
        } else if (ctx.TRUE() != null) {
            attributes.put("code", "True");
        } else if (ctx.FALSE() != null) {
            attributes.put("code", "False");
        } else if (ctx.NOT() != null) {
            ContextResult exprResult = (ContextResult) visit(ctx.primaryExpression());
            attributes.put("code", "not " + exprResult.getAttributes().get("code"));
        } else if (ctx.tupleValue() != null) {
            ContextResult tupleResult = (ContextResult) visit(ctx.tupleValue());
            attributes.put("code", tupleResult.getAttributes().get("code"));
        } else if (ctx.EMOJI_ID() != null) {
            attributes.put("code", sanitizeEmoji(ctx.EMOJI_ID().getText()));
        } else if (ctx.functionCall() != null) {
            ContextResult callResult = (ContextResult) visit(ctx.functionCall());
            attributes.put("code", callResult.getAttributes().get("code"));
        } else if (ctx.leftExpression() != null) {
            ContextResult leftResult = (ContextResult) visit(ctx.leftExpression());
            attributes.put("code", leftResult.getAttributes().get("code"));
        } else if (ctx.expression() != null) {
            ContextResult exprResult = (ContextResult) visit(ctx.expression());
            attributes.put("code", "(" + exprResult.getAttributes().get("code") + ")");
        }
        return ContextResult.valid(attributes, "primaryExpression");
    }

    @Override
    public ContextResult visitFunctionCall(EMJParser.FunctionCallContext ctx) {
        Map<String, Object> attributes = new HashMap<>();

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

        attributes.put("code", funcName + "(" + args + ")");
        return ContextResult.valid(attributes, "primaryExpression");
    }

    @Override
    public String renderTemplate(ContextResult context) {
        return "";
    }


    @Override
    public void loadTemplates(String template) {
        this.templates = new STGroupFile(template);
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
    public String generateCode(ContextResult program) {
        if (!program.isValid()) {
            return "# Code generation failed";
        }

        ST template = templates.getInstanceOf(program.getTemplateName());
        if (template == null) {
            return "# Template not found: " + program.getTemplateName();
        }

        for (Map.Entry<String, Object> entry : program.getAttributes().entrySet()) {
            template.add(entry.getKey(), entry.getValue());
        }

        return template.render();
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
        return "emoji_" + Math.abs(emoji.hashCode());
    }

    private void incrIndent() {
        this.indentLevel += 1;
    }

    private void decrIndent() throws IllegalStateException {
        if (this.indentLevel <= 0) {
            throw new IllegalStateException(String.format("YOU SHALL NOT DECREMENT INDENT (indentLvl :%d)", this.indentLevel));
        }
        this.indentLevel -= 1;
    }
}