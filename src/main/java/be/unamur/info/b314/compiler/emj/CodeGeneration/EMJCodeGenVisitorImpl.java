package be.unamur.info.b314.compiler.emj.CodeGeneration;

import be.unamur.info.b314.compiler.EMJParser;
import be.unamur.info.b314.compiler.EMJParserBaseVisitor;
import be.unamur.info.b314.compiler.emj.EMJSymbolTable;
import be.unamur.info.b314.compiler.emj.EMJVarType;
import be.unamur.info.b314.compiler.emj.Result.ContextResult;
import org.stringtemplate.v4.ST;
import org.stringtemplate.v4.STGroup;
import org.stringtemplate.v4.STGroupFile;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class EMJCodeGenVisitorImpl extends EMJParserBaseVisitor<Object> implements EMJCodeGenVisitor {
    private STGroup templates;
    private Map<String, String> emojiToIdentifier;
    private int indentLevel = 0;
    private int loopCounter = 0;


    public EMJCodeGenVisitorImpl() {
    }

    @Override
    public ContextResult visitProgramFile(EMJParser.ProgramFileContext ctx) {
        Map<String, Object> attributes = new HashMap<>();


//        if (ctx.importStatement() != null) {
//            programTemplate.add("importStt", visit(ctx.importStatement()).render());
//        }
//        programTemplate.add("mainFunction", visit(ctx.mainFunction()).render());
        // Main function
        ContextResult mainResult = (ContextResult) visit(ctx.mainFunction());
        attributes.put("main", mainResult.getAttributes());

        // function
        if (ctx.functionDecl() != null && !ctx.functionDecl().isEmpty()) {
            List<Object> functions = new ArrayList<>();
            for (EMJParser.FunctionDeclContext funcCtx : ctx.functionDecl()) {
                ContextResult funcResult = (ContextResult) visit(funcCtx);
                functions.add(funcResult.getAttributes());
            }
            attributes.put("functions", functions);
        }

        return ContextResult.valid(attributes, "program");
    }

    @Override
    public ContextResult visitMapFile(EMJParser.MapFileContext ctx) {
        return null;
    }

    @Override
    public ContextResult visitMainFunction(EMJParser.MainFunctionContext ctx) {
        Map<String, Object> attributes = new HashMap<>();
        // Visit all statements in the main function
        List<ContextResult> statementResults = new ArrayList<>();
        for (EMJParser.StatementContext stmtCtx : ctx.statement()) {
            statementResults.add((ContextResult) visit(stmtCtx));
        }

        // Combine the statements
        ContextResult bodyResult = ContextResult.combine("block", statementResults, "statements");
        attributes.put("body", bodyResult.getAttributes().get("statements"));

        return ContextResult.valid(attributes, "main_function");
    }
    @Override
    public ContextResult visitStatement(EMJParser.StatementContext ctx)
    {
        return (ContextResult) visit(ctx.varDecl());
    }
    @Override
    public ContextResult visitFunctionDecl(EMJParser.FunctionDeclContext ctx) {
//        ST funcDeclTemplate = templateGroup.getInstanceOf("functionDecl");
//        if (ctx.optionalParamList() != null && ctx.optionalParamList().paramList() != null) {
//            StringBuilder sbParams = new StringBuilder();
//            for (EMJParser.ParamContext param : ctx.optionalParamList().paramList().param()) {
//                ST paramCode = visit(param);
//                sbParams.append(paramCode.render()).append(COMMA);
//            }
//            funcDeclTemplate.add("params", sbParams.toString());
//        }
//        funcDeclTemplate.add("body", getStatementsAsStr(ctx.statement()));
//        funcDeclTemplate.add("returnType", visit(ctx.returnStatement()).render());
//        return funcDeclTemplate;
        return null;
    }

    @Override
    public ContextResult visitVarDecl(EMJParser.VarDeclContext ctx) {
        Map<String, Object> attributes = new HashMap<>();


        // Get variable name
        String varName = (ctx.EMOJI_ID().getText());
        attributes.put("name", varName);

        // Get variable type
        String typeResult = getTypeFromContext(ctx.type());
        attributes.put("type", getTypeFromContext(ctx.type()));

        // Get initial value if present
        if (ctx.expression() != null) {
            ContextResult exprResult = (ContextResult) visit(ctx.expression());
            attributes.put("value", exprResult.getAttributes().get("code"));
        } else {
            // Default values based on type
            String type = typeResult;
            switch (type) {
                case "int":
                    attributes.put("value", "0");
                    break;
                case "bool":
                    attributes.put("value", "False");
                    break;
                case "str":
                    attributes.put("value", "\"\"");
                    break;
                case "char":
                    attributes.put("value", "\"\"");
                    break;
                default:
                    if (type.startsWith("tuple")) {
                        attributes.put("value", "(None, None)");
                    } else {
                        attributes.put("value", "None");
                    }
            }
        }

        attributes.put("indent", getIndent());
        return ContextResult.valid(attributes, "var_decl");
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
    public ContextResult visitAssignment(EMJParser.AssignmentContext ctx) {
//        ST assignmentTemplate = templateGroup.getInstanceOf("assignment");
//        assignmentTemplate.add("leftExpression", visit(ctx.leftExpression()).render());
//        assignmentTemplate.add("value", visit(ctx.expression()).render());
//        return assignmentTemplate;
        return null;
    }

    @Override
    public ContextResult visitExpression(EMJParser.ExpressionContext ctx) {
        return (ContextResult) visit(ctx.orExpression());
    }

    @Override
    public ContextResult visitOrExpression(EMJParser.OrExpressionContext ctx) {
        if (ctx.andExpression().size() == 1) {
            return (ContextResult) visit(ctx.andExpression(0));
        }
        return null;
    }

    @Override
    public ContextResult visitAndExpression(EMJParser.AndExpressionContext ctx) {
        if (ctx.notExpression().size() == 1) {
            return (ContextResult) visit(ctx.notExpression(0));
        }

        return null;
    }

    @Override
    public ContextResult visitNotExpression(EMJParser.NotExpressionContext ctx) {
        if (ctx.NOT() == null) {
            return (ContextResult) visit(ctx.comparisonExpression());
        }

        return null;
    }

    @Override
    public ContextResult visitComparisonExpression(EMJParser.ComparisonExpressionContext ctx) {
        if (ctx.additiveExpression().size() == 1) {
            return (ContextResult) visit(ctx.additiveExpression(0));
        }
        return null;
    }

    @Override
    public ContextResult visitAdditiveExpression(EMJParser.AdditiveExpressionContext ctx) {
        if (ctx.multiplicativeExpression().size() == 1) {
            return (ContextResult) visit(ctx.multiplicativeExpression(0));
        }
        return null;
    }

    @Override
    public ContextResult visitMultiplicativeExpression(EMJParser.MultiplicativeExpressionContext ctx) {
        if (ctx.unaryExpression().size() == 1) {
            return (ContextResult) visit(ctx.unaryExpression(0));
        }
        return null;
    }

    @Override
    public ContextResult visitUnaryExpression(EMJParser.UnaryExpressionContext ctx) {
        if (ctx.MINUS() == null) {
            return (ContextResult) visit(ctx.primaryExpression());
        }
        return null;
    }

    @Override
    public ContextResult visitPrimaryExpression(EMJParser.PrimaryExpressionContext ctx) {
        Map<String, Object> attributes = new HashMap<>();
        if (ctx.INT_VALUE() != null) {
            attributes.put("code", ctx.INT_VALUE().getText());
        }
        return ContextResult.valid(attributes, "primary_expression");
    }
    @Override
    public ContextResult visitFunctionCall(EMJParser.FunctionCallContext ctx) {
//        ST functionCallTemplate = templateGroup.getInstanceOf("loopStatement");
//        functionCallTemplate.add("functionId", visit(ctx.EMOJI_ID()).render());
//        if (ctx.argumentList() != null && !ctx.argumentList().isEmpty()) {
//            StringBuilder argSb = new StringBuilder();
//            for (EMJParser.ExpressionContext arg : ctx.argumentList().expression()) {
//                ST argCode = visit(arg);
//                argSb.append(argCode.render()).append(COMMA);
//            }
//            functionCallTemplate.add("argumentList", argSb.toString());
//        }
//        return functionCallTemplate;
        return null;
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
        if (typeCtx == null) return EMJVarType.UNKNOWN.label();
        if (typeCtx.INT_TYPE() != null) {
            return EMJVarType.INT.label();
        }
        if (typeCtx.BOOL_TYPE() != null) {
            return EMJVarType.BOOL.label();
        }
        if (typeCtx.CHAR_TYPE() != null) {
            return EMJVarType.CHAR.label();
        }
        if (typeCtx.STRING_TYPE() != null) {
            return EMJVarType.STRING.label();
        }
        if (typeCtx.tupleType() != null) {
            EMJParser.TupleTypeContext tupleCtx = typeCtx.tupleType();
            String innerType = getTypeFromContext(tupleCtx.type());
            if (innerType.equals(EMJVarType.UNKNOWN.label())) {
                return EMJVarType.UNKNOWN.label();//TODO : on autorise "Tuple(UNKNOWN)" ? si oui, enlever ce if
            }
            return String.format("%s(%s)", EMJVarType.TUPLE.label(), innerType);
        }
        return EMJVarType.UNKNOWN.label();
    }
}