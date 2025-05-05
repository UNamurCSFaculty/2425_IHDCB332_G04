package be.unamur.info.b314.compiler.emj.CodeGeneration;

import be.unamur.info.b314.compiler.EMJParser;
import be.unamur.info.b314.compiler.emj.Result.ContextResult;
import org.antlr.v4.runtime.tree.AbstractParseTreeVisitor;
import org.stringtemplate.v4.ST;
import org.stringtemplate.v4.STGroup;

import java.util.List;
import java.util.Map;

public class EMJCodeGenVisitorImpl extends AbstractParseTreeVisitor<ST> implements EMJCodeGenVisitor {
    private static final String LINE_BREAK = "\n";
    private static final String COMMA = ",";

    private final STGroup templateGroup;

    public EMJCodeGenVisitorImpl(STGroup templateGroup) {
        this.templateGroup = templateGroup;
    }

    @Override
    public ST visitProgramFile(EMJParser.ProgramFileContext ctx) {
        ST programTemplate = templateGroup.getInstanceOf("program");
        if (ctx.importStatement() != null) {
            programTemplate.add("importStt", visit(ctx.importStatement()).render());
        }
        programTemplate.add("mainFunction", visit(ctx.mainFunction()).render());
        if (ctx.functionDecl() != null && !ctx.functionDecl().isEmpty()) {
            StringBuilder functionsSb = new StringBuilder();
            for (EMJParser.FunctionDeclContext funct : ctx.functionDecl()) {
                ST funcCode = visit(funct);
                functionsSb.append(funcCode.render()).append(LINE_BREAK);
            }
            programTemplate.add("functions", functionsSb.toString());
        }
        if (ctx.statement() != null && !ctx.statement().isEmpty()) {
            programTemplate.add("statements", getStatementsAsStr(ctx.statement()));
        }
        return programTemplate;
    }

    @Override
    public ContextResult visitMapFile(EMJParser.MapFileContext ctx) {
        return null;
    }

    @Override
    public ST visitMainFunction(EMJParser.MainFunctionContext ctx) {
        ST mainTemplate = templateGroup.getInstanceOf("mainFunction");
        mainTemplate.add("body", getStatementsAsStr(ctx.statement()));
        return mainTemplate;
    }

    @Override
    public ST visitFunctionDecl(EMJParser.FunctionDeclContext ctx) {
        ST funcDeclTemplate = templateGroup.getInstanceOf("functionDecl");
        if (ctx.optionalParamList() != null && ctx.optionalParamList().paramList() != null) {
            StringBuilder sbParams = new StringBuilder();
            for (EMJParser.ParamContext param : ctx.optionalParamList().paramList().param()) {
                ST paramCode = visit(param);
                sbParams.append(paramCode.render()).append(COMMA);
            }
            funcDeclTemplate.add("params", sbParams.toString());
        }
        funcDeclTemplate.add("body", getStatementsAsStr(ctx.statement()));
        funcDeclTemplate.add("returnType", visit(ctx.returnStatement()).render());
        return funcDeclTemplate;
    }

    @Override
    public ContextResult visitVarDecl(EMJParser.VarDeclContext ctx) {
        ST varDeclTemplate = templateGroup.getInstanceOf("varDecl");
        varDeclTemplate.add("type", visit(ctx.type()).render());
        varDeclTemplate.add("n", ctx.EMOJI_ID());
        if (ctx.expression() != null) {
            ST expressionCode = visit(ctx.expression());
            varDeclTemplate.add("value", expressionCode.render());
        }
        return null;
    }

    @Override
    public ST visitBlock(EMJParser.BlockContext ctx) {
        ST blockSttTemplate = templateGroup.getInstanceOf("block");
        blockSttTemplate.add("body", getStatementsAsStr(ctx.statement()));
        return blockSttTemplate;
    }

    private String getStatementsAsStr(List<EMJParser.StatementContext> ctx) {
        StringBuilder sbStts = new StringBuilder();
        for (EMJParser.StatementContext a : ctx) {
            ST sttCode = visit(a);
            sbStts.append(sttCode.render()).append(LINE_BREAK);
        }
        return sbStts.toString();
    }

    @Override
    public ST visitIfStatement(EMJParser.IfStatementContext ctx) {
        ST ifSttTemplate = templateGroup.getInstanceOf("ifStatement");
        ifSttTemplate.add("condition", visit(ctx.expression()).render());
        ifSttTemplate.add("thenBlock", visit(ctx.block(0)).render());
        if (ctx.block().size() == 2) {
            ifSttTemplate.add("elseBlock", visit(ctx.block(1)).render());
        }
        return ifSttTemplate;
    }

    @Override
    public ST visitLoopStatement(EMJParser.LoopStatementContext ctx) {
        ST loopSttTemplate = templateGroup.getInstanceOf("loopStatement");
        loopSttTemplate.add("condition", visit(ctx.expression()).render());
        loopSttTemplate.add("block", visit(ctx.block()).render());
        return loopSttTemplate;
    }

    @Override
    public ST visitAssignment(EMJParser.AssignmentContext ctx) {
        ST assignmentTemplate = templateGroup.getInstanceOf("assignment");
        assignmentTemplate.add("leftExpression", visit(ctx.leftExpression()).render());
        assignmentTemplate.add("value", visit(ctx.expression()).render());
        return assignmentTemplate;
    }

    @Override
    public ContextResult visitExpression(EMJParser.ExpressionContext ctx) {
        return null;
    }

    @Override
    public ContextResult visitOrExpression(EMJParser.OrExpressionContext ctx) {
        return null;
    }

    @Override
    public ContextResult visitAndExpression(EMJParser.AndExpressionContext ctx) {
        return null;
    }

    @Override
    public ContextResult visitNotExpression(EMJParser.NotExpressionContext ctx) {
        return null;
    }

    @Override
    public ContextResult visitComparisonExpression(EMJParser.ComparisonExpressionContext ctx) {
        return null;
    }

    @Override
    public ContextResult visitAdditiveExpression(EMJParser.AdditiveExpressionContext ctx) {
        return null;
    }

    @Override
    public ContextResult visitMultiplicativeExpression(EMJParser.MultiplicativeExpressionContext ctx) {
        return null;
    }

    @Override
    public ContextResult visitUnaryExpression(EMJParser.UnaryExpressionContext ctx) {
        return null;
    }

    @Override
    public ContextResult visitPrimaryExpression(EMJParser.PrimaryExpressionContext ctx) {
        return null;
    }

    @Override
    public ST visitFunctionCall(EMJParser.FunctionCallContext ctx) {
        ST functionCallTemplate = templateGroup.getInstanceOf("loopStatement");
        functionCallTemplate.add("functionId", visit(ctx.EMOJI_ID()).render());
        if (ctx.argumentList() != null && !ctx.argumentList().isEmpty()) {
            StringBuilder argSb = new StringBuilder();
            for (EMJParser.ExpressionContext arg : ctx.argumentList().expression()) {
                ST argCode = visit(arg);
                argSb.append(argCode.render()).append(COMMA);
            }
            functionCallTemplate.add("argumentList", argSb.toString());
        }
        return functionCallTemplate;
    }

    @Override
    public String renderTemplate(ContextResult context) {
        return "";
    }

    @Override
    public void loadTemplates(Map<String, String> templates) {

    }
}