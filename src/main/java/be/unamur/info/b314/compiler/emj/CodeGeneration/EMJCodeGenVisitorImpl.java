package be.unamur.info.b314.compiler.emj.CodeGeneration;

import be.unamur.info.b314.compiler.EMJParser;
import be.unamur.info.b314.compiler.emj.EMJSymbolTable;
import be.unamur.info.b314.compiler.emj.Result.ContextResult;
import com.sun.org.apache.xalan.internal.xsltc.compiler.Template;
import org.antlr.v4.runtime.tree.AbstractParseTreeVisitor;
import org.stringtemplate.v4.ST;
import org.stringtemplate.v4.STGroup;
import org.stringtemplate.v4.STGroupFile;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class EMJCodeGenVisitorImpl extends AbstractParseTreeVisitor<ST> implements EMJCodeGenVisitor {
    private static final String LINE_BREAK = "\n";
    private static final String COMMA = ",";
    private final EMJSymbolTable symbolTable;
    private final Map<String, Template> templates;
    private final STGroup templateGroup;
    //private final Handlebars handlebars;

    public EMJCodeGenVisitorImpl(EMJSymbolTable symbolTable) {
        this.symbolTable = symbolTable;
        this.templates = new HashMap<>();
        templateGroup = new STGroupFile("micropython.stg");
    }

    @Override
    public ContextResult visitProgramFile(EMJParser.ProgramFileContext ctx) {
        ST programTemplate = templateGroup.getInstanceOf("program");
        //TODO
        return null;
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
//        return ContextResult.valid(null,"mainFunction"); //???? Comment ça marche ???
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
        blockSttTemplate.add("body",getStatementsAsStr(ctx.statement()));
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
    public ContextResult visitAssignment(EMJParser.AssignmentContext ctx) {
        return null;
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
    public ContextResult visitFunctionCall(EMJParser.FunctionCallContext ctx) {
        return null;
    }

    @Override
    public String renderTemplate(ContextResult context) {
        return "";
    }

    @Override
    public void loadTemplates(Map<String, String> templates) {

    }
}