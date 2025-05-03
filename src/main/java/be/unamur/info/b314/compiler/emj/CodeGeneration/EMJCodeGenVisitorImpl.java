package be.unamur.info.b314.compiler.emj.CodeGeneration;

import be.unamur.info.b314.compiler.EMJParser;
import be.unamur.info.b314.compiler.emj.EMJSymbolTable;
import be.unamur.info.b314.compiler.emj.Result.ContextResult;
import com.sun.org.apache.xalan.internal.xsltc.compiler.Template;

import java.util.HashMap;
import java.util.Map;

public class EMJCodeGenVisitorImpl implements EMJCodeGenVisitor {
    private final EMJSymbolTable symbolTable;
    private final Map<String, Template> templates;
    //private final Handlebars handlebars;

    public EMJCodeGenVisitorImpl(EMJSymbolTable symbolTable) {
        this.symbolTable = symbolTable;
        this.templates = new HashMap<>();
        //this.handlebars = new Handlebars();
    }

    @Override
    public ContextResult visitProgramFile(EMJParser.ProgramFileContext ctx) {
        return null;
    }

    @Override
    public ContextResult visitMapFile(EMJParser.MapFileContext ctx) {
        return null;
    }

    @Override
    public ContextResult visitMainFunction(EMJParser.MainFunctionContext ctx) {
        return null;
    }

    @Override
    public ContextResult visitFunctionDecl(EMJParser.FunctionDeclContext ctx) {
        return null;
    }

    @Override
    public ContextResult visitVarDecl(EMJParser.VarDeclContext ctx) {
        return null;
    }

    @Override
    public ContextResult visitBlock(EMJParser.BlockContext ctx) {
        return null;
    }

    @Override
    public ContextResult visitIfStatement(EMJParser.IfStatementContext ctx) {
        return null;
    }

    @Override
    public ContextResult visitLoopStatement(EMJParser.LoopStatementContext ctx) {
        return null;
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