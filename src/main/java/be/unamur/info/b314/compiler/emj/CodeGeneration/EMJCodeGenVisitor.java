package be.unamur.info.b314.compiler.emj.CodeGeneration;

import be.unamur.info.b314.compiler.EMJParser;
import be.unamur.info.b314.compiler.emj.Result.ContextResult;
import org.stringtemplate.v4.ST;

import java.util.Map;

public interface EMJCodeGenVisitor {
    // Program structure
    ContextResult visitProgramFile(EMJParser.ProgramFileContext ctx);
    ContextResult visitMapFile(EMJParser.MapFileContext ctx);
    ST visitMainFunction(EMJParser.MainFunctionContext ctx);

    // Declarations
    ST visitFunctionDecl(EMJParser.FunctionDeclContext ctx);
    ContextResult visitVarDecl(EMJParser.VarDeclContext ctx);

    // Statements
    ST visitBlock(EMJParser.BlockContext ctx);
    ST visitIfStatement(EMJParser.IfStatementContext ctx);
    ST visitLoopStatement(EMJParser.LoopStatementContext ctx);
    ContextResult visitAssignment(EMJParser.AssignmentContext ctx);

    // Expressions
    ContextResult visitExpression(EMJParser.ExpressionContext ctx);
    ContextResult visitOrExpression(EMJParser.OrExpressionContext ctx);
    ContextResult visitAndExpression(EMJParser.AndExpressionContext ctx);
    ContextResult visitNotExpression(EMJParser.NotExpressionContext ctx);
    ContextResult visitComparisonExpression(EMJParser.ComparisonExpressionContext ctx);
    ContextResult visitAdditiveExpression(EMJParser.AdditiveExpressionContext ctx);
    ContextResult visitMultiplicativeExpression(EMJParser.MultiplicativeExpressionContext ctx);
    ContextResult visitUnaryExpression(EMJParser.UnaryExpressionContext ctx);
    ContextResult visitPrimaryExpression(EMJParser.PrimaryExpressionContext ctx);
    ContextResult visitFunctionCall(EMJParser.FunctionCallContext ctx);

    // Template rendering
    String renderTemplate(ContextResult context);
    void loadTemplates(Map<String, String> templates);
}
