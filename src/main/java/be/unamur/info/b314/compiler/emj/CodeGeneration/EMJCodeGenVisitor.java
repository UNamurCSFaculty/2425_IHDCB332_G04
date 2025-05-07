package be.unamur.info.b314.compiler.emj.CodeGeneration;

import be.unamur.info.b314.compiler.EMJParser;
import be.unamur.info.b314.compiler.emj.Result.ContextResult;

public interface EMJCodeGenVisitor {
    // Program structure
    ContextResult visitProgramFile(EMJParser.ProgramFileContext ctx);
    ContextResult visitMapFile(EMJParser.MapFileContext ctx);
    ContextResult visitMainFunction(EMJParser.MainFunctionContext ctx);

    // Declarations
    ContextResult visitFunctionDecl(EMJParser.FunctionDeclContext ctx);
    ContextResult visitParam(EMJParser.ParamContext ctx);
    ContextResult visitVarDecl(EMJParser.VarDeclContext ctx);

    // Statements
    ContextResult visitBlock(EMJParser.BlockContext ctx);
    ContextResult visitIfStatement(EMJParser.IfStatementContext ctx);
    ContextResult visitLoopStatement(EMJParser.LoopStatementContext ctx);
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
    String generateCode(ContextResult program);
    void loadTemplates(String templateDir);
}
