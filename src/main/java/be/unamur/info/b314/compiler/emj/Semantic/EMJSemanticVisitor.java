package be.unamur.info.b314.compiler.emj.Semantic;

import be.unamur.info.b314.compiler.EMJParser;
import be.unamur.info.b314.compiler.emj.EMJErrorLogger;
import be.unamur.info.b314.compiler.emj.EMJSymbolTable;
import be.unamur.info.b314.compiler.emj.Result.TypeResult;
import be.unamur.info.b314.compiler.emj.Result.VoidResult;

public interface EMJSemanticVisitor {
    // Program structure
    VoidResult visitProgramFile(EMJParser.ProgramFileContext ctx);
    VoidResult visitMapFile(EMJParser.MapFileContext ctx);
    VoidResult visitMainFunction(EMJParser.MainFunctionContext ctx);

    // Declarations
    VoidResult visitFunctionDecl(EMJParser.FunctionDeclContext ctx);
    VoidResult visitVarDecl(EMJParser.VarDeclContext ctx);

    // Statements
    VoidResult visitBlock(EMJParser.BlockContext ctx);
    VoidResult visitIfStatement(EMJParser.IfStatementContext ctx);
    VoidResult visitLoopStatement(EMJParser.LoopStatementContext ctx);
    VoidResult visitAssignment(EMJParser.AssignmentContext ctx);

    // Expressions (return types)
    TypeResult visitExpression(EMJParser.ExpressionContext ctx);
    TypeResult visitOrExpression(EMJParser.OrExpressionContext ctx);
    TypeResult visitAndExpression(EMJParser.AndExpressionContext ctx);
    TypeResult visitNotExpression(EMJParser.NotExpressionContext ctx);
    TypeResult visitComparisonExpression(EMJParser.ComparisonExpressionContext ctx);
    TypeResult visitAdditiveExpression(EMJParser.AdditiveExpressionContext ctx);
    TypeResult visitMultiplicativeExpression(EMJParser.MultiplicativeExpressionContext ctx);
    TypeResult visitUnaryExpression(EMJParser.UnaryExpressionContext ctx);
    TypeResult visitPrimaryExpression(EMJParser.PrimaryExpressionContext ctx);
    TypeResult visitFunctionCall(EMJParser.FunctionCallContext ctx);

    // Utility methods
    EMJErrorLogger getErrorLogger();
    EMJSymbolTable getSymbolTable();
}
