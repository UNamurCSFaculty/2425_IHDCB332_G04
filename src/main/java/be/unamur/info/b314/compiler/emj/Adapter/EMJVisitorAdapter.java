package be.unamur.info.b314.compiler.emj.Adapter;

import be.unamur.info.b314.compiler.EMJParser;
import be.unamur.info.b314.compiler.EMJParserBaseVisitor;
import be.unamur.info.b314.compiler.emj.CodeGeneration.EMJCodeGenVisitor;
import be.unamur.info.b314.compiler.emj.Semantic.EMJSemanticVisitor;

public class EMJVisitorAdapter<T> extends EMJParserBaseVisitor<T> {
    private final Object visitor;

    public EMJVisitorAdapter(Object visitor) {
        this.visitor = visitor;
    }

    @Override
    @SuppressWarnings("unchecked")
    public T visitProgramFile(EMJParser.ProgramFileContext ctx) {
        if (visitor instanceof EMJSemanticVisitor) {
            return (T) ((EMJSemanticVisitor) visitor).visitProgramFile(ctx);
        } else if (visitor instanceof EMJCodeGenVisitor) {
            return (T) ((EMJCodeGenVisitor) visitor).visitProgramFile(ctx);
        }
        throw new IllegalStateException("Unknown visitor type");
    }

    @Override
    @SuppressWarnings("unchecked")
    public T visitMainFunction(EMJParser.MainFunctionContext ctx) {
        if (visitor instanceof EMJSemanticVisitor) {
            return (T) ((EMJSemanticVisitor) visitor).visitMainFunction(ctx);
        } else if (visitor instanceof EMJCodeGenVisitor) {
            return (T) ((EMJCodeGenVisitor) visitor).visitMainFunction(ctx);
        }
        throw new IllegalStateException("Unknown visitor type");
    }

    @Override
    @SuppressWarnings("unchecked")
    public T visitFunctionDecl(EMJParser.FunctionDeclContext ctx) {
        if (visitor instanceof EMJSemanticVisitor) {
            return (T) ((EMJSemanticVisitor) visitor).visitFunctionDecl(ctx);
        } else if (visitor instanceof EMJCodeGenVisitor) {
            return (T) ((EMJCodeGenVisitor) visitor).visitFunctionDecl(ctx);
        }
        throw new IllegalStateException("Unknown visitor type");
    }

    @Override
    @SuppressWarnings("unchecked")
    public T visitVarDecl(EMJParser.VarDeclContext ctx) {
        if (visitor instanceof EMJSemanticVisitor) {
            return (T) ((EMJSemanticVisitor) visitor).visitVarDecl(ctx);
        } else if (visitor instanceof EMJCodeGenVisitor) {
            return (T) ((EMJCodeGenVisitor) visitor).visitVarDecl(ctx);
        }
        throw new IllegalStateException("Unknown visitor type");
    }

    @Override
    @SuppressWarnings("unchecked")
    public T visitExpression(EMJParser.ExpressionContext ctx) {
        if (visitor instanceof EMJSemanticVisitor) {
            return (T) ((EMJSemanticVisitor) visitor).visitExpression(ctx);
        } else if (visitor instanceof EMJCodeGenVisitor) {
            return (T) ((EMJCodeGenVisitor) visitor).visitExpression(ctx);
        }
        throw new IllegalStateException("Unknown visitor type");
    }

    @Override
    @SuppressWarnings("unchecked")
    public T visitOrExpression(EMJParser.OrExpressionContext ctx) {
        if (visitor instanceof EMJSemanticVisitor) {
            return (T) ((EMJSemanticVisitor) visitor).visitOrExpression(ctx);
        } else if (visitor instanceof EMJCodeGenVisitor) {
            return (T) ((EMJCodeGenVisitor) visitor).visitOrExpression(ctx);
        }
        throw new IllegalStateException("Unknown visitor type");
    }

    @Override
    @SuppressWarnings("unchecked")
    public T visitAndExpression(EMJParser.AndExpressionContext ctx) {
        if (visitor instanceof EMJSemanticVisitor) {
            return (T) ((EMJSemanticVisitor) visitor).visitAndExpression(ctx);
        } else if (visitor instanceof EMJCodeGenVisitor) {
            return (T) ((EMJCodeGenVisitor) visitor).visitAndExpression(ctx);
        }
        throw new IllegalStateException("Unknown visitor type");
    }

    @Override
    @SuppressWarnings("unchecked")
    public T visitNotExpression(EMJParser.NotExpressionContext ctx) {
        if (visitor instanceof EMJSemanticVisitor) {
            return (T) ((EMJSemanticVisitor) visitor).visitNotExpression(ctx);
        } else if (visitor instanceof EMJCodeGenVisitor) {
            return (T) ((EMJCodeGenVisitor) visitor).visitNotExpression(ctx);
        }
        throw new IllegalStateException("Unknown visitor type");
    }

    @Override
    @SuppressWarnings("unchecked")
    public T visitComparisonExpression(EMJParser.ComparisonExpressionContext ctx) {
        if (visitor instanceof EMJSemanticVisitor) {
            return (T) ((EMJSemanticVisitor) visitor).visitComparisonExpression(ctx);
        } else if (visitor instanceof EMJCodeGenVisitor) {
            return (T) ((EMJCodeGenVisitor) visitor).visitComparisonExpression(ctx);
        }
        throw new IllegalStateException("Unknown visitor type");
    }

    @Override
    @SuppressWarnings("unchecked")
    public T visitAdditiveExpression(EMJParser.AdditiveExpressionContext ctx) {
        if (visitor instanceof EMJSemanticVisitor) {
            return (T) ((EMJSemanticVisitor) visitor).visitAdditiveExpression(ctx);
        } else if (visitor instanceof EMJCodeGenVisitor) {
            return (T) ((EMJCodeGenVisitor) visitor).visitAdditiveExpression(ctx);
        }
        throw new IllegalStateException("Unknown visitor type");
    }

    @Override
    @SuppressWarnings("unchecked")
    public T visitMultiplicativeExpression(EMJParser.MultiplicativeExpressionContext ctx) {
        if (visitor instanceof EMJSemanticVisitor) {
            return (T) ((EMJSemanticVisitor) visitor).visitMultiplicativeExpression(ctx);
        } else if (visitor instanceof EMJCodeGenVisitor) {
            return (T) ((EMJCodeGenVisitor) visitor).visitMultiplicativeExpression(ctx);
        }
        throw new IllegalStateException("Unknown visitor type");
    }

    @Override
    @SuppressWarnings("unchecked")
    public T visitUnaryExpression(EMJParser.UnaryExpressionContext ctx) {
        if (visitor instanceof EMJSemanticVisitor) {
            return (T) ((EMJSemanticVisitor) visitor).visitUnaryExpression(ctx);
        } else if (visitor instanceof EMJCodeGenVisitor) {
            return (T) ((EMJCodeGenVisitor) visitor).visitUnaryExpression(ctx);
        }
        throw new IllegalStateException("Unknown visitor type");
    }

    @Override
    @SuppressWarnings("unchecked")
    public T visitPrimaryExpression(EMJParser.PrimaryExpressionContext ctx) {
        if (visitor instanceof EMJSemanticVisitor) {
            return (T) ((EMJSemanticVisitor) visitor).visitPrimaryExpression(ctx);
        } else if (visitor instanceof EMJCodeGenVisitor) {
            return (T) ((EMJCodeGenVisitor) visitor).visitPrimaryExpression(ctx);
        }
        throw new IllegalStateException("Unknown visitor type");
    }

    @Override
    @SuppressWarnings("unchecked")
    public T visitAssignment(EMJParser.AssignmentContext ctx) {
        if (visitor instanceof EMJSemanticVisitor) {
            return (T) ((EMJSemanticVisitor) visitor).visitAssignment(ctx);
        } else if (visitor instanceof EMJCodeGenVisitor) {
            return (T) ((EMJCodeGenVisitor) visitor).visitAssignment(ctx);
        }
        throw new IllegalStateException("Unknown visitor type");
    }

    @Override
    @SuppressWarnings("unchecked")
    public T visitFunctionCall(EMJParser.FunctionCallContext ctx) {
        if (visitor instanceof EMJSemanticVisitor) {
            return (T) ((EMJSemanticVisitor) visitor).visitFunctionCall(ctx);
        } else if (visitor instanceof EMJCodeGenVisitor) {
            return (T) ((EMJCodeGenVisitor) visitor).visitFunctionCall(ctx);
        }
        throw new IllegalStateException("Unknown visitor type");
    }

    @Override
    @SuppressWarnings("unchecked")
    public T visitIfStatement(EMJParser.IfStatementContext ctx) {
        if (visitor instanceof EMJSemanticVisitor) {
            return (T) ((EMJSemanticVisitor) visitor).visitIfStatement(ctx);
        } else if (visitor instanceof EMJCodeGenVisitor) {
            return (T) ((EMJCodeGenVisitor) visitor).visitIfStatement(ctx);
        }
        throw new IllegalStateException("Unknown visitor type");
    }

    @Override
    @SuppressWarnings("unchecked")
    public T visitLoopStatement(EMJParser.LoopStatementContext ctx) {
        if (visitor instanceof EMJSemanticVisitor) {
            return (T) ((EMJSemanticVisitor) visitor).visitLoopStatement(ctx);
        } else if (visitor instanceof EMJCodeGenVisitor) {
            return (T) ((EMJCodeGenVisitor) visitor).visitLoopStatement(ctx);
        }
        throw new IllegalStateException("Unknown visitor type");
    }

    @Override
    @SuppressWarnings("unchecked")
    public T visitBlock(EMJParser.BlockContext ctx) {
        if (visitor instanceof EMJSemanticVisitor) {
            return (T) ((EMJSemanticVisitor) visitor).visitBlock(ctx);
        } else if (visitor instanceof EMJCodeGenVisitor) {
            return (T) ((EMJCodeGenVisitor) visitor).visitBlock(ctx);
        }
        throw new IllegalStateException("Unknown visitor type");
    }

    @Override
    @SuppressWarnings("unchecked")
    public T visitMapFile(EMJParser.MapFileContext ctx) {
        if (visitor instanceof EMJSemanticVisitor) {
            return (T) ((EMJSemanticVisitor) visitor).visitMapFile(ctx);
        } else if (visitor instanceof EMJCodeGenVisitor) {
            return (T) ((EMJCodeGenVisitor) visitor).visitMapFile(ctx);
        }
        throw new IllegalStateException("Unknown visitor type");
    }
}
