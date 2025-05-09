package be.unamur.info.b314.compiler.emj.Semantic;

import be.unamur.info.b314.compiler.EMJParser;
import be.unamur.info.b314.compiler.EMJParserBaseVisitor;
import be.unamur.info.b314.compiler.emj.*;
import be.unamur.info.b314.compiler.emj.Result.TypeResult;
import be.unamur.info.b314.compiler.emj.Result.VoidResult;

import java.io.File;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class EMJSemanticVisitorImpl extends EMJParserBaseVisitor<Object> implements EMJSemanticVisitor {

    private final EMJErrorLogger errorLogger;
    private final EMJSymbolTable symbolTable;
    private String sourceFilePath; // Chemin du fichier source

    /**
     * Constructeur par défaut
     * @effects this_post.errorLogger = new EMJErrorLogger()
     *          this_post.symbolTable = new EMJSymbolTable()
     */
    public EMJSemanticVisitorImpl() {
        this.errorLogger = new EMJErrorLogger();
        this.symbolTable = new EMJSymbolTable();
        this.sourceFilePath = null;
    }
    
    /**
     * Définit le chemin du fichier source
     * @param sourceFilePath Chemin du fichier source
     */
    public void setSourceFilePath(String sourceFilePath) {
        this.sourceFilePath = sourceFilePath;
    }

    /**
     * Retourne le logger d'erreurs utilisé par ce visiteur
     * @return this.errorLogger
     */
    public EMJErrorLogger getErrorLogger() {
        return this.errorLogger;
    }

    @Override
    public EMJSymbolTable getSymbolTable() {
        return this.symbolTable;
    }

    /**
     * Visite le fichier de programme principal
     *
     * @param ctx Contexte du fichier programme
     * @return VoidResult
     * @requires ctx != null
     * @effects visite chaque déclaration de fonction dans le fichier
     * vérifie que la fonction main existe et est du bon type
     */
    @Override
    public VoidResult visitProgramFile(EMJParser.ProgramFileContext ctx) {
        // Vérifier l'importation de carte si présente
        if (ctx.importStatement() != null) {
            visitImportStatement(ctx.importStatement());
        }
        
        for (EMJParser.FunctionDeclContext functionDeclContext : ctx.functionDecl()) {
            visitFunctionDecl(functionDeclContext);
        }

        for (EMJParser.FunctionDeclContext functionDeclContext : ctx.functionDecl()) {
            if (!checkDeclaration(functionDeclContext)) {
                return VoidResult.valid();
            }
        }

        if (ctx.mainFunction() == null) {
            errorLogger.addError(new EMJError("Main function is null", ctx.getText(), ctx.start.getLine()));
        } else {
            visit(ctx.mainFunction());
        }
        return VoidResult.valid();
    }

    /**
     * Vérifie la cohérence de la déclaration de fonction
     * @param ctx Contexte de la déclaration de fonction
     * @requires ctx != null && ctx.EMOJI_ID() != null && symbolTable.lookup(ctx.EMOJI_ID().getText()) != null
     * @modifies symbolTable.currentScope
     * @effects vérifie que le type de retour de la fonction correspond à sa déclaration
     *          ajoute une erreur au errorLogger si les types ne correspondent pas
     * @return true si le type de retour correspond à la déclaration, false sinon
     */
    private boolean checkDeclaration(EMJParser.FunctionDeclContext ctx) {
        EMJSymbolInfo declaredInfo = symbolTable.lookup(ctx.EMOJI_ID().getText());
        if (declaredInfo == null) {
            errorLogger.addError(new EMJError(String.format("No declaration information for function %s in the symbol table", ctx.EMOJI_ID()), ctx.getText(), ctx.start.getLine()));
            return false;
        }
        symbolTable.enterScope("function_" + declaredInfo.getId());
        String expectedReturn = declaredInfo.getReturnType();
        String actualReturn = EMJVarType.UNKNOWN.label(); //Valeur garantissant un état cohérent en cas d'échec silencieux
        if (isAVoidReturn(ctx)) {
            actualReturn = EMJVarType.VOID.label();
        } else {
            EMJParser.ExpressionContext returnStmtExpression = ctx.returnStatement().expression();
            if (returnStmtExpression == null) {
                errorLogger.addError(new EMJError(String.format("Function %s has a null return statement (expected %s) .", declaredInfo.getId(), expectedReturn), ctx.getText(), ctx.start.getLine()));
                symbolTable.exitScope();
                return false;
            }
            actualReturn = getExpressionType(returnStmtExpression);
        }
        symbolTable.exitScope();
        if (!areTypesCompatible(expectedReturn, actualReturn)) {
            errorLogger.addError(new EMJError(String.format("Function %s returns %s instead of %s .", declaredInfo.getId(), actualReturn, expectedReturn), ctx.getText(), ctx.start.getLine()));
            return false;
        }
        return true;
    }

    /**
     * Vérifie si une déclaration de fonction a un retour de type void
     * @param ctx Contexte de la déclaration de fonction
     * @requires ctx != null && ctx.returnStatement() != null
     * @return true si l'instruction de retour est de type void, false sinon
     */
    private static boolean isAVoidReturn(EMJParser.FunctionDeclContext ctx) {
        return ctx.returnStatement().VOID_TYPE() != null || ctx.returnStatement().RETURN_VOID() != null
                || ctx.returnStatement().expression() == null || ctx.returnStatement().expression().isEmpty();
    }

    /**
     * Visite une déclaration de variable
     * @param ctx Contexte de la déclaration de variable
     * @requires ctx != null && ctx.EMOJI_ID() != null && ctx.type() != null
     * @effects ajoute une variable dans la table des symboles
     *          vérifie la compatibilité de type si une expression d'initialisation est présente
     *          ajoute une erreur au errorLogger si le nom est déjà déclaré dans la même portée
     *          ajoute une erreur au errorLogger si les types sont incompatibles
     * @return VoidResult
     */
    @Override
    public VoidResult visitVarDecl(EMJParser.VarDeclContext ctx) {

        // SEMANTIC_CHECK_VAR_ID_ALREADY_EXISTS : Check if the id in the variable declaration does not exist yet
        String varId = ctx.EMOJI_ID().getText();

        // If variable id already exist in variables throw an error
        EMJSymbolInfo varInTable = this.symbolTable.lookup(varId);
        if (varInTable != null) {
            if (varInTable.getSymbolType() == EMJSymbolType.PARAMETER) {
                errorLogger.addError(new EMJError(
                        "varIdShadowsParameter",
                        String.format("Variable '%s' cannot shadow a parameter in the same function.", varId),
                        ctx.start.getLine()
                ));
            }else {
                this.errorLogger.addError(new EMJError("varIdAlreadyExists", ctx.getText(), ctx.start.getLine()));
            }
            return VoidResult.valid();
        }

        String varType = getTypeFromContext(ctx.type());
        if (EMJVarType.UNKNOWN.label().equals(varType)) {
            errorLogger.addError(new EMJError(
                    "unknownVariableType",
                    String.format("Cannot declare variable '%s' with unknown type.", varId),
                    ctx.start.getLine()
            ));
            return VoidResult.valid();
        }
        boolean isInitialized = ctx.expression() != null;
        this.symbolTable.addVariable(varId, varType, isInitialized);
        // Need to check type compatibility
        if (isInitialized) {
            // Visit the expression to determine its type
            String exprType = getExpressionType(ctx.expression());

            if (!areTypesCompatible(varType, exprType)) {
                this.errorLogger.addError(new EMJError(
                        "typeMismatch",
                        "Cannot initialize variable of type '" + varType +
                                "' with an expression of type '" + exprType + "'",
                        ctx.start.getLine()
                ));
            }
        }
        return VoidResult.valid();
    }

    /**
     * Vérifie la compatibilité entre un type déclaré et un type d'expression
     * @param declaredType Type déclaré
     * @param exprType Type de l'expression
     * @requires declaredType != null && exprType != null
     * @effects vérifie si un type d'expression est compatible avec un type déclaré
     * @return true si les types sont compatibles, false sinon
     *         Les types sont considérés compatibles s'ils sont identiques et non null
     *         Les types "UNKNOWN" sont incompatibles avec tout type
     */
    private boolean areTypesCompatible(String declaredType, String exprType) {
        if (declaredType == null || exprType == null || EMJVarType.UNKNOWN.label().equals(declaredType) || EMJVarType.UNKNOWN.label().equals(exprType)) {
            return false;
        }

        // Si les types sont identiques, ils sont compatibles
        if (declaredType.equals(exprType)) {
            return true;
        }

        // Si l'un est un tuple et l'autre ne l'est pas, ils sont incompatibles
        boolean declaredStartsWTuple = declaredType.startsWith(String.format("%s(", EMJVarType.TUPLE));
        boolean exprStartsWTuple = exprType.startsWith(String.format("%s(", EMJVarType.TUPLE));
        if ((declaredStartsWTuple && !exprStartsWTuple) || (!declaredStartsWTuple && exprStartsWTuple)) {
            return false;
        }

        // Pour deux tuples, vérifier la compatibilité des types internes
        if (declaredStartsWTuple && exprStartsWTuple) {
            String declaredInner = declaredType.substring(6, declaredType.length() - 1).trim();
            String exprInner = exprType.substring(6, exprType.length() - 1).trim();
            return areTypesCompatible(declaredInner, exprInner);
        }

        return false;
    }

    /**
     * Vérifie si les types sont compatibles pour une opération de comparaison
     *
     * @param leftType Type de l'opérande gauche
     * @param rightType Type de l'opérande droite
     * @param ctx Le contexte de la comparaison
     * @requires leftType != null && rightType != null && ctx != null
     * @effects vérifie la compatibilité des types dans une expression de comparaison
     *          ajoute une erreur au errorLogger si les types sont incompatibles
     * @return true si les types sont compatibles pour la comparaison, false sinon
     *         Les types sont compatibles s'ils sont identiques
     *         Les types "UNKNOWN" sont incompatibles avec tout type
     *         Les comparaisons entre types différents sont considérées incompatibles
     */
    private boolean areComparisonTypesCompatible(String leftType, String rightType, EMJParser.ComparisonExpressionContext ctx) {
        // Si l'un des types est inconnu, considérer comme incompatible
        if (leftType == null || rightType == null || leftType.equals(EMJVarType.UNKNOWN.label()) || rightType.equals(EMJVarType.UNKNOWN.label())) {
            return false;
        }

        // Opérateurs == ou != → autoriser des types compatibles, pas seulement identiques
        if (ctx.DOUBLE_EQUAL() != null || ctx.NOTEQUAL() != null) {
            return areTypesCompatible(leftType, rightType);
        }

        // Opérateurs <, <=, >, >= → seulement INT vs INT
        if (ctx.LESS() != null || ctx.LEQ() != null || ctx.GREATER() != null || ctx.GEQ() != null) {
            return leftType.equals(EMJVarType.INT.label()) && rightType.equals(EMJVarType.INT.label());
        }

        // Par défaut, les types sont considérés comme incompatibles
        return false;
    }

    /**
     * Détermine le type EMJ à partir d'un contexte de type.
     *
     * @param typeCtx Contexte de type à analyser.
     * @return le type EMJ correspondant au contexte sous forme de chaîne.
     *         "INT" pour les entiers, "BOOL" pour les booléens, etc.
     *         "TUPLE(type)" pour les tuples, avec le type interne entre parenthèses
     *         "UNKNOWN" si le type n'est pas reconnu
     */
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
    
    /**
     * Détermine le type EMJ à partir d'un contexte de type de retour.
     *
     * @param returnTypeCtx Contexte de type de retour à analyser.
     * @return le type EMJ correspondant au contexte sous forme de chaîne.
     *         "INT" pour les entiers, "BOOL" pour les booléens, etc.
     *         "TUPLE(type)" pour les tuples, avec le type interne entre parenthèses
     *         "VOID" pour les types void
     *         "UNKNOWN" si le type n'est pas reconnu
     */
    private String getTypeFromReturnTypeContext(EMJParser.ReturnTypeContext returnTypeCtx) {
        if (returnTypeCtx == null) return EMJVarType.UNKNOWN.label();
        if (returnTypeCtx.VOID_TYPE() != null) {
            return EMJVarType.VOID.label();
        }
        if (returnTypeCtx.type() != null) {
            return getTypeFromContext(returnTypeCtx.type());
        }
        return EMJVarType.UNKNOWN.label();
    }

    /**
     * Détermine le type d'une expression
     * @param ctx Contexte de l'expression
     * @requires ctx != null
     * @return le type de l'expression sous forme de chaîne
     *         retourne "UNKNOWN" si le type n'a pas pu être déterminé
     */
    private String getExpressionType(EMJParser.ExpressionContext ctx) {
        // Visiter l'expression et récupérer le résultat
        Object result = visit(ctx);

        if (!(result instanceof TypeResult)) {
            errorLogger.addError(new EMJError(
                    "invalidExpressionTyping",
                    String.format("Expression did not produce a valid type: %s", ctx.getText()),
                    ctx.getStart().getLine()
            ));
            return EMJVarType.UNKNOWN.label();
        }

        return ((TypeResult) result).getTypeId();
    }

    /**
     * Visite une expression
     * @param ctx Contexte de l'expression
     * @requires ctx != null
     * @effects délègue la visite à la méthode orExpression
     * @return TypeResult contenant le type de l'expression
     */
    @Override
    public TypeResult visitExpression(EMJParser.ExpressionContext ctx) {
        // Déléguer à la méthode de visite pour orExpression
        Object result = visit(ctx.orExpression());
        if (result instanceof TypeResult) {
            return (TypeResult) result;
        }
        return TypeResult.unknown();
    }

    /**
     * Visite une expression OR
     * @param ctx Contexte de l'expression OR
     * @requires ctx != null
     * @effects visite les expressions composant l'expression OR
     *          vérifie que les opérandes sont de type BOOL
     *          ajoute une erreur au errorLogger si un opérande n'est pas de type BOOL
     * @return le type de l'expression, "BOOL" si c'est une expression OR,
     *         le type de la sous-expression si c'est une expression simple,
     *         "UNKNOWN" en cas d'erreur de type
     */
    @Override
    public TypeResult visitOrExpression(EMJParser.OrExpressionContext ctx) {
        // S'il y a plus d'une andExpression connectée par OR, c'est un booléen
        if (!ctx.OR().isEmpty()) {
            boolean hasTypeError = false;

            // Vérifier chaque opérande
            for (EMJParser.AndExpressionContext andExpr : ctx.andExpression()) {
                Object result = visit(andExpr);
                if (!(result instanceof TypeResult)) {
                    hasTypeError = true;
                    continue;
                }
                TypeResult typeResult = (TypeResult) result;
                String type = typeResult.getTypeId();
                if (!type.equals(EMJVarType.BOOL.label()) && !type.equals(EMJVarType.UNKNOWN.label())) {//TODO: UNKNOWN ????
                    errorLogger.addError(new EMJError(
                            "invalidBooleanOperand",
                            String.format("Operand of OR must be of type BOOL, found: %s", type),
                            ctx.start.getLine()
                    ));
                    hasTypeError = true;
                }
            }

            return hasTypeError ? TypeResult.unknown() : TypeResult.valid(EMJVarType.BOOL.label());
        }

        // Sinon, déléguer au premier andExpression
        Object result = visit(ctx.andExpression(0));
        if (result instanceof TypeResult) {
            return (TypeResult) result;
        }
        return TypeResult.unknown();
    }

    /**
     * Visite une expression AND
     * @param ctx Contexte de l'expression AND
     * @requires ctx != null
     * @effects visite les expressions composant l'expression AND
     *          vérifie que les opérandes sont de type BOOL
     *          ajoute une erreur au errorLogger si un opérande n'est pas de type BOOL
     * @return le type de l'expression, "BOOL" si c'est une expression AND,
     *         le type de la sous-expression si c'est une expression simple,
     *         "UNKNOWN" en cas d'erreur de type
     */
    @Override
    public TypeResult visitAndExpression(EMJParser.AndExpressionContext ctx) {
        // S'il y a plus d'une notExpression connectée par AND, c'est un booléen
        if (!ctx.AND().isEmpty()) {
            boolean hasTypeError = false;

            // Vérifier chaque opérande
            for (EMJParser.NotExpressionContext notExpr : ctx.notExpression()) {
                Object result = visit(notExpr);
                if (!(result instanceof TypeResult)) {
                    hasTypeError = true;
                    continue;
                }
                TypeResult typeResult = (TypeResult) result;
                String type = typeResult.getTypeId();
                if (!type.equals(EMJVarType.BOOL.label()) && !type.equals(EMJVarType.UNKNOWN.label())) {//TODO: UNKNOWN ????
                    errorLogger.addError(new EMJError(
                            "invalidBooleanOperand",
                            String.format("Operand of AND must be of type BOOL, found: %s", type),
                            ctx.start.getLine()
                    ));
                    hasTypeError = true;
                }
            }

            return hasTypeError ? TypeResult.unknown() : TypeResult.valid(EMJVarType.BOOL.label());
        }

        // Sinon, déléguer au premier notExpression
        Object result = visit(ctx.notExpression(0));
        if (result instanceof TypeResult) {
            return (TypeResult) result;
        }
        return TypeResult.unknown();
    }

    /**
     * Visite une expression de négation (NOT)
     * @param ctx Contexte de l'expression NOT
     * @requires ctx != null
     * @ensures ctx.NOT() == null ==> \result == visit(ctx.comparisonExpression())
     * @ensures ctx.NOT() != null && visit(ctx.comparisonExpression()).equals("BOOLEAN") ==>
     *         \result.equals("BOOLEAN")
     * @assignable \nothing
     */
    @Override
    public TypeResult visitNotExpression(EMJParser.NotExpressionContext ctx) {
        // S'il y a un NOT, c'est un booléen
        if (ctx.NOT() != null) {
            Object result = visit(ctx.comparisonExpression());
            if (!(result instanceof TypeResult)) {
                return TypeResult.unknown();
            }
            TypeResult typeResult = (TypeResult) result;
            String type = typeResult.getTypeId();
            if (!type.equals(EMJVarType.BOOL.label()) && !type.equals(EMJVarType.UNKNOWN.label())) {//TODO: UNKNOWN ????
                errorLogger.addError(new EMJError(
                        "invalidNotOperand",
                        String.format("Operand of NOT must be of type BOOL, found: %s", type),
                        ctx.start.getLine()
                ));
                return TypeResult.unknown();
            }
            return TypeResult.valid(EMJVarType.BOOL.label());
        }

        // Sinon, déléguer à comparisonExpression
        Object result = visit(ctx.comparisonExpression());
        if (result instanceof TypeResult) {
            return (TypeResult) result;
        }
        return TypeResult.unknown();
    }

    /**
     * Visite une expression de comparaison
     * @param ctx Contexte de l'expression de comparaison
     * @requires ctx != null
     * @effects visite les expressions additives dans l'expression de comparaison
     *          vérifie que les opérandes des opérateurs de comparaison ont des types compatibles
     *          ajoute une erreur au errorLogger si les types sont incompatibles
     * @return le type de l'expression de comparaison:
     *         - le type de la sous-expression si c'est une expression simple
     *         - "BOOL" si c'est une comparaison avec des opérandes de types compatibles
     *         - "UNKNOWN" en cas d'erreur de type
     */
    @Override
    public TypeResult visitComparisonExpression(EMJParser.ComparisonExpressionContext ctx) {
        // S'il y a un opérateur de comparaison, c'est un booléen
        if (ctx.DOUBLE_EQUAL() != null || ctx.NOTEQUAL() != null ||
                ctx.LESS() != null || ctx.LEQ() != null ||
                ctx.GREATER() != null || ctx.GEQ() != null) {
            // Récupérer les types des opérandes de la comparaison
            Object leftResult = visit(ctx.additiveExpression(0));
            Object rightResult = visit(ctx.additiveExpression(1));

            if (!(leftResult instanceof TypeResult) || !(rightResult instanceof TypeResult)) {
                return TypeResult.unknown();
            }

            String leftType = ((TypeResult) leftResult).getTypeId();
            String rightType = ((TypeResult) rightResult).getTypeId();

            if (leftType == null || rightType == null) {
                errorLogger.addError(new EMJError(
                        "nullOperand",
                        String.format("Cannot compare: one of the operands is null (left: %s, right: %s).", leftType, rightType),
                        ctx.start.getLine()
                ));
                return TypeResult.unknown();
            }

            // Vérifier la compatibilité des types pour l'opération de comparaison
            if (!areComparisonTypesCompatible(leftType, rightType, ctx)) {
                // Ajouter une erreur sémantique si les types sont incompatibles
                errorLogger.addError(new EMJError(
                        "incompatibleComparisonTypes",
                        String.format("Cannot compare values of incompatible types: '%s' and '%s'", leftType, rightType),
                        ctx.start.getLine()
                ));
                return TypeResult.unknown(); // Retourner UNKNOWN au lieu de BOOL quand les types sont incompatibles
            }

            return TypeResult.valid(EMJVarType.BOOL.label());
        }

        // Cas sans opérateur de comparaison, on envoie à la sous-expression unique
        Object result = visit(ctx.additiveExpression(0));
        if (result instanceof TypeResult) {
            return (TypeResult) result;
        }
        return TypeResult.unknown();
    }

    /**
     * Visite une expression additive
     * @param ctx Contexte de l'expression additive
     * @requires ctx != null
     * @effects visite les expressions multiplicatives dans l'expression additive
     *          vérifie que les opérandes des opérateurs + et - sont de type INT
     *          ajoute une erreur au errorLogger si un opérande n'est pas de type INT
     * @return le type de l'expression additive:
     *         - le type de la sous-expression si c'est une expression simple
     *         - "INT" si tous les opérandes sont de type INT
     *         - "UNKNOWN" en cas d'erreur de type
     */
    @Override
    public TypeResult visitAdditiveExpression(EMJParser.AdditiveExpressionContext ctx) {
        // On commence par le premier opérande
        Object leftObj = visit(ctx.multiplicativeExpression(0));
        String leftType = (leftObj instanceof TypeResult) ? ((TypeResult) leftObj).getTypeId() : EMJVarType.UNKNOWN.label();

        if (ctx.multiplicativeExpression().size() == 1) {
            return (leftObj instanceof TypeResult) ? (TypeResult) leftObj : TypeResult.unknown();
        }

        boolean hasTypeError = false;
        for (int i = 1; i < ctx.multiplicativeExpression().size(); i++) {
            Object rightObj = visit(ctx.multiplicativeExpression(i));
            String rightType = (rightObj instanceof TypeResult) ? ((TypeResult) rightObj).getTypeId() : EMJVarType.UNKNOWN.label();

            // Vérifie que les deux opérandes sont des entiers
            if (!leftType.equals(EMJVarType.INT.label()) || !rightType.equals(EMJVarType.INT.label())) {
                errorLogger.addError(new EMJError(
                        "invalidOperandType",
                        String.format("Operands of '+' or '-' must be of type INT, found: %s and %s", leftType, rightType),
                        ctx.start.getLine()
                ));
                hasTypeError = true;
            }

            // Pour les itérations suivantes - ne pas forcer le type si erreur
            if (!hasTypeError) {
                leftType = EMJVarType.INT.label();
            } else {//TODO: vérifier les effets de bord provoqués ici
                leftType = EMJVarType.UNKNOWN.label();
            }
        }

        // Retourner UNKNOWN en cas d'erreur de type, sinon INT
        return hasTypeError ? TypeResult.unknown() : TypeResult.valid(EMJVarType.INT.label());
    }

    /**
     * Visite une expression multiplicative (*, /)
     * @param ctx Contexte de l'expression multiplicative
     * @requires ctx != null
     * @ensures ctx.unaryExpression().size() <= 1 ==> \result == visit(ctx.unaryExpression(0))
     * @ensures ctx.unaryExpression().size() > 1 && ctx.DIV() != null &&
     *         visit(ctx.unaryExpression(0)).equals("INT") &&
     *         visit(ctx.unaryExpression(1)).equals("INT") ==>
     *         \result.equals("INT")
     * @assignable \nothing
     */
    @Override
    public TypeResult visitMultiplicativeExpression(EMJParser.MultiplicativeExpressionContext ctx) {
        Object leftObj = visit(ctx.unaryExpression(0));
        String leftType = (leftObj instanceof TypeResult) ? ((TypeResult) leftObj).getTypeId() : EMJVarType.UNKNOWN.label();
        if (ctx.unaryExpression().size() == 1) {
            return (leftObj instanceof TypeResult) ? (TypeResult) leftObj : TypeResult.unknown();
        }

        boolean hasTypeError = false;

        for (int i = 1; i < ctx.unaryExpression().size(); i++) {
            Object rightObj = visit(ctx.unaryExpression(i));
            String rightType = (rightObj instanceof TypeResult) ? ((TypeResult) rightObj).getTypeId() : EMJVarType.UNKNOWN.label();

            // Si l'un des opérandes a déjà une erreur de type, propager l'erreur
            if (leftType.equals(EMJVarType.UNKNOWN.label()) || rightType.equals(EMJVarType.UNKNOWN.label())) {
                return TypeResult.unknown();
            }

            // Vérification spécifique pour la division
            if (ctx.DIVIDE(i - 1) != null) {
                // Vérifier que les deux types sont INT
                if (!leftType.equals(EMJVarType.INT.label()) || !rightType.equals(EMJVarType.INT.label())) {
                    // Cas spécial: division d'une chaîne par un nombre, erreur sémantique
                    if (leftType.equals(EMJVarType.STRING.label()) && rightType.equals(EMJVarType.INT.label())) {
                        errorLogger.addError(new EMJError(
                                "invalidDivisionOperation",
                                String.format("Cannot divide a STRING by an INT: '%s' / '%s'", leftType, rightType),
                                ctx.start.getLine()
                        ));

                    } else {
                        errorLogger.addError(new EMJError(
                                "invalidOperandType",
                                String.format("Operands of '*' or '/' must be of type INT, found: %s and %s", leftType, rightType),
                                ctx.start.getLine()
                        ));
                    }
                    hasTypeError = true;
                }

                // Vérification de division par zéro
                EMJParser.UnaryExpressionContext rightExpr = ctx.unaryExpression(i);
                if (rightExpr.primaryExpression() != null && rightExpr.primaryExpression().INT_VALUE() != null) {
                    String valueText = rightExpr.primaryExpression().INT_VALUE().getText();
                    try {
                        int val = Integer.parseInt(valueText);
                        if (val == 0) {
                            errorLogger.addError(new EMJError(
                                    "divisionByZero",
                                    "Division by zero is not allowed.",
                                    ctx.start.getLine()
                            ));
                            hasTypeError = true;
                        }
                    } catch (NumberFormatException ignored) {
                    }
                }
            } else {
                // Pour la multiplication, vérifier simplement que les deux types sont INT
                if (!leftType.equals(EMJVarType.INT.label()) || !rightType.equals(EMJVarType.INT.label())) {
                    errorLogger.addError(new EMJError(
                            "invalidOperandType",
                            String.format("Operands of '*' must be of type INT, found: %s and %s", leftType, rightType),
                            ctx.start.getLine()
                    ));
                    hasTypeError = true;
                }
            }

            // Ne pas forcer le type à INT si une erreur a été détectée
            if (!hasTypeError) {
                leftType = EMJVarType.INT.label();
            } else {//TODO: vérifier les effets de bord provoqués ici
                leftType = EMJVarType.UNKNOWN.label();
            }
        }

        // Retourner UNKNOWN en cas d'erreur de type, sinon INT
        return hasTypeError ? TypeResult.unknown() : TypeResult.valid(EMJVarType.INT.label());
    }

    /**
     * Visite une expression unaire (-, +)
     * @param ctx Contexte de l'expression unaire
     * @requires ctx != null
     * @ensures ctx.SUB() == null ==> \result == visit(ctx.primaryExpression())
     * @ensures ctx.SUB() != null && visit(ctx.primaryExpression()).equals("INT") ==>
     *         \result.equals("INT")
     * @assignable \nothing
     */
    @Override
    public TypeResult visitUnaryExpression(EMJParser.UnaryExpressionContext ctx) {
        // S'il y a un - unaire, c'est un entier
        if (ctx.MINUS() != null) {
            return TypeResult.valid(EMJVarType.INT.label());
        }

        // Sinon, déléguer à primaryExpression
        Object result = visit(ctx.primaryExpression());
        if (result instanceof TypeResult) {
            return (TypeResult) result;
        }
        return TypeResult.unknown();
    }

    /**
     * Visite une expression primaire (littéraux, identifiants, appels de fonction)
     * @param ctx Contexte de l'expression primaire
     * @requires ctx != null
     * @ensures ctx.INT_LITERAL() != null ==> \result.equals("INT")
     * @ensures ctx.TRUE() != null || ctx.FALSE() != null ==> \result.equals("BOOLEAN")
     * @ensures ctx.EMOJI_ID() != null && symbolTable.lookup(ctx.EMOJI_ID().getText()) != null ==>
     *         \result.equals(symbolTable.lookup(ctx.EMOJI_ID().getText()).getType())
     * @ensures ctx.functionCall() != null ==> \result == visit(ctx.functionCall())
     * @ensures ctx.expression() != null ==> \result == visit(ctx.expression())
     * @assignable \nothing
     * @return le type de l'expression primaire
     */
    @Override
    public TypeResult visitPrimaryExpression(EMJParser.PrimaryExpressionContext ctx) {
        if (ctx.INT_VALUE() != null) {
            String intValue = ctx.INT_VALUE().getText();

            if (intValue.length() > 1 && intValue.charAt(0) == '0') {
                errorLogger.addError(new EMJError(
                        "intStartsWithZero",
                        String.format("Integer value cannot start with 0: %s", intValue),
                        ctx.start.getLine()));
            }
// TODO int max and int min not good
            try {
                long val = Long.parseLong(intValue);
                if (val > 1_000_000_000L) {
                    errorLogger.addError(new EMJError(
                            "integerTooBig",
                            String.format("Integer value too big: %s", intValue),
                            ctx.start.getLine()));
                } else if (val < -1_000_000_000L) {
                    errorLogger.addError(new EMJError(
                            "integerTooSmall",
                            String.format("Integer value too small: %s", intValue),
                            ctx.start.getLine()));
                }
            } catch (NumberFormatException e) {
                errorLogger.addError(new EMJError(
                        "invalidIntegerFormat",
                        String.format("Invalid integer format: %s", intValue),
                        ctx.start.getLine()));
            }
            return TypeResult.valid(EMJVarType.INT.label());
        }

        if (ctx.STRING_VALUE() != null) return TypeResult.valid(EMJVarType.STRING.label());
        if (ctx.CHAR_VALUE()   != null) return TypeResult.valid(EMJVarType.CHAR.label());
        if (ctx.TRUE() != null || ctx.FALSE() != null) return TypeResult.valid(EMJVarType.BOOL.label());

        if (ctx.tupleValue() != null) {
            Object result1 = visit(ctx.tupleValue().expression(0));
            Object result2 = visit(ctx.tupleValue().expression(1));
            String t1 = (result1 instanceof TypeResult) ? ((TypeResult) result1).getTypeId() : EMJVarType.UNKNOWN.label();
            String t2 = (result2 instanceof TypeResult) ? ((TypeResult) result2).getTypeId() : EMJVarType.UNKNOWN.label();
            if (!t1.equals(t2)) {
                errorLogger.addError(new EMJError(
                        "tupleMismatchedTypes",
                        String.format("Tuple elements must have the same type, found: %s and %s", t1, t2),
                        ctx.start.getLine()));
            }
            if (t1.equals(EMJVarType.UNKNOWN.label()) || t2.equals(EMJVarType.UNKNOWN.label())) {
                return TypeResult.unknown(); //TODO : on autorise "Tuple(UNKNOWN)" ? si oui, enlever ce if
            }
            return TypeResult.valid(String.format("%s(%s)", EMJVarType.TUPLE.label(), t1));
        }

        if (ctx.EMOJI_ID() != null) {
            String varId = ctx.EMOJI_ID().getText();
            EMJSymbolInfo info = symbolTable.lookup(varId);

            if (info == null) {
                errorLogger.addError(new EMJError(
                        "undeclaredVariable",
                        String.format("Variable '%s' is not declared", varId),
                        ctx.start.getLine()));
                return TypeResult.unknown();
            }
            if (!info.isInitialized()) {
                errorLogger.addError(new EMJError(
                        "uninitializedVariable",
                        String.format("Variable '%s' is used before being initialized", varId),
                        ctx.start.getLine()));
                return TypeResult.unknown();
            }
            return TypeResult.valid(info.getType());
        }

        if (ctx.leftExpression() != null) {
            EMJParser.LeftExpressionContext leftCtx = ctx.leftExpression();
            String varId = leftCtx.EMOJI_ID().getText();
            EMJSymbolInfo info = symbolTable.lookup(varId);

            if (info == null) {
                errorLogger.addError(new EMJError(
                        "undeclaredVariable",
                        String.format("Variable '%s' is not declared", varId),
                        ctx.start.getLine()));
                return TypeResult.unknown();
            }
            if (!info.isInitialized()) {
                errorLogger.addError(new EMJError(
                        "uninitializedVariable",
                        String.format("Tuple '%s' is used before being initialized", varId),
                        ctx.start.getLine()));
                return TypeResult.unknown();
            }
            return TypeResult.valid(getLeftExpressionType(leftCtx));
        }

        if (ctx.functionCall() != null) {
            return visitFunctionCall(ctx.functionCall());
        }

        if (ctx.expression() != null) {
            return visitExpression(ctx.expression());
        }

        if (ctx.NOT() != null && ctx.primaryExpression() != null) {
            Object result = visit(ctx.primaryExpression());
            String t = (result instanceof TypeResult) ? ((TypeResult) result).getTypeId() : EMJVarType.UNKNOWN.label();
            if (!t.equals(EMJVarType.BOOL.label())) {
                errorLogger.addError(new EMJError(
                        "invalidNegationOperand",
                        String.format("Operand of NOT must be of type BOOL, found: %s", t),
                        ctx.start.getLine()));
                return TypeResult.unknown();
            }
            return TypeResult.valid(EMJVarType.BOOL.label());
        }

        return TypeResult.unknown();
    }

    /**
     * Méthode auxiliaire pour obtenir le type d'une expression gauche
     * @param ctx Contexte de l'expression gauche
     * @requires ctx != null
     * @ensures ctx.EMOJI_ID() != null && symbolTable.lookup(ctx.EMOJI_ID().getText()) != null ==>
     *         \result.equals(symbolTable.lookup(ctx.EMOJI_ID().getText()).getType())
     * @return Le type de l'expression gauche
     * @pure
     */
    private String getLeftExpressionType(EMJParser.LeftExpressionContext ctx) {
        String varId = ctx.EMOJI_ID().getText();
        EMJSymbolInfo info = symbolTable.lookup(varId);

        if (info == null) {
            errorLogger.addError(new EMJError(
                    "undeclaredVariable",
                    String.format("Variable '%s' is not declared", varId),
                    ctx.getStart().getLine()
            ));
            return EMJVarType.UNKNOWN.label();
        }

        String varType = info.getType();

        // Si on accède à un élément d'un tuple
        if (ctx.TUPLE_FIRST() != null || ctx.TUPLE_SECOND() != null) {
            if (!varType.startsWith(String.format("%s(", EMJVarType.TUPLE.label()))) {
                errorLogger.addError(new EMJError(
                        "invalidTupleAccess",
                        String.format("Cannot access tuple element from non-tuple variable '%s'", varId),
                        ctx.getStart().getLine()
                ));
                return EMJVarType.UNKNOWN.label();
            }

            // Extraire le type interne du tuple (ce qui est entre parenthèses)
            return extractInnerTypeFromTuple(varType);
        }

        return varType;
    }

    /**
     * Extrait le type interne d'un type tuple, si valide.
     *
     * @param type Chaîne représentant un type (ex : "TUPLE(INT)")
     * @return Le type interne (ex : "INT") si format valide, "UNKNOWN" sinon.
     */
    private String extractInnerTypeFromTuple(String type) {
        String tuplePrefix = String.format("%s(", EMJVarType.TUPLE.label());

        if (type == null || !type.startsWith(tuplePrefix) || !type.endsWith(")")) {
            return EMJVarType.UNKNOWN.label();
        }

        // Extraire la sous-chaîne entre les parenthèses
        String inner = type.substring(tuplePrefix.length(), type.length() - 1).trim();

        // Vérification minimale (non vide)
        if (inner.isEmpty()) {
            return EMJVarType.UNKNOWN.label();
        }

        return inner;
    }

    /**
     * Visite une carte
     * @param ctx Contexte de la carte
     * @requires ctx != null
     * @effects vérifie que la carte est valide
     * @return VoidResult
     */
    @Override
    public VoidResult visitMapFile(EMJParser.MapFileContext ctx) {
        int width = Integer.parseInt(ctx.INT_VALUE(0).getText());
        int height = Integer.parseInt(ctx.INT_VALUE(1).getText());
        int policeCarCount = 0;
        int thiefCount = 0;
        int roadCount = 0;
        int expectedCellCount = width * height;
        int actualCellCount = ctx.mapCell().size();

        if (width < 2 || height < 2) {
            this.errorLogger.addError(new EMJError(
                    "mapTooSmall",
                    String.format("The map must at least have a width >= 2 and a height >= 2 (current : %d x %d).", width, height),
                    ctx.start.getLine()
            ));
        }

        if (expectedCellCount != actualCellCount) {
            this.errorLogger.addError(new EMJError(
                    "mapDimensionsMismatch",
                    String.format("The size given (%d x %d = %d cells) don't match with the number of cells given (%d).", width, height, expectedCellCount, actualCellCount),
                    ctx.start.getLine()
            ));
        }

        for (EMJParser.MapCellContext cellCtx : ctx.mapCell()) {
            if (cellCtx.COP() != null) {
                policeCarCount++;
            }
            if (cellCtx.THIEF() != null) {
                thiefCount++;
            }
            if (cellCtx.ROAD() != null) {
                roadCount++;
            }
        }

        if (policeCarCount != 1) {
            this.errorLogger.addError(new EMJError(
                    "mapPoliceCarCountInvalid",
                    String.format("The map must contain exactly 1 Police Car, found : %d", policeCarCount),
                    ctx.start.getLine()
            ));
        }

        if (thiefCount < 1) {
            this.errorLogger.addError(new EMJError(
                    "mapThiefMissing",
                    String.format("The map must contain at least 1 Thief, found : %d", thiefCount),
                    ctx.start.getLine()
            ));
        }

        if (roadCount < 1) {
            this.errorLogger.addError(new EMJError(
                    "mapRoadMissing",
                    String.format("The map must contain at least 1 Road, found : %d", roadCount),
                    ctx.start.getLine()
            ));
        }

        return VoidResult.valid();
    }

    /**
     * Visite la fonction principale
     * @param ctx Contexte de la fonction principale
     * @requires ctx != null
     * @modifies rien
     * @effects visite la fonction principale du programme
     * @return le résultat de la visite des enfants du nœud
     */
    @Override
    public VoidResult visitMainFunction(EMJParser.MainFunctionContext ctx) {
        //TODO : checker la structure du main (pas de param, type de retour void au moins une instruction) ?
        symbolTable.enterScope("main");
        visitChildren(ctx);
        symbolTable.exitScope();
        return VoidResult.valid();
    }

    /**
     * Visite une déclaration de fonction
     * @param ctx Contexte de la déclaration de fonction
     * @requires ctx != null && ctx.EMOJI_ID() != null
     * @modifies symbolTable
     * @effects ajoute une nouvelle déclaration de fonction à la table des symboles
     *          entre dans une nouvelle portée pour cette fonction
     *          ajoute les paramètres de la fonction à la table des symboles
     * @ensures symbolTable.functionExists(ctx.EMOJI_ID().getText())
     * @return le résultat de la visite des enfants du nœud
     */
    @Override
    public VoidResult visitFunctionDecl(EMJParser.FunctionDeclContext ctx) {
        // Récupérer l'identifiant de la fonction
        String funcId = ctx.EMOJI_ID().getText();

        // Récupérer le type de retour
        String returnType = getTypeFromReturnTypeContext(ctx.returnType());

        // Récupérer les paramètres & vérifier qu'il n'y a pas de dupes ni d'unknown
        List<EMJParameterInfo> parameters = new ArrayList<>();
        if (ctx.optionalParamList() != null && ctx.optionalParamList().paramList() != null) {
            EMJParser.ParamListContext paramListCtx = ctx.optionalParamList().paramList();
            Set<String> seenParamIds = new HashSet<>();
            for (EMJParser.ParamContext paramCtx : paramListCtx.param()) {
                String paramId = paramCtx.EMOJI_ID().getText();
                String paramType = getTypeFromContext(paramCtx.type());

                if (EMJVarType.UNKNOWN.label().equals(paramType)) {
                    errorLogger.addError(new EMJError(
                            "unknownParameterType",
                            String.format("Parameter '%s' has an unknown type.", paramId),
                            paramCtx.getStart().getLine()
                    ));
                    continue; // on n'ajoute pas ce paramètre
                }

                if (seenParamIds.contains(paramId)) {
                    errorLogger.addError(new EMJError(
                            "duplicateParameter",
                            String.format("Parameter '%s' is declared multiple times in function '%s'.", paramId, funcId),
                            paramCtx.getStart().getLine()
                    ));
                } else {
                    seenParamIds.add(paramId);
                    parameters.add(new EMJParameterInfo(paramId, paramType));
                }
            }
        }

        // Vérifier si la fonction existe déjà
        if (symbolTable.functionExists(funcId)) {
            errorLogger.addError(new EMJError("functionAlreadyDefined",
                    String.format("Function '%s' is already defined", funcId), ctx.start.getLine()));
            return VoidResult.valid();
        }

        // Ajouter la fonction à la table des symboles
        symbolTable.addFunction(funcId, returnType, parameters);

        // Entrer dans la portée de la fonction
        symbolTable.enterScope("function_" + funcId);

        // Ajouter les paramètres dans la portée de la fonction
        for (EMJParameterInfo param : parameters) {
            symbolTable.addVariable(param.getId(), param.getType(), true);
        }

        // Visiter le corps de la fonction
        visitChildren(ctx);

        // Sortir de la portée de la fonction
        symbolTable.exitScope();

        return VoidResult.valid();
    }

    /**
     * Méthode auxiliaire pour obtenir le type à partir d'un contexte de type de retour
     *
     * @param ctx Contexte de type de retour
     * @requires ctx != null
     * @modifies rien
     * @return la chaîne de caractères représentant le type, jamais null
    }
    
    // Stratégie 2: chemin relatif au répertoire courant
    mapFile = new File(System.getProperty("user.dir"), mapPath);
    if (mapFile.exists() && mapFile.isFile()) {
        return mapFile;
     * @param ctx Contexte de l'instruction de boucle
     * @requires ctx != null && ctx.expression() != null
     * @modifies symbolTable, errorLogger
     * @effects entre dans une nouvelle portée "loop"
     *          vérifie que l'expression de condition est de type BOOLEAN
     *          ajoute une erreur si la condition n'est pas de type BOOLEAN
     * @ensures getExpressionType(ctx.expression()).equals("BOOLEAN") || errorLogger.hasErrors()
     * @return le résultat de la visite des enfants du nœud
     */
    @Override
    public VoidResult visitLoopStatement(EMJParser.LoopStatementContext ctx) {
        symbolTable.enterScope("loop");

        if (ctx.expression() != null) {
            String condType = getExpressionType(ctx.expression());
            if (!condType.equals(EMJVarType.BOOL.label()) && !condType.equals(EMJVarType.INT.label())) {
                errorLogger.addError(new EMJError(
                        "invalidLoopCondition",
                        String.format("Loop condition must be of type BOOL or INT, found: %s", condType),
                        ctx.start.getLine()
                ));
            }
        } else {
            errorLogger.addError(new EMJError(
                    "missingLoopCondition",
                    "Loop statement requires a condition expression.",
                    ctx.start.getLine()
            ));
        }

        visitChildren(ctx);
        symbolTable.exitScope();
        return VoidResult.valid();
    }

   /**
 * Visite une instruction conditionnelle
 * 
 * @param ctx Contexte de l'instruction conditionnelle
 * @requires ctx != null && ctx.expression() != null
 * @modifies symbolTable, errorLogger
 * @effects entre dans une nouvelle portée "if"
 *          vérifie que la condition est de type BOOL
 *          visite les blocs then et else
 *          ajoute une erreur au errorLogger si la condition n'est pas de type BOOL
 * @return le résultat de la visite des enfants du nœud
 */
@Override
public VoidResult visitIfStatement(EMJParser.IfStatementContext ctx) {
    // Vérifier que la condition est de type booléen
    TypeResult conditionType = visitExpression(ctx.expression());
    if (!conditionType.getTypeId().equals("bool")) {
        errorLogger.addError(new EMJError(
                "conditionTypeMismatch",
                String.format("If condition must be of type BOOL, but got %s", conditionType.getTypeId()),
                ctx.getStart().getLine()
        ));
    }
    
    // Visiter le bloc 'then'
    symbolTable.enterScope("if");
    visit(ctx.block(0));
    symbolTable.exitScope();
    
    // Visiter le bloc 'else' s'il existe
    if (ctx.block().size() > 1) {
        symbolTable.enterScope("else");
        visit(ctx.block(1));
        symbolTable.exitScope();
    } else if (ctx.ELSE() != null) {
        // Cas spécial: else { SKIPPING; }
        // Ne nécessite pas de traitement sémantique particulier
    }
    
    return VoidResult.valid();
}

    /**
     * Visite un bloc de code
     *
     * @param ctx Contexte du bloc de code
     * @requires ctx != null
     * @modifies symbolTable
     * @effects entre dans une nouvelle portée "block"
     * @return le résultat de la visite des enfants du nœud
     */
    @Override
    public VoidResult visitBlock(EMJParser.BlockContext ctx) {
        symbolTable.enterScope("block");
        visitChildren(ctx);
        symbolTable.exitScope();
        return VoidResult.valid();
    }

    /**
     * Visite une instruction d'affectation
     *
     * @param ctx Contexte de l'instruction d'affectation
     * @requires ctx != null && ctx.leftExpression() != null && ctx.expression() != null
     * @modifies errorLogger, symbolTable
     * @effects vérifie que la variable à gauche est déclarée
     *          vérifie que les types sont compatibles
     *          marque la variable comme initialisée (si elle n'est pas une composante de tuple)
     *          ajoute des erreurs au errorLogger si nécessaire
     * @ensures si la variable est trouvée dans la table des symboles, elle est marquée comme initialisée
     * @return VoidResult
     */
    @Override
    public VoidResult visitAssignment(EMJParser.AssignmentContext ctx) {
        EMJParser.LeftExpressionContext leftCtx = ctx.leftExpression();
        String varId = leftCtx.EMOJI_ID().getText();

        EMJSymbolInfo varInfo = symbolTable.lookup(varId);
        if (varInfo == null) {
            errorLogger.addError(new EMJError(
                    "varIdNotDecl",
                    ctx.getText(),
                    ctx.start.getLine()));
            return VoidResult.valid();
        }

        if (ctx.expression() == null) {
            errorLogger.addError(new EMJError(
                    "missingAssignmentExpression",
                    "Assignment is missing a right-hand side expression.",
                    ctx.start.getLine()
            ));
            return VoidResult.valid();
        }

        String leftType  = getLeftExpressionType(leftCtx);
        String rightType = getExpressionType(ctx.expression());

        if (!areTypesCompatible(leftType, rightType)) {
            errorLogger.addError(new EMJError(
                    "typeMismatch",
                    String.format("Cannot assign value of type '%s' to target of type '%s'", rightType, leftType),
                    ctx.start.getLine()));
            return VoidResult.valid();
        }

        if (leftCtx.TUPLE_FIRST() == null && leftCtx.TUPLE_SECOND() == null) {
            varInfo.setInitialized(true);
        }

        return VoidResult.valid();
    }

    /**
     * Visite une instruction d'importation de fichier carte
     * 
     * @param ctx Contexte de l'instruction d'importation
     * @return VoidResult
     * @requires ctx != null && ctx.STRING_LITERAL() != null
     * @effects vérifie que le fichier carte existe et a l'extension correcte
     *          ajoute une erreur au errorLogger si le fichier n'existe pas ou n'a pas l'extension .map
     */
    @Override
    public VoidResult visitImportStatement(EMJParser.ImportStatementContext ctx) {
        // Extraire le chemin du fichier carte à partir de la chaîne littérale
        String mapPathLiteral = ctx.STRING_VALUE().getText();
        // Enlever les guillemets si nécessaire
        String mapPath = mapPathLiteral;
        // Si la chaîne commence et se termine par des guillemets, les enlever
        if (mapPath.startsWith("\"") && mapPath.endsWith("\"")) {
            mapPath = mapPath.substring(1, mapPath.length() - 1);
        }
//
//        // Résoudre le chemin complet du fichier carte
//        File mapFile = resolveMapPath(mapPath);
//
//        // Vérifier si le fichier existe
//        if (!mapFile.exists()) {
//            errorLogger.addError(new EMJError(
//                "mapFileNotFound",
//                String.format("Map file '%s' not found", mapPath),
//                ctx.start.getLine()
//            ));
//        }
//
        // Vérifier si le fichier a l'extension .map
        if (!mapPathLiteral.toLowerCase().endsWith(".map")) {
            errorLogger.addError(new EMJError(
                "invalidMapFileExtension",
                String.format("Map file '%s' must have .map extension", mapPath),
                ctx.start.getLine()
            ));
        }
        
        return VoidResult.valid();
    }
    
    /**
     * Résout le chemin complet d'un fichier carte à partir d'un chemin relatif
     * 
     * @param relativePath Chemin relatif du fichier carte
     * @return Fichier carte résolu
     * @requires relativePath != null
     * @effects résout le chemin complet du fichier carte à partir du chemin relatif
     */
    private File resolveMapPath(String relativePath) {
        // Si le chemin est absolu, l'utiliser directement
        File mapFile = new File(relativePath);
        if (mapFile.isAbsolute()) {
            return mapFile;
        }
        
        // Tenter de résoudre par rapport au répertoire du fichier source si disponible
        if (sourceFilePath != null) {
            File sourceFile = new File(sourceFilePath);
            File sourceDir = sourceFile.getParentFile();
            if (sourceDir != null) {
                File resolvedMap = new File(sourceDir, relativePath);
                if (resolvedMap.exists()) {
                    return resolvedMap;
                }
            }
        }
        
        // Tenter de résoudre par rapport au répertoire de travail courant
        File workingDirMap = new File(System.getProperty("user.dir"), relativePath);
        if (workingDirMap.exists()) {
            return workingDirMap;
        }
        
        // Tenter de résoudre dans le répertoire de test si les précédentes tentatives ont échoué
        File testDir = new File(System.getProperty("user.dir") + "/src/test/resources/10_test_python");
        if (testDir.exists()) {
            File testMap = new File(testDir, relativePath);
            if (testMap.exists()) {
                return testMap;
            }
        }
        
        // Si aucune résolution n'a fonctionné, retourner le chemin par défaut
        return new File(System.getProperty("user.dir"), relativePath);
    }
    
    /**
     * Visite un appel de fonction
     * @param ctx Contexte de l'appel de fonction
     * @requires ctx != null && ctx.EMOJI_ID() != null
     * @effects vérifie que la fonction appelée est déclarée dans la table des symboles
     *          vérifie que le nombre et les types des arguments correspondent aux paramètres déclarés
     *          vérifie que les fonctions void ne sont pas utilisées dans des expressions
     *          ajoute des erreurs au errorLogger si:
     *            - la fonction n'est pas déclarée
     *            - une fonction void est utilisée dans une expression
     *            - le nombre d'arguments ne correspond pas
     *            - les types des arguments sont incompatibles avec les types des paramètres
     * @return le type de retour de la fonction si elle est déclarée, "UNKNOWN" sinon
     */
    @Override
    public TypeResult visitFunctionCall(EMJParser.FunctionCallContext ctx) {
        String functionName = ctx.EMOJI_ID().getText(); // Retrieve the name of the called function

        // Retrieve the number of arguments passed to the function call
        List<EMJParser.ExpressionContext> args =
                ctx.argumentList() != null ? ctx.argumentList().expression() : new ArrayList<>();

        // Retrieve the function definition from the symbol table
        EMJSymbolInfo functionSymbol = symbolTable.lookup(functionName);

        if (functionSymbol == null || functionSymbol.getSymbolType() != EMJSymbolType.FUNCTION) {
            errorLogger.addError(new EMJError("Function not declared", functionName, ctx.getStart().getLine()));
            return TypeResult.unknown();
        }

        // Vérifier si la fonction est de type void et si elle est appelée dans une expression
        if (EMJVarType.VOID.label().equals(functionSymbol.getReturnType())) {
            // Pour les fonctions void, vérifier si elles sont utilisées dans une expression
            // Nous considérons tout contexte autre qu'une instruction directe comme une expression
            boolean isUsedInExpression = !(ctx.getParent() instanceof EMJParser.FunctionCallStmtContext);

            if (isUsedInExpression) {
                // Ajouter une erreur sémantique pour l'utilisation d'une fonction void dans une expression
                errorLogger.addError(new EMJError(
                        "voidFunctionInExpression",
                        String.format("Function %s has void return type and cannot be used in an expression", functionName),
                        ctx.getStart().getLine()
                ));
            }
        }

        int expected = functionSymbol.getParameters() != null ? functionSymbol.getParameters().size() : 0;
        int actual = args.size();
        if (actual != expected) {
            errorLogger.addError(new EMJError(
                    actual < expected ? "functionTooFewParameters" : "functionTooManyParameters",
                    String.format("Function '%s' expects %d parameter(s), but got %d", functionName, expected, actual),
                    ctx.getStart().getLine()
            ));
        }

        // Visit each argument expression to perform semantic checks
        for (int i = 0; i < Math.min(actual, expected); i++) {
            TypeResult result = visitExpression(args.get(i));
            String argType = result.getTypeId();
            String paramType = functionSymbol.getParameters().get(i).getType();
            if (!areTypesCompatible(paramType, argType)) {
                errorLogger.addError(new EMJError(
                        "paramTypeMismatch",
                        String.format("Parameter %d of function %s expects type %s but got %s", i + 1, functionName, paramType, argType),
                        ctx.getStart().getLine()
                ));
            }
        }

        // Return the function's return type
        return TypeResult.valid(functionSymbol.getReturnType());
    }
}
