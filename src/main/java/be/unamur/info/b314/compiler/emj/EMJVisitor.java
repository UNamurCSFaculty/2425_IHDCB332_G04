package be.unamur.info.b314.compiler.emj;

import be.unamur.info.b314.compiler.EMJLexer;
import be.unamur.info.b314.compiler.EMJParser;
import be.unamur.info.b314.compiler.emj.EMJError;
import be.unamur.info.b314.compiler.emj.EMJErrorLogger;

import java.util.ArrayList;
import java.util.List;
import java.util.HashMap;
import java.util.Map;

/**
 * Visiteur pour le langage EMJ, étendant le visiteur de base généré par ANTLR
 * Implémente les vérifications sémantiques pour le compilateur EMJ
 * 
 * @author Alix Decrop (original)
 * @version 2.0
 */
public class EMJVisitor extends be.unamur.info.b314.compiler.EMJParserBaseVisitor<Object> {

    private EMJErrorLogger errorLogger;
    private EMJSymbolTable symbolTable;

    public EMJVisitor() {
        this.errorLogger = new EMJErrorLogger();
        this.symbolTable = new EMJSymbolTable();
    }


    public EMJErrorLogger getErrorLogger() {
        return this.errorLogger;
    }

    /*
    SEMANTIC_VAR_DECL
    */
    @Override
    public Object visitVarDecl(EMJParser.VarDeclContext ctx) {

        // SEMANTIC_CHECK_VAR_ID_ALREADY_EXISTS : Check if the id in the variable declaration does not exist yet
        String varId = ctx.EMOJI_ID().getText();

        // If variable id already exists in the current scope, throw an error
        if(this.symbolTable.isVariableDefined(varId)) {
            this.errorLogger.addError(new EMJError("varIdAlreadyExists", ctx.getText(), ctx.start.getLine()));
        } else {
            // Si la variable n'existe pas encore, l'ajouter à la table des symboles
            String varType = getTypeFromContext(ctx.type());
            boolean isInitialized = ctx.expression() != null;
            try {
                this.symbolTable.addVariable(varId, varType, isInitialized);
            } catch (IllegalArgumentException e) {
                // Gérer les erreurs potentielles (type invalide, etc.)
                this.errorLogger.addError(new EMJError("invalidVariableDeclaration", e.getMessage(), ctx.start.getLine()));
            }
            
            // Vérification de compatibilité de type pour l'initialisation
            if (isInitialized) {
                // TODO: Implémenter la vérification de compatibilité de type pour l'initialisation
                // ctx.expression() contient l'expression à analyser
            }
        }

        return null;
    }

    private String getTypeFromContext(EMJParser.TypeContext typeCtx) {
        if (typeCtx.INT_TYPE() != null) {
            return "INT";
        } else if (typeCtx.BOOL_TYPE() != null) {
            return "BOOL";
        } else if (typeCtx.CHAR_TYPE() != null) {
            return "CHAR";
        } else if (typeCtx.STRING_TYPE() != null) {
            return "STRING";
        }

        return "UNKNOWN";
    }


    @Override
    public Object visitMapFile(EMJParser.MapFileContext ctx) {
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
                    "The map must at least have a width >= 2 and a height >= 2 (current : " + width + "x" + height + ").",
                    ctx.start.getLine()
            ));
        }

        if (expectedCellCount != actualCellCount) {
            this.errorLogger.addError(new EMJError(
                    "mapDimensionsMismatch",
                    "The size given (" + width + "x" + height + " = " + expectedCellCount + " cells) don't match with the number of cells given (" + actualCellCount + ").",
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
                    "The map must contain exactly 1 Police Car, found : " + policeCarCount,
                    ctx.start.getLine()
            ));
        }

        if (thiefCount < 1) {
            this.errorLogger.addError(new EMJError(
                    "mapThiefMissing",
                    "The map must contain at least 1 Thief, found : " + thiefCount,
                    ctx.start.getLine()
            ));
        }

        if (roadCount < 1) {
            this.errorLogger.addError(new EMJError(
                    "mapRoadMissing",
                    "The map must contain at least 1 Road, found : " + roadCount,
                    ctx.start.getLine()
            ));
        }

        return null;
    }



    /**
     * Visite une instruction d'affectation de variable
     * Vérifie que la variable a été déclarée et que le type de l'expression est compatible
     */
    @Override
    public Object visitVarAffect(EMJParser.VarAffectContext ctx) {
        // Vérifier si la variable a été déclarée
        String varId = ctx.EMOJI_ID().getText();
        if (!this.symbolTable.isVariableDefined(varId)) {
            this.errorLogger.addError(new EMJError(
                "varIdNotDecl",
                "Variable " + varId + " not declared before use", 
                ctx.start.getLine()
            ));
        } else {
            // TODO: Vérifier la compatibilité de type entre la variable et l'expression
            // Visiter l'expression pour vérifier sa validité
            visit(ctx.expression());
        }
        return null;
    }

    /**
     * Visite une déclaration de fonction
     * Vérifie que la fonction a un retour explicite conformément à la spécification
     */
    @Override
    public Object visitFunctionDecl(EMJParser.FunctionDeclContext ctx) {
        // Récupérer le type de retour, l'identifiant et le bloc de code
        String returnType = getTypeFromContext(ctx.type());
        String funcId = ctx.EMOJI_ID().getText();
        boolean hasExplicitReturn = false;
        
        // Vérifier si la fonction existe déjà
        if (this.symbolTable.isFunctionDefined(funcId)) {
            this.errorLogger.addError(new EMJError(
                "functionIdAlreadyExists",
                "Function " + funcId + " already defined",
                ctx.start.getLine()
            ));
            return null;
        }
        
        // Ajouter la fonction à la table des symboles
        this.symbolTable.pushScope(funcId); // Création d'un nouveau scope pour les paramètres
        
        // Traiter les paramètres de fonction s'ils existent
        List<String> paramTypes = new ArrayList<>();
        if (ctx.optionalParamList() != null && ctx.optionalParamList().paramList() != null) {
            for (EMJParser.ParamContext param : ctx.optionalParamList().paramList().param()) {
                String paramType = getTypeFromContext(param.type());
                String paramId = param.EMOJI_ID().getText();
                paramTypes.add(paramType);
                
                // Ajouter le paramètre à la table des symboles (scope actuel)
                try {
                    this.symbolTable.addVariable(paramId, paramType, true);
                } catch (IllegalArgumentException e) {
                    this.errorLogger.addError(new EMJError(
                        "invalidParameterDeclaration",
                        e.getMessage(),
                        param.start.getLine()
                    ));
                }
            }
        }
        
        // Enregistrer la fonction dans la table des symboles
        try {
            this.symbolTable.addFunction(funcId, returnType, paramTypes);
        } catch (IllegalArgumentException e) {
            this.errorLogger.addError(new EMJError(
                "invalidFunctionDeclaration",
                e.getMessage(),
                ctx.start.getLine()
            ));
        }
        
        // Visiter le corps de la fonction pour analyser les instructions
        hasExplicitReturn = checkFunctionBodyForReturn(ctx.block(), returnType);
        
        // Vérifier s'il y a un retour explicite dans le corps de la fonction
        if (!hasExplicitReturn) {
            this.errorLogger.addError(new EMJError(
                "missingReturnStatement",
                "La fonction " + funcId + " doit avoir un retour explicite",
                ctx.start.getLine()
            ));
        }
        
        this.symbolTable.popScope(); // Sortie du scope des paramètres
        return null;
    }
    
    /**
     * Vérifie si le bloc de code d'une fonction contient un retour explicite
     * @param blockCtx Le contexte du bloc de code
     * @param expectedReturnType Le type de retour attendu
     * @return true si le bloc contient un retour explicite, false sinon
     */
    private boolean checkFunctionBodyForReturn(EMJParser.BlockContext blockCtx, String expectedReturnType) {
        if (blockCtx == null || blockCtx.statement() == null) {
            return false;
        }
        
        // Parcourir toutes les instructions du bloc pour trouver un retour
        for (EMJParser.StatementContext stmtCtx : blockCtx.statement()) {
            if (stmtCtx.returnStatement() != null) {
                return true;
            }
            // Vérifier les retours dans les blocs imbriqués (if, while, etc.)
            if (stmtCtx.ifStatement() != null) {
                // Pour un if complet (avec else), les deux branches doivent avoir un retour
                if (stmtCtx.ifStatement().block().size() == 2) {
                    boolean thenHasReturn = checkFunctionBodyForReturn(stmtCtx.ifStatement().block(0), expectedReturnType);
                    boolean elseHasReturn = checkFunctionBodyForReturn(stmtCtx.ifStatement().block(1), expectedReturnType);
                    if (thenHasReturn && elseHasReturn) {
                        return true;
                    }
                }
            }
        }
        
        return false;
    }
    
    /**
     * Visite une instruction de retour
     * Vérifie la compatibilité du type de retour avec le type de la fonction contenant
     */
    @Override
    public Object visitReturnStatement(EMJParser.ReturnStatementContext ctx) {
        // Plusieurs syntaxes de retour sont possibles selon l'énoncé
        // RETURN expression?, RETURN VOID_TYPE, VOID_TYPE et RETURN_VOID
        
        // TODO: Vérifier la compatibilité du type de retour avec le type de fonction attendu
        
        // Si l'instruction contient une expression, la visiter
        if (ctx.expression() != null) {
            visit(ctx.expression());
        }
        
        return null;
    }
    
    /**
     * Visite un fichier d'instructions
     * Point d'entrée pour l'analyse des programmes EMJ
     */
    @Override
    public Object visitInstructionFile(EMJParser.InstructionFileContext ctx) {
        // Réinitialiser la table des symboles pour le nouveau fichier
        this.symbolTable = new EMJSymbolTable();
        
        // Visiter toutes les déclarations au niveau global
        for (EMJParser.GlobalDeclContext declCtx : ctx.globalDecl()) {
            visit(declCtx);
        }
        
        return null;
    }
    
    /**
     * Visite une expression
     */
    @Override
    public Object visitExpression(EMJParser.ExpressionContext ctx) {
        // TODO: Implémenter l'analyse des expressions
        return super.visitExpression(ctx);
    }
    
    /**
     * Visite un appel de fonction
     * Vérifie que la fonction existe et que les arguments sont compatibles
     */
    @Override
    public Object visitFunctionCall(EMJParser.FunctionCallContext ctx) {
        String funcId = ctx.EMOJI_ID().getText();
        
        // Vérifier si la fonction existe
        if (!this.symbolTable.isFunctionDefined(funcId)) {
            this.errorLogger.addError(new EMJError(
                "functionNotDefined",
                "Function " + funcId + " not defined before use",
                ctx.start.getLine()
            ));
            return null;
        }
        
        // TODO: Vérifier le nombre et le type des arguments
        
        // Visiter les expressions des arguments pour s'assurer qu'elles sont valides
        if (ctx.optionalArgList() != null && ctx.optionalArgList().argList() != null) {
            for (EMJParser.ExpressionContext exprCtx : ctx.optionalArgList().argList().expression()) {
                visit(exprCtx);
            }
        }
        
        return null;
    }
    
    /**
     * Visite une structure conditionnelle (if)
     */
    @Override
    public Object visitIfStatement(EMJParser.IfStatementContext ctx) {
        // Visiter la condition
        visit(ctx.expression());
        
        // Entrer dans un nouveau scope pour chaque bloc
        this.symbolTable.pushScope("if_then");
        visit(ctx.block(0)); // Bloc then
        this.symbolTable.popScope();
        
        // Bloc else si présent
        if (ctx.block().size() > 1) {
            this.symbolTable.pushScope("if_else");
            visit(ctx.block(1));
            this.symbolTable.popScope();
        }
        
        return null;
    }
    
    /**
     * Visite une structure de boucle (while)
     */
    @Override
    public Object visitWhileStatement(EMJParser.WhileStatementContext ctx) {
        // Visiter la condition
        visit(ctx.expression());
        
        // Entrer dans un nouveau scope pour le bloc
        this.symbolTable.pushScope("while");
        visit(ctx.block());
        this.symbolTable.popScope();
        
        return null;
    }
    
    /**
     * Vérifie la présence d'un retour explicite dans le corps d'une fonction
     * @param blockCtx Contexte du bloc à vérifier
     * @param returnType Type de retour attendu
     * @return true si le bloc contient un retour explicite compatible avec le type attendu, false sinon
     */
    private boolean checkFunctionBodyForReturn(EMJParser.BlockContext blockCtx, String returnType) {
        // Si le bloc est vide, il n'y a pas de retour
        if (blockCtx == null || blockCtx.statement() == null || blockCtx.statement().isEmpty()) {
            return false;
        }
        
        // Parcourir toutes les instructions du bloc
        for (EMJParser.StatementContext stmtCtx : blockCtx.statement()) {
            // Vérifier si c'est une instruction de retour
            if (stmtCtx.returnStatement() != null) {
                EMJParser.ReturnStatementContext returnStmtCtx = stmtCtx.returnStatement();
                
                // Vérifier le type de retour void
                if ("VOID".equals(returnType)) {
                    // Pour les fonctions void, toute forme de retour explicite est valide
                    if (returnStmtCtx.VOID_TYPE() != null || 
                        returnStmtCtx.RETURN_VOID() != null || 
                        (returnStmtCtx.RETURN() != null && returnStmtCtx.expression() == null)) {
                        return true;
                    }
                } else {
                    // Pour les fonctions non-void, il doit y avoir un retour avec expression
                    if (returnStmtCtx.expression() != null) {
                        return true;
                    }
                }
            }
            
            // Pour les instructions if, vérifier les blocs then et else
            if (stmtCtx.ifStatement() != null) {
                EMJParser.IfStatementContext ifStmtCtx = stmtCtx.ifStatement();
                
                // Si les deux branches (then et else) ont un retour, c'est valide
                if (ifStmtCtx.block().size() >= 2) {
                    boolean thenHasReturn = checkFunctionBodyForReturn(ifStmtCtx.block(0), returnType);
                    boolean elseHasReturn = checkFunctionBodyForReturn(ifStmtCtx.block(1), returnType);
                    
                    if (thenHasReturn && elseHasReturn) {
                        return true;
                    }
                }
            }
        }
        
        return false;
    }
    
    /**
     * Visite une instruction de retour
     * Vérifie que le type de retour est compatible avec la fonction courante
     * @param ctx Contexte de l'instruction de retour
     * @return null
     */
    @Override
    public Object visitReturnStatement(EMJParser.ReturnStatementContext ctx) {
        // Obtenir le type de la fonction courante
        String currentFunction = this.symbolTable.getCurrentScope();
        if (currentFunction == null || "global".equals(currentFunction)) {
            this.errorLogger.addError(new EMJError(
                "returnOutsideFunction",
                "Instruction de retour en dehors d'une fonction",
                ctx.start.getLine()
            ));
            return null;
        }
        
        String expectedReturnType = this.symbolTable.getFunctionReturnType(currentFunction);
        if (expectedReturnType == null) {
            // Ne devrait pas arriver si la table des symboles fonctionne correctement
            this.errorLogger.addError(new EMJError(
                "unknownFunctionReturnType",
                "Type de retour de la fonction " + currentFunction + " inconnu",
                ctx.start.getLine()
            ));
            return null;
        }
        
        // Déterminer si c'est un retour void ou avec valeur
        boolean isVoidReturn = false;
        
        // Vérifier les différentes formes de retour void explicite
        if (ctx.VOID_TYPE() != null || ctx.RETURN_VOID() != null) {
            isVoidReturn = true;
        } else if (ctx.expression() == null && ctx.RETURN() != null) {
            // RETURN sans expression (implicite)
            isVoidReturn = true;
        }
        
        // Vérifier la compatibilité des types de retour
        if (isVoidReturn) {
            if (!"VOID".equals(expectedReturnType)) {
                this.errorLogger.addError(new EMJError(
                    "incompatibleReturnType",
                    "Retour void incompatible avec le type de retour attendu: " + expectedReturnType,
                    ctx.start.getLine()
                ));
            }
            return null;
        }
        
        // Si on arrive ici, c'est un retour avec une expression (non-void)
        if ("VOID".equals(expectedReturnType)) {
            this.errorLogger.addError(new EMJError(
                "incompatibleReturnType",
                "Retour avec expression incompatible avec le type void",
                ctx.start.getLine()
            ));
            return null;
        }
        
        // Visiter l'expression pour obtenir son type 
        // (cette partie peut être complétée dans une version future pour vérifier la compatibilité des types)
        if (ctx.expression() != null) {
            visit(ctx.expression());
            // Ici, on pourrait récupérer le type de l'expression et le comparer avec expectedReturnType
            // Mais cela nécessiterait d'avoir une méthode pour déterminer le type des expressions
        }
        
        return null;
    }
}