package be.unamur.info.b314.compiler.emj;

import be.unamur.info.b314.compiler.EMJParser;

/**
 * Visiteur pour le langage EMJ, étendant le visiteur de base généré par ANTLR
 * Implémente les vérifications sémantiques pour le compilateur EMJ
 * 
 * @author Alix Decrop (original)
 * @version 2.0
 */
public class EMJVisitor extends be.unamur.info.b314.compiler.EMJParserBaseVisitor<Object> {

    private final EMJErrorLogger errorLogger;
    private final EMJSymbolTable symbolTable;
    // Ce champ sera utilisé pour les futures implémentations de vérification de retour
    private String currentFunction;

    /**
     * Constructeur du visiteur EMJ
     */
    public EMJVisitor() {
        this.errorLogger = new EMJErrorLogger();
        this.symbolTable = new EMJSymbolTable();
        this.currentFunction = null;
    }

    /**
     * Récupère le journal d'erreurs
     */
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
        int policeCarCount = 0;

        for (EMJParser.MapCellContext cellCtx : ctx.mapCell()) {
            if (cellCtx.COP() != null) {
                policeCarCount++;
            }
        }

        if (policeCarCount != 1) {
            this.errorLogger.addError(new EMJError(
                    "mapPoliceCarCountInvalid",
                    "The map must contain exactly 1 Police Car, found : " + policeCarCount,
                    ctx.start.getLine()
            ));
        }
        return null;
    }



//
//
//    SEMANTIC_VAR_AFFECT
//    */
//    @Override
//    public Object visitVarAffect(EMJParser.VarAffectContext ctx) {
//
//        // SEMANTIC_CHECK_VAR_IS_DECL : Check if an id in a variable affectation has been previously declared
//        String varId = ctx.EMOJI_ID().getText();
//
//        // If the variable id is not contained in the variable id array, add an error
//        if(!this.varIds.contains(varId)) {
//            this.errorLogger.addError(new EMJError("varIdNotDecl", ctx.getText(), ctx.start.getLine()));
//        }
//
//        return null;
//    }
}