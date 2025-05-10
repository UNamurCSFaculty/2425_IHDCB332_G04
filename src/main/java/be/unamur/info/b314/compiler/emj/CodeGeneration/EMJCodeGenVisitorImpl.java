package be.unamur.info.b314.compiler.emj.CodeGeneration;

import be.unamur.info.b314.compiler.EMJParser;
import be.unamur.info.b314.compiler.EMJParserBaseVisitor;
import be.unamur.info.b314.compiler.emj.EMJVarType;
// Utilisation du chemin complet pour éviter les problèmes de résolution de package
import be.unamur.info.b314.compiler.emj.Result.ContextResult;
import com.vdurmont.emoji.EmojiParser;
import org.stringtemplate.v4.ST;
import org.stringtemplate.v4.STGroup;
import org.stringtemplate.v4.STGroupFile;

import java.util.*;

public class EMJCodeGenVisitorImpl extends EMJParserBaseVisitor<Object> implements EMJCodeGenVisitor {
    private STGroup templates;
    private Map<String, String> emojiToIdentifier;
    private int indentLevel = 0;
    private int loopCounter = 0;


    public EMJCodeGenVisitorImpl() {
    }


    private static final Map<String, String> emojiShortNames = new HashMap<>();

    static {
        emojiShortNames.put("🚗", "car");
        emojiShortNames.put("🦹", "thief");
        emojiShortNames.put("📻", "radio");
        emojiShortNames.put("🚨", "light");
        emojiShortNames.put("⬆️", "up");
        emojiShortNames.put("⬇️", "down");
        emojiShortNames.put("➡️", "right");
        emojiShortNames.put("⬅️", "left");
        emojiShortNames.put("🛑", "stop");
        emojiShortNames.put("🔢", "int");
        emojiShortNames.put("🔟", "bool");
        emojiShortNames.put("🔣", "char");
        emojiShortNames.put("🔡", "str");
        emojiShortNames.put("🌀", "void");
        emojiShortNames.put("↩️", "return");
        emojiShortNames.put("❓", "or");
        emojiShortNames.put("🤝", "and");
        emojiShortNames.put("⛔", "not");
        emojiShortNames.put("📦", "package");
        emojiShortNames.put("🏠", "main");
        emojiShortNames.put("🚔", "cop");
        emojiShortNames.put("🛣️", "road");
        emojiShortNames.put("🌋", "volcano");
        emojiShortNames.put("🏘️", "house");
        emojiShortNames.put("🚧", "barrier");
        emojiShortNames.put("🚜", "tractor");
        emojiShortNames.put("🌊", "water");
        //emojiShortNames.put("🐜", "ant"); // si utilisé
        // Ajoute d'autres emojis si nécessaire
    }

    @Override
    public ContextResult visitRoot(EMJParser.RootContext ctx) {
        if (ctx.programFile() != null) {
            return visitProgramFile(ctx.programFile());
        }
        else if (ctx.mapFile() != null) {
            return visitMapFile(ctx.mapFile());
        }
        return null;
    }

    @Override
    public ContextResult visitProgramFile(EMJParser.ProgramFileContext ctx) {
        Map<String, Object> attributes = new HashMap<>();

        // Génère les instructions principales (ex-main)
        ContextResult mainResult = (ContextResult) visit(ctx.mainFunction());
        
        if (mainResult == null) {
            System.err.println("Erreur: mainResult est null. Impossible de générer le corps du programme.");
            return ContextResult.invalid();
        }
        
        if (!mainResult.isValid()) {
            System.err.println("Avertissement: mainResult n'est pas valide.");
        }
        
        // Vérification et ajout de l'attribut 'body'
        if (mainResult.getAttributes().containsKey("body")) {
            Object bodyObj = mainResult.getAttributes().get("body");
            if (bodyObj instanceof List) {
                List<?> bodyList = (List<?>) bodyObj;
                System.out.println("Corps du main trouvé avec " + bodyList.size() + " instructions.");
                attributes.put("body", bodyList);
            } else {
                System.err.println("Erreur: l'attribut 'body' n'est pas une liste comme attendu. Type: " + 
                                 (bodyObj != null ? bodyObj.getClass().getName() : "null"));
                // Créer une liste vide plutôt que de générer une erreur
                attributes.put("body", new ArrayList<String>());
            }
        } else {
            System.err.println("Erreur: l'attribut 'body' est manquant dans mainResult.");
            // Créer une liste vide plutôt que de générer une erreur
            attributes.put("body", new ArrayList<String>());
        }

        // Génère les fonctions utilisateur
        List<String> renderedFunctions = new ArrayList<>();
        if (ctx.functionDecl() != null && !ctx.functionDecl().isEmpty()) {
            System.out.println("Génération de " + ctx.functionDecl().size() + " fonctions utilisateur.");
            
            for (EMJParser.FunctionDeclContext funcCtx : ctx.functionDecl()) {
                try {
                    incrIndent();
                    ContextResult funcResult = (ContextResult) visit(funcCtx);
                    decrIndent();

                    if (funcResult == null || !funcResult.isValid()) {
                        System.err.println("Erreur lors de la génération de la fonction: " + 
                                         (funcCtx.EMOJI_ID() != null ? funcCtx.EMOJI_ID().getText() : "<sans nom>"));
                        continue;
                    }

                    ST funcTemplate = templates.getInstanceOf(funcResult.getTemplateName());
                    if (funcTemplate == null) {
                        System.err.println("Template de fonction non trouvé: " + funcResult.getTemplateName());
                        continue;
                    }

                    for (Map.Entry<String, Object> entry : funcResult.getAttributes().entrySet()) {
                        try {
                            funcTemplate.add(entry.getKey(), entry.getValue());
                        } catch (Exception e) {
                            System.err.println("Erreur lors de l'ajout de l'attribut '" + 
                                             entry.getKey() + "' au template de fonction: " + e.getMessage());
                        }
                    }
                    
                    String renderedFunction = funcTemplate.render();
                    renderedFunctions.add(renderedFunction);
                    System.out.println("Fonction rendue avec succès: " + 
                                     (funcCtx.EMOJI_ID() != null ? funcCtx.EMOJI_ID().getText() : "<sans nom>"));
                } catch (Exception e) {
                    System.err.println("Exception lors de la génération d'une fonction: " + e.getMessage());
                    e.printStackTrace();
                }
            }
        } else {
            System.out.println("Aucune fonction utilisateur à générer.");
        }
        
        attributes.put("functions", renderedFunctions);
        System.out.println("Génération du programme terminée avec " + renderedFunctions.size() + 
                          " fonctions utilisateur.");

        return ContextResult.valid(attributes, "program");
    }

    @Override
    public ContextResult visitMapFile(EMJParser.MapFileContext ctx) {
        Map<String, Object> attributes = new HashMap<>();

        int width = Integer.parseInt(ctx.INT_VALUE(0).getText());
        int height = Integer.parseInt(ctx.INT_VALUE(1).getText());

        // Nettoie l'orientation (⬆️ -> up, etc.)
        String orientation = sanitizeEmoji(ctx.orientation().getText());

        // Construction des lignes de la carte
        List<String> mapLines = new ArrayList<>();
        int index = 0;
        for (int i = 0; i < height; i++) {
            StringBuilder row = new StringBuilder();
            for (int j = 0; j < width; j++) {
                EMJParser.MapCellContext cellCtx = ctx.mapCell(index++);
                String emoji = cellCtx.getText();
                String cleaned = emojiShortNames.getOrDefault(emoji, "unknown");
                row.append(cleaned);
            }
            mapLines.add("\"" + row + "\"");
        }

        attributes.put("width", width);
        attributes.put("height", height);
        attributes.put("orientation", orientation);
        attributes.put("map", mapLines); // List<String>, dans le template avec wrap="\""

        return ContextResult.valid(attributes, "mapProgram");
    }

    @Override
    public ContextResult visitMainFunction(EMJParser.MainFunctionContext ctx) {
        Map<String, Object> attributes = new HashMap<>();

        // Visit all statements and render them
        List<String> renderedStatements = new ArrayList<>();
        for (EMJParser.StatementContext stmtCtx : ctx.statement()) {
            ContextResult stmtResult = (ContextResult) visit(stmtCtx);
            if (stmtResult == null) {
                System.err.println("Erreur: stmtResult est null pour le statement: " + stmtCtx.getText());
                continue;
            }
            
            if (!stmtResult.isValid()) {
                System.err.println("Avertissement: stmtResult n'est pas valide pour le statement: " + stmtCtx.getText());
            }
            
            String renderedStatement = renderResult(stmtResult);
            if (renderedStatement != null && !renderedStatement.isEmpty()) {
                renderedStatements.add(renderedStatement);
            }
        }

        // Vérifier si le template existe réellement et quels sont ses attributs
        if (templates != null) {
            ST mainFunctionTemplate = templates.getInstanceOf("mainFunction");
            if (mainFunctionTemplate != null) {
                System.out.println("Template mainFunction trouvé!");
                // Test du template avec l'attribut 'body'
                ST testTemplate = new ST(mainFunctionTemplate);
                try {
                    testTemplate.add("body", renderedStatements);
                    System.out.println("Rendu test du template mainFunction: \n" + testTemplate.render());
                } catch (Exception e) {
                    System.err.println("Erreur lors du test du template mainFunction avec l'attribut 'body': " + e.getMessage());
                }
            } else {
                System.err.println("Template mainFunction non trouvé!");
            }
        }

        // Debug: afficher le nombre d'instructions renderisées
        System.out.println("Nombre d'instructions renderisées pour le main: " + renderedStatements.size());
        if (!renderedStatements.isEmpty()) {
            System.out.println("Exemple d'une instruction renderisée: " + renderedStatements.get(0));
        }

        attributes.put("body", renderedStatements);
        return ContextResult.valid(attributes, "mainFunction");
    }

    private String renderResult(ContextResult result) {
        if (!result.isValid()) {
            return "";
        }
        
        // Vérifier que les templates sont chargés
        if (templates == null) {
            System.err.println("Templates not loaded. Check initialization.");
            return "# Templates not loaded";
        }

        // Obtenir le template
        String templateName = result.getTemplateName();
        ST template = templates.getInstanceOf(templateName);
        if (template == null) {
            System.err.println("Template not found: " + templateName);
            return "# Template not found: " + templateName;
        }

        // Ajouter les attributs de manière sécurisée
        for (Map.Entry<String, Object> entry : result.getAttributes().entrySet()) {
            String key = entry.getKey();
            Object value = entry.getValue();
            
            try {
                template.add(key, value);
            } catch (IllegalArgumentException e) {
                System.err.println("Error adding attribute '" + key + "' to template '" + templateName + "': " + e.getMessage());
                // Continuer avec les autres attributs plutôt que d'échouer complètement
            }
        }

        return template.render();
    }

    @Override
    public ContextResult visitStatement(EMJParser.StatementContext ctx) {
        if (ctx.varDecl() != null) {
            return (ContextResult) visit(ctx.varDecl());
        } else if (ctx.assignment() != null) {
            return (ContextResult) visit(ctx.assignment());
        } else if (ctx.functionCallStmt() != null) {
            return (ContextResult) visit(ctx.functionCallStmt());
        } else if (ctx.ifStatement() != null) {
            return (ContextResult) visit(ctx.ifStatement());
        } else if (ctx.loopStatement() != null) {
            return (ContextResult) visit(ctx.loopStatement());
        } else if (ctx.returnStatement() != null) {
            return (ContextResult) visit(ctx.returnStatement());
        } else if (ctx.predefinedStmt() != null) {
            return (ContextResult) visit(ctx.predefinedStmt());
        }

        return ContextResult.invalid();
    }

    @Override
    public ContextResult visitFunctionDecl(EMJParser.FunctionDeclContext ctx) {
        Map<String, Object> attributes = new HashMap<>();
        List<String> parameters = new ArrayList<>();
        List<String> bodyLines = new ArrayList<>();

        String varName = sanitizeEmoji(ctx.EMOJI_ID().getText());
        attributes.put("name", varName);

        if (ctx.optionalParamList() != null && ctx.optionalParamList().paramList() != null) {
            List<EMJParser.ParamContext> parametersContext = ctx.optionalParamList().paramList().param();
            for (EMJParser.ParamContext paramCtx : parametersContext) {
                ContextResult result = (ContextResult) visit(paramCtx);
                if (result.isValid()) {
                    ST subTemplate = templates.getInstanceOf(result.getTemplateName());
                    for (Map.Entry<String, Object> entry : result.getAttributes().entrySet()) {
                        subTemplate.add(entry.getKey(), entry.getValue());
                    }
                    parameters.add(subTemplate.render());
                }
            }
        }
        attributes.put("parameters", parameters);

        for (EMJParser.StatementContext stmtCtx : ctx.statement()) {
            ContextResult result = (ContextResult) visit(stmtCtx);
            if (result.isValid()) {
                ST subTemplate = templates.getInstanceOf(result.getTemplateName());
                for (Map.Entry<String, Object> entry : result.getAttributes().entrySet()) {
                    subTemplate.add(entry.getKey(), entry.getValue());
                }
                bodyLines.add(subTemplate.render());
            }
        }
        attributes.put("body", bodyLines);

        ContextResult returnStmtResult = (ContextResult) visit(ctx.returnStatement());
        attributes.put("return", returnStmtResult.getAttributes().values());

        return ContextResult.valid(attributes, "functionDecl");
    }

    @Override
    public ContextResult visitReturnStatement(EMJParser.ReturnStatementContext ctx) {
        Map<String, Object> attributes = new HashMap<>();

        // Check if it's a void return
        if (ctx.VOID_TYPE() != null || ctx.RETURN_VOID() != null || ctx.expression() == null) {
            attributes.put("value", "None");
        } else {
            // Visit the expression
            ContextResult exprResult = (ContextResult) visit(ctx.expression());
            attributes.put("value", exprResult.getAttributes().get("code"));
        }

        return ContextResult.valid(attributes, "return");
    }

    @Override
    public ContextResult visitParam(EMJParser.ParamContext ctx) {
        Map<String, Object> attributes = new HashMap<>();

        String varName = sanitizeEmoji(ctx.EMOJI_ID().getText());
        attributes.put("name", varName);
        return ContextResult.valid(attributes, "parameter");
    }

    @Override
    public ContextResult visitTupleValue(EMJParser.TupleValueContext ctx) {
        Map<String, Object> attributes = new HashMap<>();

        // First value
        ContextResult val1Result = (ContextResult) visit(ctx.expression(0));
        // Second value
        ContextResult val2Result = (ContextResult) visit(ctx.expression(1));

        attributes.put("code", "(" + val1Result.getAttributes().get("code") + ", " +
                val2Result.getAttributes().get("code") + ")");

        return ContextResult.valid(attributes, "primaryExpression");
    }

    @Override
    public ContextResult visitVarDecl(EMJParser.VarDeclContext ctx) {
        Map<String, Object> attributes = new HashMap<>();

        String varName = sanitizeEmoji(ctx.EMOJI_ID().getText());
        attributes.put("name", varName);

        // Obtenir le type
        String typeResult = getTypeFromContext(ctx.type());
        attributes.put("type", typeResult);

        // Gérer la valeur initiale
        if (ctx.expression() != null) {
            ContextResult exprResult = (ContextResult) visit(ctx.expression());
            attributes.put("value", exprResult.getAttributes().get("code"));
        } else {
            // Valeur par défaut selon le type
            switch (typeResult) {
                case "int":
                    attributes.put("value", "0");
                    break;
                case "bool":
                    attributes.put("value", "False");
                    break;
                case "str":
                case "char":
                    attributes.put("value", "\"\"");
                    break;
                default:
                    if (typeResult.startsWith("tuple")) {
                        attributes.put("value", "(None, None)");
                    } else {
                        attributes.put("value", "None");
                    }
            }
        }

        attributes.put("indent", getIndent());
        return ContextResult.valid(attributes, "varDecl");
    }

    @Override
    public ContextResult visitBlock(EMJParser.BlockContext ctx) {
        Map<String, Object> attributes = new HashMap<>();

        // Visit all statements and render them
        List<String> renderedStatements = new ArrayList<>();
        for (EMJParser.StatementContext stmtCtx : ctx.statement()) {
            ContextResult stmtResult = (ContextResult) visit(stmtCtx);

            // Debug: Print what result we got
//            System.out.println("Block Statement type: " + stmtResult.getTemplateName());
//            System.out.println("Block Attributes: " + stmtResult.getAttributes().keySet());

            renderedStatements.add(renderResult(stmtResult));
        }

        // Put the rendered statements in attributes - use consistent naming with templates
        attributes.put("statements", renderedStatements); // For block template

        return ContextResult.valid(attributes, "block");
    }

    @Override
    public ContextResult visitIfStatement(EMJParser.IfStatementContext ctx) {
        Map<String, Object> attributes = new HashMap<>();
        attributes.put("indent",getIndent());
        String emptyBlock = "pass #empty block";

        ContextResult conditionResult = (ContextResult) visit(ctx.expression());
        attributes.put("condition", renderResult(conditionResult));

        incrIndent();
        String renderedIfBlock = String.format("%s%s", getIndent(), emptyBlock);
        if (!ctx.block().isEmpty()) {
            if (!ctx.block(0).isEmpty()) {
                renderedIfBlock = renderResult((ContextResult) visit(ctx.block(0)));
            }
        }
        decrIndent();
        attributes.put("bodyIf", renderedIfBlock);

        // Bloc else si présent
        if (ctx.block().size() > 1) {
            incrIndent();
            String renderedElseBlock = String.format("%s%s", getIndent(), emptyBlock);
            if (!ctx.block().isEmpty() && !ctx.block(1).isEmpty()) {
                renderedElseBlock = renderResult((ContextResult) visit(ctx.block(1)));
            }
            decrIndent();
            attributes.put("bodyElse", renderedElseBlock);
        }else if (ctx.SKIPPING()!=null){
            incrIndent();
            attributes.put("bodyElse", String.format("%spass  # skip", getIndent()));
            decrIndent();
        }
        return ContextResult.valid(attributes, "ifStatement");
    }

    @Override
    public ContextResult visitLoopStatement(EMJParser.LoopStatementContext ctx) {
        Map<String, Object> attributes = new HashMap<>();
        attributes.put("indent",getIndent());
        String emptyBlock="pass #empty block";

        // Vérifier si c'est une boucle while (identifiée par l'emoji ♾️)
        if (ctx.WHILE() != null) {
            // Condition
            ContextResult conditionResult = (ContextResult) visit(ctx.expression());
            attributes.put("condition", renderResult(conditionResult));

            incrIndent();
            String renderedBlock = String.format("%s%s", getIndent(), emptyBlock);
            if (!ctx.block().statement().isEmpty()) {
                renderedBlock = renderResult((ContextResult) visit(ctx.block()));
            }
            decrIndent();
            // Ensure attribute name matches template parameter name
            attributes.put("body", renderedBlock);
            return ContextResult.valid(attributes, "whileStatement");
        } else if (ctx.FOR() != null) {// Cas pour la boucle for (identifiée par l'emoji 🔁)
            // Nombre d'itérations
            ContextResult exprResult = (ContextResult) visit(ctx.expression());
            attributes.put("range", renderResult(exprResult));
            attributes.put("counter", loopCounter++);

            incrIndent();
            String renderedBlock = String.format("%s%s", getIndent(), emptyBlock);
            if (!ctx.block().statement().isEmpty()) {
                renderedBlock = renderResult((ContextResult) visit(ctx.block()));
            }
            decrIndent();

            // Ensure attribute name matches template parameter name
            attributes.put("body", renderedBlock);
            return ContextResult.valid(attributes, "forStatement");
        }
        return null;
    }

    @Override
    public ContextResult visitLeftExpression(EMJParser.LeftExpressionContext ctx) {
        Map<String, Object> attributes = new HashMap<>();

        // Get variable name
        String varName = sanitizeEmoji(ctx.EMOJI_ID().getText());

        // Check if it's a tuple access
        if (ctx.TUPLE_FIRST() != null) {
            attributes.put("code", varName + "[0]");
        } else if (ctx.TUPLE_SECOND() != null) {
            attributes.put("code", varName + "[1]");
        } else {
            attributes.put("code", varName);
        }

        return ContextResult.valid(attributes, "leftExpression");
    }


    @Override
    public ContextResult visitAssignment(EMJParser.AssignmentContext ctx) {
        Map<String, Object> attributes = new HashMap<>();

        // Left expression
        ContextResult leftResult = (ContextResult) visit(ctx.leftExpression());
        attributes.put("left", leftResult.getAttributes().get("code"));

        // Right expression
        ContextResult rightResult = (ContextResult) visit(ctx.expression());
        attributes.put("right", rightResult.getAttributes().get("code"));

        attributes.put("indent", getIndent());
        return ContextResult.valid(attributes,"assignment");
    }

    @Override
    public ContextResult visitExpression(EMJParser.ExpressionContext ctx) {
        return (ContextResult) visit(ctx.orExpression());
    }

    @Override
    public ContextResult visitOrExpression(EMJParser.OrExpressionContext ctx) {
        if (!ctx.OR().isEmpty()) {
            Map<String, Object> attributes = new HashMap<>();
            StringBuilder code = new StringBuilder();

            for (int i = 0; i < ctx.andExpression().size(); i++) {
                ContextResult exprResult = (ContextResult) visit(ctx.andExpression(i));
                code.append(exprResult.getAttributes().get("code"));

                if (i < ctx.andExpression().size() - 1) {
                    code.append(" or ");
                }
            }

            attributes.put("code", code.toString());
            return ContextResult.valid(attributes, "primaryExpression");
        } else if (!ctx.andExpression().isEmpty()) {
            return (ContextResult) visit(ctx.andExpression(0));
        }

        return null;
    }

    @Override
    public ContextResult visitAndExpression(EMJParser.AndExpressionContext ctx) {
        if (!ctx.AND().isEmpty()) {
            Map<String, Object> attributes = new HashMap<>();
            StringBuilder code = new StringBuilder();

            for (int i = 0; i < ctx.notExpression().size(); i++) {
                ContextResult exprResult = (ContextResult) visit(ctx.notExpression(i));
                code.append(exprResult.getAttributes().get("code"));

                if (i < ctx.notExpression().size() - 1) {
                    code.append(" and ");
                }
            }

            attributes.put("code", code.toString());
            return ContextResult.valid(attributes, "primaryExpression");
        } else if (!ctx.notExpression().isEmpty()) {
            return (ContextResult) visit(ctx.notExpression(0));
        }

        return null;
    }

    @Override
    public ContextResult visitNotExpression(EMJParser.NotExpressionContext ctx) {
        if (ctx.NOT() != null) {
            Map<String, Object> attributes = new HashMap<>();
            ContextResult exprResult = (ContextResult) visit(ctx.comparisonExpression());
            attributes.put("code", "not " + exprResult.getAttributes().get("code"));

            return ContextResult.valid(attributes, "notExpression");
        } else if (!ctx.comparisonExpression().isEmpty()) {
            return (ContextResult) visit(ctx.comparisonExpression());
        }

        return null;
    }

    @Override
    public ContextResult visitComparisonExpression(EMJParser.ComparisonExpressionContext ctx) {
        if (ctx.DOUBLE_EQUAL() != null || ctx.NOTEQUAL() != null ||
                ctx.LESS() != null || ctx.LEQ() != null ||
                ctx.GREATER() != null || ctx.GEQ() != null) {
            Map<String, Object> attributes = new HashMap<>();
            StringBuilder code = new StringBuilder();

            // Left operand
            ContextResult leftResult = (ContextResult) visit(ctx.additiveExpression(0));
            code.append(leftResult.getAttributes().get("code"));

            // Operator
            String op;
            if (ctx.DOUBLE_EQUAL() != null) op = " == ";
            else if (ctx.NOTEQUAL() != null) op = " != ";
            else if (ctx.LESS() != null) op = " < ";
            else if (ctx.LEQ() != null) op = " <= ";
            else if (ctx.GREATER() != null) op = " > ";
            else if (ctx.GEQ() != null) op = " >= ";
            else op = " ? "; // Should never happen

            code.append(op);

            // Right operand
            ContextResult rightResult = (ContextResult) visit(ctx.additiveExpression(1));
            code.append(rightResult.getAttributes().get("code"));

            attributes.put("code", code.toString());
            return ContextResult.valid(attributes, "primaryExpression");
        } else if (!ctx.additiveExpression().isEmpty()) {
            return (ContextResult) visit(ctx.additiveExpression(0));
        }
        return null;
    }

    @Override
    public ContextResult visitAdditiveExpression(EMJParser.AdditiveExpressionContext ctx) {
        if (!ctx.PLUS().isEmpty() || !ctx.MINUS().isEmpty()) {
            Map<String, Object> attributes = new HashMap<>();
            StringBuilder code = new StringBuilder();

            for (int i = 0; i < ctx.multiplicativeExpression().size(); i++) {
                ContextResult exprResult = (ContextResult) visit(ctx.multiplicativeExpression(i));
                code.append(exprResult.getAttributes().get("code"));

                if (i < ctx.multiplicativeExpression().size() - 1) {
                    if (ctx.PLUS(i) != null) {
                        code.append(" + ");
                    } else {
                        code.append(" - ");
                    }
                }
            }
            attributes.put("code", code.toString());
            return ContextResult.valid(attributes, "additiveExpression");
        } else if (!ctx.multiplicativeExpression().isEmpty()) {
            return (ContextResult) visit(ctx.multiplicativeExpression(0));
        }
        return null;
    }

    @Override
    public ContextResult visitMultiplicativeExpression(EMJParser.MultiplicativeExpressionContext ctx) {
        if (!ctx.MULTIPLY().isEmpty() || !ctx.DIVIDE().isEmpty()) {
            Map<String, Object> attributes = new HashMap<>();
            ContextResult leftExprResult = (ContextResult) visit(ctx.unaryExpression(0));
            StringBuilder code = new StringBuilder();

            for (int i = 0; i < ctx.unaryExpression().size(); i++) {
                ContextResult exprResult = (ContextResult) visit(ctx.unaryExpression(i));
                code.append(exprResult.getAttributes().get("code"));

                if (i < ctx.unaryExpression().size() - 1) {
                    if (ctx.MULTIPLY(i) != null) {
                        code.append(" * ");
                    } else {
                        code.append(" / ");
                    }
                }
            }

            attributes.put("code", code.toString());
            return ContextResult.valid(attributes, "multiplicativeExpression");
        } else if (!ctx.unaryExpression().isEmpty()) {
            return (ContextResult) visit(ctx.unaryExpression(0));
        }
        return null;
    }

    @Override
    public ContextResult visitUnaryExpression(EMJParser.UnaryExpressionContext ctx) {
        if (ctx.MINUS() != null) {
            Map<String, Object> attributes = new HashMap<>();
            ContextResult exprResult = (ContextResult) visit(ctx.primaryExpression());
            attributes.put("code", "-" + exprResult.getAttributes().get("code"));
            return ContextResult.valid(attributes, "unaryExpression");
        } else {
            return (ContextResult) visit(ctx.primaryExpression());
        }
    }

    @Override
    public ContextResult visitPrimaryExpression(EMJParser.PrimaryExpressionContext ctx) {
        Map<String, Object> attributes = new HashMap<>();
        if (ctx.INT_VALUE() != null) {
            attributes.put("code", ctx.INT_VALUE().getText());
        } else if (ctx.STRING_VALUE() != null) {
            attributes.put("code", ctx.STRING_VALUE().getText());
        } else if (ctx.CHAR_VALUE() != null) {
            attributes.put("code", ctx.CHAR_VALUE().getText());
        } else if (ctx.TRUE() != null) {
            attributes.put("code", "True");
        } else if (ctx.FALSE() != null) {
            attributes.put("code", "False");
        } else if (ctx.NOT() != null) {
            ContextResult exprResult = (ContextResult) visit(ctx.primaryExpression());
            attributes.put("code", "not " + exprResult.getAttributes().get("code"));
        } else if (ctx.tupleValue() != null) {
            ContextResult tupleResult = (ContextResult) visit(ctx.tupleValue());
            attributes.put("code", tupleResult.getAttributes().get("code"));
        } else if (ctx.EMOJI_ID() != null) {
            attributes.put("code", sanitizeEmoji(ctx.EMOJI_ID().getText()));
        } else if (ctx.functionCall() != null) {
            ContextResult callResult = (ContextResult) visit(ctx.functionCall());
            attributes.put("code", callResult.getAttributes().get("code"));
        } else if (ctx.leftExpression() != null) {
            ContextResult leftResult = (ContextResult) visit(ctx.leftExpression());
            attributes.put("code", leftResult.getAttributes().get("code"));
        } else if (ctx.expression() != null) {
            ContextResult exprResult = (ContextResult) visit(ctx.expression());
            attributes.put("code", "(" + exprResult.getAttributes().get("code") + ")");
        }
        return ContextResult.valid(attributes, "primaryExpression");
    }

    @Override
    public ContextResult visitFunctionCall(EMJParser.FunctionCallContext ctx) {
        Map<String, Object> attributes = new HashMap<>();

        // Function name
        String funcName = sanitizeEmoji(ctx.EMOJI_ID().getText());

        // Arguments
        StringBuilder args = new StringBuilder();
        if (ctx.argumentList() != null) {
            List<EMJParser.ExpressionContext> argCtxs = ctx.argumentList().expression();
            for (int i = 0; i < argCtxs.size(); i++) {
                ContextResult argResult = (ContextResult) visit(argCtxs.get(i));
                args.append(argResult.getAttributes().get("code"));
                if (i < argCtxs.size() - 1) {
                    args.append(", ");
                }
            }
        }

        attributes.put("code", funcName + "(" + args + ")");
        return ContextResult.valid(attributes, "primaryExpression");
    }
    
    @Override
    public ContextResult visitPredefinedStmt(EMJParser.PredefinedStmtContext ctx) {
        Map<String, Object> attributes = new HashMap<>();
        
        // Générer le code pour l'instruction prédéfinie (comme le stop ✴)
        StringBuilder code = new StringBuilder();
        code.append(getIndent()).append("stop()");
        
        // Seul l'attribut 'code' est attendu par le template predefinedStmt
        attributes.put("code", code.toString());
        
        return ContextResult.valid(attributes, "predefinedStmt");
    }
    
    @Override
    public ContextResult visitFunctionCallStmt(EMJParser.FunctionCallStmtContext ctx) {
        Map<String, Object> attributes = new HashMap<>();
        
        // Visite l'appel de fonction et récupère son code
        ContextResult callResult = (ContextResult) visit(ctx.functionCall());
        String functionCallCode = callResult.getAttributes().get("code").toString();
        
        // Ajoute l'indentation appropriée
        String statement = getIndent() + functionCallCode;
        
        attributes.put("body", Arrays.asList(statement));
        return ContextResult.valid(attributes, "block");
    }
    
    // Cette méthode est déjà définie ailleurs dans la classe

    /**
     * Generate indentation for the current level
     */
    private String getIndent() {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < indentLevel; i++) {
            sb.append("    ");
        }
        return sb.toString();
    }

    @Override
    public String renderTemplate(ContextResult context) {
        return "";
    }
    
    @Override
    public void loadTemplates(String templateDir) {
        try {
            // Essai 1: Chemins relatifs par rapport au classpath
            this.templates = new STGroupFile(templateDir);
            if (this.templates == null || !this.templates.isDefined("mainFunction")) {
                // Essai 2: Avec slash au début pour ressources dans le classpath
                this.templates = new STGroupFile("/" + templateDir);
            }
            
            // Essai 3: Dossier templates dans les ressources
            if (this.templates == null || !this.templates.isDefined("mainFunction")) {
                this.templates = new STGroupFile("/templates/" + templateDir);
            }
            
            // Essai 4: Chemin absolu avec resources
            if (this.templates == null || !this.templates.isDefined("mainFunction")) {
                String resourcePath = "src/main/resources/" + templateDir;
                this.templates = new STGroupFile(resourcePath);
            }
            
            // Si toujours pas de templates valides, c'est une erreur
            if (this.templates == null || !this.templates.isDefined("mainFunction")) {
                System.err.println("Templates valides introuvables pour le chemin: " + templateDir);
                System.err.println("Templates disponibles: " + (this.templates != null ? String.join(", ", this.templates.getTemplateNames()) : "aucun"));
                throw new IllegalStateException("Impossible de charger le template: " + templateDir);
            }
            
            // Si on arrive ici, c'est que les templates sont chargés avec succès
            System.out.println("Templates chargés avec succès à partir de: " + templateDir);
            System.out.println("Templates disponibles: " + String.join(", ", this.templates.getTemplateNames()));
        } catch (Exception e) {
            System.err.println("Erreur lors du chargement des templates: " + e.getMessage());
            throw new IllegalStateException("Impossible de charger le template: " + templateDir, e);
        }
    }

    @Override
    public String generateCode(ContextResult program) {
        if (!program.isValid()) {
            System.err.println("Erreur: Le programme n'est pas valide.");
            return "# Code generation failed: invalid program";
        }

        String templateName = program.getTemplateName();
        System.out.println("Génération de code avec le template: " + templateName);
        
        // Vérifier que les templates sont chargés
        if (templates == null) {
            System.err.println("Erreur: Les templates n'ont pas été chargés.");
            return "# Code generation failed: templates not loaded";
        }
        
        ST template = templates.getInstanceOf(templateName);
        if (template == null) {
            System.err.println("Erreur: Template '" + templateName + "' non trouvé.");
            System.err.println("Templates disponibles: " + String.join(", ", templates.getTemplateNames()));
            return "# Template not found: " + templateName;
        }

        // Afficher les attributs pour débogage
        System.out.println("Attributs du programme:");
        for (Map.Entry<String, Object> entry : program.getAttributes().entrySet()) {
            String key = entry.getKey();
            Object value = entry.getValue();
            System.out.println("  - " + key + ": " + (value instanceof Collection ? "Collection de taille " + ((Collection<?>) value).size() : value));
            
            try {
                template.add(key, value);
            } catch (Exception e) {
                System.err.println("Erreur lors de l'ajout de l'attribut '" + key + "': " + e.getMessage());
            }
        }

        // S'assurer spécifiquement que l'attribut 'body' existe si nécessaire
        if (templateName.equals("program") && !program.getAttributes().containsKey("body")) {
            System.err.println("Avertissement: L'attribut 'body' est manquant pour le template 'program'.");
        }

        try {
            String renderedCode = template.render();
            System.out.println("Génération de code réussie!");
            return renderedCode;
        } catch (Exception e) {
            System.err.println("Erreur lors du rendu du template '" + templateName + "': " + e.getMessage());
            e.printStackTrace();
            return "# Code generation failed: " + e.getMessage();
        }
    }

    private String getTypeFromContext(EMJParser.TypeContext typeCtx) {
        if (typeCtx == null) return EMJVarType.UNKNOWN.pyLabel();
        if (typeCtx.INT_TYPE() != null) {
            return EMJVarType.INT.pyLabel();
        }
        if (typeCtx.BOOL_TYPE() != null) {
            return EMJVarType.BOOL.pyLabel();
        }
        if (typeCtx.CHAR_TYPE() != null) {
            return EMJVarType.CHAR.pyLabel();
        }
        if (typeCtx.STRING_TYPE() != null) {
            return EMJVarType.STRING.pyLabel();
        }
        if (typeCtx.tupleType() != null) {
            EMJParser.TupleTypeContext tupleCtx = typeCtx.tupleType();
            String innerType = getTypeFromContext(tupleCtx.type());
            if (innerType.equals(EMJVarType.UNKNOWN.pyLabel())) {
                return EMJVarType.UNKNOWN.pyLabel();//TODO : on autorise "Tuple(UNKNOWN)" ? si oui, enlever ce if
            }
            return String.format("%s(%s)", EMJVarType.TUPLE.pyLabel(), innerType);
        }
        return EMJVarType.UNKNOWN.pyLabel();
    }

    private String sanitizeEmoji(String emoji) {
        // Nettoyer l'emoji pour créer un nom de variable Python valide
        String rawName = emoji.replaceAll("[\\[\\]]", "");

        // Supprime les variation selectors (comme U+FE0F)
        String normalized = rawName.replaceAll("\\p{M}|\\uFE0F", "");

        if (emojiShortNames.containsKey(normalized)) {
            return emojiShortNames.get(normalized);
        }
        String parsedEmoji = EmojiParser.parseToAliases(emoji);
        parsedEmoji = parsedEmoji.replaceAll("\\W", "");
        return "emoji_" + parsedEmoji;
    }

    private void incrIndent() {
        this.indentLevel += 1;
    }

    private void decrIndent() throws IllegalStateException {
        if (this.indentLevel <= 0) {
            throw new IllegalStateException(String.format("YOU SHALL NOT DECREMENT INDENT (indentLvl :%d)", this.indentLevel));
        }
        this.indentLevel -= 1;
    }
}