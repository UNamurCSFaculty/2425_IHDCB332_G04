package be.unamur.info.b314.compiler.emj;

import be.unamur.info.b314.compiler.EMJParser;
import be.unamur.info.b314.compiler.EMJParserBaseVisitor;
import com.github.jknack.handlebars.Handlebars;
import com.github.jknack.handlebars.Template;
import com.github.jknack.handlebars.io.ClassPathTemplateLoader;
import com.github.jknack.handlebars.io.TemplateLoader;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Simplified EMJ Code Generator - returns strings directly from visitor methods
 */
public class EMJCodeGenerator extends EMJParserBaseVisitor<String> {

    private final Handlebars handlebars;
    private final Map<String, Template> templateCache = new HashMap<>();

    /**
     * Constructor initializes Handlebars
     */
    public EMJCodeGenerator() {
        TemplateLoader loader = new ClassPathTemplateLoader();
        loader.setPrefix("/templates");
        loader.setSuffix(".hbs");

        handlebars = new Handlebars(loader)
                .prettyPrint(false); // Disable pretty printing to control whitespace

        // Pre-compile templates
        try {
            cacheTemplate("program");
            cacheTemplate("imports");
            cacheTemplate("importStatement");
            cacheTemplate("mainFunction");
            cacheTemplate("varDeclaration");
            cacheTemplate("predefinedStatement");
            cacheTemplate("returnVoid");
            cacheTemplate("returnValue");
        } catch (IOException e) {
            throw new RuntimeException("Failed to compile templates", e);
        }
    }

    private void cacheTemplate(String name) throws IOException {
        templateCache.put(name, handlebars.compile(name));
    }

    private String applyTemplate(String templateName, Map<String, Object> context) {
        try {
            Template template = templateCache.get(templateName);
            if (template == null) {
                template = handlebars.compile(templateName);
                templateCache.put(templateName, template);
            }
            String result = template.apply(context);

            // Fix common whitespace issues
            result = result.replaceAll("\\n\\s*\\n\\s*\\n", "\n"); // Remove triple newlines
            return result;
        } catch (IOException e) {
            throw new RuntimeException("Error applying template: " + templateName, e);
        }
    }

    /**
     * Main code generation method
     */
    public String generate(EMJParser.RootContext rootContext) {
        return visit(rootContext);
    }

    // Root visitor
    @Override
    public String visitRoot(EMJParser.RootContext ctx) {
        if (ctx.programFile() != null) {
            return visit(ctx.programFile());
        }
        return "";
    }

    // Program file visitor - generates the full program
    @Override
    public String visitProgramFile(EMJParser.ProgramFileContext ctx) {
        Map<String, Object> programContext = new HashMap<>();

        // Standard imports
        programContext.put("standardImports",
                "from microbit import *\nimport music\nfrom cutebot import *");

        // Import statement
        String importStatement = "";
        if (ctx.importStatement() != null) {
            importStatement = visit(ctx.importStatement());
        }
        programContext.put("importStatement", importStatement);

        // Main function
        String mainFunction = "";
        if (ctx.mainFunction() != null) {
            mainFunction = visit(ctx.mainFunction());
        }
        programContext.put("mainFunction", mainFunction);

        // Function declarations
        List<String> functions = new ArrayList<>();
        for (EMJParser.FunctionDeclContext fctx : ctx.functionDecl()) {
            String functionCode = visit(fctx);
            if (functionCode != null && !functionCode.isEmpty()) {
                functions.add(functionCode);
            }
        }
        programContext.put("functions", functions);

        return applyTemplate("program", programContext);
    }

    // Import statement visitor
    @Override
    public String visitImportStatement(EMJParser.ImportStatementContext ctx) {
        Map<String, Object> context = new HashMap<>();

        String mapFile = ctx.STRING_VALUE().getText();
        // Remove quotes from map file name
        mapFile = mapFile.substring(1, mapFile.length() - 1);
        context.put("mapFile", mapFile);

        return applyTemplate("importStatement", context);
    }

    // Main function visitor
    @Override
    public String visitMainFunction(EMJParser.MainFunctionContext ctx) {
        Map<String, Object> context = new HashMap<>();
        List<String> statements = new ArrayList<>();

        // Visit each statement
        for (EMJParser.StatementContext stmt : ctx.statement()) {
            String stmtCode = visit(stmt);
            if (stmtCode != null && !stmtCode.isEmpty()) {
                statements.add(stmtCode);
            }
        }

        // Add placeholder if empty
        if (statements.isEmpty()) {
            statements.add("pass  # Empty function body");
        }

        context.put("statements", statements);
        return applyTemplate("mainFunction", context);
    }

    // Statement router
    @Override
    public String visitStatement(EMJParser.StatementContext ctx) {
        if (ctx.varDecl() != null) {
            return visit(ctx.varDecl());
        } else if (ctx.assignment() != null) {
            return visit(ctx.assignment());
        } else if (ctx.functionCallStmt() != null) {
            return visit(ctx.functionCallStmt());
        } else if (ctx.predefinedStmt() != null) {
            return visit(ctx.predefinedStmt());
        } else if (ctx.ifStatement() != null) {
            return visit(ctx.ifStatement());
        } else if (ctx.loopStatement() != null) {
            return visit(ctx.loopStatement());
        } else if (ctx.returnStatement() != null) {
            return visit(ctx.returnStatement());
        }
        return "";
    }

    // Variable declaration visitor
    @Override
    public String visitVarDecl(EMJParser.VarDeclContext ctx) {
        Map<String, Object> context = new HashMap<>();

        String varId = convertEmojiId(ctx.EMOJI_ID().getText());
        String varType = getTypeString(ctx.type());
        String varValue = ctx.expression() != null ?
                visit(ctx.expression()) :
                getDefaultValue(varType);

        context.put("varId", varId);
        context.put("varType", varType);
        context.put("varValue", varValue);

        return applyTemplate("varDeclaration", context);
    }

    // Predefined statement visitor
    @Override
    public String visitPredefinedStmt(EMJParser.PredefinedStmtContext ctx) {
        Map<String, Object> context = new HashMap<>();

        if (ctx.STOP_THIEF() != null) {
            context.put("function", "arrest_thief");
            context.put("hasArgs", false);
        } else if (ctx.SOUND_TOGGLE() != null) {
            context.put("function", "toggle_sound");
            context.put("hasArgs", false);
        } else if (ctx.LIGHT_TOGGLE() != null) {
            context.put("function", "toggle_lights");
            context.put("hasArgs", false);
        } else if (ctx.UP_ARROW() != null) {
            context.put("function", "move_up");
            context.put("hasArgs", true);
            context.put("args", ctx.INT_VALUE().getText());
        } else if (ctx.DOWN_ARROW() != null) {
            context.put("function", "move_down");
            context.put("hasArgs", true);
            context.put("args", ctx.INT_VALUE().getText());
        } else if (ctx.LEFT_ARROW() != null) {
            context.put("function", "move_left");
            context.put("hasArgs", true);
            context.put("args", ctx.INT_VALUE().getText());
        } else if (ctx.RIGHT_ARROW() != null) {
            context.put("function", "move_right");
            context.put("hasArgs", true);
            context.put("args", ctx.INT_VALUE().getText());
        }

        return applyTemplate("predefinedStatement", context);
    }

    // Return statement visitor
    @Override
    public String visitReturnStatement(EMJParser.ReturnStatementContext ctx) {
        if (ctx.VOID_TYPE() != null || ctx.RETURN_VOID() != null) {
            return applyTemplate("returnVoid", new HashMap<>());
        } else if (ctx.expression() != null) {
            Map<String, Object> context = new HashMap<>();
            context.put("value", visit(ctx.expression()));
            return applyTemplate("returnValue", context);
        }
        return applyTemplate("returnVoid", new HashMap<>());
    }

    // Primary expression visitor
    @Override
    public String visitPrimaryExpression(EMJParser.PrimaryExpressionContext ctx) {
        if (ctx.INT_VALUE() != null) {
            return ctx.INT_VALUE().getText();
        } else if (ctx.STRING_VALUE() != null) {
            return ctx.STRING_VALUE().getText();
        } else if (ctx.CHAR_VALUE() != null) {
            return ctx.CHAR_VALUE().getText();
        } else if (ctx.TRUE() != null) {
            return "True";
        } else if (ctx.FALSE() != null) {
            return "False";
        } else if (ctx.EMOJI_ID() != null) {
            return convertEmojiId(ctx.EMOJI_ID().getText());
        } else if (ctx.expression() != null) {
            return "(" + visit(ctx.expression()) + ")";
        } else if (ctx.functionCall() != null) {
            return visit(ctx.functionCall());
        }
        return "None"; // Default
    }

    // Expression visitor - implement based on your grammar
    @Override
    public String visitExpression(EMJParser.ExpressionContext ctx) {
        return visit(ctx.orExpression());
    }

    // OrExpression visitor - implement with OR operators
    @Override
    public String visitOrExpression(EMJParser.OrExpressionContext ctx) {
        if (ctx.andExpression().size() == 1) {
            return visit(ctx.andExpression(0));
        }

        StringBuilder result = new StringBuilder();
        for (int i = 0; i < ctx.andExpression().size(); i++) {
            if (i > 0) {
                result.append(" or ");
            }
            result.append(visit(ctx.andExpression(i)));
        }
        return result.toString();
    }

    // AndExpression visitor
    @Override
    public String visitAndExpression(EMJParser.AndExpressionContext ctx) {
        if (ctx.notExpression().size() == 1) {
            return visit(ctx.notExpression(0));
        }

        StringBuilder result = new StringBuilder();
        for (int i = 0; i < ctx.notExpression().size(); i++) {
            if (i > 0) {
                result.append(" and ");
            }
            result.append(visit(ctx.notExpression(i)));
        }
        return result.toString();
    }

    // NotExpression visitor
    @Override
    public String visitNotExpression(EMJParser.NotExpressionContext ctx) {
        if (ctx.NOT() != null) {
            return "not " + visit(ctx.comparisonExpression());
        }
        return visit(ctx.comparisonExpression());
    }

    // Helper methods

    /**
     * Converts emoji ID to Python variable name
     */
    private String convertEmojiId(String emojiId) {
        // Remove brackets
        String cleanId = emojiId.replace("[", "").replace("]", "");

        // Build a Python-safe identifier
        StringBuilder pythonId = new StringBuilder("var_");
        for (int i = 0; i < cleanId.length();) {
            int codePoint = cleanId.codePointAt(i);
            if (Character.charCount(codePoint) > 1) {
                pythonId.append(String.format("e%x", codePoint));
                i += Character.charCount(codePoint);
            } else {
                pythonId.append(cleanId.charAt(i));
                i++;
            }
        }

        return pythonId.toString();
    }

    /**
     * Gets type string from EMJ type
     */
    private String getTypeString(EMJParser.TypeContext ctx) {
        if (ctx.INT_TYPE() != null) return "int";
        if (ctx.BOOL_TYPE() != null) return "bool";
        if (ctx.CHAR_TYPE() != null) return "char";
        if (ctx.STRING_TYPE() != null) return "str";
        if (ctx.tupleType() != null) return "tuple";
        return "any";
    }

    /**
     * Gets default value for type
     */
    private String getDefaultValue(String type) {
        switch (type) {
            case "int": return "0";
            case "bool": return "False";
            case "char": return "''";
            case "str": return "\"\"";
            case "tuple": return "(None, None)";
            default: return "None";
        }
    }

    /**
     * Debug method to print template context
     */
    private void debugContext(String templateName, Map<String, Object> context) {
        System.out.println("--- Template: " + templateName + " ---");
        for (Map.Entry<String, Object> entry : context.entrySet()) {
            System.out.println(entry.getKey() + ": " + entry.getValue());
        }
        System.out.println("-------------------------");
    }
}