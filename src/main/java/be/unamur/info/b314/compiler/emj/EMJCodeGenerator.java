package be.unamur.info.b314.compiler.emj;

import be.unamur.info.b314.compiler.EMJParser;
import be.unamur.info.b314.compiler.EMJParserBaseVisitor;


 //Code generator for EMJ language targeting MicroPython.

public class EMJCodeGenerator extends EMJParserBaseVisitor<String> {

    private final StringBuilder output = new StringBuilder();
    private String indentation = "";


     //Entry-point : génère le python à partir du contexte racine.

    public String generate(EMJParser.RootContext ctx) {
        output.append("from microbit import *\n");
        output.append("import music\n\n");
        visit(ctx);                     // on visite tout l’arbre
        return output.toString();
    }


     //Visiteurs de haut niveau


    @Override
    public String visitRoot(EMJParser.RootContext ctx) {
        if (ctx.programFile() != null) {
            visit(ctx.programFile());
        } // sinon, c’était un mapFile qu’on ignore ici
        return null;
    }

    @Override
    public String visitProgramFile(EMJParser.ProgramFileContext ctx) {
        // fonctions utilisateur d’abord
        for (EMJParser.FunctionDeclContext fn : ctx.functionDecl()) {
            visit(fn);
        }
        // puis la fonction main
        visit(ctx.mainFunction());
        return null;
    }

    @Override
    public String visitMainFunction(EMJParser.MainFunctionContext ctx) {
        output.append("def main():\n");
        indentation = "    ";

        for (EMJParser.StatementContext st : ctx.statement()) {
            String line = visit(st);        // délègue au visiteur approprié
            if (line != null && !line.trim().isEmpty()) {
                output.append(indentation).append(line).append("\n");
            }
        }
        output.append("\nmain()\n");
        return null;
    }


     // Visiteurs ‘statement’ et expressions


    @Override
    public String visitVarDecl(EMJParser.VarDeclContext ctx) {
        // exemple très simple : ↩️ « 🔢 age = 5 »  devient « age = 5 »
        String id = ctx.EMOJI_ID().getText();
        String expr = ctx.expression() != null ? visit(ctx.expression()) : "None";
        return id + " = " + expr;
    }

    @Override
    public String visitAssignment(EMJParser.AssignmentContext ctx) {
        return visit(ctx.leftExpression()) + " = " + visit(ctx.expression());
    }

    @Override
    public String visitLeftExpression(EMJParser.LeftExpressionContext ctx) {
        String id = ctx.EMOJI_ID().getText();
        if (ctx.TUPLE_FIRST() != null)       return id + "[0]";
        if (ctx.TUPLE_SECOND() != null)      return id + "[1]";
        return id;
    }

    // à compléter

}
