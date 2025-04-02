package be.unamur.info.b314.compiler.emj;

import org.antlr.v4.runtime.tree.ParseTreeProperty;

import java.util.*;

public class EMJSymbolTable {
    private final Stack<String> scopes;
    private final Map<String, EMJSymbolInfo> symbols;
    private final Map<String, List<String>> scopeSymbols;

    private String currentScope;

    public EMJSymbolTable() {
        this.scopes = new Stack<>();
        this.symbols = new HashMap<>();
        this.scopeSymbols = new HashMap<>();

        enterScope("global");
    }

    public void enterScope(String scopeName) {

        String fullScopeName = currentScope == null ?
                scopeName : currentScope + "." + scopeName;

        scopes.push(fullScopeName);
        currentScope = fullScopeName;

        scopeSymbols.put(currentScope, new ArrayList<>());
    }

    public void exitScope() {
        if (!scopes.isEmpty()) {
            scopes.pop();
            currentScope = scopes.isEmpty() ? null : scopes.peek();
        }
    }

    private String getFullId(String id) {
        return currentScope + ":" + id;
    }

    public void addVariable(String id, String dataType, boolean initialized) {
        String fullId = getFullId(id);

        EMJSymbolInfo info = new EMJSymbolInfo(id, dataType, currentScope, EMJSymbolType.VARIABLE, initialized);
        symbols.put(fullId, info);

        scopeSymbols.get(currentScope).add(fullId);
    }

    public EMJSymbolInfo lookup(String id) {
        // Chercher d'abord dans la portée actuelle
        String fullId = getFullId(id);
        if (symbols.containsKey(fullId)) {
            return symbols.get(fullId);
        }

        // Chercher dans les portées parentes
        String scope = currentScope;
        while (scope.contains(".")) {
            scope = scope.substring(0, scope.lastIndexOf('.'));
            fullId = scope + ":" + id;

            if (symbols.containsKey(fullId)) {
                return symbols.get(fullId);
            }
        }
        return null;
    }
}
