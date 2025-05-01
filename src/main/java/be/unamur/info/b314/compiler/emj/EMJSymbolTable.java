package be.unamur.info.b314.compiler.emj;

import org.antlr.v4.runtime.tree.ParseTreeProperty;

import java.util.*;

/**
 * Table des symboles pour la gestion des portées et des symboles dans le compilateur EMJ
 */
/*@ public invariant scopes != null;
  @ public invariant symbols != null;
  @ public invariant scopeSymbols != null;
  @ public invariant !scopes.isEmpty() ==> currentScope != null;
  @ public invariant scopes.isEmpty() ==> currentScope == null;
  @ public invariant (\forall String scope; scopeSymbols.containsKey(scope); 
  @                   scopeSymbols.get(scope) != null);
  @*/
public class EMJSymbolTable {
    private final Stack<String> scopes;
    private final Map<String, EMJSymbolInfo> symbols;
    private final Map<String, List<String>> scopeSymbols;

    private String currentScope;

    /*@ ensures scopes != null && symbols != null && scopeSymbols != null;
      @ ensures currentScope.equals("global");
      @ ensures scopes.size() == 1 && scopes.peek().equals("global");
      @ ensures scopeSymbols.containsKey("global");
      @ ensures scopeSymbols.get("global") != null && scopeSymbols.get("global").isEmpty();
      @*/
    public EMJSymbolTable() {
        this.scopes = new Stack<>();
        this.symbols = new HashMap<>();
        this.scopeSymbols = new HashMap<>();

        enterScope("global");
    }

    /*@ requires scopeName != null;
      @ ensures currentScope != null;
      @ ensures scopes.peek().equals(currentScope);
      @ ensures scopeSymbols.containsKey(currentScope);
      @ ensures scopeSymbols.get(currentScope) != null;
      @ ensures scopeSymbols.get(currentScope).isEmpty();
      @ assignable scopes, currentScope, scopeSymbols;
      @*/
    public void enterScope(String scopeName) {

        String fullScopeName = currentScope == null ?
                scopeName : currentScope + "." + scopeName;

        scopes.push(fullScopeName);
        currentScope = fullScopeName;

        scopeSymbols.put(currentScope, new ArrayList<>());
    }

    /*@ requires !scopes.isEmpty();
      @ ensures scopes.isEmpty() ==> currentScope == null;
      @ ensures !scopes.isEmpty() ==> currentScope.equals(scopes.peek());
      @ assignable scopes, currentScope;
      @*/
    public void exitScope() {
        if (!scopes.isEmpty()) {
            scopes.pop();
            currentScope = scopes.isEmpty() ? null : scopes.peek();
        }
    }

    /*@ private pure
      @ requires id != null;
      @ requires currentScope != null;
      @ ensures \result != null;
      @ ensures \result.equals(currentScope + ":" + id);
      @*/
    private String getFullId(String id) {
        return currentScope + ":" + id;
    }

    /*@ requires id != null;
      @ requires dataType != null;
      @ requires currentScope != null;
      @ ensures symbols.containsKey(getFullId(id));
      @ ensures symbols.get(getFullId(id)).getId().equals(id);
      @ ensures symbols.get(getFullId(id)).getType().equals(dataType);
      @ ensures symbols.get(getFullId(id)).getScope().equals(currentScope);
      @ ensures symbols.get(getFullId(id)).getSymbolType() == EMJSymbolType.VARIABLE;
      @ ensures symbols.get(getFullId(id)).isInitialized() == initialized;
      @ ensures scopeSymbols.get(currentScope).contains(getFullId(id));
      @ assignable symbols, scopeSymbols;
      @*/
    public void addVariable(String id, String dataType, boolean initialized) {
        String fullId = getFullId(id);

        EMJSymbolInfo info = new EMJSymbolInfo(id, dataType, currentScope, EMJSymbolType.VARIABLE, initialized);
        symbols.put(fullId, info);

        scopeSymbols.get(currentScope).add(fullId);
    }

    /*@ pure
      @ requires id != null;
      @ requires currentScope != null;
      @ ensures \result == null || 
      @         (\exists String scope; scope.equals(currentScope) || isAncestorScope(scope, currentScope); 
      @          symbols.containsKey(scope + ":" + id) && \result == symbols.get(scope + ":" + id));
      @*/
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

    /*@ requires id != null;
      @ requires returnType != null;
      @ requires parameters != null;
      @ ensures symbols.containsKey("global:" + id);
      @ ensures symbols.get("global:" + id).getId().equals(id);
      @ ensures symbols.get("global:" + id).getReturnType().equals(returnType);
      @ ensures symbols.get("global:" + id).getParameters() == parameters;
      @ ensures symbols.get("global:" + id).getSymbolType() == EMJSymbolType.FUNCTION;
      @ ensures scopeSymbols.get("global").contains("global:" + id);
      @ assignable symbols, scopeSymbols;
      @*/
    public void addFunction(String id, String returnType, List<EMJParameterInfo> parameters) {
        // Utiliser la portée globale pour les fonctions
        String fullId = "global:" + id;

        EMJSymbolInfo info = new EMJSymbolInfo(id, null, fullId, EMJSymbolType.FUNCTION, true);
        info.SetReturnType(returnType);
        info.SetParameters(parameters);

        symbols.put(fullId, info);
        scopeSymbols.get("global").add(fullId);
    }

    /*@ pure
      @ requires id != null;
      @ ensures \result == (symbols.containsKey("global:" + id) && 
      @          symbols.get("global:" + id).getSymbolType() == EMJSymbolType.FUNCTION);
      @*/
    public boolean functionExists(String id) {
        String fullId = "global:" + id;
        EMJSymbolInfo info = symbols.get(fullId);
        return info != null && EMJSymbolType.FUNCTION.toString().equals(info.getSymbolType().toString());
    }
    
    /*@ private pure
      @ requires ancestorScope != null;
      @ requires currentScope != null;
      @ ensures \result == (currentScope.startsWith(ancestorScope) && 
      @                    (currentScope.equals(ancestorScope) || 
      @                     currentScope.charAt(ancestorScope.length()) == '.'));
      @*/
    private boolean isAncestorScope(String ancestorScope, String currentScope) {
        return currentScope.startsWith(ancestorScope) && 
               (currentScope.equals(ancestorScope) || 
                currentScope.charAt(ancestorScope.length()) == '.');
    }
}