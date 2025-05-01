package be.unamur.info.b314.compiler.emj;

import org.antlr.v4.runtime.tree.ParseTreeProperty;

import java.util.*;

/**
 * Table des symboles pour la gestion des portées et des symboles dans le compilateur EMJ
 * 
 * @invariant scopes != null
 * @invariant symbols != null
 * @invariant scopeSymbols != null
 * @invariant !scopes.isEmpty() ==> currentScope != null
 * @invariant scopes.isEmpty() ==> currentScope == null
 * @invariant (\forall String scope; scopeSymbols.containsKey(scope); scopeSymbols.get(scope) != null)
 */
public class EMJSymbolTable {
    private final Stack<String> scopes;
    private final Map<String, EMJSymbolInfo> symbols;
    private final Map<String, List<String>> scopeSymbols;

    private String currentScope;

    /**
     * Constructeur par défaut - initialise la table des symboles avec une portée globale
     * 
     * @ensures scopes != null && symbols != null && scopeSymbols != null
     * @ensures currentScope.equals("global")
     * @ensures scopes.size() == 1 && scopes.peek().equals("global")
     * @ensures scopeSymbols.containsKey("global")
     * @ensures scopeSymbols.get("global") != null && scopeSymbols.get("global").isEmpty()
     */
    public EMJSymbolTable() {
        this.scopes = new Stack<>();
        this.symbols = new HashMap<>();
        this.scopeSymbols = new HashMap<>();

        enterScope("global");
    }

    /**
     * Entre dans une nouvelle portée
     * 
     * @param scopeName Le nom de la nouvelle portée
     * @requires scopeName != null
     * @ensures currentScope != null
     * @ensures scopes.peek().equals(currentScope)
     * @ensures scopeSymbols.containsKey(currentScope)
     * @ensures scopeSymbols.get(currentScope) != null
     * @ensures scopeSymbols.get(currentScope).isEmpty()
     * @assignable scopes, currentScope, scopeSymbols
     */
    public void enterScope(String scopeName) {

        String fullScopeName = currentScope == null ?
                scopeName : currentScope + "." + scopeName;

        scopes.push(fullScopeName);
        currentScope = fullScopeName;

        scopeSymbols.put(currentScope, new ArrayList<>());
    }

    /**
     * Sort de la portée courante et revient à la portée parente
     * 
     * @requires !scopes.isEmpty()
     * @ensures scopes.isEmpty() ==> currentScope == null
     * @ensures !scopes.isEmpty() ==> currentScope.equals(scopes.peek())
     * @assignable scopes, currentScope
     */
    public void exitScope() {
        if (!scopes.isEmpty()) {
            scopes.pop();
            currentScope = scopes.isEmpty() ? null : scopes.peek();
        }
    }

    /**
     * Génère un identifiant complet en combinant la portée courante et l'identifiant local
     * 
     * @param id L'identifiant local
     * @return L'identifiant complet au format "portée:id"
     * @private
     * @pure
     * @requires id != null
     * @requires currentScope != null
     * @ensures \result != null
     * @ensures \result.equals(currentScope + ":" + id)
     */
    private String getFullId(String id) {
        return currentScope + ":" + id;
    }

    /**
     * Ajoute une variable à la table des symboles dans la portée courante
     * 
     * @param id Identifiant de la variable
     * @param dataType Type de données de la variable
     * @param initialized État d'initialisation de la variable
     * @requires id != null
     * @requires dataType != null
     * @requires currentScope != null
     * @ensures symbols.containsKey(getFullId(id))
     * @ensures symbols.get(getFullId(id)).getId().equals(id)
     * @ensures symbols.get(getFullId(id)).getType().equals(dataType)
     * @ensures symbols.get(getFullId(id)).getScope().equals(currentScope)
     * @ensures symbols.get(getFullId(id)).getSymbolType() == EMJSymbolType.VARIABLE
     * @ensures symbols.get(getFullId(id)).isInitialized() == initialized
     * @ensures scopeSymbols.get(currentScope).contains(getFullId(id))
     * @assignable symbols, scopeSymbols
     */
    public void addVariable(String id, String dataType, boolean initialized) {
        String fullId = getFullId(id);

        EMJSymbolInfo info = new EMJSymbolInfo(id, dataType, currentScope, EMJSymbolType.VARIABLE, initialized);
        symbols.put(fullId, info);

        scopeSymbols.get(currentScope).add(fullId);
    }

    /**
     * Recherche un symbole dans la portée courante ou dans les portées parentes
     * 
     * @param id Identifiant du symbole à rechercher
     * @return L'information du symbole trouvé, ou null s'il n'existe pas
     * @pure
     * @requires id != null
     * @requires currentScope != null
     * @ensures \result == null || 
     *         (\exists String scope; scope.equals(currentScope) || isAncestorScope(scope, currentScope); 
     *          symbols.containsKey(scope + ":" + id) && \result == symbols.get(scope + ":" + id))
     */
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

    /**
     * Ajoute une fonction à la table des symboles dans la portée globale
     * 
     * @param id Identifiant de la fonction
     * @param returnType Type de retour de la fonction
     * @param parameters Liste des paramètres de la fonction
     * @requires id != null
     * @requires returnType != null
     * @requires parameters != null
     * @ensures symbols.containsKey("global:" + id)
     * @ensures symbols.get("global:" + id).getId().equals(id)
     * @ensures symbols.get("global:" + id).getReturnType().equals(returnType)
     * @ensures symbols.get("global:" + id).getScope().equals("global")
     * @ensures symbols.get("global:" + id).getSymbolType() == EMJSymbolType.FUNCTION
     * @ensures scopeSymbols.get("global").contains("global:" + id)
     * @assignable symbols, scopeSymbols
     */
    public void addFunction(String id, String returnType, List<EMJParameterInfo> parameters) {
        // Utiliser la portée globale pour les fonctions
        String fullId = "global:" + id;

        EMJSymbolInfo info = new EMJSymbolInfo(id, null, fullId, EMJSymbolType.FUNCTION, true);
        info.SetReturnType(returnType);
        info.SetParameters(parameters);

        symbols.put(fullId, info);
        scopeSymbols.get("global").add(fullId);
    }

    /**
     * Vérifie si une fonction existe dans la table des symboles
     * 
     * @param id Identifiant de la fonction à vérifier
     * @return true si la fonction existe, false sinon
     * @pure
     * @requires id != null
     * @ensures \result == (symbols.containsKey("global:" + id) && 
     *          symbols.get("global:" + id).getSymbolType() == EMJSymbolType.FUNCTION)
     */
    public boolean functionExists(String id) {
        String fullId = "global:" + id;
        EMJSymbolInfo info = symbols.get(fullId);
        return info != null && EMJSymbolType.FUNCTION.toString().equals(info.getSymbolType().toString());
    }
    
    /**
     * Vérifie si une portée est ancêtre de la portée courante
     * 
     * @param ancestorScope Portée potentiellement ancêtre
     * @param currentScope Portée courante
     * @return true si ancestorScope est ancêtre de currentScope, false sinon
     * @private
     * @pure
     * @requires ancestorScope != null
     * @requires currentScope != null
     * @ensures \result == (currentScope.startsWith(ancestorScope) && 
     *                    (currentScope.equals(ancestorScope) || 
     *                     currentScope.charAt(ancestorScope.length()) == '.'))
     */
    private boolean isAncestorScope(String ancestorScope, String currentScope) {
        return currentScope.startsWith(ancestorScope) && 
               (currentScope.equals(ancestorScope) || 
                currentScope.charAt(ancestorScope.length()) == '.');
    }

    /**
     * Affiche tous les symboles présents dans la table des symboles avec leur information détaillée
     * Les symboles sont organisés par portée et par type (variables, fonctions, paramètres)
     * 
     * @public
     * @requires symbols != null
     * @requires scopeSymbols != null
     */
    public void displaySymbolTable() {
        System.out.println("\n════════════════════════ TABLE DES SYMBOLES EMJ ════════════════════════");
        
        if (symbols.isEmpty()) {
            System.out.println("\nLa table des symboles est vide.");
            return;
        }
        
        // Affichage par portées
        System.out.println("\nTotal des symboles: " + symbols.size());
        
        // Trier les portées pour un affichage ordonné
        List<String> sortedScopes = new ArrayList<>(scopeSymbols.keySet());
        Collections.sort(sortedScopes);
        
        for (String scope : sortedScopes) {
            List<String> scopeSymbolList = scopeSymbols.get(scope);
            if (scopeSymbolList.isEmpty()) {
                continue;
            }
            
            System.out.println("\n[PORTÉE: " + scope + "] " + scopeSymbolList.size() + " symbole(s)");
            System.out.println("────────────────────────────────────────────────────────────────────");
            
            // Regrouper par type de symbole pour un affichage plus structuré
            List<EMJSymbolInfo> variables = new ArrayList<>();
            List<EMJSymbolInfo> functions = new ArrayList<>();
            List<EMJSymbolInfo> parameters = new ArrayList<>();
            
            for (String symbolId : scopeSymbolList) {
                EMJSymbolInfo symbolInfo = symbols.get(symbolId);
                switch (symbolInfo.getSymbolType()) {
                    case VARIABLE:
                        variables.add(symbolInfo);
                        break;
                    case FUNCTION:
                        functions.add(symbolInfo);
                        break;
                    case PARAMETER:
                        parameters.add(symbolInfo);
                        break;
                }
            }
            
            // Afficher les variables
            if (!variables.isEmpty()) {
                System.out.println("  ◼️ VARIABLES:");
                for (EMJSymbolInfo variable : variables) {
                    System.out.printf("    • %-15s : %-15s (type: %-10s) %s%n", 
                        variable.getId(), 
                        variable.getScope() + ":" + variable.getId(),
                        variable.getType(),
                        variable.isInitialized() ? "[initialisé]" : "[non initialisé]");
                }
            }
            
            // Afficher les fonctions
            if (!functions.isEmpty()) {
                System.out.println("  ◼️ FONCTIONS:");
                for (EMJSymbolInfo function : functions) {
                    StringBuilder signature = new StringBuilder();
                    signature.append(function.getId()).append("(");
                    
                    List<EMJParameterInfo> params = function.getParameters();
                    if (params != null && !params.isEmpty()) {
                        for (int i = 0; i < params.size(); i++) {
                            EMJParameterInfo param = params.get(i);
                            signature.append(param.getType()).append(" ").append(param.getId());
                            if (i < params.size() - 1) {
                                signature.append(", ");
                            }
                        }
                    }
                    signature.append(") : ").append(function.getReturnType());
                    
                    System.out.printf("    • %-50s%n", signature.toString());
                    
                    // Afficher les paramètres si présents
                    if (params != null && !params.isEmpty()) {
                        System.out.println("      Paramètres:");
                        for (EMJParameterInfo param : params) {
                            System.out.printf("        ◦ %-15s : %-10s%n", param.getId(), param.getType());
                        }
                    } else {
                        System.out.println("      Aucun paramètre");
                    }
                }
            }
            
            // Afficher les paramètres qui sont dans cette portée (rare, mais possible)
            if (!parameters.isEmpty()) {
                System.out.println("  ◼️ PARAMÈTRES (non liés à une fonction):");
                for (EMJSymbolInfo param : parameters) {
                    System.out.printf("    • %-15s : %-10s%n", param.getId(), param.getType());
                }
            }
        }
        
        System.out.println("════════════════════════════════════════════════════════════════════════");
    }
}