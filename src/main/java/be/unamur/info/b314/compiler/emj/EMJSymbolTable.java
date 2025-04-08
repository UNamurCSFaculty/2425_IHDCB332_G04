package be.unamur.info.b314.compiler.emj;

import java.util.*;

/**
 * Table des symboles pour le compilateur EMJ
 * Gère les symboles (variables, fonctions, paramètres) et leurs portées
 */
public class EMJSymbolTable {
    private final Stack<String> scopeStack;
    private final Map<String, EMJSymbolInfo> symbols;
    private final Set<String> validTypes;
    
    private String currentScope;

    /**
     * Constructeur de la table des symboles
     */
    public EMJSymbolTable() {
        this.scopeStack = new Stack<>();
        this.symbols = new HashMap<>();
        this.validTypes = new HashSet<>(Arrays.asList("INT", "BOOL", "CHAR", "STRING", "VOID", "TUPLE"));
        
        pushScope("global");
    }
    
    /**
     * Ajoute une nouvelle portée à la pile des portées
     * @param scopeName Nom de la nouvelle portée
     */
    public void pushScope(String scopeName) {
        String fullScopeName = currentScope == null ?
                scopeName : currentScope + "." + scopeName;
        
        scopeStack.push(fullScopeName);
        currentScope = fullScopeName;
    }
    
    /**
     * Retire la portée actuelle de la pile des portées
     */
    public void popScope() {
        if (!scopeStack.isEmpty()) {
            scopeStack.pop();
            currentScope = scopeStack.isEmpty() ? "global" : scopeStack.peek();
        }
    }
    
    /**
     * Obtient le scope actuel
     * @return Le scope actuel
     */
    public String getCurrentScope() {
        return currentScope;
    }
    
    /**
     * Retourne la portée actuelle
     * @return Nom complet de la portée actuelle
     */
    public String getScope() {
        return currentScope;
    }
    
    /**
     * Vérifie si un type est valide
     * @param type Type à vérifier
     * @return true si le type est valide, false sinon
     */
    public boolean isValidType(String type) {
        return validTypes.contains(type);
    }
    
    /**
     * Construit l'identifiant complet (avec portée) pour un identifiant simple
     * @param id Identifiant simple
     * @return Identifiant complet (portée:id)
     */
    private String getFullId(String id) {
        return currentScope + ":" + id;
    }
    
    /**
     * Vérifie si une variable est définie dans la portée actuelle ou une portée parente
     * @param id Identifiant de la variable
     * @return true si la variable est définie, false sinon
     */
    public boolean isVariableDefined(String id) {
        return lookupVariable(id) != null;
    }
    
    /**
     * Vérifie si une variable est définie uniquement dans la portée actuelle
     * @param id Identifiant de la variable
     * @return true si la variable est définie dans la portée actuelle, false sinon
     */
    public boolean isVariableDefinedInCurrentScope(String id) {
        String fullId = getFullId(id);
        return symbols.containsKey(fullId) && 
               symbols.get(fullId).getSymbolType() == EMJSymbolType.VARIABLE;
    }
    
    /**
     * Cherche une variable dans la portée actuelle puis dans les portées parentes
     * @param id Identifiant de la variable
     * @return Information sur la variable ou null si non trouvée
     */
    public EMJSymbolInfo lookupVariable(String id) {
        // Chercher d'abord dans la portée actuelle
        String fullId = getFullId(id);
        if (symbols.containsKey(fullId) && 
            symbols.get(fullId).getSymbolType() == EMJSymbolType.VARIABLE) {
            return symbols.get(fullId);
        }
        
        // Chercher dans les portées parentes
        String scope = currentScope;
        while (scope.contains(".")) {
            scope = scope.substring(0, scope.lastIndexOf('.'));
            fullId = scope + ":" + id;
            if (symbols.containsKey(fullId) && 
                symbols.get(fullId).getSymbolType() == EMJSymbolType.VARIABLE) {
                return symbols.get(fullId);
            }
        }
        return null;
    }
    
    /**
     * Ajoute une variable à la table des symboles
     * @param id Identifiant de la variable
     * @param dataType Type de la variable
     * @param initialized Indique si la variable est initialisée
     * @throws IllegalArgumentException Si le type est invalide
     */
    public void addVariable(String id, String dataType, boolean initialized) throws IllegalArgumentException {
        if (!isValidType(dataType)) {
            throw new IllegalArgumentException("Type invalide: " + dataType);
        }
        
        String fullId = getFullId(id);
        EMJSymbolInfo info = new EMJSymbolInfo(id, dataType, currentScope, EMJSymbolType.VARIABLE, initialized);
        symbols.put(fullId, info);
    }

    /**
     * Ajoute une fonction à la table des symboles
     * @param id Identifiant de la fonction
     * @param returnType Type de retour de la fonction
     */
    public void addFunction(String id, String returnType) {
        if (!isValidType(returnType)) {
            throw new IllegalArgumentException("Type de retour invalide: " + returnType);
        }
        
        String fullId = getFullId(id);
        EMJSymbolInfo info = new EMJSymbolInfo(id, null, currentScope, EMJSymbolType.FUNCTION, true);
        info.setReturnType(returnType);
        symbols.put(fullId, info);
    }
    
    /**
     * Ajoute une fonction à la table des symboles avec ses types de paramètres
     * @param id Identifiant de la fonction
     * @param returnType Type de retour de la fonction
     * @param paramTypes Liste des types des paramètres de la fonction
     * @throws IllegalArgumentException Si le type de retour est invalide
     */
    public void addFunction(String id, String returnType, List<String> paramTypes) {
        // Vérifier le type de retour
        if (!isValidType(returnType)) {
            throw new IllegalArgumentException("Type de retour invalide: " + returnType);
        }
        
        // Vérifier les types des paramètres
        for (String paramType : paramTypes) {
            if (!isValidType(paramType)) {
                throw new IllegalArgumentException("Type de paramètre invalide: " + paramType);
            }
        }
        
        String fullId = getFullId(id);
        EMJSymbolInfo info = new EMJSymbolInfo(id, null, currentScope, EMJSymbolType.FUNCTION, true);
        info.setReturnType(returnType);
        
        // Stocker les informations sur les paramètres
        // Les identifiants spécifiques des paramètres seront ajoutés séparément avec addParameter
        info.setParameterTypes(paramTypes);
        
        symbols.put(fullId, info);
    }
    
    /**
     * Ajoute un paramètre à une fonction
     * @param functionId Identifiant de la fonction
     * @param parameterId Identifiant du paramètre
     * @param dataType Type du paramètre
     */
    public void addParameter(String functionId, String parameterId, String dataType) {
        if (!isValidType(dataType)) {
            throw new IllegalArgumentException("Type de paramètre invalide: " + dataType);
        }
        
        EMJSymbolInfo functionInfo = lookupFunction(functionId);
        if (functionInfo == null) {
            throw new IllegalArgumentException("Fonction non définie: " + functionId);
        }
        
        EMJSymbolInfo paramInfo = new EMJSymbolInfo(parameterId, dataType, currentScope, EMJSymbolType.PARAMETER, true);
        functionInfo.addParameter(paramInfo);
        
        // Ajouter également le paramètre comme un symbole indépendant
        String fullParamId = getFullId(parameterId);
        symbols.put(fullParamId, paramInfo);
    }
    
    /**
     * Détermine le type d'une variable
     * @param id Identifiant de la variable
     * @return Type de la variable ou null si non trouvée
     */
    public String getVariableType(String id) {
        EMJSymbolInfo info = lookupVariable(id);
        return info != null ? info.getDataType() : null;
    }
    
    /**
     * Vérifie si une fonction est définie
     * @param id Identifiant de la fonction
     * @return true si la fonction est définie, false sinon
     */
    public boolean isFunctionDefined(String id) {
        String fullId = getFullId(id);
        EMJSymbolInfo info = symbols.get(fullId);
        return info != null && info.isFunction();
    }
    
    /**
     * Cherche une fonction dans la table des symboles
     * @param id Identifiant de la fonction
     * @return Information sur la fonction ou null si non trouvée
     */
    public EMJSymbolInfo lookupFunction(String id) {
        String fullId = getFullId(id);
        if (symbols.containsKey(fullId) && 
            symbols.get(fullId).getSymbolType() == EMJSymbolType.FUNCTION) {
            return symbols.get(fullId);
        }
        return null;
    }
    
    /**
     * Récupère toutes les variables dans une portée donnée
     * @param scope Portée à explorer
     * @return Liste des informations sur les variables
     */
    public List<EMJSymbolInfo> getVariablesInScope(String scope) {
        List<EMJSymbolInfo> result = new ArrayList<>();
        for (EMJSymbolInfo info : symbols.values()) {
            if (info.getSymbolType() == EMJSymbolType.VARIABLE && 
                info.getScope().equals(scope)) {
                result.add(info);
            }
        }
        return result;
    }
    
    /**
     * Récupère toutes les fonctions dans une portée donnée
     * @param scope Portée à explorer
     * @return Liste des informations sur les fonctions
     */
    public List<EMJSymbolInfo> getFunctionsInScope(String scope) {
        List<EMJSymbolInfo> result = new ArrayList<>();
        for (EMJSymbolInfo info : symbols.values()) {
            if (info.getSymbolType() == EMJSymbolType.FUNCTION && 
                info.getScope().equals(scope)) {
                result.add(info);
            }
        }
        return result;
    }
    
    /**
     * Vérifie si une variable est initialisée
     * @param id Identifiant de la variable
     * @return true si la variable est initialisée, false sinon
     */
    public boolean isVariableInitialized(String id) {
        EMJSymbolInfo info = lookupVariable(id);
        return info != null && info.isInitialized();
    }
    
    /**
     * Marque une variable comme initialisée
     * @param id Identifiant de la variable
     */
    public void setVariableInitialized(String id) {
        EMJSymbolInfo info = lookupVariable(id);
        if (info != null) {
            info.setInitialized(true);
        }
    }
    
    /**
     * Vérifie si deux types sont compatibles pour une opération
     * @param type1 Premier type
     * @param type2 Second type
     * @return true si les types sont compatibles, false sinon
     */
    public boolean areTypesCompatible(String type1, String type2) {
        // Types identiques sont toujours compatibles
        if (type1.equals(type2)) {
            return true;
        }
        
        // Règles de compatibilité spécifiques au langage EMJ
        // À compléter selon les spécifications exactes du langage
        return false;
    }
    
    /**
     * Vérifie si les arguments d'un appel de fonction sont compatibles avec les paramètres
     * @param functionId Identifiant de la fonction
     * @param argTypes Liste des types des arguments
     * @return true si les arguments sont compatibles, false sinon
     */
    public boolean checkFunctionCallArguments(String functionId, List<String> argTypes) {
        EMJSymbolInfo functionInfo = lookupFunction(functionId);
        if (functionInfo == null) {
            return false;
        }
        
        List<EMJSymbolInfo> parameters = functionInfo.getParameters();
        if (parameters.size() != argTypes.size()) {
            return false;
        }
        
        for (int i = 0; i < parameters.size(); i++) {
            if (!areTypesCompatible(parameters.get(i).getDataType(), argTypes.get(i))) {
                return false;
            }
        }
        
        return true;
    }
    
    /**
     * Récupère le type de retour d'une fonction
     * @param functionId Identifiant de la fonction
     * @return Type de retour de la fonction ou null si non trouvée
     */
    public String getFunctionReturnType(String functionId) {
        EMJSymbolInfo functionInfo = lookupFunction(functionId);
        return functionInfo != null ? functionInfo.getReturnType() : null;
    }
    
    // Pour compatibilité avec l'ancienne implémentation
    @Deprecated
    public EMJSymbolInfo lookup(String id) {
        return lookupVariable(id);
    }
}
