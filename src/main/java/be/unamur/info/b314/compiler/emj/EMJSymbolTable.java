package be.unamur.info.b314.compiler.emj;

import java.util.*;

/**
 * Classe représentant la table des symboles pour le langage EMJ.
 * Gère les variables, fonctions et paramètres avec leur portée et type.
 */
public class EMJSymbolTable {

    private final Map<String, EMJSymbolInfo> symbols;
    private String currentScope;
    private final Stack<String> scopeStack;
    private final Set<String> validTypes;

    /**
     * Constructeur de la table des symboles
     */
    public EMJSymbolTable() {
        this.symbols = new HashMap<>();
        this.currentScope = "global";
        this.scopeStack = new Stack<>();
        this.scopeStack.push("global");
        
        // Initialisation des types valides
        this.validTypes = new HashSet<>();
        this.validTypes.add("INT");
        this.validTypes.add("BOOL");
        this.validTypes.add("CHAR");
        this.validTypes.add("STRING");
        this.validTypes.add("VOID");
        this.validTypes.add("TUPLE");
    }

    /**
     * Définit la portée actuelle
     */
    public void setScope(String scope) {
        this.currentScope = scope;
        // Ne pas empiler si on change à la même portée
        if (!scopeStack.isEmpty() && !scopeStack.peek().equals(scope)) {
            scopeStack.push(scope);
        }
    }

    /**
     * Retourne à la portée précédente
     */
    public void popScope() {
        if (scopeStack.size() > 1) { // Garder au moins la portée globale
            scopeStack.pop();
            this.currentScope = scopeStack.peek();
        }
    }

    /**
     * Obtient la portée actuelle
     */
    public String getScope() {
        return this.currentScope;
    }

    /**
     * Vérifie si un type est valide
     */
    public boolean isValidType(String type) {
        if (type == null) return false;
        
        // Vérification de type tuple avec type interne
        if (type.startsWith("TUPLE<") && type.endsWith(">")) {
            String innerType = type.substring(6, type.length() - 1);
            return validTypes.contains(innerType) && !innerType.equals("TUPLE") && !innerType.equals("VOID");
        }
        
        return validTypes.contains(type);
    }

    /**
     * Construit un nom qualifié avec la portée actuelle
     */
    private String getQualifiedName(String id) {
        return this.currentScope + "." + id;
    }

    /**
     * Construit un nom qualifié avec une portée spécifique
     */
    private String getQualifiedName(String scope, String id) {
        return scope + "." + id;
    }

    /**
     * Ajoute une variable à la table des symboles
     */
    public void addVariable(String id, String dataType, boolean initialized) {
        // Vérifier que le type est valide
        if (!isValidType(dataType)) {
            throw new IllegalArgumentException("Type invalide: " + dataType);
        }
        
        // Extraire le nom qualifié
        String qualifiedName = getQualifiedName(id);
        
        // Vérifier si la variable existe déjà dans la portée actuelle
        if (this.symbols.containsKey(qualifiedName)) {
            throw new IllegalArgumentException("Variable " + id + " déjà définie dans la portée " + this.currentScope);
        }
        
        // Créer un objet EMJSymbolInfo approprié
        EMJSymbolInfo symbolInfo;
        
        // Gérer les tuples avec leurs types internes
        if (dataType.startsWith("TUPLE<") && dataType.endsWith(">")) {
            String innerType = dataType.substring(6, dataType.length() - 1);
            symbolInfo = new EMJSymbolInfo(id, this.currentScope, EMJSymbolType.VARIABLE, initialized, innerType);
        } else {
            // Variable standard
            symbolInfo = new EMJSymbolInfo(id, dataType, this.currentScope, EMJSymbolType.VARIABLE, initialized);
        }
        
        // Ajouter la variable à la table des symboles
        this.symbols.put(qualifiedName, symbolInfo);
    }

    /**
     * Ajoute une fonction à la table des symboles
     */
    public void addFunction(String id, String returnType) {
        // Vérifier que le type de retour est valide
        if (!isValidType(returnType)) {
            throw new IllegalArgumentException("Type de retour invalide: " + returnType);
        }
        
        // Vérifier si la fonction existe déjà dans la portée actuelle
        String qualifiedName = getQualifiedName(id);
        if (this.symbols.containsKey(qualifiedName)) {
            throw new IllegalArgumentException("Fonction " + id + " déjà définie dans la portée " + this.currentScope);
        }
        
        // Ajouter la fonction à la table des symboles
        EMJSymbolInfo functionInfo = new EMJSymbolInfo(id, returnType, this.currentScope);
        this.symbols.put(qualifiedName, functionInfo);
        
        // Créer une nouvelle portée pour la fonction
        setScope(this.currentScope + "." + id);
    }

    /**
     * Ajoute un paramètre à une fonction
     */
    public void addParameter(String functionId, String paramId, String dataType) {
        // Vérifier que le type est valide
        if (!isValidType(dataType)) {
            throw new IllegalArgumentException("Type de paramètre invalide: " + dataType);
        }
        
        // Trouver la fonction parent
        String functionQualifiedName = getQualifiedName(this.currentScope.substring(0, this.currentScope.lastIndexOf('.')), functionId);
        if (!this.symbols.containsKey(functionQualifiedName) || !this.symbols.get(functionQualifiedName).isFunction()) {
            throw new IllegalArgumentException("Fonction parent introuvable: " + functionId);
        }
        
        // Créer le paramètre
        EMJSymbolInfo paramInfo = new EMJSymbolInfo(paramId, dataType, this.currentScope, EMJSymbolType.PARAMETER, true);
        
        // Ajouter le paramètre à la table des symboles
        String paramQualifiedName = getQualifiedName(paramId);
        this.symbols.put(paramQualifiedName, paramInfo);
        
        // Ajouter le paramètre à la fonction
        EMJSymbolInfo functionInfo = this.symbols.get(functionQualifiedName);
        functionInfo.addParameter(paramInfo);
    }

    /**
     * Récupère une variable de la table des symboles
     */
    public EMJSymbolInfo getVariable(String id) {
        // Essayer de trouver la variable dans la portée actuelle et les portées parentes
        String currentScopeTemp = this.currentScope;
        while (currentScopeTemp != null) {
            String qualifiedName = getQualifiedName(currentScopeTemp, id);
            if (this.symbols.containsKey(qualifiedName)) {
                EMJSymbolInfo info = this.symbols.get(qualifiedName);
                if (info.isVariable() || info.isParameter()) {
                    return info;
                }
            }
            // Remonter à la portée parente
            int lastDotIndex = currentScopeTemp.lastIndexOf('.');
            if (lastDotIndex == -1) {
                // Essayer la portée globale si on n'y est pas déjà
                if (!currentScopeTemp.equals("global")) {
                    currentScopeTemp = "global";
                } else {
                    currentScopeTemp = null;
                }
            } else {
                currentScopeTemp = currentScopeTemp.substring(0, lastDotIndex);
            }
        }
        
        throw new IllegalArgumentException("Variable " + id + " introuvable dans la portée " + this.currentScope + " et les portées parentes");
    }

    /**
     * Récupère une fonction de la table des symboles
     */
    public EMJSymbolInfo getFunction(String id) {
        // Essayer de trouver la fonction dans la portée actuelle et les portées parentes
        String currentScopeTemp = this.currentScope;
        while (currentScopeTemp != null) {
            String qualifiedName = getQualifiedName(currentScopeTemp, id);
            if (this.symbols.containsKey(qualifiedName)) {
                EMJSymbolInfo info = this.symbols.get(qualifiedName);
                if (info.isFunction()) {
                    return info;
                }
            }
            // Remonter à la portée parente
            int lastDotIndex = currentScopeTemp.lastIndexOf('.');
            if (lastDotIndex == -1) {
                // Essayer la portée globale si on n'y est pas déjà
                if (!currentScopeTemp.equals("global")) {
                    currentScopeTemp = "global";
                } else {
                    currentScopeTemp = null;
                }
            } else {
                currentScopeTemp = currentScopeTemp.substring(0, lastDotIndex);
            }
        }
        
        throw new IllegalArgumentException("Fonction " + id + " introuvable dans la portée " + this.currentScope + " et les portées parentes");
    }

    /**
     * Vérifie si une variable est définie dans la portée actuelle ou les portées parentes
     */
    public boolean isVariableDefined(String id) {
        try {
            getVariable(id);
            return true;
        } catch (IllegalArgumentException e) {
            return false;
        }
    }

    /**
     * Vérifie si une fonction est définie dans la portée actuelle ou les portées parentes
     */
    public boolean isFunctionDefined(String id) {
        try {
            getFunction(id);
            return true;
        } catch (IllegalArgumentException e) {
            return false;
        }
    }

    /**
     * Récupère toutes les variables dans une portée spécifique
     */
    public Set<String> getVariablesInScope(String scope) {
        Set<String> result = new HashSet<>();
        String prefix = scope + ".";
        for (Map.Entry<String, EMJSymbolInfo> entry : this.symbols.entrySet()) {
            String key = entry.getKey();
            EMJSymbolInfo info = entry.getValue();
            if (key.startsWith(prefix) && (info.isVariable() || info.isParameter())) {
                result.add(key.substring(prefix.length()));
            }
        }
        return result;
    }

    /**
     * Récupère toutes les fonctions dans une portée spécifique
     */
    public Set<String> getFunctionsInScope(String scope) {
        Set<String> result = new HashSet<>();
        String prefix = scope + ".";
        for (Map.Entry<String, EMJSymbolInfo> entry : this.symbols.entrySet()) {
            String key = entry.getKey();
            EMJSymbolInfo info = entry.getValue();
            if (key.startsWith(prefix) && info.isFunction()) {
                result.add(key.substring(prefix.length()));
            }
        }
        return result;
    }

    /**
     * Vérifie si une variable est initialisée
     */
    public boolean isVariableInitialized(String id) {
        EMJSymbolInfo variable = getVariable(id);
        return variable.isInitialized();
    }

    /**
     * Définit une variable comme initialisée
     */
    public void setVariableInitialized(String id) {
        EMJSymbolInfo variable = getVariable(id);
        variable.setInitialized(true);
    }

    /**
     * Vérifie la compatibilité des types
     */
    public boolean areTypesCompatible(String type1, String type2) {
        if (type1 == null || type2 == null) return false;
        if (type1.equals(type2)) return true;
        
        // Gérer les tuples
        if (type1.startsWith("TUPLE<") && type2.startsWith("TUPLE<")) {
            String innerType1 = type1.substring(6, type1.length() - 1);
            String innerType2 = type2.substring(6, type2.length() - 1);
            return innerType1.equals(innerType2);
        }
        
        return false;
    }

    /**
     * Vérifie la compatibilité des arguments pour un appel de fonction
     */
    public boolean checkFunctionCallArguments(String functionId, List<String> argTypes) {
        try {
            EMJSymbolInfo function = getFunction(functionId);
            List<EMJSymbolInfo> parameters = function.getParameters();
            
            if (parameters.size() != argTypes.size()) {
                return false;
            }
            
            for (int i = 0; i < parameters.size(); i++) {
                String paramType = parameters.get(i).getDataType();
                String argType = argTypes.get(i);
                if (!areTypesCompatible(paramType, argType)) {
                    return false;
                }
            }
            
            return true;
        } catch (IllegalArgumentException e) {
            return false;
        }
    }

    /**
     * Récupère le type de retour d'une fonction
     */
    public String getFunctionReturnType(String functionId) {
        EMJSymbolInfo function = getFunction(functionId);
        return function.getReturnType();
    }

    /**
     * Affiche toutes les entrées de la table des symboles (pour débogage)
     */
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder("EMJSymbolTable:\n");
        for (Map.Entry<String, EMJSymbolInfo> entry : this.symbols.entrySet()) {
            sb.append(entry.getKey()).append(" -> ").append(entry.getValue()).append("\n");
        }
        return sb.toString();
    }
}
