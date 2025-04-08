package be.unamur.info.b314.compiler.emj;

import java.util.ArrayList;
import java.util.List;

public class EMJSymbolInfo {
    private final String id;
    private final String dataType;
    private final String scope;
    private final EMJSymbolType symbolType;
    private boolean isInitialized;
    private List<String> paramTypes; // Pour stocker les types des paramètres d'une fonction

    EMJSymbolInfo(String id, String dataType, String scope, EMJSymbolType symbolType, boolean initialized) {
        this.id = id;
        this.dataType = dataType;
        this.scope = scope;
        this.symbolType = symbolType;
        this.isInitialized = initialized;
        this.paramTypes = new ArrayList<>();
    }
    
    /**
     * Constructeur pour les fonctions avec paramètres
     */
    EMJSymbolInfo(String id, String dataType, String scope, EMJSymbolType symbolType, boolean initialized, List<String> paramTypes) {
        this.id = id;
        this.dataType = dataType;
        this.scope = scope;
        this.symbolType = symbolType;
        this.isInitialized = initialized;
        this.paramTypes = paramTypes;
    }
    
    /**
     * Get the data type of this symbol
     * 
     * @return The data type as a string
     */
    public String getDataType() {
        return this.dataType;
    }
    
    /**
     * Vérifie si ce symbole est une fonction
     * 
     * @return true si ce symbole est une fonction, false sinon
     */
    public boolean isFunction() {
        return this.symbolType == EMJSymbolType.FUNCTION;
    }
    
    /**
     * Récupère les types des paramètres de la fonction
     * 
     * @return Une liste contenant les types des paramètres
     */
    public List<String> getParamTypes() {
        return this.paramTypes;
    }
    
    /**
     * Ajoute un type de paramètre à la liste des types de paramètres
     * Utile lors de la construction progressive d'une fonction
     * 
     * @param paramType Le type du paramètre à ajouter
     */
    public void addParamType(String paramType) {
        this.paramTypes.add(paramType);
    }
}
