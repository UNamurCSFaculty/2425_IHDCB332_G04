package be.unamur.info.b314.compiler.emj;

import java.util.List;

/**
 * Représente les informations d'un symbole dans le compilateur EMJ
 * 
 * @invariant id != null
 * @invariant scope != null
 * @invariant symbolType != null
 */
public class EMJSymbolInfo {

    private final String id;
    private final String dataType;          // type d'une variable OU type de retour d'une fonction
    private final String scope;
    private final EMJSymbolType symbolType;

    private boolean isInitialized;          // nouvel état d'initialisation

    private List<EMJParameterInfo> parameters;
    private String returnType;

    /**
     * @param id Identifiant du symbole
     * @param dataType Type de données du symbole
     * @param scope Portée du symbole
     * @param symbolType Type du symbole
     * @param initialized État d'initialisation initial
     * @requires id != null
     * @requires scope != null
     * @requires symbolType != null
     * @ensures this.id == id
     * @ensures this.dataType == dataType
     * @ensures this.scope == scope
     * @ensures this.symbolType == symbolType
     * @ensures this.isInitialized == initialized
     */
    public EMJSymbolInfo(String id,
                         String dataType,
                         String scope,
                         EMJSymbolType symbolType,
                         boolean initialized) {
        this.id            = id;
        this.dataType      = dataType;
        this.scope         = scope;
        this.symbolType    = symbolType;
        this.isInitialized = initialized;
    }

    /**
     * @return L'identifiant du symbole
     * @pure
     */
    public String getId()               { return id; }
    
    /**
     * @return Le type de données du symbole
     * @pure
     */
    public String getType()             { return dataType; }
    
    /**
     * @return La portée du symbole
     * @pure
     */
    public String getScope()            { return scope; }
    
    /**
     * @return Le type du symbole
     * @pure
     */
    public EMJSymbolType getSymbolType(){ return symbolType; }
    
    /**
     * @return Le type de retour de la fonction
     * @pure
     */
    public String getReturnType()       { return returnType; }
    
    /**
     * @return La liste des paramètres de la fonction
     * @pure
     */
    public List<EMJParameterInfo> getParameters() { return parameters; }

    /**
     * Indique si la variable / le tuple a déjà reçu une valeur
     * @return L'état d'initialisation du symbole
     * @pure
     * @ensures \result == isInitialized
     */
    public boolean isInitialized() {
        return isInitialized;
    }

    /**
     * Marque la variable / le tuple comme initialisé ou non
     * @param initialized Le nouvel état d'initialisation
     * @ensures isInitialized == initialized
     * @assignable isInitialized
     */
    public void setInitialized(boolean initialized) {
        this.isInitialized = initialized;
    }

    /**
     * Définit le type de retour de la fonction
     * @param returnType Le type de retour
     * @requires returnType != null || returnType.equals("VOID")
     * @ensures this.returnType == returnType
     * @assignable this.returnType
     */
    public void SetReturnType(String returnType) {
        this.returnType = returnType;
    }

    /**
     * Définit les paramètres de la fonction
     * @param parameters La liste des paramètres
     * @requires parameters != null
     * @ensures this.parameters == parameters
     * @assignable this.parameters
     */
    public void SetParameters(List<EMJParameterInfo> parameters) {
        this.parameters = parameters;
    }
}