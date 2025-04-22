package be.unamur.info.b314.compiler.emj;

import java.util.List;

public class EMJSymbolInfo {

    /* ----------------------- Champs ----------------------- */
    private final String id;
    private final String dataType;          // type d’une variable OU type de retour d’une fonction
    private final String scope;
    private final EMJSymbolType symbolType;

    private boolean isInitialized;          // nouvel état d’initialisation

    /* Pour les fonctions */
    private List<EMJParameterInfo> parameters;
    private String returnType;

    /* ------------------- Constructeur(s) ------------------ */
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

    /* -------------------- Getters ------------------------- */
    public String getId()               { return id; }
    public String getType()             { return dataType; }
    public String getScope()            { return scope; }
    public EMJSymbolType getSymbolType(){ return symbolType; }
    public String getReturnType()       { return returnType; }
    public List<EMJParameterInfo> getParameters() { return parameters; }

    /** Indique si la variable / le tuple a déjà reçu une valeur */
    public boolean isInitialized() {
        return isInitialized;
    }

    /* -------------------- Setters ------------------------- */
    /** Marque la variable / le tuple comme initialisé ou non */
    public void setInitialized(boolean initialized) {
        this.isInitialized = initialized;
    }

    public void SetReturnType(String returnType) {
        this.returnType = returnType;
    }

    public void SetParameters(List<EMJParameterInfo> parameters) {
        this.parameters = parameters;
    }
}
