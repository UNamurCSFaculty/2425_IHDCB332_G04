package be.unamur.info.b314.compiler.emj;

import java.util.List;

/**
 * Représente les informations d'un symbole dans le compilateur EMJ
 */
/*@ public invariant id != null;
  @ public invariant scope != null;
  @ public invariant symbolType != null;
  @*/
public class EMJSymbolInfo {

    private final String id;
    private final String dataType;          // type d'une variable OU type de retour d'une fonction
    private final String scope;
    private final EMJSymbolType symbolType;

    private boolean isInitialized;          // nouvel état d'initialisation

    private List<EMJParameterInfo> parameters;
    private String returnType;

    /*@ requires id != null;
      @ requires scope != null;
      @ requires symbolType != null;
      @ ensures this.id == id;
      @ ensures this.dataType == dataType;
      @ ensures this.scope == scope;
      @ ensures this.symbolType == symbolType;
      @ ensures this.isInitialized == initialized;
      @*/
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

    /*@ pure @*/
    public String getId()               { return id; }
    
    /*@ pure @*/
    public String getType()             { return dataType; }
    
    /*@ pure @*/
    public String getScope()            { return scope; }
    
    /*@ pure @*/
    public EMJSymbolType getSymbolType(){ return symbolType; }
    
    /*@ pure @*/
    public String getReturnType()       { return returnType; }
    
    /*@ pure @*/
    public List<EMJParameterInfo> getParameters() { return parameters; }

    /** Indique si la variable / le tuple a déjà reçu une valeur */
    /*@ pure
      @ ensures \result == isInitialized;
      @*/
    public boolean isInitialized() {
        return isInitialized;
    }

    /** Marque la variable / le tuple comme initialisé ou non */
    /*@ ensures isInitialized == initialized;
      @ assignable isInitialized;
      @*/
    public void setInitialized(boolean initialized) {
        this.isInitialized = initialized;
    }

    /*@ requires returnType != null || returnType.equals("VOID");
      @ ensures this.returnType == returnType;
      @ assignable this.returnType;
      @*/
    public void SetReturnType(String returnType) {
        this.returnType = returnType;
    }

    /*@ requires parameters != null;
      @ ensures this.parameters == parameters;
      @ assignable this.parameters;
      @*/
    public void SetParameters(List<EMJParameterInfo> parameters) {
        this.parameters = parameters;
    }
}