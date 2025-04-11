package be.unamur.info.b314.compiler.emj;

import java.util.List;

public class EMJSymbolInfo {
    private final String id;
    private final String dataType;
    private final String scope;
    private final EMJSymbolType symbolType;
    private boolean isInitialized;

    private List<EMJParameterInfo> parameters;  // Paramètres de la fonction
    private String returnType;              // Type de retour

    EMJSymbolInfo(String id, String dataType, String scope, EMJSymbolType symbolType, boolean initialized) {
        this.id = id;
        this.dataType = dataType;
        this.scope = scope;
        this.symbolType = symbolType;
        this.isInitialized = initialized;
    }

    public String getId() {
        return id;
    }

    public void SetReturnType(String returnType) {
        this.returnType = returnType;
    }

    public void SetParameters(List<EMJParameterInfo> parameters) {
        this.parameters = parameters;
    }
    public String getType() {
        return dataType;
    }

    public String getReturnType() {
        return returnType;
    }
}


