package be.unamur.info.b314.compiler.emj;

public class EMJSymbolInfo {
    private final String id;
    private final String dataType;
    private final String scope;
    private final EMJSymbolType symbolType;
    private boolean isInitialized;

    EMJSymbolInfo(String id, String dataType, String scope, EMJSymbolType symbolType, boolean initialized) {
        this.id = id;
        this.dataType = dataType;
        this.scope = scope;
        this.symbolType = symbolType;
        this.isInitialized = initialized;
    }
    
    /**
     * Get the data type of this symbol
     * 
     * @return The data type as a string
     */
    public String getDataType() {
        return this.dataType;
    }
}
