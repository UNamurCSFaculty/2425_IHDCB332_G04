package be.unamur.info.b314.compiler.emj;

public class EMJParameterInfo {
    private final String id;
    private final String dataType;

    public EMJParameterInfo(String id, String dataType) {
        this.id = id;
        this.dataType = dataType;
    }

    public String getId() {
        return id;
    }

    public String getType() {
        return dataType;
    }
}