package be.unamur.info.b314.compiler.emj.Result;

import be.unamur.info.b314.compiler.emj.EMJVarType;

public class TypeResult extends Result {
    private final String typeId;

    private TypeResult(String typeId, boolean valid) {
        super(valid);
        this.typeId = typeId;
    }

    public String getTypeId() {
        return typeId;
    }

    public static TypeResult valid(String typeId) {
        return new TypeResult(typeId, true);
    }

    public static TypeResult invalid(String typeId) {
        return new TypeResult(typeId, false);
    }

    public static TypeResult unknown() {
        return new TypeResult(EMJVarType.UNKNOWN.label(), false);
    }
}
