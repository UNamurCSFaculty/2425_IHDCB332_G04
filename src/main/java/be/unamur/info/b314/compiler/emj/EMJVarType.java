package be.unamur.info.b314.compiler.emj;

public enum EMJVarType {
    TUPLE("TUPLE"), INT("INT"), BOOL("BOOL"), STRING("STRING"), CHAR("CHAR"), UNKNOWN("UNKNOWN"), VOID("VOID");

    private final String label;

    private EMJVarType(String label) {
        this.label = label;
    }

    public String label() {
        return label;
    }
}
