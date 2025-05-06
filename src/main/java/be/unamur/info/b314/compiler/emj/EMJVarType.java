package be.unamur.info.b314.compiler.emj;

public enum EMJVarType {
    TUPLE("tuple"), INT("int"), BOOL("bool"), STRING("str"), CHAR("char"), UNKNOWN("Unknown"), VOID("Void"); //Pas de char en python

    private final String label;

    private EMJVarType(String label) {
        this.label = label;
    }

    public String label() {
        return label;
    }

    public String pyLabel() {
        switch (this) {
            case CHAR:
                return "str";
            case UNKNOWN:
            case VOID:
                return "None";
            default:
                return label;
        }
    }
}
