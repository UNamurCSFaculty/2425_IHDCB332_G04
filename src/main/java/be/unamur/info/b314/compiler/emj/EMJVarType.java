package be.unamur.info.b314.compiler.emj;

public enum EMJVarType {
    TUPLE("tuple"), INT("int"), BOOL("bool"), STRING("str"), CHAR("str"), UNKNOWN("None"), VOID("None"); //Pas de char en python

    private final String label;

    private EMJVarType(String label) {
        this.label = label;
    }

    public String label() {
        return label;
    }
}
