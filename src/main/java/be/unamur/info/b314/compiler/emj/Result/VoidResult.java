package be.unamur.info.b314.compiler.emj.Result;

public class VoidResult extends Result {
    private VoidResult(boolean valid) {
        super(valid);
    }

    public static VoidResult valid() {
        return new VoidResult(true);
    }

    public static VoidResult invalid() {
        return new VoidResult(false);
    }
}
