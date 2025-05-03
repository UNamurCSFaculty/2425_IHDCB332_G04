package be.unamur.info.b314.compiler.emj.Result;

public abstract class Result {
    private final boolean valid;

    protected Result(boolean valid) {
        this.valid = valid;
    }

    public boolean isValid() {
        return valid;
    }
}
