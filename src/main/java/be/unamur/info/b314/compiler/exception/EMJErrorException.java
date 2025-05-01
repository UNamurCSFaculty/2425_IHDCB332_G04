package be.unamur.info.b314.compiler.exception;

/**
 * @overview Exception lancée lorsque des erreurs sont détectées lors de la visite de l'arbre syntaxique EMJ, immutable.
 * 
 * @invariant getMessage() != null
 * @invariant getMessage().contains("Error(s)")
 * @invariant getMessage().contains("tree visit")
 */
public class EMJErrorException extends Exception {

    /**
     * @requires errors != null
     * @ensures getMessage().contains(errors)
     */
    public EMJErrorException(String errors) {
        super("Error(s) were caught during EMJ tree visit. Stacktrace:\n" + errors);
    }
}