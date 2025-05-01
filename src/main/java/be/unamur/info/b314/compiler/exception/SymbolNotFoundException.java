package be.unamur.info.b314.compiler.exception;

/**
 *
 * @author James Ortiz - james.ortizvega@unamur.be
 *  * @overview Exception levée lorsqu'un symbole n'est pas trouvé dans la table des symboles, immutable.
 *  *
 *  * @invariant getMessage() != null
 */
/*@ public invariant getMessage() != null;
  @*/
public class SymbolNotFoundException extends RuntimeException {

    /**
     * @requires message != null
     * @ensures getMessage().equals(message)
     * @ensures getCause() == null
     */
    public SymbolNotFoundException(String message) {
        super(message);
    }

    /**
     * @requires message != null
     * @requires cause != null
     * @ensures getMessage().equals(message)
     * @ensures getCause() == cause
     */
    public SymbolNotFoundException(String message, Exception cause) {
        super(message, cause);
    }
}