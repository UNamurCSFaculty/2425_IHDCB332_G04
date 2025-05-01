package be.unamur.info.b314.compiler.exception;

/**
 *
 * @author James Ortiz - james.ortizvega@unamur.be
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