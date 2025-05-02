package be.unamur.info.b314.compiler.exception;

/**
 * @overview Exception lors d'erreurs d'analyse du code EMJ.
 */
public class ParsingException extends Exception {
    
    /**
     * @effects this_post = nouvelle exception avec message spécifié
     */
    public ParsingException(String message) {
        super(message);
    }
    
    /**
     * @effects this_post = nouvelle exception avec message et cause spécifiés
     */
    public ParsingException(String message, Throwable cause) {
        super(message, cause);
    }
}