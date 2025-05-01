package be.unamur.info.b314.compiler.exception;

/**
 * Exception class representing parsing errors.
 * @author James Ortiz - james.ortizvega@unamur.be
 */
/*@ public invariant getMessage() != null;
  @*/
public class ParsingException extends Exception {

    /*@ requires message != null;
      @ requires e != null;
      @ ensures getMessage().equals(message);
      @ ensures getCause() == e;
      @*/
    public ParsingException(String message, Exception e) {
        super(message, e);
    }
    
    /*@ requires message != null;
      @ ensures getMessage().equals(message);
      @ ensures getCause() == null;
      @*/
    public ParsingException(String message){
        super(message);
    }
}