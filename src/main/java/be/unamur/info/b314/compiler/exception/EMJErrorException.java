package be.unamur.info.b314.compiler.exception;

/*
EMJErrorException extending an Exception, to warn when error(s) occured during the tree visit
@author : Alix Decrop
@version : 1.0
*/
/*@ public invariant getMessage() != null;
  @ public invariant getMessage().contains("Error(s)");
  @ public invariant getMessage().contains("tree visit");
  @*/
public class EMJErrorException extends Exception {

    /*@ requires errors != null;
      @ ensures getMessage().contains(errors);
      @*/
    public EMJErrorException(String errors) {
        super("Error(s) were caught during EMJ tree visit. Stacktrace:\n" + errors);
    }
}