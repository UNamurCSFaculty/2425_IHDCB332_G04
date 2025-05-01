package be.unamur.info.b314.compiler.emj;

/*
EMJError class to define an EMJ error
@author : Alix Decrop
@version : 1.0
*/
/*@ public invariant name != null;
  @ public invariant location != null;
  @ public invariant line >= 0;
  @*/
public class EMJError {

    private final String name;
    private final String location;
    private final int line;

    /*@ requires name != null;
      @ requires location != null;
      @ requires line >= 0;
      @ ensures this.name.equals(name);
      @ ensures this.location.equals(location);
      @ ensures this.line == line;
      @*/
    public EMJError(String name, String location, int line) {
        this.name = name;
        this.location = location;
        this.line = line;
    }

    /*@ pure
      @ ensures \result != null;
      @ ensures \result.contains(name);
      @ ensures \result.contains(location);
      @ ensures \result.contains(Integer.toString(line));
      @*/
    public String getErrorString() {
        return "[EMJ ERROR] " + this.name + " for " + this.location + " at line " + this.line;
    }
}