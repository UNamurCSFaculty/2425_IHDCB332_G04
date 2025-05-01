package be.unamur.info.b314.compiler.emj;

import be.unamur.info.b314.compiler.emj.EMJError;
import java.util.ArrayList;

/*
Error logger for EMJ ; Will store errors when visiting a tree
@author : Alix Decrop
@version : 1.0
*/
/*@ public invariant errors != null;
  @ public invariant hasErrors == !errors.isEmpty();
  @*/
public class EMJErrorLogger {

    private ArrayList<EMJError> errors;
    private boolean hasErrors;

    /*@ ensures errors != null;
      @ ensures errors.isEmpty();
      @ ensures !hasErrors;
      @*/
    public EMJErrorLogger() {
        this.errors = new ArrayList<EMJError>();
        this.hasErrors = false;
    }

    /*@ pure
      @ ensures \result == errors;
      @*/
    public ArrayList<EMJError> getErrors() {
        return this.errors;
    }

    /*@ requires error != null;
      @ ensures errors.contains(error);
      @ ensures hasErrors;
      @ ensures errors.size() == \old(errors.size()) + 1;
      @ assignable errors, hasErrors;
      @*/
    public void addError(EMJError error) {
        this.errors.add(error);
        this.hasErrors = true;
    }

    /*@ pure
      @ ensures \result == hasErrors;
      @ ensures \result == !errors.isEmpty();
      @*/
    public boolean containsErrors() {
        return this.hasErrors;
    }

    /*@ pure
      @ ensures \result != null;
      @ ensures errors.isEmpty() ==> \result.equals("");
      @ ensures !errors.isEmpty() ==> \result.contains(errors.get(0).getErrorString());
      @*/
    public String getErrorsString() {
        String errorsString = "";

        for(EMJError error : this.errors) {
            errorsString = errorsString + error.getErrorString() + "\n";
        }

        return errorsString;
    }
}