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

    /**
     * @effects initialise un nouveau journal d'erreurs vide
     *          this_post.errors est une liste vide
     *          this_post.hasErrors est false
     */
    public EMJErrorLogger() {
        this.errors = new ArrayList<EMJError>();
        this.hasErrors = false;
    }

    /**
     * @return this.errors - la liste des erreurs enregistrées
     */
    public ArrayList<EMJError> getErrors() {
        return this.errors;
    }

    /**
     * @requires error != null
     * @modifies this.errors, this.hasErrors
     * @effects ajoute error à this.errors
     *          this_post.hasErrors est true
     *          this_post.errors.size() = this_pre.errors.size() + 1
     */
    public void addError(EMJError error) {
        this.errors.add(error);
        this.hasErrors = true;
    }

    /**
     * @return true si des erreurs ont été enregistrées, false sinon
     */
    public boolean containsErrors() {
        return this.hasErrors;
    }

    /**
     * @return une chaîne de caractères formatant toutes les erreurs enregistrées
     *         chaîne vide si aucune erreur n'a été enregistrée
     */
    public String getErrorsString() {
        String errorsString = "";

        for(EMJError error : this.errors) {
            errorsString = errorsString + error.getErrorString() + "\n";
        }

        return errorsString;
    }
}