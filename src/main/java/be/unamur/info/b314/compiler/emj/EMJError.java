package be.unamur.info.b314.compiler.emj;

/**
 * @overview Classe représentant une erreur EMJ immutable.
 * @specfield name : String — nom de l'erreur
 * @specfield location : String — localisation où l'erreur s'est produite
 * @specfield line : int — numéro de ligne où l'erreur a été détectée
 * 
 * @invariant name != null
 * @invariant location != null
 * @invariant line >= 0
 */
public class EMJError {

    private final String name;
    private final String location;
    private final int line;

    /**
     * @requires name != null
     * @requires location != null
     * @requires line >= 0
     * @effects this.name = name
     *          this.location = location
     *          this.line = line
     */
    public EMJError(String name, String location, int line) {
        this.name = name;
        this.location = location;
        this.line = line;
    }

    /**
     * @return une chaîne de caractères formatant l'erreur avec son nom, sa localisation et son numéro de ligne
     *         au format "[EMJ ERROR] {name} for {location} at line {line}"
     */
    public String getErrorString() {
        return "[EMJ ERROR] " + this.name + " for " + this.location + " at line " + this.line;
    }
}