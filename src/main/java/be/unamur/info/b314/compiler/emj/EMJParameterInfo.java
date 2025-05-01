package be.unamur.info.b314.compiler.emj;

/**
 * Représente les informations d'un paramètre de fonction dans le compilateur EMJ
 * 
 * @invariant id != null
 * @invariant dataType != null
 */
public class EMJParameterInfo {
    private final String id;
    private final String dataType;

    /**
     * Constructeur pour les informations d'un paramètre
     * 
     * @param id Identifiant du paramètre
     * @param dataType Type de données du paramètre
     * @requires id != null
     * @requires dataType != null
     * @ensures this.id.equals(id)
     * @ensures this.dataType.equals(dataType)
     */
    public EMJParameterInfo(String id, String dataType) {
        this.id = id;
        this.dataType = dataType;
    }

    /**
     * Obtient l'identifiant du paramètre
     * 
     * @return L'identifiant du paramètre
     * @pure
     * @ensures \result != null
     * @ensures \result.equals(id)
     */
    public String getId() {
        return id;
    }

    /**
     * Obtient le type de données du paramètre
     * 
     * @return Le type de données du paramètre
     * @pure
     * @ensures \result != null
     * @ensures \result.equals(dataType)
     */
    public String getType() {
        return dataType;
    }
}