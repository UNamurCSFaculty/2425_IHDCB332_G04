package be.unamur.info.b314.compiler.emj;

/**
 * Représente les informations d'un paramètre de fonction dans le compilateur EMJ
 */
/*@ public invariant id != null;
  @ public invariant dataType != null;
  @*/
public class EMJParameterInfo {
    private final String id;
    private final String dataType;

    /*@ requires id != null;
      @ requires dataType != null;
      @ ensures this.id.equals(id);
      @ ensures this.dataType.equals(dataType);
      @*/
    public EMJParameterInfo(String id, String dataType) {
        this.id = id;
        this.dataType = dataType;
    }

    /*@ pure
      @ ensures \result != null;
      @ ensures \result.equals(id);
      @*/
    public String getId() {
        return id;
    }

    /*@ pure
      @ ensures \result != null;
      @ ensures \result.equals(dataType);
      @*/
    public String getType() {
        return dataType;
    }
}