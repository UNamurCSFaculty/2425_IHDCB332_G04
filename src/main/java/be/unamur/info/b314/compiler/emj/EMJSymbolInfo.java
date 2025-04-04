package be.unamur.info.b314.compiler.emj;

import java.util.ArrayList;
import java.util.List;

/**
 * Classe représentant les informations d'un symbole dans la table des symboles.
 * Un symbole peut être une variable, une fonction ou un paramètre.
 */
public class EMJSymbolInfo {
    private final String id;               // Identifiant du symbole
    private final String dataType;        // Type de données (INT, BOOL, CHAR, STRING, TUPLE, VOID)
    private final String scope;           // Portée du symbole
    private final EMJSymbolType symbolType; // Type du symbole (VARIABLE, FUNCTION, PARAMETER)
    private boolean isInitialized;        // Si le symbole est initialisé
    
    // Attributs spécifiques aux fonctions
    private final List<EMJSymbolInfo> parameters; // Liste des paramètres pour une fonction
    private String returnType;            // Type de retour pour une fonction
    
    // Attributs spécifiques aux tuples
    private final String tupleInnerType;        // Type des éléments du tuple

    /**
     * Constructeur pour une variable ou un paramètre
     */
    EMJSymbolInfo(String id, String dataType, String scope, EMJSymbolType symbolType, boolean initialized) {
        this.id = id;
        this.dataType = dataType;
        this.scope = scope;
        this.symbolType = symbolType;
        this.isInitialized = initialized;
        this.parameters = new ArrayList<>();
        this.returnType = null;
        this.tupleInnerType = null;
    }
    
    /**
     * Constructeur pour une fonction
     */
    EMJSymbolInfo(String id, String returnType, String scope) {
        this.id = id;
        this.dataType = null;
        this.scope = scope;
        this.symbolType = EMJSymbolType.FUNCTION;
        this.isInitialized = true;
        this.parameters = new ArrayList<>();
        this.returnType = returnType;
        this.tupleInnerType = null;
    }
    
    /**
     * Constructeur pour un tuple
     */
    EMJSymbolInfo(String id, String scope, EMJSymbolType symbolType, boolean initialized, String tupleInnerType) {
        this.id = id;
        this.dataType = "TUPLE";
        this.scope = scope;
        this.symbolType = symbolType;
        this.isInitialized = initialized;
        this.parameters = new ArrayList<>();
        this.returnType = null;
        this.tupleInnerType = tupleInnerType;
    }

    // Getters
    public String getId() {
        return id;
    }

    public String getDataType() {
        return dataType;
    }

    public String getScope() {
        return scope;
    }

    public EMJSymbolType getSymbolType() {
        return symbolType;
    }

    public boolean isInitialized() {
        return isInitialized;
    }

    public void setInitialized(boolean initialized) {
        isInitialized = initialized;
    }
    
    public List<EMJSymbolInfo> getParameters() {
        return parameters;
    }
    
    public void addParameter(EMJSymbolInfo parameter) {
        parameters.add(parameter);
    }
    
    public String getReturnType() {
        return returnType;
    }
    
    public void setReturnType(String returnType) {
        this.returnType = returnType;
    }
    
    public String getTupleInnerType() {
        return tupleInnerType;
    }

    /**
     * Vérifie si ce symbole est une fonction
     */
    public boolean isFunction() {
        return symbolType == EMJSymbolType.FUNCTION;
    }

    /**
     * Vérifie si ce symbole est une variable
     */
    public boolean isVariable() {
        return symbolType == EMJSymbolType.VARIABLE;
    }

    /**
     * Vérifie si ce symbole est un paramètre
     */
    public boolean isParameter() {
        return symbolType == EMJSymbolType.PARAMETER;
    }
    
    /**
     * Vérifie si ce symbole est un tuple
     */
    public boolean isTuple() {
        return "TUPLE".equals(dataType);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("EMJSymbolInfo{");
        sb.append("id='").append(id).append("', ");
        sb.append("type=").append(symbolType);
        
        if (isFunction()) {
            sb.append(", returnType='").append(returnType).append("'");
            sb.append(", parameters=[");
            for (int i = 0; i < parameters.size(); i++) {
                if (i > 0) sb.append(", ");
                sb.append(parameters.get(i).getId()).append(":").append(parameters.get(i).getDataType());
            }
            sb.append("]");
        } else {
            sb.append(", dataType='").append(dataType).append("'");
            sb.append(", initialized=").append(isInitialized);
            if (isTuple()) {
                sb.append(", tupleInnerType='").append(tupleInnerType).append("'");
            }
        }
        
        sb.append(", scope='").append(scope).append("'");
        sb.append('}');
        return sb.toString();
    }
}
