package be.unamur.info.b314.compiler.emj;

import java.util.ArrayList;
import java.util.List;

/**
 * Classe représentant les informations relatives à un symbole dans la table des symboles
 * Un symbole peut être une variable, une fonction ou un paramètre
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
    private List<String> parameterTypes;   // Liste des types des paramètres
    
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
        this.parameterTypes = new ArrayList<>();
    }

    /**
     * Constructeur pour une variable de type tuple
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
    
    /**
     * Vérifie si ce symbole est une fonction
     * @return true si c'est une fonction, false sinon
     */
    public boolean isFunction() {
        return symbolType == EMJSymbolType.FUNCTION;
    }
    
    /**
     * Vérifie si ce symbole est une variable
     * @return true si c'est une variable, false sinon
     */
    public boolean isVariable() {
        return symbolType == EMJSymbolType.VARIABLE;
    }
    
    /**
     * Vérifie si ce symbole est un paramètre
     * @return true si c'est un paramètre, false sinon
     */
    public boolean isParameter() {
        return symbolType == EMJSymbolType.PARAMETER;
    }
    
    /**
     * Vérifie si ce symbole est de type tuple
     * @return true si c'est un tuple, false sinon
     */
    public boolean isTuple() {
        return "TUPLE".equals(dataType);
    }
    
    /**
     * Obtient l'identifiant du symbole
     * @return Identifiant du symbole
     */
    public String getId() {
        return id;
    }
    
    /**
     * Obtient la portée du symbole
     * @return Portée du symbole
     */
    public String getScope() {
        return scope;
    }
    
    /**
     * Obtient le type du symbole (VARIABLE, FUNCTION, PARAMETER)
     * @return Type du symbole
     */
    public EMJSymbolType getSymbolType() {
        return symbolType;
    }
    
    /**
     * Obtient le type de données du symbole
     * @return Type de données (INT, BOOL, CHAR, STRING, TUPLE, VOID)
     */
    public String getDataType() {
        return dataType;
    }
    
    /**
     * Vérifie si le symbole est initialisé
     * @return true si initialisé, false sinon
     */
    public boolean isInitialized() {
        return isInitialized;
    }
    
    /**
     * Définit l'état d'initialisation du symbole
     * @param initialized Nouvel état d'initialisation
     */
    public void setInitialized(boolean initialized) {
        this.isInitialized = initialized;
    }
    
    /**
     * Obtient le type des éléments du tuple
     * @return Type des éléments du tuple ou null si ce n'est pas un tuple
     */
    public String getTupleInnerType() {
        return tupleInnerType;
    }
    
    /**
     * Obtient le type de retour de la fonction
     * @return Type de retour ou null si ce n'est pas une fonction
     */
    public String getReturnType() {
        return returnType;
    }
    
    /**
     * Définit le type de retour de la fonction
     * @param returnType Nouveau type de retour
     */
    public void setReturnType(String returnType) {
        this.returnType = returnType;
    }
    
    /**
     * Obtient la liste des paramètres de la fonction
     * @return Liste des paramètres ou liste vide si ce n'est pas une fonction
     */
    public List<EMJSymbolInfo> getParameters() {
        return parameters;
    }
    
    /**
     * Ajoute un paramètre à la fonction
     * @param parameter Information sur le paramètre à ajouter
     */
    public void addParameter(EMJSymbolInfo parameter) {
        parameters.add(parameter);
    }
    
    /**
     * Obtient la liste des types des paramètres de la fonction
     * @return Liste des types des paramètres ou liste vide si ce n'est pas une fonction
     */
    public List<String> getParameterTypes() {
        return parameterTypes;
    }
    
    /**
     * Définit la liste des types des paramètres de la fonction
     * @param parameterTypes Liste des types des paramètres
     */
    public void setParameterTypes(List<String> parameterTypes) {
        this.parameterTypes = new ArrayList<>(parameterTypes);
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
            
            // Ajouter les types de paramètres si disponibles
            if (parameterTypes != null && !parameterTypes.isEmpty()) {
                sb.append(", parameterTypes=[");
                for (int i = 0; i < parameterTypes.size(); i++) {
                    if (i > 0) sb.append(", ");
                    sb.append(parameterTypes.get(i));
                }
                sb.append("]");
            }
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
