package be.unamur.info.b314.compiler.emj.Result;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Result class for code generation with StringTemplate
 */
public class ContextResult extends Result {
    private final Map<String, Object> attributes;
    private final String templateName;

    private ContextResult(Map<String, Object> attributes, String templateName, boolean valid) {
        super(valid);
        this.attributes = attributes;
        this.templateName = templateName;
    }

    public Map<String, Object> getAttributes() {
        return attributes;
    }

    public String getTemplateName() {
        return templateName;
    }

    // Factory methods
    public static ContextResult valid(Map<String, Object> attributes, String templateName) {
        return new ContextResult(attributes, templateName, true);
    }

    public static ContextResult invalid() {
        return new ContextResult(new HashMap<>(), "", false);
    }

    // Helper method for combining results (e.g., statements in a block)
    public static ContextResult combine(String templateName, List<ContextResult> results, String collectionName) {
        Map<String, Object> combined = new HashMap<>();
        List<Object> collection = new ArrayList<>();

        for (ContextResult result : results) {
            if (result.isValid()) {
                collection.add(result.getAttributes());
            }
        }

        combined.put(collectionName, collection);
        return new ContextResult(combined, templateName, !collection.isEmpty());
    }
}