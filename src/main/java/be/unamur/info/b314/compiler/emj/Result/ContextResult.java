package be.unamur.info.b314.compiler.emj.Result;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

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

    public static ContextResult combineRendered(String templateName,
                                                List<ContextResult> results,
                                                String collectionName,
                                                Function<ContextResult, String> renderer) {
        Map<String, Object> combined = new HashMap<>();
        List<String> collection = new ArrayList<>();

        for (ContextResult result : results) {
            if (result.isValid()) {
                collection.add(renderer.apply(result));
            }
        }

        combined.put(collectionName, collection);
        return new ContextResult(combined, templateName, !collection.isEmpty());
    }
}