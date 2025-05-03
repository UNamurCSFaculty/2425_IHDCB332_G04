package be.unamur.info.b314.compiler.emj.Result;

import java.util.HashMap;
import java.util.Map;

public class ContextResult extends Result {
    private final Map<String, Object> data;
    private final String templateName;

    private ContextResult(Map<String, Object> data, String templateName, boolean valid) {
        super(valid);
        this.data = data;
        this.templateName = templateName;
    }

    public Map<String, Object> getData() {
        return data;
    }

    public String getTemplateName() {
        return templateName;
    }

    public static ContextResult valid(Map<String, Object> data, String templateName) {
        return new ContextResult(data, templateName, true);
    }

    public static ContextResult invalid() {
        return new ContextResult(new HashMap<>(), "", false);
    }
}