package pascal.taie.analysis.dataflow.analysis.methodsummary.plugin;

import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

public record TaintTransfer(JMethod method, IndexRef from, IndexRef to, String type) {

    @Override
    public String toString() {
        return method + ": " + from + " -> " + to + "(" + type + ")";
    }

}
