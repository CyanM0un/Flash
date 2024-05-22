package pascal.taie.analysis.dataflow.analysis.methodsummary.plugin;

import pascal.taie.language.classes.JMethod;

public interface Plugin {

    Plugin DUMMY = new Plugin() {};

    /**
     * Invoked when analysis starts.
     */
    default void onStart() {
    }

    /**
     * Invoked when analysis finishes.
     */
    default void onFinish() {
    }


    default void onNewMethod(JMethod method) {
    }
}
