package pascal.taie.analysis.dataflow.analysis.methodsummary;

import java.util.*;

public class GadgetChainNode {

    private Set<String> nexts;

    public String name;

    public GadgetChainNode(String name) {
        this.name = name;
        this.nexts = new HashSet<>();
    }

    public void addNext(String next) {
        nexts.add(next);
    }

    public boolean isLeaf() {
        return nexts.isEmpty();
    }

    public Set<String> getNexts() {
        return new HashSet<>(nexts);
    }

    @Override
    public String toString() {
        return name;
    }
}
