package pascal.taie.analysis.dataflow.analysis.methodsummary;

import java.util.*;

public class GadgetChainNode {

    private Set<String> nexts;

    private Map<String, List<Integer>> tcAttr;

    public String name;

    public GadgetChainNode(String name) {
        this.name = name;
        this.nexts = new HashSet<>();
        this.tcAttr = new HashMap<>();
    }

    public void addNext(String next) {
        nexts.add(next);
    }

    public boolean containsNext(String next) {
        return nexts.contains(next);
    }

    public boolean isLeaf() {
        return nexts.isEmpty();
    }

    public Set<String> getNexts() {
        return new HashSet<>(nexts);
    }

    public void updateTC(String sink, List<Integer> tc) {
        if (!tcAttr.containsKey(sink)) tcAttr.put(sink, tc);
    }

    public boolean containsTC() {
        return !tcAttr.isEmpty();
    }

    public List<Integer> getTC(String sink) {
        return tcAttr.get(sink);
    }

    @Override
    public String toString() {
        return name;
    }
}
