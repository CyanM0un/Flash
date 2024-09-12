package pascal.taie.analysis.dataflow.analysis.methodsummary;

import pascal.taie.analysis.dataflow.analysis.methodsummary.Utils.ContrUtil;
import pascal.taie.analysis.pta.core.cs.element.Pointer;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

public class PointsTo {

    private Map<Pointer, Contr> relatedMap;

    public PointsTo() {
        relatedMap = new HashMap<>();
    }

    public static PointsTo make() {
        return new PointsTo();
    }

    public boolean add(Pointer p, Contr contr) { // 简单实现了merge策略
        if (contr == null) return false;
        if (relatedMap.isEmpty()) {
            relatedMap.put(p, contr);
            return true;
        } else {
            Contr old = relatedMap.entrySet().iterator().next().getValue();
            if (ContrUtil.needUpdateInMerge(old.getValue(), contr.getValue())) {
                relatedMap.clear();
                relatedMap.put(p, contr);
                return true;
            } else {
                return false;
            }
        }
    }

    public void add(PointsTo pointsTo) {
        for (Pointer p : pointsTo.keySet()) {
            add(p, pointsTo.get(p));
        }
    }

    private Contr get(Pointer p) {
        return relatedMap.get(p);
    }

    private Set<Pointer> keySet() {
        return relatedMap.keySet();
    }

    public boolean isEmpty() {
        return relatedMap.isEmpty();
    }

    public Contr getMergedContr() {
        if (relatedMap.isEmpty()) return null;
        return relatedMap.entrySet().iterator().next().getValue();
    }

    public void setValue(String value) {
        Map.Entry<Pointer, Contr> entry = relatedMap.entrySet().iterator().next();
        Pointer key = entry.getKey();
        Contr newValue = entry.getValue();
        newValue.setValue(value);
        relatedMap.put(key, newValue);
    }
}
