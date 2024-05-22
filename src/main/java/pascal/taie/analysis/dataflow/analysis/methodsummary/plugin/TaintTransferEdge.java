package pascal.taie.analysis.dataflow.analysis.methodsummary.plugin;

import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.solver.OtherEdge;

public class TaintTransferEdge extends OtherEdge {

    public TaintTransferEdge(Pointer source, Pointer target) {
        super(source, target);
    }
}
