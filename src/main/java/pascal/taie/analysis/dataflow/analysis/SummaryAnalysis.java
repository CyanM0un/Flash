package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.dataflow.analysis.methodsummary.Contr;
import pascal.taie.analysis.dataflow.analysis.methodsummary.ContrFact;
import pascal.taie.analysis.dataflow.analysis.methodsummary.StackManger;
import pascal.taie.analysis.dataflow.analysis.methodsummary.StmtProcessor;
import pascal.taie.analysis.dataflow.analysis.methodsummary.Utils.ContrUtil;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.solver.PointerFlowGraph;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.Stmt;

import java.util.List;

public class SummaryAnalysis extends AbstractDataflowAnalysis<Stmt, ContrFact> {

    private StmtProcessor stmtProcessor;

    private CSManager csManager;

    private Context context;

    private HeapModel heapModel;

    private CSCallGraph csCallGraph;

    public SummaryAnalysis(CFG<Stmt> body, StackManger stackManger, CSManager csManager, HeapModel heapModel, Context context, PointerFlowGraph pointerFlowGraph, CSCallGraph csCallGraph) {
        super(body);
        this.csManager = csManager;
        this.heapModel = heapModel;
        this.context = context;
        this.csCallGraph = csCallGraph;
        this.stmtProcessor = new StmtProcessor(stackManger, csCallGraph, pointerFlowGraph, heapModel, csManager, context);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public ContrFact newBoundaryFact() {
        List<Var> params = cfg.getIR().getParams();
        for (int i = 0; i < params.size(); i++) {
            CSVar param = csManager.getCSVar(context, params.get(i));
            CSObj csContrParam = ContrUtil.getObj(param, ContrUtil.int2String(i), heapModel, context, csManager);
            stmtProcessor.addPFGEdge(csContrParam, param, FlowKind.NEW_CONTR, cfg.getEntry().getLineNumber());
        }
        Var thisVar = cfg.getIR().getThis();
        if (thisVar != null) {
            CSVar csThisVar = csManager.getCSVar(context, thisVar);
            stmtProcessor.setThis(csThisVar);
            CSObj csContrThis = ContrUtil.getObj(csThisVar, ContrUtil.sTHIS, heapModel, context, csManager);
            stmtProcessor.addPFGEdge(csContrThis, csThisVar, FlowKind.NEW_CONTR, cfg.getEntry().getLineNumber());
        }
        // 顺序处理前前先行处理所有的new语句
        cfg.getIR().forEach(stmt -> {
            if (stmt instanceof New) {
                stmtProcessor.process(stmt);
            }
        });
        return newInitialFact();
    }

    @Override
    public ContrFact newInitialFact() {
        return new ContrFact();
    }

    @Override
    public void meetInto(ContrFact fact, ContrFact target) {
        fact.forEach((p, contr) -> target.update(p, merge(contr, target.get(p))));
    }

    private Contr merge(Contr c1, Contr c2) {
        if (c2 == null) {
            return c1;
        } else if (c2.equals(c1)) {
            return c2;
        } else {
            c2.merge(c1);
            return c2;
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, ContrFact in, ContrFact out) {
        ContrFact newIn = in.copy();
        stmtProcessor.setFact(newIn);
        if (!(stmt instanceof New))stmtProcessor.process(stmt);
        return out.copyFrom(stmtProcessor.getFact());
    }

    public void complementSummary() { // 返回值已经处理,这里补充对参数的影响
        stmtProcessor.complementSummary(cfg.getIR().getParams(), cfg.getIR().getThis());
    }

}
