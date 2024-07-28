package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.methodsummary.ContrFact;
import pascal.taie.analysis.dataflow.analysis.methodsummary.StackManger;
import pascal.taie.analysis.dataflow.analysis.methodsummary.plugin.*;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.solver.Solver;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelectorFactory;
import pascal.taie.analysis.pta.core.heap.AllocationSiteBasedModel;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.solver.PointerFlowGraph;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.IR;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;

public class SummaryAnalysisDriver extends MethodAnalysis<DataflowResult<Stmt, ContrFact>> {

    public static final String ID = "method-summary";

    private HeapModel heapModel;

    private Context emptyContext;

    private CSManager csManager;

    private StackManger stackManger;

    private PointerFlowGraph pointerFlowGraph;

    private CSCallGraph csCallGraph;

    private Solver<Stmt, ContrFact> solver;

    private CompositePlugin plugin;

    public SummaryAnalysisDriver(AnalysisConfig config) {
        super(config);
        this.heapModel = new AllocationSiteBasedModel(getOptions());
        this.emptyContext = ContextSelectorFactory.makeCISelector().getEmptyContext();
        this.csManager = new MapBasedCSManager();
        this.stackManger = new StackManger();
        this.pointerFlowGraph = new PointerFlowGraph(csManager);
        this.csCallGraph = new CSCallGraph(csManager);
        this.solver = Solver.getSolver();
        setPlugin(getOptions());
    }

    private void setPlugin(AnalysisOptions options) {
        plugin = new CompositePlugin();
        plugin.addPlugin(
                new AnalysisTimer(),
                new ClassInitializer(),
                new PrioriKnow(options.getString("priori-knowledge"))
        );
        plugin.onStart();
    }

    public void finish() {
        plugin.onFinish();
        stackManger.count();
    }

    @Override
    public DataflowResult<Stmt, ContrFact> analyze(IR ir) {
        JMethod method = ir.getMethod();
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        if (cfg == null) return null; // 跳过abstract方法分析
        plugin.onNewMethod(method);
        stackManger.pushMethod(method);
        csCallGraph.addReachableMethod(csManager.getCSMethod(emptyContext, method));
        SummaryAnalysis analysis = makeAnalysis(cfg, stackManger, csManager, heapModel, emptyContext, pointerFlowGraph, csCallGraph);
        DataflowResult<Stmt, ContrFact> ret = solver.solve(analysis);
        analysis.complementSummary();
        stackManger.popMethod();
        if (!method.hasSummary()) method.setSummary("return", "null");
        return ret;
    }

    public static SummaryAnalysis makeAnalysis(CFG<Stmt> body, StackManger stackManger, CSManager csManager, HeapModel heapModel, Context context, PointerFlowGraph pointerFlowGraph, CSCallGraph csCallGraph) {
        return new SummaryAnalysis(body, stackManger, csManager, heapModel, context, pointerFlowGraph, csCallGraph);
    }

}
