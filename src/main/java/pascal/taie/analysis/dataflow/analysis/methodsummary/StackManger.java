package pascal.taie.analysis.dataflow.analysis.methodsummary;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.methodsummary.Utils.ContrUtil;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.ReferenceType;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Lists;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.*;
import java.util.stream.Collectors;

public class StackManger {

    private CSCallGraph csCallGraph;

    private Stack<JMethod> methodStack;

    private Stack<Edge> edgeStack;

    private Stack<Pointer> queryStack;

    private LinkedList<Stmt> ifStack;

    private Map<Stmt, JMethod> ifEndMap;

    private Map<Stmt, Set<If>> ifMap;

    private static final Logger logger = LogManager.getLogger(StackManger.class);

    public static final int MAX_LEN = World.get().getOptions().getGC_MAX_LEN();

    private static final String GC_OUT = World.get().getOptions().getGC_OUT();

    private Set<List<String>> GCs;

    private PrintWriter pw;

    private Map<JMethod, Set<Stack<Edge>>> tempGCMap;

    private GadgetChainGraph gcGraph;

    private Map<CSVar, Pointer> instanceOfRet;

    private Map<Pointer, Type> instanceOfType;

    private Map<Stmt, Pointer> instanceOfEnd;

    private ClassHierarchy hierarchy;

    public StackManger(CSCallGraph csCallGraph) {
        this.csCallGraph = csCallGraph;
        this.edgeStack = new Stack<>();
        this.methodStack = new Stack<>();
        this.queryStack = new Stack<>();
        this.ifStack = new LinkedList<>();
        this.ifEndMap = new HashMap<>();
        this.ifMap = new HashMap<>();
        this.gcGraph = new GadgetChainGraph();
        try {
            pw = new PrintWriter(new BufferedWriter(new FileWriter(GC_OUT)));
        } catch (Exception e) {
            logger.info(e);
        }
        this.GCs = new HashSet<>();
        this.tempGCMap = new HashMap<>();
        this.instanceOfEnd = new HashMap<>();
        this.instanceOfRet = new HashMap<>();
        this.instanceOfType = new HashMap<>();
        this.hierarchy = World.get().getClassHierarchy();
    }

    public void pushMethod(JMethod method) {
        methodStack.push(method);
    }

    public void popMethod() {
        JMethod m = methodStack.pop();
        if (!edgeStack.isEmpty()) {
            Edge e = edgeStack.peek();
            JMethod callee = ((CSMethod) e.getCallee()).getMethod();
            if (m.equals(callee)) edgeStack.pop();
        }
    }

    public boolean containsMethod(JMethod method) {
        return methodStack.contains(method);
    }

    public JMethod curMethod() {
        return methodStack.peek();
    }

    public void pushQuery(Pointer pointer) {
        queryStack.push(pointer);
    }

    public void popQuery() {
        queryStack.pop();
    }

    public boolean containsQuery(Pointer pointer) {
        return queryStack.contains(pointer);
    }

    public void pushIf(Stmt ifEnd, JMethod method, If ifStart) {
        ifStack.push(ifEnd);
        ifEndMap.put(ifEnd, method);
        ifMap.computeIfAbsent(ifEnd, k -> new HashSet<>()).add(ifStart);
    }

    public boolean isInIf() {
        return !ifStack.isEmpty();
    }

    public boolean isIfEnd(Stmt stmt) {
        return ifStack.contains(stmt);
    }

    public void popIf(Stmt stmt) {
        ifStack.remove(stmt);
        ifEndMap.remove(stmt);
        ifMap.remove(stmt);
    }

    public Set<ConditionExp> getIfConditions(JMethod m) {
        Set<ConditionExp> ret = new HashSet<>();
        Stmt ifEnd = getCurIfEnd();
        if (ifEndMap.containsKey(ifEnd) && ifEndMap.get(ifEnd).equals(m)) {
            ifMap.get(ifEnd).forEach(ifStart -> ret.add(ifStart.getCondition()));
        }
        return ret;
    }

    public Stmt getCurIfEnd() {
        return ifStack.peek();
    }

    public JMethod getCurIfEndMethod() {
        return ifEndMap.getOrDefault(getCurIfEnd(), null);
    }

    public int getIfEnd() {
        return isInIf() ? getCurIfEnd().getLineNumber() : -1;
    }

    public void recordGC(Edge sinkEdge, JMethod sink) {
        List<Integer> tcList = Arrays.stream(sink.getSink()).boxed().collect(Collectors.toList());
        List<Edge> gcEdgeList = backPropagate(tcList, sinkEdge, edgeStack, 0);
        if (gcEdgeList == null || gcEdgeList.isEmpty()) return;

        List<String> gcList = getGCList(gcEdgeList);
        if (gcList == null) return;
        if (!startWithSource(gcEdgeList)) {
            updateToSinkGC(gcList, false);
        } else {
            updateToSinkGC(gcList, true);
            List<Edge> simplyGC = simplyGC(gcList, gcEdgeList);
            if (addGC(simplyGC)) {
                logAndWriteGC(simplyGC);
            }
        }
    }

    private boolean addGC(List<Edge> gcEdgeList) {
        List<String> gc = getGCList(gcEdgeList);
        if (gc == null) return false;
        return GCs.add(gc);
    }

    private List<Edge> simplyGC(List<String> gc, List<Edge> gcEdgeList) {
        List<String> subSigList = new ArrayList<>();
        List<Edge> simplyGC = new ArrayList<>();
        String source = gc.get(0);
        for (int i = 0; i < gc.size() - 1; i++) {
            String gadget = gc.get(i);
            String subSig = getSubSignature(gadget);
            Edge edge = getEdge(gcEdgeList, gadget);
            if (subSigList.contains(subSig)) {
                int from = subSigList.lastIndexOf(subSig);
                int end = subSigList.size();
                Edge fromEdge = simplyGC.get(from - 1);
                if (fromEdge.getKind() != CallKind.STATIC) {
                    List<Integer> tcList = recoveryTCList(gadget, gcEdgeList);
                    if (tcList != null) {
                        List<Edge> sourceEdgeList = new ArrayList<>(simplyGC.subList(0, from));
                        Collections.reverse(sourceEdgeList);
                        Map<String, List<Integer>> tcMap = recoveryTCMap(sourceEdgeList, tcList);
                        if (tcMap.containsKey(source)) {
                            Lists.clearList(subSigList, from, end);
                            Lists.clearList(simplyGC, from - 1, end);
                            CSCallSite csCallSite = (CSCallSite) fromEdge.getCallSite();
                            CSMethod csCallee = csCallGraph.getCSMethod(gadget);
                            Edge replaceEdge = new Edge<>(fromEdge.getKind(), csCallSite, csCallee, fromEdge.getCSContr(), fromEdge.getLineNo());
                            csCallGraph.addEdge(replaceEdge);
                            simplyGC.add(replaceEdge);
                        }
                    }
                }
            }
            subSigList.add(subSig);
            simplyGC.add(edge);
        }
        return simplyGC;
    }

    private String getSubSignature(String method) {
        String sub = method.split(":")[1];
        return sub.substring(1, sub.length() - 1);
    }

    private boolean updateToSinkGC(List<String> gc, boolean startWithSource) {
        if (gc.size() > MAX_LEN || (startWithSource && gc.size() > 2)) {
            gc = gc.subList(1, gc.size());
        }
        return gcGraph.addPath(gc);
    }

    private boolean startWithSource(List<Edge> gc) {
        return CSCallGraph.getCaller(gc.get(gc.size() - 1)).isSource();
    }

    private void logAndWriteGC(List<Edge> gcEdgeList) {
        int gcSize = gcEdgeList.size();
        for (int i = 0; i < gcSize; i++) {
            Edge edge = gcEdgeList.get(i);
            String caller = CSCallGraph.getCaller(edge).toString();
            StringBuilder line = new StringBuilder(caller);
            line.append("->").append(edge.getCSIntContr());
            String writeLine = line.toString();
            logger.info(writeLine);
            pw.println(writeLine);
        }
        String sink = CSCallGraph.getCallee(gcEdgeList.get(gcSize - 1)).toString();
        logger.info(sink);
        pw.println(sink);
        logger.info("");
        pw.println("");
        pw.flush();
    }

    private List<Edge> backPropagate(List<Integer> tcList, Edge initEdge, Stack<Edge> edges, int sinkLen) { // 这里需要多获取一个，保证simply
        List<Edge> edgeList = new ArrayList<>();
        List<Integer> tempNewTC = getNewTCList(tcList, initEdge.getCSIntContr());
        if (!ContrUtil.allControllable(tempNewTC)) return edgeList;
        edgeList.add(initEdge);
        int range = MAX_LEN - sinkLen - 1;
        for (int i = 0; i < range; i ++) {
            Edge lastEdge = edgeList.get(i);
            JMethod caller = CSCallGraph.getCaller(lastEdge);
            if (caller.isSource() || i == edges.size()) break;
            Edge newEdge = edges.get(edges.size() - i - 1);
            if (caller.getName().equals("<clinit>") || !caller.equals(CSCallGraph.getCallee(newEdge))) return null; // 忽略类加载器
            tempNewTC = getNewTCList(tempNewTC, newEdge.getCSIntContr());
            if (!ContrUtil.allControllable(tempNewTC)) break;
            edgeList.add(newEdge);
        }
        return edgeList;
    }

    private List<Edge> backPropagate(Edge initEdge, Stack<Edge> edges, int sinkLen) {
        List<Edge> edgeList = new ArrayList<>();
        edgeList.add(initEdge);
        int range = MAX_LEN - sinkLen - 1;
        for (int i = 0; i < range; i ++) {
            Edge lastEdge = edgeList.get(i);
            JMethod caller = CSCallGraph.getCaller(lastEdge);
            if (caller.isSource() || i == edges.size()) break;
            Edge newEdge = edges.get(edges.size() - i - 1);
            if (caller.getName().equals("<clinit>") || !caller.equals(CSCallGraph.getCallee(newEdge))) return null; // 忽略类加载器
            edgeList.add(newEdge);
        }
        return edgeList;
    }

    private Map<String, List<Integer>> recoveryTCMap(List<Edge> edgeList, List<Integer> tcList) {
        Map<String, List<Integer>> tempTCMap = new HashMap<>();
        for (Edge edge : edgeList) {
            tcList = getNewTCList(tcList, edge.getCSIntContr());
            if (!ContrUtil.allControllable(tcList)) return tempTCMap;
            JMethod sGadget = CSCallGraph.getCaller(edge);
            tempTCMap.put(sGadget.toString(), tcList);
        }
        return tempTCMap;
    }

    private List<Integer> getNewTCList(List<Integer> tcList, List<Integer> csIntContr) {
        List<Integer> tempTC = new ArrayList<>();
        for (int i = 0; i < tcList.size(); i++) {
            Integer tc = tcList.get(i);
            Integer newTC = tc > ContrUtil.iPOLLUTED ? csIntContr.get(tc + 1) : ContrUtil.iPOLLUTED;
            if (!tempTC.contains(newTC)) tempTC.add(newTC);
        }
        return tempTC;
    }

    private List<String> getGCList(List<Edge> edgeList) {
        ArrayList<String> gc = new ArrayList<>();
        List<Edge> copy = new ArrayList<>(edgeList);
        Collections.reverse(copy);
        int edgeListSize = edgeList.size();
        for (int i = 0; i < edgeListSize; i++) {
            Edge edge = copy.get(i);
            if (edge.isFilterInvoke() && i != 0) {
                Edge before = copy.get(i - 1);
                String filter = edge.getFilterInvoke();
                String invokeTarget = ((CSCallSite) before.getCallSite()).getCallSite().getInvokeExp().getMethodRef().getName();
                if (!invokeTarget.equals(filter)) return null;
            }
            JMethod m = CSCallGraph.getCaller(edge);
            String key = m.toString();
            gc.add(key);
        }
        gc.add(CSCallGraph.getCallee(edgeList.get(0)).toString());
        return gc;
    }

    public void pushCallEdge(Edge callEdge, boolean isInStack) {
        JMethod callee = CSCallGraph.getCallee(callEdge);
        String calleeSig = callee.toString();
        if (callee.isSink()) {
            recordGC(callEdge, callee);
        } else if (callee.hasSummary()) {
            if (gcGraph.containsNode(calleeSig)) {
                Set<List<String>> toSinkGCs = gcGraph.collectPath(calleeSig);
                linkGC(callEdge, toSinkGCs, edgeStack);
            }
        } else if (isInStack) {
            List<Edge> edgeList = backPropagate(callEdge, edgeStack, 1); // 先存下来，之后再处理
            if (edgeList != null && !edgeList.isEmpty()) {
                Stack<Edge> edges = list2Stack(edgeList);
                tempGCMap.putIfAbsent(callee, new HashSet<>());
                tempGCMap.get(callee).add(edges);
            }
        } else {
            edgeStack.push(callEdge);
        }
        Set<JMethod> copyKeys = new HashSet<>(tempGCMap.keySet());
        for (JMethod keyMethod : copyKeys) {
            String keySig = keyMethod.toString();
            if (keyMethod.hasSummary() && gcGraph.containsNode(keySig)) {
                Set<Stack<Edge>> edgeLists = tempGCMap.remove(keyMethod);
                Set<List<String>> toSinkGCs = gcGraph.collectPath(keySig);
                edgeLists.forEach(edges -> {
                    Edge edge = edges.pop();
                    linkGC(edge, toSinkGCs, edges);
                });
            }
        }
    }

    private void linkGC(Edge callEdge, Set<List<String>> toSinkGCs, Stack<Edge> edges) {
        for (List<String> toSinkGC : toSinkGCs) {
            List<Edge> gcEdgeList = getEdgeListOfGC(toSinkGC);
            Collections.reverse(gcEdgeList);
            List<Integer> tcList = recoveryTCList(toSinkGC.get(0), gcEdgeList);
            if (tcList == null) continue;

            List<Edge> sourceEdgeList = backPropagate(tcList, callEdge, edges, toSinkGC.size() - 1);
            if (sourceEdgeList == null || sourceEdgeList.isEmpty()) continue;

            gcEdgeList.addAll(sourceEdgeList);
            List<String> gc = getGCList(gcEdgeList);
            if (gc == null) return;
            if (!startWithSource(gcEdgeList)) {
                updateToSinkGC(gc, false);
            } else {
                updateToSinkGC(gc, true);
                List<Edge> simplyGC = simplyGC(gc, gcEdgeList);
                if (addGC(simplyGC)) {
                    logAndWriteGC(simplyGC);
                }
            }
        }
    }

    private Stack<Edge> list2Stack(List<Edge> edgeList) {
        Stack<Edge> stack = new Stack<>();
        stack.addAll(edgeList);
        Collections.reverse(stack);
        return stack;
    }

    public void count() {
        logger.info("total GC count: {}", GCs.size());
        pw.println("total GC count: " + GCs.size());
        pw.flush();
    }

    public void putInstanceOfInfo(CSVar retVar, Pointer pointer, ReferenceType type) {
        instanceOfRet.put(retVar, pointer);
        instanceOfType.put(pointer, type);
    }

    public boolean containsInstanceOfRet(CSVar var) {
        return instanceOfRet.containsKey(var);
    }

    public Pointer removeInstanceOfRet(CSVar var) {
        return instanceOfRet.remove(var);
    }

    public void putInstanceOfEnd(Stmt end, Pointer p) {
        instanceOfEnd.put(end, p);
    }

    public boolean containsInstanceOfEnd(Stmt stmt) {
        return instanceOfEnd.containsKey(stmt);
    }

    public void removeInstanceOfEnd(Stmt stmt) {
        Pointer p = instanceOfEnd.get(stmt);
        instanceOfType.remove(p);
        instanceOfEnd.remove(stmt);
    }

    public boolean containsInstanceOfType(Pointer p) {
        return instanceOfType.containsKey(p);
    }

    public Type getInstanceofType(Pointer p) {
        return instanceOfType.get(p);
    }

    private List<Edge> getEdgeListOfGC(List<String> gc) {
        List<Edge> edgeList = new ArrayList<>();
        for (int i = 0; i < gc.size() - 1; i++) {
            edgeList.add(getEdge(gc.get(i), gc.get(i + 1)));
        }
        return edgeList;
    }

    private Edge getEdge(String caller, String callee) {
        JMethod calleeMethod = hierarchy.getMethod(callee);
        return csCallGraph.edgesInTo(calleeMethod)
                .filter(edge -> CSCallGraph.getCaller(edge).toString().equals(caller))
                .findFirst()
                .get();
    }

    private Edge getEdge(List<Edge> edgeList, String caller) {
        return edgeList.stream()
                .filter(edge -> CSCallGraph.getCaller(edge).toString().equals(caller))
                .findFirst()
                .get();
    }

    private List<Integer> recoveryTCList(String tcKey, List<Edge> edgeList) {
        JMethod sink = CSCallGraph.getCallee(edgeList.get(0));

        List<Edge> subEdgeList = new ArrayList<>();
        for (Edge edge : edgeList) {
            if (CSCallGraph.getCallee(edge).toString().equals(tcKey)) {
                break;
            } else {
                subEdgeList.add(edge);
            }
        }

        List<Integer> sinkTC = Arrays.stream(sink.getSink()).boxed().collect(Collectors.toList());
        Map<String, List<Integer>> tcMap = recoveryTCMap(subEdgeList, sinkTC);
        return tcMap.getOrDefault(tcKey, null);
    }
}
