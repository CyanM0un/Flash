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

    private static final Logger logger = LogManager.getLogger(StackManger.class);

    public static final int MAX_LEN = World.get().getOptions().getGC_MAX_LEN();

    private static final String GC_OUT = World.get().getOptions().getGC_OUT();

    private static final int ENTRY_DEPTH = World.get().getOptions().getENTRY_DEPTH();

    private Set<List<String>> GCs;

    private Set<String> entrySinkPair;

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
        this.entrySinkPair = new HashSet<>();
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

    public void pushIf(Stmt ifEnd, JMethod method) {
        ifStack.push(ifEnd);
        ifEndMap.put(ifEnd, method);
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
        List<Edge> edgeList = getMaxLenEdgeList(sinkEdge, edgeStack, 0);
        if (edgeList == null || edgeList.isEmpty()) return;
        Map<String, List<Integer>> tempTCMap = backPropagate(edgeList, tcList);
        if (tempTCMap.isEmpty()) return;

        List<String> gc = getGCList(edgeList, tempTCMap);
        gc.add(sink.toString());

        if (!startWithSource(gc)) {
            if (gc.size() > MAX_LEN) {
                tempTCMap.remove(gc.get(0));
                gc = gc.subList(1, gc.size());
            }
            updateToSinkGC(gc);
        } else {
            if (gc.size() > 2) {
                List toSinkGC = gc.subList(1, gc.size());
                updateToSinkGC(toSinkGC);
            }
            List<String> simplyGC = simplyGC(gc, tempTCMap, edgeList);
            if (addGC(simplyGC)) {
                logAndWriteGC(simplyGC, tempTCMap);
            }
        }
        updateTCMap(tempTCMap, sink.toString());
    }

    private boolean addGC(List<String> gc) {
        if (gc.size() > ENTRY_DEPTH) {
            String pair = getEntrySinkPair(gc);
            if (entrySinkPair.add(pair)) {
                GCs.add(gc);
                return true;
            } else {
                return false;
            }
        } else {
            return GCs.add(gc);
        }
    }

    private String getEntrySinkPair(List<String> gc) {
        StringBuilder pair = new StringBuilder();
        for (int i = 0; i < ENTRY_DEPTH; i++) {
            pair.append(gc.get(i));
            pair.append("#");
        }
        pair.append(gc.get(gc.size() - 1));
        return pair.toString();
    }

    private List<String> simplyGC(List<String> gc, Map<String, List<Integer>> tempTCMap, List<Edge> edgeList) {
        List<String> subSigList = new ArrayList<>();
        List<String> simplyGC = new ArrayList<>();
        for (int i = 0; i < gc.size(); i++) {
            String gadget = gc.get(i);
            String subSig = getSubSignature(gadget);
            if (subSigList.contains(subSig)) {
                int from = subSigList.indexOf(subSig);
                int end = subSigList.size();
                Edge edge = getEdge(edgeList, simplyGC.get(from - 1));
                if (edge.getKind() != CallKind.STATIC) {
                    List<Integer> edgeContr = edge.getCSIntContr();
                    List<Integer> tcList = getTCList(gadget, tempTCMap, edgeList);
                    if (tcList != null) {
                        tcList = getNewTCList(tcList, edgeContr);
                        if (!tcList.contains(ContrUtil.iNOT_POLLUTED)) {
                            Lists.clearList(subSigList, from, end);
                            Lists.clearList(simplyGC, from, end);
                            CSCallSite csCallSite = (CSCallSite) edge.getCallSite();
                            CSMethod csCallee = csCallGraph.getCSMethod(gadget);
                            Edge newEdge = new Edge<>(edge.getKind(), csCallSite, csCallee, edge.getCSContr(), edge.getLineNo());
                            csCallGraph.addEdge(newEdge);
                        }
                    }
                }
            }
            subSigList.add(subSig);
            simplyGC.add(gadget);
        }
        return simplyGC;
    }

    private String getSubSignature(String method) {
        String sub = method.split(":")[1];
        return sub.substring(1, sub.length() - 1);
    }

    private boolean updateToSinkGC(List<String> gc) {
        return gcGraph.addPath(gc);
    }

    private void updateTCMap(Map<String, List<Integer>> tempTCMap, String sink) {
        for (String key : tempTCMap.keySet()) {
            gcGraph.updateTC(key, tempTCMap.get(key), sink);
        }
    }

    private boolean startWithSource(List<String> gc) {
        return hierarchy.getMethod(gc.get(0)).isSource();
    }

    private void logAndWriteGC(List<String> gc, Map<String, List<Integer>> tempTCMap) {
        int gcSize = gc.size();
        String sink = gc.get(gcSize - 1);
        List<Edge> edgeList = getEdgeListOfGC(gc);
        Collections.reverse(edgeList);
        for (int i = 0; i < gcSize - 1; i++) {
            String caller = gc.get(i);
            List<Integer> tc = i == 0 ? null : getTCList(caller, tempTCMap, edgeList);
            StringBuilder line = new StringBuilder(caller);
            Edge edge = edgeList.get(edgeList.size() - i - 1);
            line.append("->").append(edge.getCSIntContr());
            line.append("  ").append(tc);
            String writeLine = line.toString();
            logger.info(writeLine);
            pw.println(writeLine);
        }
        logger.info(sink);
        pw.println(sink);
        logger.info("");
        pw.println("");
        pw.flush();
    }

    private List<Edge> getMaxLenEdgeList(Edge initEdge, Stack<Edge> edges, int sinkLen) { // 这里需要多获取一个，保证simply
        List<Edge> edgeList = new ArrayList<>();
        edgeList.add(initEdge);
        int range = MAX_LEN - sinkLen - 1;
        for (int i = 0; i < range; i ++) {
            Edge lastEdge = edgeList.get(i);
            JMethod caller = CSCallGraph.getCaller(lastEdge);
            if (caller.isSource() || i == edges.size()) break;
            Edge newEdge = edges.get(edges.size() - i - 1);
            if (caller.getName().equals("<clinit>") || !caller.equals(CSCallGraph.getCallee(newEdge))) return null; // 忽略类加载器，因为不可控
            edgeList.add(newEdge);
        }
        return edgeList;
    }

    private Map<String, List<Integer>> backPropagate(List<Edge> edgeList, List<Integer> tcList) {
        Map<String, List<Integer>> tempTCMap = new HashMap<>();
        for (Edge edge : edgeList) {
            tcList = getNewTCList(tcList, edge.getCSIntContr());
            if (tcList.contains(ContrUtil.iNOT_POLLUTED)) return tempTCMap;
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

    private List<String> getGCList(List<Edge> edgeList, Map<String, List<Integer>> tcMap) {
        ArrayList<String> gc = new ArrayList<>();
        int edgeListSize = edgeList.size();
        for (int i = 0; i < edgeListSize; i++) {
            JMethod m = CSCallGraph.getCaller(edgeList.get(i));
            String key = m.toString();
            if (tcMap.containsKey(key)) gc.add(key);
            else break;
        }
        Collections.reverse(gc);
        return gc;
    }

    private List<String> getUnSafeGCList(List<Edge> edgeList) {
        ArrayList<String> gc = new ArrayList<>();
        for (int i = edgeList.size() - 1; i >= 0; i--) {
            String key = CSCallGraph.getCaller(edgeList.get(i)).toString();
            gc.add(key);
        }
        return gc;
    }

    public void pushCallEdge(Edge callEdge, boolean isInStack) {
        JMethod callee = CSCallGraph.getCallee(callEdge);
        String calleeSig = callee.toString();
        if (callee.isSink()) {
            recordGC(callEdge, callee);
        } else if (callee.hasSummary()) {
            if (gcGraph.containsTC(calleeSig)) {
                Set<List<String>> toSinkGCs = gcGraph.collectPath(calleeSig);
                linkGC(callEdge, toSinkGCs, edgeStack);
            }
        } else if (isInStack) {
            List<Edge> edgeList = getMaxLenEdgeList(callEdge, edgeStack, 1); // 先存下来，之后再处理
            if (edgeList != null) {
                Collections.reverse(edgeList);
                Stack<Edge> tempEdgeStack = new Stack<>();
                tempEdgeStack.addAll(edgeList);
                tempGCMap.putIfAbsent(callee, new HashSet<>());
                tempGCMap.get(callee).add(tempEdgeStack);
            }
        } else {
            edgeStack.push(callEdge);
        }
        Set<JMethod> copyKeys = new HashSet<>(tempGCMap.keySet());
        for (JMethod keyMethod : copyKeys) {
            String keySig = keyMethod.toString();
            if (keyMethod.hasSummary() && gcGraph.containsTC(keySig)) {
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
            int sinkGCLen = toSinkGC.size();
            List<Edge> edgeList = getMaxLenEdgeList(callEdge, edges, sinkGCLen - 1);
            if (edgeList == null || edgeList.isEmpty()) return;
            List<Edge> gcEdgeList = getEdgeListOfGC(toSinkGC);
            Collections.reverse(gcEdgeList);
            List<Integer> tcList = getTCList(toSinkGC.get(0), new HashMap<>(), gcEdgeList);
            if (tcList == null) continue;
            gcEdgeList.addAll(edgeList);
            doLinkGC(gcEdgeList, tcList, toSinkGC);
        }
    }

    private void doLinkGC(List<Edge> gcEdgeList, List<Integer> tcList, List<String> toSinkGC) {
        List<Edge> subEdgeList = gcEdgeList.subList(toSinkGC.size() - 1, gcEdgeList.size());
        List<String> unSafeGC = getUnSafeGCList(subEdgeList); // 可以用来避免重复操作
        unSafeGC.addAll(toSinkGC);
        if (gcGraph.containsPath(unSafeGC)
                || (unSafeGC.size() > ENTRY_DEPTH && entrySinkPair.contains(getEntrySinkPair(unSafeGC)))) return;

        Map<String, List<Integer>> tempTCMap = backPropagate(subEdgeList, tcList);
        if (tempTCMap.isEmpty()) return;
        List<String> gc = getGCList(subEdgeList, tempTCMap);
        gc.addAll(toSinkGC);
        if (!startWithSource(gc)) {
            if (gc.size() > MAX_LEN) {
                tempTCMap.remove(gc.get(0));
                gc = gc.subList(1, gc.size());
            }
            updateToSinkGC(gc);
        } else {
            if (gc.size() > 2) {
                updateToSinkGC(gc.subList(1, gc.size()));
            }
            List<String> simplyGC = simplyGC(gc, tempTCMap, gcEdgeList);
            if (addGC(simplyGC)) {
                logAndWriteGC(simplyGC, tempTCMap);
            }
        }
        updateTCMap(tempTCMap, gc.get(gc.size() - 1));
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

    private List<Integer> getTCList(String tcKey, Map<String, List<Integer>> tempTCMap, List<Edge> edgeList) {
        List<Integer> tcList;
        JMethod sink = CSCallGraph.getCallee(edgeList.get(0));
        String sinkSig = sink.toString();
        if (tempTCMap.containsKey(tcKey)) {
            return tempTCMap.get(tcKey);
        } else {
            tcList = gcGraph.getTCList(tcKey, sinkSig);
        }
        if (tcList == null) { // can't figure out why
            List<Integer> sinkTC = Arrays.stream(sink.getSink()).boxed().collect(Collectors.toList());
            Map<String, List<Integer>> restoreTCMap = backPropagate(edgeList, sinkTC);
            tcList = restoreTCMap.getOrDefault(tcKey, null);
            if (tcList != null) updateTCMap(restoreTCMap, sinkSig);
        }
        return tcList;
    }
}
