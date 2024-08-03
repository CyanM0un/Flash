package pascal.taie.analysis.dataflow.analysis.methodsummary;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.methodsummary.Utils.ContrUtil;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
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

    private Map<String, List<Integer>> tcMap;

    private Map<JMethod, Set<List<Edge>>> tempGCMap;

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
        this.tcMap = new HashMap<>();
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
        ArrayList<Edge> edgeList = getMaxLenEdgeList(sinkEdge, 0);
        if (edgeList == null) return;
        Map<String, List<Integer>> tempTCMap = backPropagate(edgeList, tcList);
        if (tempTCMap.isEmpty()) return;

        List<String> gc = getGCList(edgeList, tempTCMap);
        gc.add(sink.toString());
//        debug(gc);
        int gcSize = gc.size();

        if (!startWithSource(edgeList, gcSize - 1, tempTCMap.size())) {
            if (!updateToSinkGC(gc)) return;
        } else {
            if (gc.size() > 2) {
                List toSinkGC = gc.subList(1, gcSize);
                updateToSinkGC(toSinkGC);
            }
            List<String> simplyGC = simplyGC(gc);
            if (addGC(simplyGC)) {
                logAndWriteGC(simplyGC, tempTCMap);
            }
        }
        updateTCMap(tempTCMap);
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

    private List<String> simplyGC(List<String> gc) {
        List<String> subSigList = new ArrayList<>();
        List<String> simplyGC = new ArrayList<>();
        for (String c : gc) {
            String subSig = getSubSignature(c);
            if (subSigList.contains(subSig)) {
                int from = subSigList.indexOf(subSig);
                int end = subSigList.size();
                Lists.clearList(subSigList, from, end);
                Lists.clearList(simplyGC, from, end);
            }
            subSigList.add(subSig);
            simplyGC.add(c);
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

    private void updateTCMap(Map<String, List<Integer>> tempTCMap) {
        for (String key : tempTCMap.keySet()) {
            if (!tcMap.containsKey(key)) tcMap.put(key, tempTCMap.get(key));
        }
    }

    private boolean startWithSource(List<Edge> edgeList, int gcSize, int tcMapSize) {
        int idx = (gcSize > tcMapSize ? gcSize : tcMapSize) - 1;
        return CSCallGraph.getCaller(edgeList.get(idx)).isSource();
    }

    private void logAndWriteGC(List<String> gc, Map<String, List<Integer>> tempTCMap) {
        for (int i = 0; i < gc.size(); i++) {
            String caller_s = gc.get(i);
            JMethod caller = hierarchy.getMethod(caller_s);
            if (i == gc.size() - 1) {
                logger.info(caller_s);
                pw.println(caller_s);
            } else {
                JMethod callee = hierarchy.getMethod(gc.get(i + 1));
                List<Integer> tc = tempTCMap.containsKey(caller_s) ? tempTCMap.get(caller_s) : tcMap.get(caller_s);
                csCallGraph.edgesInTo(callee).forEach(edge -> {
                    if (CSCallGraph.getCaller(edge).equals(caller)) {
                        String line = caller_s + "-" + edge.getCSIntContr() + "->" + tc;
                        logger.info(line);
                        pw.println(line);
                    }
                });
            }
        }
        logger.info("");
        pw.println("");

        gc.forEach(line -> {
            logger.info(line);
            pw.println(line);
        });
        logger.info("");
        pw.println("");
        pw.flush();
    }

    private ArrayList<Edge> getMaxLenEdgeList(Edge sinkEdge, int sinkLen) {
        int edgeStackSize = edgeStack.size();
        ArrayList<Edge> edgeList = new ArrayList<>();
        edgeList.add(sinkEdge);
        for (int i = 0; i < MAX_LEN - 1 - sinkLen; i ++) {
            Edge lastEdge = edgeList.get(i);
            JMethod caller = CSCallGraph.getCaller(lastEdge);
            if (caller.isSource()) break;
            Edge newEdge = edgeStack.get(edgeStackSize - i - 1);
            if (caller.getName().equals("<clinit>") || !caller.equals(CSCallGraph.getCallee(newEdge))) return null; // 忽略类加载器
            if (i == MAX_LEN - 2 - sinkLen && !CSCallGraph.getCaller(newEdge).isSource()) return edgeList; // 返回片段处理
            edgeList.add(newEdge);
        }
        return edgeList;
    }

    private Map<String, List<Integer>> backPropagate(List<Edge> edgeList, List<Integer> tcList) {
        Map<String, List<Integer>> tempTCMap = new HashMap<>();
        for (Edge edge : edgeList) {
            List<Integer> temp = new ArrayList<>();
            for (int i = 0; i < tcList.size(); i++) {
                Integer value = tcList.get(i);
                Integer newTC = value > ContrUtil.iPOLLUTED ? (Integer) edge.getCSIntContr().get(value + 1) : ContrUtil.iPOLLUTED;
                if (newTC.equals(ContrUtil.iNOT_POLLUTED)) {
                    return tempTCMap;
                } else {
                    temp.add(newTC);
                }
            }
            tcList = temp;
            JMethod sGadget = CSCallGraph.getCaller(edge);
            if (!sGadget.isSource()) {
                tempTCMap.put(sGadget.toString(), tcList);
            }
        }
        return tempTCMap;
    }

    private List<String> getGCList(List<Edge> edgeList, Map<String, List<Integer>> tcMap) {
        ArrayList<String> gc = new ArrayList<>();
        for (int i = edgeList.size() - 1; i >= 0; i--) {
            JMethod m = CSCallGraph.getCaller(edgeList.get(i));
            String key = m.toString();
            if (tcMap.containsKey(key) || m.isSource()) gc.add(key);
        }
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
        if (callee.isSink()) {
            recordGC(callEdge, callee);
        } else if (callee.hasSummary()) {
            linkGC(callEdge, callee);
        } else if (isInStack) {
            List<Edge> edgeList = getMaxLenEdgeList(callEdge, 1); // 先存下来，之后再处理
            if (edgeList == null) return;
            tempGCMap.putIfAbsent(callee, new HashSet<>());
            tempGCMap.get(callee).add(edgeList);
        } else {
            edgeStack.push(callEdge);
        }
        Set<JMethod> copyKeys = new HashSet<>(tempGCMap.keySet());
        for (JMethod key : copyKeys) {
            String keyStr = key.toString();
            if (key.hasSummary() && tcMap.containsKey(keyStr)) {
                Set<List<Edge>> edgeLists = tempGCMap.get(key);
                tempGCMap.remove(key);
                reLinkGC(edgeLists, keyStr);
            }
        }
    }

    private void linkGC(Edge callEdge, JMethod callee) {
        String key = callee.toString();
        if (tcMap.containsKey(key)) {
            List<Integer> tcList = tcMap.get(key);
            Set<List<String>> newToSinkGCs = new HashSet<>();
            for (List<String> toSinkGC : gcGraph.collectPath(key)) {
                int sinkGCLen = toSinkGC.size();
                ArrayList<Edge> edgeList = getMaxLenEdgeList(callEdge, sinkGCLen - 1);
                if (edgeList == null) return;

                doLinkGC(edgeList, tcList, toSinkGC, newToSinkGCs);
            }
            gcGraph.addPaths(newToSinkGCs);
        }
    }

    private void reLinkGC(Set<List<Edge>> edgeLists, String key) {
        List<Integer> tcList = tcMap.get(key);
        edgeLists.forEach(edgeList -> {
            Set<List<String>> newToSinkGCs = new HashSet<>();
            for (List<String> toSinkGC : gcGraph.collectPath(key)) {
                int sinkLen = toSinkGC.size();
                List<Edge> edge = getMaxLenEdgeList(edgeList, MAX_LEN - sinkLen + 1);
                if (edge == null || edge.isEmpty()) continue;
                doLinkGC(edge, tcList, toSinkGC, newToSinkGCs);
            }
            gcGraph.addPaths(newToSinkGCs);
        });
    }

    private List<Edge> getMaxLenEdgeList(List<Edge> edgeList, int len) {
        List<Edge> retList = new ArrayList<>();
        int edgeSize = edgeList.size();
        for (int i = 0; i < len; i ++) {
            if (i >= edgeSize) break;
            Edge edge = edgeList.get(i);
            JMethod caller = CSCallGraph.getCaller(edge);
            if (caller.getName().equals("<clinit>")) return null;
            if (i == len - 1 && !caller.isSource()) return retList;
            if (i > 0) {
                Edge old = retList.get(i - 1);
                if (!CSCallGraph.getCaller(old).equals(CSCallGraph.getCallee(edge))) return null;
            }
            retList.add(edge);
            if (CSCallGraph.getCaller(edge).isSource()) break;
        }
        return retList;
    }

    private void doLinkGC(List<Edge> edgeList, List<Integer> tcList, List<String> toSinkGC, Set<List<String>> newToSinkGCs) {
        List<String> unSafeGC = getUnSafeGCList(edgeList); // 可以用来避免重复操作
        unSafeGC.addAll(toSinkGC);
        if (gcGraph.containsPath(unSafeGC)
                || (unSafeGC.size() > ENTRY_DEPTH && entrySinkPair.contains(simplyGC(unSafeGC)))
                || GCs.contains(simplyGC(unSafeGC))
                || newToSinkGCs.contains(unSafeGC)) return;

        Map<String, List<Integer>> tempTCMap = backPropagate(edgeList, tcList);
        if (tempTCMap.isEmpty()) return;
        List<String> gc = getGCList(edgeList, tempTCMap);
        int checkGCSize = gc.size();
        gc.addAll(toSinkGC);
        int gcSize = gc.size();
        if (!startWithSource(edgeList, checkGCSize, tempTCMap.size())) {
            if (!gc.equals(unSafeGC) && gcGraph.containsPath(gc)) return;
            newToSinkGCs.add(gc);
        } else {
            if (gcSize > 2) {
                List newToSinkGC = gc.subList(1, gcSize);
                newToSinkGCs.add(newToSinkGC);
            }
            List<String> simplyGC = simplyGC(gc);
            if (addGC(simplyGC)) {
                logAndWriteGC(simplyGC, tempTCMap);
            }
        }
        updateTCMap(tempTCMap);
    }


    public void count() {
        logger.info("total GC count: {}", GCs.size());
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
}
