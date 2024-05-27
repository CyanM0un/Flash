package pascal.taie.analysis.dataflow.analysis.methodsummary;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.AbstractWorldBuilder;
import pascal.taie.World;
import pascal.taie.analysis.AnalysisManager;
import pascal.taie.analysis.dataflow.analysis.ContrAlloc;
import pascal.taie.analysis.dataflow.analysis.methodsummary.Utils.ContrUtil;
import pascal.taie.analysis.dataflow.analysis.methodsummary.plugin.TaintTransfer;
import pascal.taie.analysis.dataflow.analysis.methodsummary.plugin.TaintTransferEdge;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Descriptor;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.MockObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.core.solver.*;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.*;
import pascal.taie.util.InvokeUtils;
import pascal.taie.util.Strings;
import pascal.taie.util.collection.Sets;

import java.util.*;
import java.util.stream.Collectors;

public class StmtProcessor {

    private ContrFact drivenMap; // 需求

    private Visitor visitor;

    private CSCallGraph csCallGraph;

    private PointerFlowGraph pointerFlowGraph;

    private HeapModel heapModel;

    private CSManager csManager;

    private StackManger stackManger;

    private Context context; // empty context

    private TypeSystem typeSystem;

    private int lineNumber;

    private CSVar thisVar;

    private JMethod curMethod;

    private static final Logger logger = LogManager.getLogger(StmtProcessor.class);

    public StmtProcessor(StackManger stackManger, CSCallGraph callGraph, PointerFlowGraph pointerFlowGraph, HeapModel heapModel, CSManager csManager, Context context) {
        this.drivenMap = new ContrFact();
        this.visitor = new Visitor();
        this.stackManger = stackManger;
        this.csCallGraph = callGraph;
        this.pointerFlowGraph = pointerFlowGraph;
        this.heapModel = heapModel;
        this.csManager = csManager;
        this.context = context;
        this.typeSystem = World.get().getTypeSystem();
        this.curMethod = stackManger.curMethod();
        this.lineNumber = -1;
    }

    public void setThis(CSVar thisVar) {
        this.thisVar = thisVar;
    }

    public void setFact(ContrFact fact) {
        this.drivenMap = fact;
    }

    public ContrFact getFact() {
        return this.drivenMap;
    }

    private Contr getOrAddContr(Pointer p) {
        if (!drivenMap.contains(p)) {
            Contr ret = getContr(p);
            if (ret == null) ret = Contr.newInstance(p);
            updateContr(p, ret);
            return ret;
        } else {
            return drivenMap.get(p);
        }
    }

    private void updateContr(Pointer k, Contr v) {
        if (k!= null && v != null && curMethod.equals(getPointerMethod(k))) drivenMap.update(k, v);
    }

    public void addPFGEdge(CSObj from, Pointer to, FlowKind kind, int lineNumber) {
        if (from != null && to != null) {
            addPFGEdge(new PointerFlowEdge(kind, from, to), Identity.get(), lineNumber);
        }
    }

    public void addPFGEdge(Pointer from, Pointer to, FlowKind kind, int lineNumber) {
        if (from != null && to != null) {
            addPFGEdge(new PointerFlowEdge(kind, from, to), Identity.get(), lineNumber);
        }
    }

    public void addPFGEdge(PointerFlowEdge edge, Transfer transfer, int lineNumber) {
        edge.addTransfer(transfer);
        edge.setLineNumber(lineNumber);
        pointerFlowGraph.addEdge(edge);
        varsToReFind(edge.target(), new HashSet<>());
    }

    private void addWL(JMethod method) {
        if (!isIgnored(method)) AnalysisManager.addWL(method);
    }

    private void varsToReFind(Pointer p, HashSet<Pointer> visited) { // drivenMap会缓存结果，如果缓存的变量新增加了指向边，则需要重新查询
        if (visited.add(p)) {
            if (drivenMap.contains(p)) {
                drivenMap.remove(p);
            }
            for (PointerFlowEdge outEdge : p.getOutEdges()) {
                varsToReFind(outEdge.target(), visited);
            }
        }
    }

    public void process(Stmt stmt) {
        this.lineNumber = stmt.getLineNumber();
        stmt.accept(visitor);
        if (stackManger.isInIf() && stackManger.isIfEnd(stmt)) stackManger.popIf(stmt);
    }

    private class Visitor implements StmtVisitor<Void> {

        public Visitor() {
        }

        @Override
        public Void visit(New stmt) {
            NewExp rvalue = stmt.getRValue();
            Obj obj = heapModel.getObj(stmt);
            CSObj from = csManager.getCSObj(context, obj);
            CSVar to = csManager.getCSVar(context, stmt.getLValue());
            addPFGEdge(from, to, FlowKind.NEW, lineNumber);
            if (rvalue instanceof NewMultiArray) {
//                logger.info("[TODO] handle NewMultiArray"); // TODO
            }
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            Var rvalue = stmt.getRValue();
            if (!isIgnored(rvalue.getType())) {
                CSVar from = csManager.getCSVar(context, rvalue);
                CSVar to = csManager.getCSVar(context, stmt.getLValue());
                addPFGEdge(from, to, FlowKind.LOCAL_ASSIGN, lineNumber);
            }
            return null;
        }

        @Override
        public Void visit(Cast stmt) {
            CastExp cast = stmt.getRValue();
            if (!isIgnored(cast.getCastType())) {
                CSVar from = csManager.getCSVar(context, cast.getValue());
                CSVar to = csManager.getCSVar(context, stmt.getLValue());
                addPFGEdge(new PointerFlowEdge(FlowKind.CAST, from, to), new SpecialType(cast.getCastType()), lineNumber);
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            Var lValue = stmt.getLValue();
            if (!isIgnored(lValue.getType())) {
                JField field = stmt.getFieldRef().resolve();
                if (field == null) {
                    logger.info("[ERR] can not resolve {}", stmt);
                    return null;
                }
                CSVar to = csManager.getCSVar(context, stmt.getLValue());
                if (stmt.isStatic()) {
                    StaticField sfield = csManager.getStaticField(field);
                    addPFGEdge(sfield, to, FlowKind.STATIC_LOAD, lineNumber);
                } else {
                    CSVar base = csManager.getCSVar(context, ((InstanceFieldAccess) stmt.getFieldAccess()).getBase());
                    InstanceField iField = csManager.getInstanceField(base, field);
                    addPFGEdge(iField, to, FlowKind.INSTANCE_LOAD, lineNumber);
                }
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            Var rValue = stmt.getRValue();
            if (!isIgnored(rValue.getType())) {
                JField field = stmt.getFieldRef().resolve();
                if (field == null) {
                    logger.info("[ERR] can not resolve {}", stmt);
                    return null;
                }
                CSVar from = csManager.getCSVar(context, rValue);
                if (stmt.isStatic()) {
                    StaticField sfield = csManager.getStaticField(field);
                    addPFGEdge(from, sfield, FlowKind.STATIC_STORE, lineNumber);
                } else {
                    CSVar base = csManager.getCSVar(context, ((InstanceFieldAccess) stmt.getFieldAccess()).getBase());
                    InstanceField iField = csManager.getInstanceField(base, field);
                    PointerFlowEdge edge = new PointerFlowEdge(FlowKind.INSTANCE_STORE, from, iField);
                    addPFGEdge(edge, Identity.get(), lineNumber);
                    int ifEnd = stackManger.getIfEnd();
                    if (ifEnd != -1) pointerFlowGraph.addIfRange(edge, ifEnd);
                }
            }
            return null;
        }

        @Override
        public Void visit(LoadArray stmt) {
            Var lValue = stmt.getLValue();
            if (!isIgnored(lValue.getType())) {
                CSVar to = csManager.getCSVar(context, lValue);
                CSVar base = csManager.getCSVar(context, stmt.getArrayAccess().getBase());
                ArrayIndex varArray = csManager.getArrayIndex(base);
                addPFGEdge(varArray, to, FlowKind.INSTANCE_LOAD, lineNumber);
            }
            return null;
        }

        @Override
        public Void visit(StoreArray stmt) {
            Var rValue = stmt.getRValue();
            if (!isIgnored(rValue.getType())) {
                CSVar from = csManager.getCSVar(context, rValue);
                CSVar base = csManager.getCSVar(context, stmt.getArrayAccess().getBase());
                ArrayIndex varArray = csManager.getArrayIndex(base);
                addPFGEdge(from, varArray, FlowKind.INSTANCE_STORE, lineNumber);
                if (getContr(base) != null) {
                    Pointer to = drivenMap.get(base).getOrigin();
                    addPFGEdge(from, to, FlowKind.ELEMENT_STORE, lineNumber);
                }
            }
            return null;
        }

        @Override
        public Void visit(If stmt) {
            CSVar ifVar = csManager.getCSVar(context, stmt.getCondition().getOperand1()); // 一般都是左值，当然也可以都检测一下
            Contr ifContr = getContr(ifVar);
            if (ContrUtil.isControllable(ifContr)) {
                stackManger.pushIf(stmt.getTarget());
            }
            return null;
        }

        @Override
        public Void visit(Return stmt) {
            Var ret = stmt.getValue();
            if (ret == null || isIgnored(ret.getType())) {
                String oldV = curMethod.getSummary("return");
                if (oldV == null) curMethod.setSummary("return", "null");
            } else {
                String oldV = curMethod.getSummary("return");
                CSVar retVar = csManager.getCSVar(context, ret);
                String newV;
                if (!drivenMap.contains(retVar)) {
                    newV = getContrValue(retVar);
                } else {
                    newV = drivenMap.get(retVar).getValue();
                }
                newV = newV + "+" + (drivenMap.contains(retVar) ? drivenMap.get(retVar).getType() : "null");
                if (oldV == null || ContrUtil.needUpdateInMerge(oldV, newV)) {
                    curMethod.setSummary("return", newV);
                }
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            InvokeExp invokeExp = stmt.getInvokeExp();
            if (stmt.isDynamic()) return null;
            JMethod ref = invokeExp.getMethodRef().resolve();
            if (isIgnored(ref)) return null;
            if (ref.isTransfer()) {
                processTransfer(ref.getTransfer(), stmt);
                return null;
            }
            CSVar base = null;
            List<CSVar> callSiteVars = invokeExp.getArgs().stream()
                    .map(arg -> csManager.getCSVar(context, arg))
                    .collect(Collectors.toList());
            List<String> csContr;
            Set<JMethod> callees = new HashSet<>();
            if (invokeExp instanceof InvokeInstanceExp instanceExp) {
                base = csManager.getCSVar(context, instanceExp.getBase());
            }
            callSiteVars.add(0, base);
            csContr = getCallSiteContr(callSiteVars);
            if (isIgnoredCallSite(csContr, ref)) return null;
            processReceiver(ref, base, csContr);
            if (ref.isSink()) {
                checkReceiverType(ref, base, csContr);
                csCallGraph.addEdge(getCallEdge(stmt, ref, csContr));
                if (ref.hasImitatedBehavior()) processBehavior(ref, stmt, callSiteVars, csContr);
                return null;
            }
            callees.addAll(getCallees(stmt, base, csContr));
            for (JMethod callee : callees) {
                if (!isIgnored(callee)) {
                    csCallGraph.addEdge(getCallEdge(stmt, callee, csContr));
                    if (callee.hasImitatedBehavior()) {
                        processBehavior(callee, stmt, callSiteVars, csContr);
                        continue;
                    }
                    if (!(callee.hasSummary()
                            || callee.isSink()
                            || stackManger.containsMethod(callee)
                            || callee.isNative())) {
                        AnalysisManager.runMethodAnalysis(callee);
                    }
                }
            }
            // 处理返回值以及对参数的影响
            Var ret = stmt.getResult();
            CSVar csRet = null;
            Contr retContr = null;
            if (ret != null && !isIgnored(ret.getType())) {
                csRet = csManager.getCSVar(context, ret);
                retContr = getOrAddContr(csRet);
            }
            for (JMethod callee : callees) {
                if (isIgnored(callee)) continue;
                Map<String, String> summary = callee.getSummaryMap();
                if (stackManger.containsMethod(callee) && summary.isEmpty() && retContr != null) retContr.setValue(ContrUtil.sPOLLUTED); // 处理递归导致的忽略问题，直接设为可控
                for (String sKey : summary.keySet()) {
                    String sValue = summary.get(sKey);
                    if (sKey.equals("return")) { // return
                        if (retContr == null || !ContrUtil.needUpdateInMerge(retContr.getValue(), sValue)) continue;
                        String retValue = sValue.substring(0, sValue.lastIndexOf("+"));
                        String retType = sValue.substring(sValue.lastIndexOf("+") + 1);
                        if (!retType.equals("null")) retContr.setType(typeSystem.getType(retType));
                        if (ContrUtil.isCallSite(retValue)) { // 返回值来源于参数
                            Contr fromContr = getCallSiteCorrespondContr(retValue, callSiteVars);
                            retContr.updateValue(fromContr.getValue());
                            if (fromContr.getOrigin() instanceof ArrayIndex a) { // 忘了哪个例子了
                                addPFGEdge(a.getArrayVar(), retContr.getOrigin(), FlowKind.SUMMARY_ASSIGN, lineNumber);
                            }
                        } else {
                            retContr.setValue(retValue);
                        }
                        updateContr(csRet, retContr);
                    } else if (ContrUtil.isCallSite(sKey)) { // 参数
                        Contr toContr = getCallSiteCorrespondContr(sKey, callSiteVars);
                        if (ContrUtil.isCallSite(sValue)) {
                            Contr fromContr = getCallSiteCorrespondContr(sValue, callSiteVars);
                            toContr.updateValue(fromContr.getValue());
                            polluteBase(toContr);
                            if (!Objects.equals(getPointerMethod(toContr.getOrigin()), curMethod)) curMethod.setSummary(toContr.getName(), fromContr.getValue());
                            else addPFGEdge(fromContr.getOrigin(), toContr.getOrigin(), FlowKind.SUMMARY_ASSIGN, lineNumber);
                        } else if (sValue.equals(ContrUtil.sPOLLUTED)) {
                            toContr.setValue(sValue);
                            Pointer origin = toContr.getOrigin();
                            if (origin != null) {
                                CSObj csContrObj = ContrUtil.getObj(origin, ContrUtil.sPOLLUTED, heapModel, context, csManager);
                                addPFGEdge(csContrObj, toContr.getOrigin(), FlowKind.NEW_CONTR, lineNumber);
                            }
                        } else {
                            toContr.setValue(sValue);
                            if (ContrUtil.isCallSite(toContr.getName())) curMethod.setSummary(toContr.getName(), sValue);
                        }
                        updateContr(toContr.getOrigin(), toContr);
                    }
                }
            }
            return null;
        }
    }

    private boolean isIgnored(Type type) {
        return type instanceof PrimitiveType || type instanceof NullType;
    }

    private boolean isIgnored(JMethod method) {
        return method == null ||
                method.isIgnored() ||
                method.getDeclaringClass().getName().equals("java.lang.String") && isIgnored(method.getReturnType());
    }

    private boolean isIgnoredCallSite(List<String> csContr, JMethod ref) {
        if (!ref.isConstructor() && ref.getParamTypes().stream().anyMatch(p -> p.getName().equals("java.lang.String"))) return false; // 字符串操作？
        else return csContr.stream().allMatch(s -> !ContrUtil.isControllable(s));
    }

    private boolean isThis(CSVar var) {
        return var.getVar().getName().equals("%this");
    }

    private JMethod getPointerMethod(Pointer p) {
        if (p instanceof CSVar var) return var.getVar().getMethod();
        else if (p instanceof InstanceField iField) return iField.getBaseVar().getVar().getMethod();
        else if (p instanceof ArrayAccess array) return array.getBase().getMethod();
        else return null;
    }

    private List<String> getCallSiteContr(List<CSVar> callSiteVars) {
        List<String> list = new ArrayList<>();
        callSiteVars.forEach(var -> list.add(getContrValue(var)));
        return list;
    }

    private String getContrValue(Pointer p) {
        Contr contr = getContr(p);
        return contr != null ? contr.getValue() : ContrUtil.sNOT_POLLUTED;
    }

    private Contr getContr(Pointer p) {
        if (p != null && !isIgnored(p.getType())) {
            if (drivenMap.contains(p)) {
                return drivenMap.get(p);
            } else if (p instanceof CSVar var // 处理常量字符串
                    && var.getVar().isConst()
                    && var.getVar().getConstValue() instanceof StringLiteral s) {
                Contr cs = Contr.newInstance(p);
                cs.setConstString(s.getString());
                drivenMap.update(p, cs);
                return cs;
            } else {
                Contr query = findPointsTo(p).getMergedContr();
                updateContr(p, query);
                return query;
            }
        }
        return null;
    }

    private Type getContrType(Contr contr) {
        if (contr.getType() instanceof ArrayType at) {
            if (contr.getArrayElements().size() != 0) {
                Type max = null;
                for (Contr e : contr.getArrayElements()) {
                    if (max == null || typeSystem.isSubtype(max, e.getType())) max = e.getType();
                }
                return max;
            } else {
                return at.elementType();
            }
        } else {
            return contr.getType();
        }
    }

    private Edge getCallEdge(Invoke callSite, JMethod callee, List<String> csContr) {
        CSCallSite csCallSite = csManager.getCSCallSite(context, callSite);
        CSMethod csCallee = csManager.getCSMethod(context, callee);
        return new Edge<>(CallGraphs.getCallKind(callSite), csCallSite, csCallee, csContr, lineNumber);
    }

    private Set<JMethod> getCallees(Invoke stmt, CSVar base, List<String> csContr) {
        Set<JMethod> ret = new HashSet<>();
        if (base == null) {
            ret.add(CallGraphs.resolveCallee(null, stmt));
        } else if (drivenMap.contains(base)) {
            Contr baseFact = drivenMap.get(base);
            if (!ContrUtil.isControllable(csContr.get(0)) || baseFact.isNew()) {
                ret.add(CallGraphs.resolveCallee(baseFact.getType(), stmt));
            } else {
                Set<JMethod> chaTargets = CallGraphs.resolveCalleesOf(stmt);
                if (chaTargets.size() <= 1) { // 不做过滤
                    ret.addAll(chaTargets);
                } else {
                    ret.addAll(filterCHA(chaTargets, baseFact.getType()));
                    if (stmt.isInterface()) processDynamicProxy(stmt, csContr); // 粗略认为上面的方法base无法接到invoke
                }
            }
        } else {
            ret.addAll(CallGraphs.resolveCalleesOf(stmt));
        }
        return ret;
    }

    private Contr getCallSiteCorrespondContr(String value, List<CSVar> callSiteVars) {
        Pointer origin;
        String contrValue;
        boolean repalce = false;
        if (value.contains(ContrUtil.sTHIS)) {
            CSVar base = callSiteVars.get(0);
            if (base != null) {
                String baseValue = getContrValue(base);
                if (value.contains("-")) {
                    String fieldName = Strings.extractFieldName(value);
                    JField field = base.getVar().getClassField(fieldName);
                    if (field == null) {
                        origin = null;
                        contrValue = ContrUtil.sNOT_POLLUTED;
                    } else {
                        origin = csManager.getInstanceField(base, field);
                        contrValue = ContrUtil.isControllable(baseValue) ? baseValue + "-" + fieldName : baseValue;
                    }
                } else {
                    origin = base;
                    contrValue = baseValue;
                }
            } else { // 静态方法调用
                origin = null;
                contrValue = ContrUtil.sNOT_POLLUTED;
            }
        } else if (value.contains(ContrUtil.sPOLLUTED)) {
            origin = null;
            contrValue = ContrUtil.sPOLLUTED;
        } else {
            int paramIdx = ContrUtil.string2Int(value) + 1;
            origin = paramIdx >= callSiteVars.size() ? null : callSiteVars.get(paramIdx);
            if (origin == null || isIgnored(origin.getType())) {
                contrValue = "null";
            } else if (drivenMap.contains(origin)) {
                repalce = true;
                contrValue = value.replace("param-" + paramIdx, drivenMap.get(origin).getValue());
            } else {
                contrValue = "null";
            }
        }
        Contr ret;
        if (drivenMap.contains(origin)) {
            ret = drivenMap.get(origin);
            if (repalce) {
                ret.setValue(contrValue);
                drivenMap.remove(origin);
            }
        } else {
            ret = Contr.newInstance(origin);
            if (!ret.isTransient()) ret.setValue(contrValue);
        }
        return ret;
    }

    private PointsTo findPointsTo(Pointer pointer) {
        PointsTo pt = PointsTo.make();
        if (stackManger.containsQuery(pointer)) return pt; // 防止递归
        stackManger.pushQuery(pointer);

        LinkedList<Pointer> workList = new LinkedList<>();
        workList.add(pointer);
        Set<Pointer> marked = Sets.newSet();

        while (!workList.isEmpty()) {
            Pointer p = workList.poll();
            if (drivenMap.contains(p)) {
                pt.add(p, drivenMap.get(p));
                continue;
            }
            for (PointerFlowEdge pfe : p.getInEdges()) {
                switch (pfe.kind()) {
                    case NEW, NEW_CONTR -> {
                        Contr newContr = Contr.newInstance(p);
                        Obj obj = pfe.sourceObj().getObject();
                        newContr.setType(obj.getType());
                        if (obj instanceof MockObj mockObj && mockObj.getDescriptor().string().equals("Controllable")) {
                            newContr.setValue(((ContrAlloc) mockObj.getAllocation()).contr());
                        } else {
                            String newType = "new " + obj.getType();
                            newContr.setValue(newType);
                            newContr.setNew();
                        }
                        pt.add(p, newContr);
                    }
                    case LOCAL_ASSIGN, SUMMARY_ASSIGN -> propagate(pfe.source(), marked, workList);
                    case CAST -> {
                        Contr from = findPointsTo(pfe.source()).getMergedContr();
                        if (from != null && ContrUtil.isControllable(from)) {
                            pfe.getTransfers().forEach(transfer -> { // 转换类型
                                if (transfer instanceof SpecialType st) {
                                    Contr contr = Contr.newInstance(p);
                                    contr.setType(st.getType());
                                    contr.setValue(from.getValue());
                                    pt.add(p, contr);
                                }
                            });
                        }
                    }
                    case STATIC_LOAD, STATIC_STORE -> pt.add(findPointsTo(pfe.source()));
                    case INSTANCE_LOAD -> {
                        CSVar base = null;
                        Set<PointerFlowEdge> matchEdges = null;
                        String fieldName = null;
                        Pointer source = pfe.source();
                        Contr contr = Contr.newInstance(source);
                        if (source instanceof InstanceField iField) {
                            base = iField.getBaseVar();
                            fieldName = iField.getField().getName();
                            matchEdges = pointerFlowGraph.getMatchEdges(iField.getField());
                        } else if (source instanceof ArrayIndex arrayIndex) {
                            base = arrayIndex.getArrayVar();
                            fieldName = "arr";
                            matchEdges = pointerFlowGraph.getMatchEdges(base.getVar().getMethod().getDeclaringClass(), base.getType());
                            contr.setType(p.getType()); // element type
                        }
                        if (!processAlias(source, matchEdges, pt, pfe.getLineNumber())) {
                            Contr baseContr = getContr(base);
                            if (ContrUtil.isControllable(baseContr) && !base.isTransient()) {
                                if (fieldName.equals("this$0")) contr.updateValue(baseContr.getValue()); // Class.this的一种访问形式
                                else contr.updateValue(baseContr.getValue() + "-" +fieldName);
                            }
                            pt.add(base, contr);
                        }
                    }
                    case ELEMENT_STORE -> {
                        Contr arrContr = getOrAddContr(p);
                        arrContr.addArrElement(getContr(pfe.source()));
                        updateContr(p, arrContr);
                        pt.add(p, arrContr);
                    }
                    case OTHER -> {
                        if (pfe instanceof TaintTransferEdge tte) {
                            tte.getTransfers().forEach(t -> {
                                Contr from = getContr(pfe.source());
                                if (ContrUtil.isControllable(from)) {
                                    Type type = t instanceof SpecialType st ? st.getType() : tte.target().getType();
                                    Contr contr = from.copy();
                                    contr.setType(type);
                                    pt.add(p, contr);
                                }
                            });
                        }
                    }
                }
            }
        }
        stackManger.popQuery();
        return pt;
    }

    private void propagate(Pointer p, Set<Pointer> marked, LinkedList<Pointer> workList) {
        if (marked.add(p)) {
            workList.addFirst(p);
        }
    }

    private boolean processAlias(Pointer source, Set<PointerFlowEdge> matchEdges, PointsTo pt, int lineNumber) {
        for (PointerFlowEdge matchEdge : matchEdges) { // TODO field sensitive
            Pointer matchSource = matchEdge.source();
            Pointer matchTarget = matchEdge.target();
            if (same(source, matchTarget)) {
                int ifEnd = pointerFlowGraph.getIfRange(matchEdge);
                if (ifEnd != -1 && lineNumber >= ifEnd) continue;
                pt.add(source, findPointsTo(matchSource).getMergedContr());
                if (!Objects.equals(getPointerMethod(source), getPointerMethod(matchTarget)) // 如果来源变量不属于当前方法，则参数来源可能不一致
                        && !pt.isEmpty()
                        && ContrUtil.isControllableParam(pt.getMergedContr())) {
                    pt.setValue(ContrUtil.sPOLLUTED);
                }
            }
        }
        return !pt.isEmpty();
    }

    private void processTransfer(Set<TaintTransfer> transfers, Invoke callSite) {
        transfers.forEach(transfer -> {
            Var toVar = InvokeUtils.getVar(callSite, transfer.to().index());
            if (toVar == null) {
                return;
            }
            Var fromVar = InvokeUtils.getVar(callSite, transfer.from().index());
            CSVar to = csManager.getCSVar(context, toVar);
            CSVar from = csManager.getCSVar(context, fromVar);
            Contr fromContr = getContr(from);
            if (ContrUtil.isControllable(fromContr)) {
                addPFGEdge(new TaintTransferEdge(from, to), Identity.get(), lineNumber);
            }
        });
    }

    private void processReceiver(JMethod ref, CSVar base, List<String> csContr) { // 处理receiver可控性传递
        if (ref.isConstructor()) {
            for (int i = 1; i < csContr.size(); i++) {
                if (ContrUtil.isControllable(csContr.get(i))) {
                    drivenMap.get(base).setValue(ContrUtil.sPOLLUTED);
                    break;
                }
            }
        } else if (ref.hasImitatedBehavior()) {
            Map behavior = ref.getImitatedBehavior();
            if (behavior.containsKey("polluteRec")) {
                List<String> copy = new ArrayList<>();
                copy.addAll(csContr);
                copy.remove(0);
                if (copy.stream().allMatch(i -> ContrUtil.isControllable(i))
                        && drivenMap.contains(base)) {
                    drivenMap.get(base).setValue(ContrUtil.sPOLLUTED);
                }
            }
        }
    }

    private void processBehavior(JMethod method, Invoke stmt, List<CSVar> callSiteVars, List<String> csContr) {
        Map<String, String> imitatedBehavior = method.getImitatedBehavior();
        String behavior = imitatedBehavior.get("jump");
        switch (behavior) {
            case "constructor" -> { // TODO 做一个类型的过滤以及数组参数的模拟
                int idx = InvokeUtils.toInt(imitatedBehavior.get("fromIdx")) + 1;
                Contr fromContr = getContr(callSiteVars.get(idx));
                Set<JMethod> callees = World.get().filterMethods("<init>", fromContr.getOrigin().getType());
                for (JMethod init : callees) {
                    List<String> edgeContr = new ArrayList<>();
                    edgeContr.add(csContr.get(0));
                    int pSize = init.getIR().getParams().size(); // 适应性PP
                    List<String> copied = Collections.nCopies(pSize, csContr.get(1));
                    edgeContr.addAll(copied);
                    csCallGraph.addEdge(getCallEdge(stmt, init, edgeContr));
                    addWL(init); // 并没有继续递归分析，防止栈溢出
                }
            }
            case "inference" -> {
                int idx = InvokeUtils.toInt(imitatedBehavior.get("fromIdx")) + 1;
                int ridx = InvokeUtils.toInt(imitatedBehavior.get("recIdx")) + 1;
                int pidx = InvokeUtils.toInt(imitatedBehavior.get("paramIdx")) + 1;
                CSVar name = callSiteVars.get(idx);
                String contrValue = getContrValue(name);
                String reg = ContrUtil.convert2Reg(contrValue);
                if (reg != null && !Strings.anyMatch(reg)) { // anyMatch当作sink
                    logger.info("[+] possible method name regex {}", reg);
                    List<String> edgeContr = new ArrayList<>();
                    edgeContr.add(csContr.get(ridx));
                    CSVar param = callSiteVars.get(pidx);
                    ArrayList<Contr> argContrs = drivenMap.contains(param) ? drivenMap.get(param).getArrayElements() : new ArrayList<>();
                    argContrs.forEach(argContr -> edgeContr.add(argContr.getValue()));
                    List<Type> argTypes = argContrs.stream().map(Contr::getType).toList();
                    Set<JMethod> callees = World.get().filterMethods(reg, drivenMap.get(callSiteVars.get(ridx)).getType(), argTypes); // for example getxxx
                    for (JMethod callee : callees) {
                        csCallGraph.addEdge(getCallEdge(stmt, callee, edgeContr));
                        addWL(callee);
                    }
                }
            }
            case "get" -> {
                int getIdx = InvokeUtils.toInt(imitatedBehavior.get("fromIdx")) + 1;
                if (ContrUtil.isControllable(csContr.get(getIdx)) && stmt.getResult() != null) {
                    Pointer p = csManager.getCSVar(context, stmt.getResult());
                    Contr retContr = getOrAddContr(p);
                    retContr.setValue("get+polluted");
                    updateContr(p, retContr);
                }
            }
            case "set" -> {
                int setIdx = InvokeUtils.toInt(imitatedBehavior.get("fromIdx")) + 1;
                if (ContrUtil.isControllable(csContr.get(setIdx)) && stmt.getResult() != null) {
                    Pointer p = csManager.getCSVar(context, stmt.getResult());
                    Contr retContr = getOrAddContr(p);
                    retContr.setValue("set+polluted");
                    updateContr(p, retContr);
                }
            }
            case "toString" -> {
                List<String> edgeContr = new ArrayList<>();
                int fromIdx = InvokeUtils.toInt(imitatedBehavior.get("fromIdx")) + 1;
                if (!ContrUtil.isControllable(csContr.get(fromIdx))) break;
                edgeContr.add(csContr.get(fromIdx));
                CSVar toStringVar = callSiteVars.get(fromIdx);
                Contr toStringContr = drivenMap.get(toStringVar);
                Type recType = getContrType(toStringContr);
                Set<JMethod> callees = World.get().filterMethods("toString", recType, new ArrayList<>());
                for (JMethod toString : callees) {
                    csCallGraph.addEdge(getCallEdge(stmt, toString, edgeContr));
                    addWL(toString);
                }
            }
        }
    }

    private void processDynamicProxy(Invoke stmt, List<String> csContr) {
        for (JMethod invoker : World.get().getInvocationHandlerMethod()) {
            List<String> invoke = new ArrayList<>(); // 适应参数长度
            invoke.add(csContr.get(0));
            invoke.add(csContr.get(0));
            invoke.add(ContrUtil.sNOT_POLLUTED);
            for (int i = 1; i < csContr.size(); i++) {
                String v = csContr.get(i);
                if (ContrUtil.isControllable(v)) {
                    invoke.add(v);
                    break;
                }
            }
            if (invoke.size() == 3) invoke.add(ContrUtil.sNOT_POLLUTED);
            csCallGraph.addEdge(getCallEdge(stmt, invoker, invoke));
            AnalysisManager.addWL(invoker);
        }
    }

    private boolean same(Pointer p1, Pointer p2) {
        if (p1 == null || p2 == null) return false;
        if (Objects.equals(p1, p2)) return true;
        if (p1 instanceof InstanceField f1 && p2 instanceof InstanceField f2) {
            JField f1Field = f1.getField();
            JField f2Field = f2.getField();
            return f1Field.equals(f2Field) && sameBase(f1.getBaseVar(), f2.getBaseVar());
        } else if (p1 instanceof ArrayIndex a1 && p2 instanceof ArrayIndex a2) {
            return sameBase(a1.getArrayVar(), a2.getArrayVar());
        }
        return false;
    }

    private boolean sameBase(CSVar var1, CSVar var2) {
        if (Objects.equals(var1, var2)) return true;
        if (isThis(var1) && isThis(var2) && Objects.equals(var1.getType(), var2.getType())) return true;
        return false;
    }

    private void checkReceiverType(JMethod ref, CSVar base, List<String> csContr) {
        if (ref.toString().equals("<java.lang.Class: java.lang.Object newInstance()>")
                && drivenMap.get(base).getOrigin() instanceof InstanceField iField
                && iField.getField().getGSignature() != null) {
            String gSignature = iField.getField().getGSignature().toString();
            if (gSignature.contains("extends")) {
                csContr.clear();
                csContr.add(ContrUtil.sNOT_POLLUTED); // 直接设为不可控
            }
        }
    }

    private Collection<? extends JMethod> filterCHA(Set<JMethod> methods, Type type) {
        boolean isFilterNonSerializable = World.get().getOptions().isFilterNonSerializable();
        return methods.stream()
                .filter(method -> isFilterNonSerializable ? method.getDeclaringClass().isSerializable() : true)
                .filter(method -> typeSystem.isSubtype(type, method.getDeclaringClass().getType()))
                .filter(method -> !method.isPrivate())
                .collect(Collectors.toSet());
    }

    private void polluteBase(Contr contr) {
        Pointer origin = contr.getOrigin();
        if (origin instanceof InstanceField iField) {
            CSVar base = iField.getBaseVar();
            if (!ContrUtil.isControllable(getContr(base))
                    && ContrUtil.isControllable(contr)) {
                Contr old = drivenMap.get(base);
                if (old != null) {
                    old.setValue(ContrUtil.sPOLLUTED);
                    drivenMap.update(base, old);
                }
            }
        }
    }

    public void complementSummary(List<Var> params, Var tv) {
        for (int i = 0; i < params.size(); i++) {
            CSVar param = csManager.getCSVar(context, params.get(i));
            if (param.getInEdges().size() > 1) { // 说明存在参数操作
                param.removePFG(FlowKind.NEW_CONTR); // 削除初始操作影响
                drivenMap.remove(param);
                String key = "param-" + i;
                String oldV = curMethod.getSummary(key);
                String newV = getContrValue(param);
                if (ContrUtil.needUpdateInMerge(oldV, newV)) curMethod.setSummary(key, newV);
            }
        }
        if (tv != null) {
            CSVar thisVar = csManager.getCSVar(context, tv);
            tv.getUsedFields().forEach(field -> {
                if (!isIgnored(field.getType())) {
                    InstanceField to = csManager.getInstanceField(thisVar, field);
                    String key = tv.getName().substring(1) + "-" + field.getName();
                    String oldV = curMethod.getSummary(key);
                    String newV;
                    if (!drivenMap.contains(to)) newV = getContrValue(to);
                    else newV = drivenMap.get(to).getValue();
                    if (ContrUtil.needUpdateInMerge(oldV, newV)) {
                        curMethod.setSummary(key, newV);
                    }
                }
            });
        }
    }
}
