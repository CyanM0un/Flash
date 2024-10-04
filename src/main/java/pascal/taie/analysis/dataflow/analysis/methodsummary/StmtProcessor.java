package pascal.taie.analysis.dataflow.analysis.methodsummary;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
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
import pascal.taie.analysis.pta.core.heap.ConstantObj;
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

import java.lang.reflect.Method;
import java.util.*;
import java.util.stream.Collectors;

import static pascal.taie.analysis.dataflow.analysis.methodsummary.Utils.PUtil.getPointerMethod;

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

    private boolean isFilterNonSerializable =  World.get().getOptions().isFilterNonSerializable();

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
            Contr ret = Contr.newInstance(p);
            updateContr(p, ret);
            return ret;
        } else {
            return drivenMap.get(p);
        }
    }

    private void updateContr(Pointer k, Contr v) {
        if (k!= null && v != null && curMethod.equals(getPointerMethod(k))) {
            drivenMap.update(k, v);
        }
    }

    private boolean containsContr(Pointer p) {
        return drivenMap.contains(p);
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
        if (pointerFlowGraph.addEdge(edge) != null) varsToReQuery(edge.target(), new HashSet<>());
    }

    private void addWL(Invoke stmt, JMethod callee, List<String> edgeContr) {
        if (!isIgnored(callee) && (callee.isSink() || (!callee.isTransfer() && !callee.hasImitatedBehavior()))) {
            List<CSVar> callSiteVars = getCallsiteVars(stmt.getInvokeExp());
            List<Contr> callSiteContr = new ArrayList<>();
            callSiteVars.forEach(csVar -> callSiteContr.add(getContr(csVar)));
            List<Type> edgeType = getCallSiteType(callSiteContr);
            Edge callEdge = getCallEdge(stmt, callee, edgeContr, edgeType);
            filterByCaller(stmt, callEdge, edgeContr);
            setEdgeCasted(callEdge, callSiteContr);
            boolean inStack = stackManger.containsMethod(callee);
            if (csCallGraph.addEdge(callEdge)) stackManger.pushCallEdge(callEdge, inStack);
            if (!inStack) AnalysisManager.runMethodAnalysis(callee);
        }
    }

    private void setEdgeCasted(Edge callEdge, List<Contr> callSiteContr) {
        for (int i = 0; i < callSiteContr.size(); i++) {
            Contr contr = callSiteContr.get(i);
            if (contr != null && contr.isCasted()) callEdge.setCasted(i);
        }
    }

    private void varsToReQuery(Pointer p, HashSet<Pointer> visited) { // drivenMap会缓存结果，如果缓存的变量新增加了指向边，则需要重新查询
        if (Objects.equals(getPointerMethod(p), curMethod) && visited.add(p)) {
            if (drivenMap.contains(p)) {
                drivenMap.remove(p);
                updateContr(p, getContr(p));
            }
            for (PointerFlowEdge outEdge : p.getOutEdges()) {
                varsToReQuery(outEdge.target(), visited);
            }
        }
    }

    public void process(Stmt stmt) {
        this.lineNumber = stmt.getLineNumber();
        stmt.accept(visitor);
        if (stackManger.isInIf() && stackManger.isIfEnd(stmt)) stackManger.popIf(stmt);
        if (stackManger.containsInstanceOfEnd(stmt)) stackManger.removeInstanceOfEnd(stmt);
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
        public Void visit(AssignLiteral stmt) {
            Literal literal = stmt.getRValue();
            Type type = literal.getType();
            CSVar to = csManager.getCSVar(context, stmt.getLValue());
            to.setAssigned();
            if (type instanceof ClassType) {
                // here we only generate objects of ClassType
                Obj obj = heapModel.getConstantObj((ReferenceLiteral) literal);
                addPFGEdge(csManager.getCSObj(context, obj), to, FlowKind.NEW, lineNumber);
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
                    return null;
                }
                CSVar to = csManager.getCSVar(context, stmt.getLValue());
                if (stmt.isStatic()) {
                    // 先确保类加载器
                    JMethod clinit = field.getDeclaringClass().getClinit();
                    if (clinit != null && !stackManger.containsMethod(clinit)) AnalysisManager.runMethodAnalysis(clinit);
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
                    int ifEnd = Objects.equals(curMethod, stackManger.getCurIfEndMethod()) ? stackManger.getIfEnd() : -1;
                    pointerFlowGraph.addIfRange(edge, ifEnd);
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
            if (ContrUtil.isControllable(ifContr) || curMethod.getInvokeDispatch(ifVar) != null) {
                stackManger.pushIf(stmt.getTarget(), curMethod, stmt);
            } else if (stackManger.containsInstanceOfRet(ifVar)) {
                Pointer p = stackManger.removeInstanceOfRet(ifVar);
                Var cmpVar = stmt.getCondition().getOperand2();
                if (cmpVar.isConst() && cmpVar.getConstValue() instanceof IntLiteral i && i.getValue() == 0) {
                    stackManger.putInstanceOfEnd(stmt.getTarget(), p);
                }
            }
            return null;
        }

        @Override
        public Void visit(InstanceOf stmt) {
            InstanceOfExp exp = stmt.getRValue();
            Contr checkedContr = getContr(csManager.getCSVar(context, exp.getValue()));
            if (ContrUtil.isControllable(checkedContr)) {
                CSVar retVar = csManager.getCSVar(context, stmt.getLValue());
                stackManger.putInstanceOfInfo(retVar, checkedContr.getOrigin(), exp.getCheckedType());
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
            List<CSVar> callSiteVars = getCallsiteVars(invokeExp);
            CSVar base = callSiteVars.get(0);
            List<String> csContr;
            Set<JMethod> callees = new HashSet<>();
            csContr = getCallSiteContr(callSiteVars);
            if (isIgnoredCallSite(csContr, ref, stmt.getContainer().getDeclaringClass().getType())) return null;
            processReceiver(ref, base, csContr);
            if (ref.hasImitatedBehavior()) {
                processBehavior(ref, stmt, callSiteVars, csContr, base);
                return null;
            }
            if (ref.isSink()) {
                if (!checkExtendInstance(ref, base)) return null;
                addWL(stmt, ref, csContr);
                return null;
            }
            callees.addAll(getCallees(stmt, base, csContr, ref.getDeclaringClass().getType()));
            for (JMethod callee : callees) {
                addWL(stmt, callee, callee.isInvoke() ? getDynamicProxyEdge(csContr) : csContr);
            }
            // 处理返回值以及对参数的影响
            if (callees.size() == 0) return null;
            Var ret = stmt.getResult();
            CSVar csRet = null;
            Contr retContr = null;
            if (ret != null && !isIgnored(ret.getType())) {
                csRet = csManager.getCSVar(context, ret);
                retContr = getOrAddContr(csRet);
                for (CSVar arg : callSiteVars) {
                    Contr argContr = getContr(arg);
                    if (argContr != null && argContr.isSerializable()) {
                        retContr.setSerializable();
                        break;
                    }
                }
            }
            for (JMethod callee : callees) {
                if (isIgnored(callee)) continue;
                if (stackManger.containsMethod(callee)) { // 处理递归导致的忽略问题, 暂时没有更好的方法
                    if (retContr != null) {
                        for (String contr : csContr) {
                            if (ContrUtil.isControllable(contr)) {
                                retContr.setValue(contr);
                                break;
                            }
                        }
                    }
                    continue;
                }
                Map<String, String> summary = callee.getSummaryMap();
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
                            csRet.setAssigned();
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

    private List<Type> getCallSiteType(List<Contr> csContr) {
        List<Type> ret = new ArrayList<>();
        csContr.forEach(contr-> ret.add(contr != null ? contr.getType() : null));
        return ret;
    }

    private List<CSVar> getCallsiteVars(InvokeExp invokeExp) {
        List<CSVar> vars = new ArrayList<>();
        invokeExp.getArgs().stream()
                .map(arg -> csManager.getCSVar(context, arg))
                .forEach(arg -> vars.add(arg));
        CSVar base = null;
        if (invokeExp instanceof InvokeInstanceExp instanceExp) {
            base = csManager.getCSVar(context, instanceExp.getBase());
        }
        vars.add(0, base);
        return vars;
    }

    private boolean checkExtendInstance(JMethod ref, CSVar base) { // 一些特殊情况，减少误报
        if (ref.toString().equals("<java.lang.Class: java.lang.Object newInstance()>")) {
            Contr contr = getContr(base);
            if (contr != null
                    && contr.getOrigin() instanceof InstanceField iField
                    && iField.getField().getGSignature() != null) {
                String gSignature = iField.getField().getGSignature().toString();
                if (gSignature.contains("extends")) {
                    return false;
                }
            }
        }
        return true;
    }

    private boolean isIgnored(Type type) {
        return type instanceof PrimitiveType || type instanceof NullType || (type instanceof ClassType ct && ct.getName().equals("java.lang.Short"));
    }

    private boolean isIgnored(JMethod method) {
        return method == null ||
                method.isIgnored() ||
                method.getDeclaringClass().isMethodIgnored() ||
                (method.getDeclaringClass().getName().equals("java.lang.String")
                        && isIgnored(method.getReturnType())
                        && method.getSummaryMap().isEmpty()
                        && !method.getName().equals("equals"));
    }

    private boolean isIgnoredCallSite(List<String> csContr, JMethod ref, Type containerType) {
        if (!ref.isConstructor() && ref.getParamTypes().stream().anyMatch(p -> p.getName().equals("java.lang.String"))) return false; // 字符串操作？
        else if (ref.getName().equals("equals") && !ref.getDeclaringClass().getName().equals("java.lang.String") && !ContrUtil.isControllable(csContr.get(1))) return true;
        else if (typeSystem.isSubtype(typeSystem.getType("java.io.ObjectInputStream"), containerType)
                && csContr.get(0).startsWith(ContrUtil.sTHIS)) return true;
        else return csContr.stream().allMatch(s -> !ContrUtil.isControllable(s));
    }

    private boolean isThis(CSVar var) {
        return var.getVar().getName().equals("%this");
    }

    private List<String> getCallSiteContr(List<CSVar> callSiteVars) {
        List<String> list = new ArrayList<>();
        List<Contr> contrList = new ArrayList<>();
        callSiteVars.forEach(var -> contrList.add(getContr(var)));
        Contr baseContr = contrList.get(0);
        if (ContrUtil.isControllable(baseContr) && isFilterNonSerializable && !baseContr.isSerializable()
                && !baseContr.isNew() && !(baseContr.getOrigin() instanceof ArrayIndex)) {
            list.add(ContrUtil.sNOT_POLLUTED);
        } else {
            list.add(getContrValue(baseContr));
        }
        for (int i = 1; i < callSiteVars.size(); i++) {
            list.add(getContrValue(contrList.get(i)));
        }
        return list;
    }

    private String getContrValue(Pointer p) {
        Contr contr = getContr(p);
        return getContrValue(contr);
    }

    private String getContrValue(Contr c) {
        return c != null ? c.getValue() : ContrUtil.sNOT_POLLUTED;
    }

    private Contr getContr(Pointer p) {
        if (p != null && !isIgnored(p.getType())) {
            if (containsContr(p)) {
                Contr query = drivenMap.get(p);
                if (stackManger.containsInstanceOfType(p)) {
                    Contr checkedContr = query.copy(); // 返回副本可以方便还原状态
                    checkedContr.setType(stackManger.getInstanceofType(p));
                    return checkedContr;
                }
                return query;
            } else if (p instanceof CSVar var // 处理常量字符串
                    && getConstString(var.getVar()) != null) {
                Contr cs = Contr.newInstance(p);
                cs.setConstString(getConstString(var.getVar()));
                updateContr(p, cs);
                return cs;
            } else {
                Contr query = findPointsTo(p).getMergedContr();
                updateContr(p, query);
                if (query != null && stackManger.containsInstanceOfType(p)) {
                    Contr checkedContr = query.copy();
                    checkedContr.setType(stackManger.getInstanceofType(p));
                    return checkedContr;
                }
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

    private String getConstString(Var var) {
        if (var.isConst() && var.getConstValue() instanceof StringLiteral s) {
            return s.getString();
        } else {
            return null;
        }
    }

    private Edge getCallEdge(Invoke callSite, JMethod callee, List<String> csContr, List<Type> edgeType) {
        CSCallSite csCallSite = csManager.getCSCallSite(context, callSite);
        CSMethod csCallee = csManager.getCSMethod(context, callee);
        return new Edge<>(CallGraphs.getCallKind(callSite), csCallSite, csCallee, csContr, lineNumber, edgeType);
    }

    private Set<JMethod> getCallees(Invoke stmt, CSVar base, List<String> csContr, Type refType) {
        Set<JMethod> ret = new HashSet<>();
        if (base == null) {
            ret.add(CallGraphs.resolveCallee(null, stmt));
        } else if (getContr(base) != null) {
            Contr baseFact = getContr(base);
            if (!ContrUtil.isControllable(csContr.get(0)) || baseFact.isNew()) {
                ret.add(CallGraphs.resolveCallee(baseFact.getType(), stmt));
            } else {
                Set<JMethod> chaTargets = CallGraphs.resolveCalleesOf(stmt);
                if (chaTargets.size() <= 1) { // 不做过滤
                    ret.addAll(chaTargets);
                } else {
                    ret.addAll(filterCHA(chaTargets, baseFact, refType));
                    if (stmt.isInterface()
                            && ContrUtil.isCallSite(baseFact.getValue())
                            && !baseFact.isCasted()) {
                        ret.addAll(World.get().getInvocationHandlerMethod());
                    }
                }
            }
        } else {
            ret.addAll(CallGraphs.resolveCalleesOf(stmt));
        }
        Set<JMethod> callees = new HashSet<>(ret.stream()
                .filter(Objects::nonNull)
                .collect(Collectors.toSet()));
        return callees;
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
                    origin = field == null ? base : csManager.getInstanceField(base, field);
                    contrValue = ContrUtil.isControllable(baseValue) ? baseValue + "-" + fieldName : baseValue;
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
                contrValue = value.replace("param-" + (paramIdx - 1), drivenMap.get(origin).getValue());
            } else {
                contrValue = "null";
            }
        }
        Contr ret;
        if (drivenMap.contains(origin)) {
            ret = drivenMap.get(origin);
            if (repalce) {
                ret.setValue(contrValue);
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
            if (containsContr(p)) {
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
                        } else if (obj instanceof ConstantObj co && co.getAllocation() instanceof ClassLiteral cl) {
                            newContr.setType(cl.getTypeValue());
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
                        if (from != null && (ContrUtil.isControllable(from) || from.isNew())) {
                            pfe.getTransfers().forEach(transfer -> { // 转换类型
                                if (transfer instanceof SpecialType st) {
                                    Contr contr = from.copy();
                                    contr.setCasted();
                                    contr.setType(st.getType());
                                    if (from.isNew()) contr.setValue("new " + st.getType());
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
                            if (ContrUtil.isControllable(baseContr)) {
                                if (source instanceof ArrayIndex) {
                                    contr.updateValue(baseContr.getValue() + "-" + fieldName);
                                } else if (!contr.isTransient()) {
                                    if (fieldName.equals("this$0")) contr.updateValue(baseContr.getValue()); // Class.this的一种访问形式
                                    else contr.updateValue(baseContr.getValue() + "-" +fieldName);
                                }
                            }
                            pt.add(base, contr);
                        }
                    }
                    case ELEMENT_STORE -> {
                        Contr arrContr = getOrAddContr(p);
                        if (pfe.source() != null) {
                            arrContr.addArrElement(getContr(pfe.source()));
                        } else if (pfe.sourceObj() != null) {
                            Obj obj = pfe.sourceObj().getObject();
                            if (obj instanceof MockObj mockObj && mockObj.getDescriptor().string().equals("Controllable")) arrContr.setValue(((ContrAlloc) mockObj.getAllocation()).contr());
                        }
                        updateContr(p, arrContr);
                        pt.add(p, arrContr);
                    }
                    case OTHER -> {
                        if (pfe instanceof TaintTransferEdge tte) {
                            tte.getTransfers().forEach(t -> {
                                Contr from = getContr(pfe.source());
                                if (from != null && (ContrUtil.isControllable(from) || from.isNew() || from.getCS() != null)) {
                                    Type type = t instanceof SpecialType st ? st.getType() : tte.target().getType();
                                    Contr contr = from.copy();
                                    contr.setType(type);
                                    if (tte.isNewTransfer()) contr.setNew();
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
        boolean ret = false;
        for (PointerFlowEdge matchEdge : matchEdges) { // TODO field sensitive
            Pointer matchSource = matchEdge.source();
            Pointer matchTarget = matchEdge.target();
            if (same(source, matchTarget)) {
                int ifEnd = pointerFlowGraph.getIfRange(matchEdge);
                JMethod targetMethod = getPointerMethod(matchTarget);
                if ((ifEnd != -1 && lineNumber >= ifEnd)
                        || targetMethod == null
                        || targetMethod.getName().equals("<init>")) continue;
                Contr aliasContr = findPointsTo(matchSource).getMergedContr();
//                if (targetMethod.getName().equals("<init>")) {
//                    if (!ContrUtil.isControllableParam(aliasContr)) continue;
//                    List<String> initEdge = targetMethod.getInitEdge();
//                    if (initEdge == null) continue;
//                    int idx = Strings.extractParamIndex(aliasContr.getValue());
//                    if (!ContrUtil.isControllable(initEdge.get(idx))) continue;
//                }
                if(!ret) ret = pt.add(source, aliasContr);
                if (!Objects.equals(getPointerMethod(source), targetMethod) // 如果来源变量不属于当前方法，则参数来源可能不一致
                        && !pt.isEmpty()
                        && ContrUtil.isControllableParam(pt.getMergedContr())) {
                    String value = pt.getMergedContr().getValue();
                    pt.setValue(source instanceof InstanceField ? ContrUtil.replaceContr(value, ContrUtil.sTHIS) : ContrUtil.replaceContr(value, ContrUtil.sPOLLUTED));
                }
            }
        }
        return ret;
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
            if (fromContr != null && (ContrUtil.isControllable(fromContr) || fromContr.getCS() != null || fromContr.isNew())) {
                String stype = transfer.type();
                Type type = stype.equals("from") ? fromContr.getType() : typeSystem.getType(stype);
                addPFGEdge(new TaintTransferEdge(from, to, transfer.isNewTransfer()), new SpecialType(type), lineNumber);
            }
        });
    }

    private void processReceiver(JMethod ref, CSVar base, List<String> csContr) { // 处理receiver可控性传递
        Contr baseContr = drivenMap.get(base);
        if (baseContr == null) return;
        if (ref.isConstructor()) {
            ref.setInitEdge(csContr.subList(1, csContr.size()));
            for (int i = 1; i < csContr.size(); i++) {
                String contr = csContr.get(i);
                if (ContrUtil.isControllable(contr)) {
                    baseContr.setValue(contr);
                    break;
                }
            }
        }
    }

    private void processBehavior(JMethod method, Invoke stmt, List<CSVar> callSiteVars, List<String> csContr, CSVar base) {
        Map<String, String> imitatedBehavior = method.getImitatedBehavior();
        if (imitatedBehavior.containsKey("jump")) {
            String target = imitatedBehavior.get("jump");
            switch (target) {
                case "constructor" -> {
                    int idx = InvokeUtils.toInt(imitatedBehavior.get("fromIdx")) + 1;
                    Contr fromContr = getContr(callSiteVars.get(idx));
                    if (fromContr == null) return;
                    if (method.isSink()) { // special for forName
                        Contr loaderContr = getContr(callSiteVars.get(callSiteVars.size() - 1));
                        if (ContrUtil.isControllable(fromContr)
                                && ContrUtil.isControllable(loaderContr)
                                && loaderContr.getType().equals(typeSystem.getType("java.net.URLClassLoader"))) {
                            addWL(stmt, method, csContr);
                            return;
                        }
                    }
                    String clzName;
                    Set<JMethod> callees;
                    if (fromContr.getType().getName().equals("java.lang.String")) { // Class#forName
                        clzName = ContrUtil.convert2Reg(fromContr.getValue());
                        callees = World.get().filterMethods("<clinit>", clzName, new ArrayList<>(), ContrUtil.isControllableParam(fromContr), isFilterNonSerializable);
                    } else {
                        Contr paramContr = getContr(callSiteVars.get(1));
                        ArrayList<Contr> argContrs = paramContr != null ? paramContr.getArrayElements() : new ArrayList<>();
                        List<Type> argTypes = argContrs.stream().map(Contr::getType).toList();
                        clzName = fromContr.getOrigin().getType().getName();
                        if (clzName.equals("java.lang.Class")) clzName = "java.lang.Object";
                        callees = World.get().filterMethods("<init>", clzName, argTypes, ContrUtil.isControllableParam(fromContr), isFilterNonSerializable);
                    }
                    if (callees.size() > 1) logger.info("[+] {} possible init target in {}", callees.size(), curMethod);
                    for (JMethod init : callees) {
                        if (init.isPrivate()) continue;
                        List<String> edgeContr = new ArrayList<>();
                        edgeContr.add(csContr.get(0));
                        int pSize = init.getIR().getParams().size(); // 适应性PP
                        List<String> copied = Collections.nCopies(pSize, csContr.get(1));
                        edgeContr.addAll(copied);
                        addWL(stmt, init, edgeContr);
                    }
                }
                case "inference" -> {
                    int idx = InvokeUtils.toInt(imitatedBehavior.get("fromIdx")) + 1;
                    int ridx = InvokeUtils.toInt(imitatedBehavior.get("recIdx")) + 1;
                    int pidx = InvokeUtils.toInt(imitatedBehavior.get("paramIdx")) + 1;
                    Contr nameContr = getContr(callSiteVars.get(idx));
                    if (nameContr == null) return;
                    String nameValue = nameContr.getValue();
                    if (isFilterNonSerializable && !nameContr.isSerializable() && ContrUtil.isThis(nameValue)) return;
                    if (nameValue.startsWith(ContrUtil.sParam)) {
                        stmt.setFilterByCaller("edge:" + nameValue);
                    }
                    String nameReg = ContrUtil.convert2Reg(nameValue);
                    Contr paramContr = getContr(callSiteVars.get(pidx));
                    boolean expandArg = false;
                    Type expandArgType = null;
                    ArrayList<Contr> argContrs = paramContr != null ? paramContr.getArrayElements() : new ArrayList<>();
                    if (argContrs.isEmpty() && ContrUtil.isControllable(paramContr)) {
                        expandArg = true;
                        expandArgType = getContrType(paramContr);
                    }
                    List<Type> argTypes = argContrs.stream().map(Contr::getType).toList();
                    Contr recvContr = getContr(callSiteVars.get(ridx));
                    if (recvContr == null) return;
                    Set<JMethod> callees = World.get().filterMethods(nameReg, recvContr.getType(), argTypes, ContrUtil.isControllableParam(recvContr), isFilterNonSerializable, expandArgType); // for example getxxx
                    if (callees.size() > 1) logger.info("[+] {} possible invoke target in {}", callees.size(), curMethod);
                    if (nameReg.equals(".*")) callees.addAll(World.get().getInvocationHandlerMethod());
                    for (JMethod callee : callees) {
                        List<String> edgeContr = new ArrayList<>();
                        edgeContr.add(csContr.get(ridx));
                        if (callee.isInvoke()) {
                            edgeContr.add(csContr.get(ridx));
                            edgeContr.add(nameValue);
                            edgeContr.add(csContr.get(pidx));
                        } else {
                            if (expandArg) {
                                callee.getIR().getParams().forEach(p -> edgeContr.add(paramContr.getValue()));
                            } else {
                                argContrs.forEach(argContr -> edgeContr.add(argContr.getValue()));
                            }
                        }
                        addWL(stmt, callee, edgeContr);
                    }
                }
                case "get" -> {
                    int getIdx = InvokeUtils.toInt(imitatedBehavior.get("fromIdx")) + 1;
                    String fromValue = csContr.get(getIdx);
                    if (ContrUtil.isControllable(fromValue) && stmt.getResult() != null) {
                        Pointer p = csManager.getCSVar(context, stmt.getResult());
                        Contr retContr = getOrAddContr(p);
                        retContr.setValue("get+" + fromValue);
                        updateContr(p, retContr);
                    }
                }
                case "set" -> {
                    int setIdx = InvokeUtils.toInt(imitatedBehavior.get("fromIdx")) + 1;
                    String fromValue = csContr.get(setIdx);
                    if (ContrUtil.isControllable(fromValue) && stmt.getResult() != null) {
                        Pointer p = csManager.getCSVar(context, stmt.getResult());
                        Contr retContr = getOrAddContr(p);
                        retContr.setValue("set+" + fromValue);
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
                    Set<JMethod> callees = World.get().filterMethods("toString", recType, new ArrayList<>(), ContrUtil.isControllableParam(toStringContr), isFilterNonSerializable, null);
                    for (JMethod toString : callees) {
                        addWL(stmt, toString, edgeContr);
                    }
                }
            }
        } else if (imitatedBehavior.containsKey("action")) {
            String behavior = imitatedBehavior.get("action");
            switch (behavior) {
                case "replace" -> {
                    if (ContrUtil.isControllable(csContr.get(0))
                            || csContr.get(0).equals(ContrUtil.sNOT_POLLUTED)
                            || csContr.subList(1, 2).stream().allMatch(s -> ContrUtil.isControllable(s)))
                        return;
                    try {
                        Class c = Class.forName(method.getDeclaringClass().getName());
                        Class[] paramTypes = new Class[2];
                        for (int i = 0; i < method.getParamCount(); i++) {
                            paramTypes[i] = Class.forName(method.getParamType(i).getName());
                        }
                        Method rep = c.getDeclaredMethod(method.getName(), paramTypes);
                        String s = csContr.get(0);
                        String replacedValue = (String) rep.invoke(s, ContrUtil.convert2Reg(csContr.get(1)), csContr.get(2));
                        Contr replacedContr = getContr(base);
                        replacedContr.setValue(replacedValue);
                        updateContr(base, replacedContr);
                    } catch (Exception e) {
                        throw new RuntimeException(e);
                    }
                }
                case "polluteRec" -> {
                    for (int i = 1; i < callSiteVars.size(); i++) {
                        String contr = csContr.get(i);
                        if (ContrUtil.isControllable(contr) && containsContr(base)) {
                            drivenMap.get(base).setValue(contr);
                            CSObj csFrom = ContrUtil.getObj(callSiteVars.get(i), contr, heapModel, context, csManager);
                            addPFGEdge(csFrom, base, FlowKind.ELEMENT_STORE, lineNumber);
                            break;
                        }
                    }
                }
            }
        }

    }

    private List<String> getDynamicProxyEdge(List<String> csContr) {
        List<String> invokeEdge = new ArrayList<>(); // 适应参数长度
        invokeEdge.add(csContr.get(0));
        invokeEdge.add(csContr.get(0));
        invokeEdge.add(ContrUtil.sNOT_POLLUTED);
        for (int i = 1; i < csContr.size(); i++) {
            String v = csContr.get(i);
            if (ContrUtil.isControllable(v)) {
                invokeEdge.add(v);
                break;
            }
        }
        if (invokeEdge.size() == 3) invokeEdge.add(ContrUtil.sNOT_POLLUTED);
        return invokeEdge;
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

    private Collection<? extends JMethod> filterCHA(Set<JMethod> methods, Contr baseContr, Type refType) {
        Type type = baseContr.getType();
        boolean ignoredType = !typeSystem.isSubtype(refType, type); // 消除iterator的transfer副作用
        boolean isConstruct = baseContr.isSerializable() && ContrUtil.isControllable(baseContr) && baseContr.getOrigin() instanceof CSVar var && var.isAssigned();
        return methods.stream()
                .filter(method -> isFilterNonSerializable ? (method.getDeclaringClass().isSerializable() ? true : isConstruct) : true)
                .filter(method -> ignoredType || typeSystem.isSubtype(type, method.getDeclaringClass().getType()))
                .filter(method -> !method.isPrivate())
                .collect(Collectors.toSet());
    }

    private void filterByCaller(Invoke stmt, Edge callEdge, List<String> edgeContr) {
        if (curMethod.isInvoke()) {
            if (stackManger.isInIf()) {
                stackManger.getIfConditions(curMethod).forEach(condition -> {
                    CSVar ifVar = csManager.getCSVar(context, condition.getOperand1());
                    if (getPointerMethod(ifVar).equals(curMethod)) {
                        String invokeDispatch = curMethod.getInvokeDispatch(ifVar);
                        if (invokeDispatch != null) {
                            callEdge.setFilterByCaller("name:" + invokeDispatch);
                        }
                    }
                });
            }
            List<Var> args = stmt.getInvokeExp().getArgs();
            if (args.size() == 1 && stmt.getLValue() != null) {
                String constString = getConstString(args.get(0));
                if (edgeContr.get(0).startsWith(ContrUtil.sParam + "-1") && constString != null) {
                    curMethod.addInvokeDispatch(csManager.getCSVar(context, stmt.getLValue()), constString);
                }
            }
        }
        if (stmt.isFilterByCaller()) {
            callEdge.setFilterByCaller(stmt.getFilterByCaller());
        }
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
