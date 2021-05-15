/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2020-- Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2020-- Yue Li <yueli@nju.edu.cn>
 * All rights reserved.
 *
 * Tai-e is only for educational and academic purposes,
 * and any form of commercial use is disallowed.
 * Distribution of Tai-e is disallowed without the approval.
 */

package pascal.taie.analysis.graph.callgraph;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.proginfo.MemberRef;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.util.collection.MapUtils;
import pascal.taie.util.collection.SetUtils;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.LinkedList;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

/**
 * Builds call graph via class hierarchy analysis.
 */
class CHABuilder implements CGBuilder<InvokeExp, JMethod> {

    private static final Logger logger = LogManager.getLogger(CHABuilder.class);

    private ClassHierarchy hierarchy;

    /**
     * Cache resolve results for interface/virtual invocations.
     */
    private Map<JClass, Map<MemberRef, Set<JMethod>>> resolveTable;

    @Override
    public CallGraph<InvokeExp, JMethod> build() {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(World.getMainMethod());
        buildCallGraph(callGraph);
        return callGraph;
    }

    private void buildCallGraph(DefaultCallGraph callGraph) {
        hierarchy = World.getClassHierarchy();
        resolveTable = MapUtils.newMap();
        Queue<JMethod> queue = new LinkedList<>(callGraph.getEntryMethods());
        while (!queue.isEmpty()) {
            JMethod method = queue.remove();
            for (InvokeExp callSite : callGraph.getCallSitesIn(method)) {
                Set<JMethod> callees = resolveCalleesOf(callSite);
                callees.forEach(callee -> {
                    if (!callGraph.contains(callee)) {
                        queue.add(callee);
                    }
                    callGraph.addEdge(callSite, callee,
                            CGUtils.getCallKind(callSite));
                });
            }
        }
        hierarchy = null;
        resolveTable = null;
    }

    /**
     * Resolves callees of a call site via class hierarchy analysis.
     */
    private Set<JMethod> resolveCalleesOf(InvokeExp callSite) {
        MethodRef methodRef = callSite.getMethodRef();
        CallKind kind = CGUtils.getCallKind(callSite);
        switch (kind) {
            case INTERFACE:
            case VIRTUAL: {
                JClass cls = methodRef.getDeclaringClass();
                Set<JMethod> callees = MapUtils.getMapMap(resolveTable, cls, methodRef);
                if (callees != null) {
                    return callees;
                }
                callees = SetUtils.newHybridSet();
                Deque<JClass> workList = new ArrayDeque<>();
                workList.add(cls);
                while (!workList.isEmpty()) {
                    JClass c = workList.poll();
                    if (!c.isAbstract()) {
                        JMethod callee = hierarchy.dispatch(c, methodRef);
                        if (callee != null) {
                            callees.add(callee);
                        }
                    }
                    hierarchy.getAllSubclassesOf(c, false)
                            .stream()
                            .filter(subclass -> !subclass.isAbstract())
                            .forEach(workList::add);
                }
                MapUtils.addToMapMap(resolveTable, cls, methodRef, callees);
                return callees;
            }
            case SPECIAL:
            case STATIC: {
                return Set.of(methodRef.resolve());
            }
            default:
                throw new AnalysisException("Failed to resolve call site: " + callSite);
        }
    }
}