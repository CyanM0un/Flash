package pascal.taie.analysis.dataflow.analysis.methodsummary;

import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Stack;

public class StackManger {

    private Stack<JMethod> methodStack;

    private Stack<Pointer> queryStack;

    private LinkedList<Stmt> ifStack;

    private Map<Stmt, JMethod> ifEndMap;

    public StackManger() {
        this.methodStack = new Stack<>();
        this.queryStack = new Stack<>();
        this.ifStack = new LinkedList<>();
        this.ifEndMap = new HashMap<>();
    }

    public void pushMethod(JMethod method) {
        methodStack.push(method);
    }

    public void popMethod() {
        methodStack.pop();
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
}
