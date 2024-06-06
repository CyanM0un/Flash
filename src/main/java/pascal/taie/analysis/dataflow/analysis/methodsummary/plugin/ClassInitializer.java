package pascal.taie.analysis.dataflow.analysis.methodsummary.plugin;

import pascal.taie.analysis.AnalysisManager;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;

import java.util.HashSet;
import java.util.Set;

public class ClassInitializer implements Plugin {

    private Set<JClass> noReadObject;

    private Set<JClass> initConstruct;

    private Set<JClass> initReadObject;

    @Override
    public void onStart() {
        noReadObject = new HashSet<>();
        initConstruct = new HashSet<>();
        initReadObject = new HashSet<>();
    }

    @Override
    public void onNewMethod(JMethod method) {
        JClass clz = method.getDeclaringClass();
        if (method.isSource()) {
            initReadObject.add(clz);
        }
        if (!method.getName().equals("<clinit>")) initializeReadObject(clz); //  防止未初始化类即恢复对象
        initializeClass(clz);
    }

    public void initializeClass(JClass cls) {
        if (cls == null || cls.isIgnored() || initConstruct.contains(cls)) {
            return;
        }
        JClass superclass = cls.getSuperClass();
        if (superclass != null) {
            initializeClass(superclass);
        }
        JMethod clinit = cls.getClinit();
        if (clinit != null) {
            initConstruct.add(cls);
            if (!clinit.hasSummary()) {
                AnalysisManager.runMethodAnalysis(clinit);
            }
        }
    }

    private void initializeReadObject(JClass cls) {
        if (cls == null || noReadObject.contains(cls) || initReadObject.contains(cls)) {
            return;
        }
        boolean existReadObject = false;
        for (JMethod readObject : cls.getDeclaredMethods()) {
            if (readObject.isSource()) {
                initReadObject.add(cls);
                existReadObject = true;
                if (!readObject.hasSummary()) AnalysisManager.runMethodAnalysis(readObject);
                break;
            }
        }
        if (!existReadObject) noReadObject.add(cls);
    }

}
