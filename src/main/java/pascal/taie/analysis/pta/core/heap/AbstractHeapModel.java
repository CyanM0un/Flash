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

package pascal.taie.analysis.pta.core.heap;

import pascal.taie.World;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.ReferenceLiteral;
import pascal.taie.language.type.Type;
import pascal.taie.language.type.TypeManager;

import java.util.Map;
import java.util.function.Function;

import static pascal.taie.language.classes.StringReps.STRING;
import static pascal.taie.language.classes.StringReps.STRING_BUFFER;
import static pascal.taie.language.classes.StringReps.STRING_BUILDER;
import static pascal.taie.language.classes.StringReps.THROWABLE;
import static pascal.taie.util.collection.CollectionUtils.newHybridMap;
import static pascal.taie.util.collection.CollectionUtils.newMap;

/**
 * All heap models should inherit this class, and we can define
 * some uniform behaviors of heap modeling here.
 */
abstract class AbstractHeapModel implements HeapModel {

    private final boolean isMergeStringConstants;

    private final boolean isMergeStringObjects;

    private final boolean isMergeStringBuilders;

    private final boolean isMergeExceptionObjects;

    private final TypeManager typeManager;

    private final Type string;

    private final Type stringBuilder;

    private final Type stringBuffer;

    private final Type throwable;

    private final Map<NewExp, NewObj> objs = newMap();

    private final Map<Type, Map<ReferenceLiteral, ConstantObj>> constantObjs
            = newHybridMap();

    /**
     * The merged object representing string constants.
     */
    private final MergedObj mergedSC;

    private final Map<Type, MergedObj> mergedObjs = newMap();

    protected AbstractHeapModel(AnalysisOptions options) {
        isMergeStringConstants = options.getBoolean("merge-string-constants");
        isMergeStringObjects = options.getBoolean("merge-string-objects");
        isMergeStringBuilders = options.getBoolean("merge-string-builders");
        isMergeExceptionObjects = options.getBoolean("merge-exception-objects");
        typeManager = World.getTypeManager();
        string = typeManager.getClassType(STRING);
        stringBuilder = typeManager.getClassType(STRING_BUILDER);
        stringBuffer = typeManager.getClassType(STRING_BUFFER);
        throwable = typeManager.getClassType(THROWABLE);
        mergedSC = new MergedObj(string, "<Merged string constants>");
    }

    @Override
    public Obj getObj(NewExp newExp) {
        Type type = newExp.getType();
        if (isMergeStringObjects && type.equals(string)) {
            return getMergedObj(newExp);
        }
        if (isMergeStringBuilders &&
                (type.equals(stringBuilder) || type.equals(stringBuffer))) {
            return getMergedObj(newExp);
        }
        if (isMergeExceptionObjects && typeManager.isSubtype(throwable, type)) {
            return getMergedObj(newExp);
        }
        return doGetObj(newExp);
    }

    @Override
    public Obj getConstantObj(ReferenceLiteral value) {
        Obj obj = doGetConstantObj(value);
        if (isMergeStringConstants && value.getType().equals(string)) {
            mergedSC.addRepresentedObj(obj);
            return mergedSC;
        }
        return obj;
    }

    protected Obj doGetConstantObj(ReferenceLiteral value) {
        return constantObjs.computeIfAbsent(value.getType(), t -> newMap())
                .computeIfAbsent(value, ConstantObj::new);
    }

    @Override
    public Obj getMockObj(Obj obj) {
        return mockObjs.computeIfAbsent(obj, Function.identity());
    }

    /**
     * Merge given object given by its type.
     * @param newExp the allocation site of the object
     * @return the merged object
     */
    protected MergedObj getMergedObj(NewExp newExp) {
        MergedObj mergedObj = mergedObjs.computeIfAbsent(newExp.getType(),
                t -> new MergedObj(t, "<Merged " + t + ">"));
        mergedObj.addRepresentedObj(getNewObj(newExp));
        return mergedObj;
    }

    protected NewObj getNewObj(NewExp newExp) {
        return objs.computeIfAbsent(newExp, NewObj::new);
    }

    /**
     * The method which controls the heap modeling for normal objects.
     */
    protected abstract Obj doGetObj(NewExp newExp);
}
