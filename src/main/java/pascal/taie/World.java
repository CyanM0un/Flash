/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie;

import pascal.taie.analysis.dataflow.analysis.methodsummary.Utils.ContrUtil;
import pascal.taie.config.Options;
import pascal.taie.frontend.cache.CachedIRBuilder;
import pascal.taie.frontend.soot.SootClassLoader;
import pascal.taie.ir.IRBuilder;
import pascal.taie.ir.exp.Var;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.natives.NativeModel;
import pascal.taie.language.type.ClassType;
import pascal.taie.language.type.Type;
import pascal.taie.language.type.TypeSystem;
import pascal.taie.util.AbstractResultHolder;
import pascal.taie.util.collection.Sets;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serial;
import java.io.Serializable;
import java.lang.reflect.Field;
import java.util.*;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Manages the whole-program information of the program being analyzed.
 * Note that the setters of this class are protected: they are supposed
 * to be called (once) by the world builder, not analysis classes.
 */
public final class World extends AbstractResultHolder
        implements Serializable {

    /**
     * ZA WARUDO, i.e., the current world.
     */
    private static World theWorld;

    /**
     * The callbacks that will be invoked at resetting.
     * This is useful to clear class-level caches.
     */
    private static final List<Runnable> resetCallbacks = new ArrayList<>();

    /**
     * Notes: This field is {@code transient} because it
     * should be set after deserialization.
     */
    private transient Options options;

    private TypeSystem typeSystem;

    private ClassHierarchy classHierarchy;

    /**
     * Notes: add {@code transient} to wrap this {@link IRBuilder} using
     * {@link pascal.taie.frontend.cache.CachedIRBuilder} in serialization.
     *
     * @see #writeObject(ObjectOutputStream)
     * @see #readObject(ObjectInputStream)
     */
    private transient IRBuilder irBuilder;

    private NativeModel nativeModel;

    private JMethod mainMethod;

    private Collection<JMethod> implicitEntries;

    private LinkedList<JMethod> GCEntries = new LinkedList<>();

    private Set<JMethod> invocationHandlerMethods = new HashSet<>();

    /**
     * Sets current world to {@code world}.
     */
    public static void set(World world) {
        theWorld = world;
    }

    /**
     * @return the current {@code World} instance.
     */
    public static World get() {
        return theWorld;
    }

    public static void registerResetCallback(Runnable callback) {
        resetCallbacks.add(callback);
    }

    public static void reset() {
        theWorld = null;
        resetCallbacks.forEach(Runnable::run);
    }

    public Options getOptions() {
        return options;
    }

    public void setOptions(Options options) {
        checkAndSet("options", options);
    }

    public TypeSystem getTypeSystem() {
        return typeSystem;
    }

    public void setTypeSystem(TypeSystem typeSystem) {
        checkAndSet("typeSystem", typeSystem);
    }

    public ClassHierarchy getClassHierarchy() {
        return classHierarchy;
    }

    public void setClassHierarchy(ClassHierarchy classHierarchy) {
        checkAndSet("classHierarchy", classHierarchy);
    }

    public IRBuilder getIRBuilder() {
        return irBuilder;
    }

    public void setIRBuilder(IRBuilder irBuilder) {
        checkAndSet("irBuilder", irBuilder);
    }

    public NativeModel getNativeModel() {
        return nativeModel;
    }

    public void setNativeModel(NativeModel nativeModel) {
        checkAndSet("nativeModel", nativeModel);
    }

    public JMethod getMainMethod() {
        return mainMethod;
    }

    public void setMainMethod(JMethod mainMethod) {
        checkAndSet("mainMethod", mainMethod);
    }

    public Collection<JMethod> getImplicitEntries() {
        return implicitEntries;
    }

    public void setImplicitEntries(Collection<JMethod> implicitEntries) {
        checkAndSet("implicitEntries", implicitEntries);
    }

    /**
     * Sets value for specified field (by {@code fieldName}).
     * Ensures that the specified field is set at most once.
     */
    private void checkAndSet(String fieldName, Object value) {
        try {
            Field field = World.class.getDeclaredField(fieldName);
            if (field.get(this) != null) {
                throw new IllegalStateException(
                        "World." + fieldName + " already set");
            }
            field.set(this, value);
        } catch (NoSuchFieldException | IllegalAccessException e) {
            throw new RuntimeException("Failed to set World." + fieldName);
        }
    }

    @Serial
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        s.writeObject(new CachedIRBuilder(irBuilder, classHierarchy));
    }

    @Serial
    private void readObject(ObjectInputStream s) throws IOException,
            ClassNotFoundException {
        s.defaultReadObject();
        setIRBuilder((IRBuilder) s.readObject());
    }

    public void addGCEntry(JMethod m) {
        if (!GCEntries.contains(m)) {
            GCEntries.add(m);
            if (SootClassLoader.readSubSigList.contains(m.getSubsignature().toString())
                    || getOptions().getSources().contains(m.toString())) m.setSource();
        }
    }

    public LinkedList<JMethod> getGCEntries() {
        return GCEntries;
    }

    public void addInvocationHandlerMethod(JMethod m) {
        invocationHandlerMethods.add(m);
        m.setInvoke();
    }

    public Set<JMethod> getInvocationHandlerMethod() {
        return invocationHandlerMethods;
    }

    public void filterHandler() {
        if (options.isFilterNonSerializable()) {
            Set<JMethod> methods = new HashSet<>(invocationHandlerMethods);
            for (JMethod method : methods) {
                if (!method.getDeclaringClass().isSerializable()) invocationHandlerMethods.remove(method);
            }
        }
    }

    public Stream<JMethod> allMethods() {
        return World.get()
                .getClassHierarchy()
                .allClasses()
                .flatMap(j -> j.getDeclaredMethods().stream());
    }

    public Set<JMethod> filterMethods(String name, String clzName, List<Type> argTypes, boolean recSer, boolean paramSer) {
        boolean hasStar = clzName.contains("*");
        Pattern pattern = hasStar ? Pattern.compile(clzName) : null;
        Type clsType = null;
        if (!hasStar) {
            clsType = typeSystem.getType(clzName);
            if (clsType == null || (clsType instanceof ClassType ct && ct.getJClass() == null)) return Sets.newSet();
        }

        Type finalClsType = clsType;
        return allMethods()
                .filter(m -> hasStar ? pattern.matcher(m.getDeclaringClass().getName()).find() : m.getName().equals(name))
                .filter(m -> typeSystem.isSubtype(finalClsType, m.getDeclaringClass().getType())
                        && !m.isAbstract()
                        && !m.isPrivate()
                        && (recSer || m.getDeclaringClass().isSerializable())
                        && (!paramSer || m.getIR().getParams().stream().allMatch(p -> ContrUtil.isSerializableType(p.getType()))))
                .filter(m -> typeSystem.allSubType(null, argTypes, m.getIR().getParams().stream()
                        .map(Var::getType)
                        .collect(Collectors.toList())))
                .collect(Collectors.toSet());
    }

    public Set<JMethod> filterMethods(String nameReg, Type clsType, List<Type> argTypes, boolean recSer, boolean paramSer, Type expandArgType) {
        boolean hasStar = nameReg.contains("*");
        Pattern pattern = Pattern.compile(nameReg);

        return allMethods()
                .filter(m -> hasStar ? pattern.matcher(m.getName()).find() : m.getName().equals(nameReg))
                .filter(m -> !m.isAbstract()
                        && !m.isPrivate()
                        && typeSystem.isSubtype(clsType, m.getDeclaringClass().getType())
                        && (recSer || m.getDeclaringClass().isSerializable())
                        && (!paramSer || m.getIR().getParams().stream().allMatch(p -> ContrUtil.isSerializableType(p.getType()))))
                .filter(m -> typeSystem.allSubType(expandArgType, argTypes, m.getIR().getParams().stream()
                        .map(Var::getType)
                        .collect(Collectors.toList())))
                .collect(Collectors.toSet());
    }
}
