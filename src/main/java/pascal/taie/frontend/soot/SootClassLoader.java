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

package pascal.taie.frontend.soot;

import pascal.taie.World;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JClassLoader;
import pascal.taie.util.collection.Maps;
import soot.Scene;
import soot.SootClass;

import java.util.*;

public class SootClassLoader implements JClassLoader {

    private final transient Scene scene;

    private final ClassHierarchy hierarchy;

    private final boolean allowPhantom;

    private transient Converter converter;

    private final Map<String, JClass> classes = Maps.newMap(1024);

    private List<String> sources;

    public static Set<String> readSubSigList = Set.of(
            "void readObject(java.io.ObjectInputStream)",
            "void readExternal(java.io.ObjectInput)",
            "java.lang.Object readSolve()"
            );

    private static String invokeSubSig = "java.lang.Object invoke(java.lang.Object,java.lang.reflect.Method,java.lang.Object[])";

    SootClassLoader(Scene scene, ClassHierarchy hierarchy, boolean allowPhantom, List<String> sources) {
        this.scene = scene;
        this.hierarchy = hierarchy;
        this.allowPhantom = allowPhantom;
        this.sources = sources;
    }

    @Override
    public JClass loadClass(String name) {
        JClass jclass = classes.get(name);
        if (jclass == null && scene != null) {
            SootClass sootClass = scene.getSootClassUnsafe(name, false);
            if (sootClass != null && (!sootClass.isPhantom() || allowPhantom)) {
                // TODO: handle phantom class more comprehensively
                jclass = new JClass(this, sootClass.getName(),
                        sootClass.moduleName);
                // New class must be put into classes map at first,
                // at build(jclass) may also trigger the loading of
                // the new created class. Not putting the class into classes
                // may cause infinite recursion.
                classes.put(name, jclass);
                new SootClassBuilder(converter, sootClass).build(jclass);
                hierarchy.addClass(jclass);

                boolean isSerImpl = sootClass.implementsInterface("java.io.Serializable");
                if (isSerImpl) jclass.setSerializable();
                boolean isInvokeImpl = sootClass.implementsInterface("java.lang.reflect.InvocationHandler");
                jclass.getDeclaredMethods().forEach(m -> {
                    if (sources.contains(m.getSignature()) ||
                            (sources.contains("serializable") && readSubSigList.contains(m.getSubsignature().toString()))) {
                        World.get().addGCEntry(m);
                    }
                    if (m.getSubsignature().toString().equals(invokeSubSig) && isInvokeImpl) {
                        World.get().addInvocationHandlerMethod(m);
                    }
                });
            }
        }
        // TODO: add warning for missing classes
        return jclass;
    }

    @Override
    public Collection<JClass> getLoadedClasses() {
        return classes.values();
    }

    void setConverter(Converter converter) {
        this.converter = converter;
    }
}
