/*
 * Tai-e: A Program Analysis Framework for Java
 *
 * Copyright (C) 2020 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2020 Yue Li <yueli@nju.edu.cn>
 * All rights reserved.
 *
 * This software is designed for the "Static Program Analysis" course at
 * Nanjing University, and it supports a subset of Java features.
 * Tai-e is only for educational and academic purposes, and any form of
 * commercial use is disallowed.
 */

package pascal.taie.frontend.soot;

import org.junit.Test;
import pascal.taie.ir.IRPrinter;
import pascal.taie.java.World;
import pascal.taie.java.classes.JClass;

import java.util.Collections;
import java.util.List;

public class IRTest {

    private static final List<String> targets
            = Collections.singletonList("AllInOne");

    private static void initWorld(String mainClass) {
        String[] args = new String[]{
                "-cp",
                "java-benchmarks/jre1.6.0_24/rt.jar;" +
                        "java-benchmarks/jre1.6.0_24/jce.jar;" +
                        "java-benchmarks/jre1.6.0_24/jsse.jar;" +
                        "analyzed/ir",
                mainClass
        };
        TestUtils.buildWorld(args);
    }

    @Test
    public void testIRBuilder() {
        // This will enable PackManager run several BodyTransformers
        // to optimize Jimple body.
        System.setProperty("ENABLE_JIMPLE_OPT", "true");

        targets.forEach(main -> {
            initWorld(main);
            JClass mainClass = World.getMainMethod().getDeclaringClass();
            mainClass.getDeclaredMethods().forEach(m ->
                    IRPrinter.print(m.getNewIR(), System.out));
            System.out.println("------------------------------\n");
        });
    }
}