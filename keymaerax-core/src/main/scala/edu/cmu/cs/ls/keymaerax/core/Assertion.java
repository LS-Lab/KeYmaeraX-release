/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * @note Code Review: 2020-02-14
 */
package edu.cmu.cs.ls.keymaerax.core;

import java.util.function.Supplier;

/**
 * A wrapper around the Java `assert` keyword.
 * Lazy evaluation of conditions and messages.
 *
 * Disabled by default.
 * Enable at run-time with `java -ea`.
 * Disable with `java -da`.
 * @author Fabian Immler
 */
public class Assertion {
    /** assert `assertion(argument)` evaluated lazily, lazy evaluation of `message` */
    public static <A> A assertion(java.util.function.Function<A,Boolean> assertion, A argument, Supplier<Object> message) {
        assert assertion.apply(argument) : "assertion failed: " + message.get();
        return argument;
    }
    /** assert `assertion(argument)` evaluated lazily */
    public static <A> A assertion(java.util.function.Function<A,Boolean> assertion, A argument) {
        assert assertion.apply(argument)  : "assertion failed";
        return argument;
    }
    /** assert `assertion()` evaluated lazily, lazy evaluation of `message` */
    public static void assertion(Supplier<Boolean> assertion, Supplier<Object> message) {
        assert assertion.get() : "assertion failed: " + message.get();
    }
    /** assert `assertion()` evaluated lazily*/
    public static void assertion(Supplier<Boolean> assertion) {
        assert assertion.get() : "assertion failed";
    }
}
