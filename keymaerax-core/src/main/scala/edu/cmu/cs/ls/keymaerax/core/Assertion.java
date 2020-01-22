package edu.cmu.cs.ls.keymaerax.core;

import java.util.function.Supplier;

/**
 * A wrapper around the Java `assert` keyword.
 * Lazy evaluation of conditions and messages.
 *
 * Disabled by default.
 * Enable at run-time with `java -ea`.
 * Disable with `java -da`.
 *
 * */
public class Assertion {
    public static <A> A assertion(java.util.function.Function<A,Boolean> assertion, A argument, Supplier<Object> message) {
        assert assertion.apply(argument) : "assertion failed: " + message.get();
        return argument;
    }
    public static <A> A assertion(java.util.function.Function<A,Boolean> assertion, A argument) {
        assert assertion.apply(argument)  : "assertion failed";
        return argument;
    }
    public static void assertion(Supplier<Boolean> assertion, Supplier<Object> message) {
        assert assertion.get() : "assertion failed: " + message.get();
    }
    public static void assertion(Supplier<Boolean> assertion) {
        assert assertion.get() : "assertion failed";
    }
}
