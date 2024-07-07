/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics.macros;

import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

/**
 * Axioms, proof rules and tactics are found at runtime via reflection. Because of this, we need a java annotation that
 * is not erased at compile time. Also, annotation macros consume their annotations, so even if they stayed around at
 * runtime, we could not use them.
 */
@Retention(RetentionPolicy.RUNTIME)
public @interface InternalAnnotation {
}
