/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax

/**
 * Arithmetic back-ends and arithmetic utilities for tactics, including an SMT interface.
 *
 *    - `[[edu.cmu.cs.ls.keymaerax.tools.Mathematica]]` - Mathematica interface for real arithmetic and ODE solver etc.
 *    - `[[edu.cmu.cs.ls.keymaerax.tools.Z3]]` - Z3 interface for real arithmetic.
 *    - `[[edu.cmu.cs.ls.keymaerax.tools.Polya]]` - Polya interface for real arithmetic.
 *    - `[[edu.cmu.cs.ls.keymaerax.tools.SMTConverter]]` - SMT converter for real arithmetic.
 *
 * @todo Stub. Describe for real.
 */
package object tools {
  /** Gather diagnostic information about the system configuration relevant to KeYmaera X and its tool integrations. */
  def diagnostic: String =
    "Java Virtual Machine: " + System.getProperties.getProperty("sun.arch.data.model") + "-bit Java " + System.getProperties.getProperty("java.runtime.version") +
    "\nJava home:            " + System.getProperties.getProperty("java.home") +
    "\nOperating system:     " + System.getProperties.getProperty("os.name") + " " + System.getProperties.getProperty("os.version") +
    "\nMathematica J/Link:   " + Configuration.getOption(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR)
}
