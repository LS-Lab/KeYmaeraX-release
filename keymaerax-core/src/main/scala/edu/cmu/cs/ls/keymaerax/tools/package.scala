/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax

/**
 * Arithmetic back-ends and arithmetic utilities for tactics, including an SMT interface.
 *
 *   - `[[edu.cmu.cs.ls.keymaerax.tools.ext.Mathematica]]` - Mathematica interface for real arithmetic and ODE solver
 *     etc.
 *   - `[[edu.cmu.cs.ls.keymaerax.tools.ext.Z3]]` - Z3 interface for real arithmetic.
 *   - `[[edu.cmu.cs.ls.keymaerax.tools.qe.SMTConverter]]` - SMT converter for real arithmetic.
 *
 * @todo
 *   Stub. Describe for real.
 */
package object tools {

  /** Gather diagnostic information about the system configuration relevant to KeYmaera X and its tool integrations. */
  def diagnostic: String =
    ("Java Virtual Machine: " + System.getProperties.getProperty("sun.arch.data.model") + "-bit Java " +
      System.getProperties.getProperty("java.runtime.version")) +
      ("\nJava home:            " + System.getProperties.getProperty("java.home")) +
      ("\nOperating system:     " + System.getProperties.getProperty("os.name") + " " +
        System.getProperties.getProperty("os.version")) +
      ("\nQE tool:              " + Configuration.getString(Configuration.Keys.QE_TOOL).getOrElse("undefined")) +
      ("\nMathematica J/Link:   " +
        Configuration.getString(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR).getOrElse("undefined")) +
      ("\nWolfram Engine J/Link:" +
        Configuration.getString(Configuration.Keys.WOLFRAMENGINE_JLINK_LIB_DIR).getOrElse("undefined")) +
      ("\nZ3:                   " + Configuration.getString(Configuration.Keys.Z3_PATH).getOrElse("undefined"))
}
