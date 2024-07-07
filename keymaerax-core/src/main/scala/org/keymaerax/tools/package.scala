/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax

import org.keymaerax.info.Os

/**
 * Arithmetic back-ends and arithmetic utilities for tactics, including an SMT interface.
 *
 *   - `[[org.keymaerax.tools.ext.Mathematica]]` - Mathematica interface for real arithmetic and ODE solver etc.
 *   - `[[org.keymaerax.tools.ext.Z3]]` - Z3 interface for real arithmetic.
 *   - `[[org.keymaerax.tools.qe.SMTConverter]]` - SMT converter for real arithmetic.
 *
 * @todo
 *   Stub. Describe for real.
 */
package object tools {

  /** Gather diagnostic information about the system configuration relevant to KeYmaera X and its tool integrations. */
  def diagnostic: String = {
    val qeTool = Configuration.getString(Configuration.Keys.QE_TOOL).getOrElse("undefined")
    val mathematicaLibDir = Configuration.getString(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR).getOrElse("undefined")
    val wolframLibDir = Configuration.getString(Configuration.Keys.WOLFRAMENGINE_JLINK_LIB_DIR).getOrElse("undefined")
    val z3path = Configuration.getString(Configuration.Keys.Z3_PATH).getOrElse("undefined")
    s"""Java Virtual Machine: Java ${System.getProperty("java.runtime.version")}
       |Java home:            ${System.getProperty("java.home")}
       |Operating system:     ${Os.Name} ${Os.Version}
       |QE tool:              $qeTool
       |Mathematica J/Link:   $mathematicaLibDir
       |Wolfram Engine J/Link:$wolframLibDir
       |Z3:                   $z3path
       |""".stripMargin
  }
}
