/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * @note Code Review: 2016-08-02
  */
package edu.cmu.cs.ls.keymaerax.tools

import java.io.File

import edu.cmu.cs.ls.keymaerax.core.{QETool, Term}

/**
 * Common interface for SMT solvers.
 * @author Ran Ji
 */
trait SMTSolver extends QETool {
  type KExpr = edu.cmu.cs.ls.keymaerax.core.Expression

  lazy val smt2path: File = {
    val file = new File(System.getProperty("user.home") + File.separator +
      ".keymaerax" + File.separator + "cache" + File.separator + "smt2")
    file.mkdirs
    file
  }

}