/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tools

import java.io.File

import edu.cmu.cs.ls.keymaerax.core.{QETool, Term}

/**
 * Created by ran on 3/17/15.
 */
trait SMTSolver extends QETool {
  type KExpr = edu.cmu.cs.ls.keymaerax.core.Expression
  type SExpr = SMTLib

  def run(cmd : String) : (String, KExpr)

  /**
   * @return true if the job is finished, false if it is still running.
   */
  def ready : Boolean = ???

  /** Cancels the current request.
    * @return True if job is successfully cancelled, or False if the new
    * status is unknown.
    */
  def cancel : Boolean = ???

  lazy val smt2path: File = {
    val file = new File(System.getProperty("user.home") + File.separator +
      ".keymaerax" + File.separator + "cache" + File.separator + "smt2")
    file.mkdirs
    file
  }

  def getUniqueSmt2File(idx: Int = 0): File = {
    val id = "SMT" + idx.toString
    val f = new File(smt2path, id + ".smt2")
    if (f.exists()) getUniqueSmt2File(idx + 1)
    else f
  }


}