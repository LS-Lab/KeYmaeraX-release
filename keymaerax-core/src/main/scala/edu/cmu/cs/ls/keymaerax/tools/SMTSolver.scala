/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * @note Code Review: 2016-06-01
  */
package edu.cmu.cs.ls.keymaerax.tools

import java.io.File

import edu.cmu.cs.ls.keymaerax.core.{QETool, Term}

/**
 * Created by ran on 3/17/15.
 * @author Ran Ji
 */
trait SMTSolver extends QETool {
  type KExpr = edu.cmu.cs.ls.keymaerax.core.Expression

//  def run(cmd : String) : (String, KExpr)
//
  lazy val smt2path: File = {
    val file = new File(System.getProperty("user.home") + File.separator +
      ".keymaerax" + File.separator + "cache" + File.separator + "smt2")
    file.mkdirs
    file
  }

}