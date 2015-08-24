/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core.{Evidence, Formula, QETool}

/**
 * Z3 quantifier elimination tool.
 *
 * Created by smitsch on 4/27/15.
 * @author Ran Ji
 * @author Stefan Mitsch
 */
class Z3 extends ToolBase("Z3") with QETool {
  private val z3 = new Z3Solver

  def init(config : Map[String,String]) = {initialized = true}

  override def qe(formula: Formula): Formula = z3.qe(formula)
  override def qeEvidence(formula: Formula): (Formula, Evidence) = z3.qeEvidence(formula)

  override def restart() = {}

  override def shutdown() = {}
}
