/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core.{Evidence, Formula, QETool}

/**
 * Polya quantifier elimination tool.
 *
 * Created by smitsch on 4/27/15.
 * @author Ran Ji
 * @author Stefan Mitsch
 */
class Polya extends ToolBase("Polya") with QETool {
  private val polya = new PolyaSolver

  def init(config : Map[String,String]) = {initialized = true}

  override def qe(formula: Formula): Formula = polya.qe(formula)
  override def qeEvidence(formula: Formula): (Formula, Evidence) = polya.qeEvidence(formula)

  override def restart() = {}

  override def shutdown() = {}
}
