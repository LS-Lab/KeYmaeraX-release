/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * @note Code Review: 2016-08-02
  */
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core.{NamedSymbol, Term, _}

import scala.collection.immutable.Map

/**
 * Polya quantifier elimination tool.
 *
 * Created by smitsch on 4/27/15.
 * @author Ran Ji
 * @author Stefan Mitsch
 */
class Polya extends ToolBase("Polya") with QETool {
  private val polya = new PolyaSolver

  override def init(config: Map[String,String]) = {
    initialized = true
  }

  override def qeEvidence(formula: Formula): (Formula, Evidence) = {
    require(isInitialized, "Polya needs to be initialized before use")
    polya.qeEvidence(formula)
  }

  override def restart() = ???

  override def shutdown() = {
    initialized = false
  }
}
