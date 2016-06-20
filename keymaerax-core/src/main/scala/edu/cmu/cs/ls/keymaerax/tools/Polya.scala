/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core.{NamedSymbol, Term, _}

import scala.collection.immutable.Map

/**
 * Polya quantifier elimination tool.
 * Still need Mathematica to do diffSolve and CounterExample
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

  //def qe(formula: Formula): Formula = polya.qe(formula)
  override def qeEvidence(formula: Formula): (Formula, Evidence) = polya.qeEvidence(formula)

  override def restart() = ???

  override def shutdown() = {}
}
