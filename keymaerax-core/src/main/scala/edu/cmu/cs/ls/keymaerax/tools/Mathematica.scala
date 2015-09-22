/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.immutable.Map

/**
 * Mathematica tool for quantifier elimination and solving differential equations.
 *
 * Created by smitsch on 4/27/15.
 * @author Stefan Mitsch
 */
class Mathematica extends ToolBase("Mathematica") with QETool with DiffSolutionTool {
  private val jlink = new JLinkMathematicaLink

  // TODO replace with constructor and dependency injection
  override def init(config: Map[String,String]) = {
    val linkName = config.get("linkName") match {
      case Some(l) => l
      case None => throw new IllegalArgumentException("Missing configuration parameter 'linkName'")
    }
    val libDir = config.get("libDir") // doesn't need to be defined
    initialized = jlink.init(linkName, libDir)
  }

  override def shutdown() = jlink.shutdown()

  override def qe(formula: Formula): Formula = jlink.qe(formula)
  override def qeEvidence(formula: Formula): (Formula, Evidence) = jlink.qeEvidence(formula)
  def getCounterExample(formula: Formula): String = jlink.getCounterExample(formula)
  override def diffSol(diffSys: DifferentialProgram, diffArg: Variable,
                       iv: Predef.Map[Variable, Function]): Option[Formula] = jlink.diffSol(diffSys, diffArg, iv)

  //@todo Implement Mathematica recovery actions
  override def restart() = ???
}
