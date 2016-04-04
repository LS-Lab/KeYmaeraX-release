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
class Polya extends ToolBase("Polya") with QETool with DiffSolutionTool with CounterExampleTool {
  private val polya = new PolyaSolver
  private val jlink = new JLinkMathematicaLink

  override def init(config: Map[String,String]) = {
    val linkName = config.get("linkName") match {
      case Some(l) => l
      case None => throw new IllegalArgumentException("Mathematica not configured. Configure Mathematica and restart KeYmaera X.\nMissing configuration parameter 'linkName'\n")
      //        "You should configure settings in the UI and restart KeYmaera X." +
      //        "Or specify the paths explicitly from command line by running\n" +
      //        "  java -jar keymaerax.jar -mathkernel pathtokernel -jlink pathtojlink")
    }
    val libDir = config.get("libDir") // doesn't need to be defined
    initialized = jlink.init(linkName, libDir)
  }

  def qe(formula: Formula): Formula = polya.qe(formula)
  override def qeEvidence(formula: Formula): (Formula, Evidence) = polya.qeEvidence(formula)

  override def diffSol(diffSys: DifferentialProgram, diffArg: Variable,
                       iv: Predef.Map[Variable, Variable]): Option[Formula] = jlink.diffSol(diffSys, diffArg, iv)
  override def findCounterExample(formula: Formula): Option[Predef.Map[NamedSymbol, Term]] = jlink.findCounterExample(formula)

  override def restart() = ???

  override def shutdown() = jlink.shutdown()
}
