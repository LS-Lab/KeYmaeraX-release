/**
* Copyright (c) Carnegie Mellon University.
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
class Mathematica extends ToolBase("Mathematica") with QETool with DiffSolutionTool with CounterExampleTool with SimulationTool {
  private val jlink = new JLinkMathematicaLink

  // TODO replace with constructor and dependency injection
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

  override def shutdown() = jlink.shutdown()

  def qe(formula: Formula): Formula = jlink.qe(formula)
  override def qeEvidence(formula: Formula): (Formula, Evidence) = jlink.qeEvidence(formula)
  @deprecated("Use findCounterExample instead")
  def getCounterExample(formula: Formula): String = jlink.getCounterExample(formula)
  override def diffSol(diffSys: DifferentialProgram, diffArg: Variable,
                       iv: Predef.Map[Variable, Variable]): Option[Formula] = jlink.diffSol(diffSys, diffArg, iv)

  /**
   * Returns a counterexample for the specified formula.
   * @param formula The formula.
   * @return A counterexample, if found. None otherwise.
   */
  override def findCounterExample(formula: Formula): Option[Predef.Map[NamedSymbol, Term]] = jlink.findCounterExample(formula)

  override def simulate(initial: Formula, stateRelation: Formula, steps: Int = 10, n: Int = 1): Simulation = jlink.simulate(initial, stateRelation, steps, n)
  override def simulateRun(initial: SimState, stateRelation: Formula, steps: Int = 10): SimRun = jlink.simulateRun(initial, stateRelation, steps)

  //@todo Implement Mathematica recovery actions
  override def restart() = ???
}
