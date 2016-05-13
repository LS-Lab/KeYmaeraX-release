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

  /** Closes the connection to Mathematica */
  override def shutdown() = jlink.shutdown()

  /** Quantifier elimination on the specified formula, returns an equivalent quantifier-free formula plus Mathematica input/output as evidence */
  override def qeEvidence(formula: Formula): (Formula, Evidence) = jlink.qeEvidence(formula)

  /** Returns a formula describing the symbolic solution of the specified differential equation system.
   * @param diffSys The differential equation system
   * @param diffArg The independent variable of the ODE, usually time
   * @param iv Names of initial values per variable, e.g., x -> x_0
   * @return The solution, if found. None otherwise.
   */
  override def diffSol(diffSys: DifferentialProgram, diffArg: Variable,
                       iv: Predef.Map[Variable, Variable]): Option[Formula] = jlink.diffSol(diffSys, diffArg, iv)

  /**
   * Returns a counterexample for the specified formula.
   * @param formula The formula.
   * @return A counterexample, if found. None otherwise.
   */
  override def findCounterExample(formula: Formula): Option[Predef.Map[NamedSymbol, Term]] = jlink.findCounterExample(formula)

  /**
    * Returns a list of simulated states, where consecutive states in the list satisfy 'stateRelation'. The state
    * relation is a modality-free first-order formula. The simulation starts in a state where initial holds (first-order
    * formula).
    * @param initial A first-order formula describing the initial state.
    * @param stateRelation A first-order formula describing the relation between consecutive states. The relationship
    *                      is by name convention: postfix 'pre': prior state; no postfix: posterior state.
    * @param steps The length of the simulation run (i.e., number of states).
    * @param n The number of simulations (different initial states) to create.
    * @return 'n' lists (length 'steps') of simulated states.
    */
  override def simulate(initial: Formula, stateRelation: Formula, steps: Int = 10, n: Int = 1): Simulation = jlink.simulate(initial, stateRelation, steps, n)

  /**
    * Returns a list of simulated states, where consecutive states in the list satisfy 'stateRelation'. The state
    * relation is a modality-free first-order formula. The simulation starts in the specified initial state.
    * @param initial The initial state: concrete values .
    * @param stateRelation A first-order formula describing the relation between consecutive states. The relationship
    *                      is by name convention: postfix 'pre': prior state; no postfix: posterior state.
    * @param steps The length of the simulation run (i.e., number of states).
    * @return A list (length 'steps') of simulated states.
    */
  override def simulateRun(initial: SimState, stateRelation: Formula, steps: Int = 10): SimRun = jlink.simulateRun(initial, stateRelation, steps)

  /** Restarts the MathKernel with the current configuration */
  override def restart() = jlink.restart()
}
