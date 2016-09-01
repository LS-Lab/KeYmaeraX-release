/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * @note Code Review: 2016-08-02
  */
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tools.SimulationTool.{SimRun, SimState, Simulation}

import scala.collection.immutable.Map

/**
 * Mathematica tool for quantifier elimination and solving differential equations.
 *
 * Created by smitsch on 4/27/15.
 * @author Stefan Mitsch
 * @todo Code Review: Move non-critical tool implementations into a separate package tactictools
 */
class Mathematica extends ToolBase("Mathematica") with QETool with DiffSolutionTool with CounterExampleTool with SimulationTool with DerivativeTool with SolutionTool with SimplificationTool with AlgebraTool {
  // JLink, shared between tools
  private val link = new JLinkMathematicaLink

  private val mQE = new MathematicaQETool(link)
  private val mCEX = new MathematicaCEXTool(link)
  private val mODE = new MathematicaODETool(link)
  private val mSim = new MathematicaSimulationTool(link)
  private val mSolve = new MathematicaSolutionTool(link)
  private val mAlgebra = new MathematicaAlgebraTool(link)
  private val mSimplify = new MathematicaSimplificationTool(link)

  override def init(config: Map[String,String]) = {
    val linkName = config.get("linkName") match {
      case Some(l) => l
      case None => throw new IllegalArgumentException("Mathematica not configured. Configure Mathematica and restart KeYmaera X.\nMissing configuration parameter 'linkName'\n")
        //@todo More helpful error messages about how to solve configuration issues again.
//        "You should configure settings in the UI and restart KeYmaera X." +
//        "Or specify the paths explicitly from command line by running\n" +
//        "  java -jar keymaerax.jar -mathkernel pathtokernel -jlink pathtojlink")
    }
    val libDir = config.get("libDir") // doesn't need to be defined
    initialized = link.init(linkName, libDir)
  }

  /** Closes the connection to Mathematica */
  override def shutdown() = {
    mQE.shutdown()
    mCEX.shutdown()
    mODE.shutdown()
    mSim.shutdown()
    mSolve.shutdown()
    mAlgebra.shutdown()
    mSimplify.shutdown()
    //@note last, because we want to shut down all executors (tool threads) before shutting down the JLink interface
    link.shutdown()
    initialized = false
  }

  /** Quantifier elimination on the specified formula, returns an equivalent quantifier-free formula plus Mathematica input/output as evidence */
  override def qeEvidence(formula: Formula): (Formula, Evidence) = mQE.qeEvidence(formula)

  /** Returns a formula describing the symbolic solution of the specified differential equation system.
   * @param diffSys The differential equation system
   * @param diffArg The independent variable of the ODE, usually time
   * @param iv Names of initial values per variable, e.g., x -> x_0
   * @return The solution, if found. None otherwise.
   */
  override def diffSol(diffSys: DifferentialProgram, diffArg: Variable,
                       iv: Predef.Map[Variable, Variable]): Option[Formula] = mODE.diffSol(diffSys, diffArg, iv)

  override def deriveBy(term: Term, v: Variable): Term = mODE.deriveBy(term, v)

  /**
   * Returns a counterexample for the specified formula.
   * @param formula The formula.
   * @return A counterexample, if found. None otherwise.
   */
  override def findCounterExample(formula: Formula): Option[Predef.Map[NamedSymbol, Term]] = mCEX.findCounterExample(formula)

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
  override def simulate(initial: Formula, stateRelation: Formula, steps: Int = 10, n: Int = 1): Simulation = mSim.simulate(initial, stateRelation, steps, n)

  /**
    * Returns a list of simulated states, where consecutive states in the list satisfy 'stateRelation'. The state
    * relation is a modality-free first-order formula. The simulation starts in the specified initial state.
    * @param initial The initial state: concrete values .
    * @param stateRelation A first-order formula describing the relation between consecutive states. The relationship
    *                      is by name convention: postfix 'pre': prior state; no postfix: posterior state.
    * @param steps The length of the simulation run (i.e., number of states).
    * @return A list (length 'steps') of simulated states.
    */
  override def simulateRun(initial: SimState, stateRelation: Formula, steps: Int = 10): SimRun = mSim.simulateRun(initial, stateRelation, steps)

  override def solve(equations: Formula, vars: List[Expression]): Option[Formula] = mSolve.solve(equations,vars)
  override def quotientRemainder(term: Term, div: Term, x:Variable): (Term,Term) = mAlgebra.quotientRemainder(term,div,x)
  override def groebnerBasis(polynomials: List[Term]): List[Term] = mAlgebra.groebnerBasis(polynomials)
  override def polynomialReduce(polynomial: Term, GB: List[Term]): Term = mAlgebra.polynomialReduce(polynomial, GB)
  override def simplify(expr: Expression, assumptions: List[Formula]): Expression = mSimplify.simplify(expr, assumptions)
  override def simplify(expr: Formula, assumptions: List[Formula]): Formula = mSimplify.simplify(expr, assumptions)
  override def simplify(expr: Term, assumptions: List[Formula]): Term = mSimplify.simplify(expr, assumptions)

  /** Restarts the MathKernel with the current configuration */
  override def restart() = link.restart()
}
