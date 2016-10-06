/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core._

/**
 * Base trait tagging interfaces to tools.
 */
trait ToolInterface

/**
  * Tool for computing the symbolic solution of a differential equation system.
  * @author smitsch
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.ToolProvider]]
  */
trait ODESolverTool extends ToolInterface {
  /**
    * Computes the symbolic solution of a differential equation in normal form.
    * @param diffSys The system of differential equations of the form x' = theta & H.
    * @param diffArg The name of the differential argument (dx/d diffArg = theta).
    * @param iv The initial values per derivative.
    * @return The solution if found; None otherwise
    *         The solution should be a
    */
  def odeSolve(diffSys: DifferentialProgram, diffArg: Variable, iv: Map[Variable, Variable]): Option[Formula]
}

/**
  * Tool for computing the solution of an equation system.
  * @author Andre Platzer
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.ToolProvider]]
  */
trait EquationSolverTool extends ToolInterface {
  /**
    * Computes the symbolic solution of an equation system.
    * @param equations The system of equations as a conjunction of equations.
    * @param vars The variables or symbols to solve for.
    *            Within reason, it may also be possible to solve for compound expressions like solve for j(z).
    * @return The solution if found; None otherwise
    *         The solution should be a conjunction of explicit equations for the vars.
    *         Or a disjunction of a conjunction of explicit equations for the vars.
    * @example{{{
    *           solve("z+1=3&x+5=z-1".asFormula, Variable("z")::Variable("x")::Nil) == Some("z=2&x=-4")
    * }}}
    */
  def solve(equations: Formula, vars: List[Expression]): Option[Formula]
}

/**
  * Tool for computing the symbolic solution of a partial differential equation system.
  * @author Andre Platzer
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.ToolProvider]]
  */
trait PDESolverTool extends ToolInterface {
  /**
    * Computes the symbolic solution of the inverse characteristic partial differential equation corresponding to an ordinary differential equation.
    * @param diffSys The system of differential equations of the form x'=theta,y'=eta.
    * @return A list of solutions for `f` of the inverse characteristic PDE
    *         {{{
    *            theta*df/dx + eta*df/dy = 0
    *         }}}
    *         if found.
    */
  def pdeSolve(diffSys: DifferentialProgram): Iterator[Term]
}

/**
  * Quantifier elimination tool.
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.ToolProvider]]
  */
trait CounterExampleTool extends ToolInterface {
  /**
    * Returns a counterexample for the specified formula.
    * @param formula The formula.
    * @return A counterexample, if found. None otherwise.
    */
  def findCounterExample(formula: Formula): Option[Map[NamedSymbol, Term]]
}

/**
  * Tool for simplifying logical and/or arithmetical expressions.
  * @author Andre Platzer
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.ToolProvider]]
  */
trait SimplificationTool extends ToolInterface {
  /**
    * Simplifies the given expression `expr`, under the list of assumptions.
    * @param expr The formula or term to simplify.
    * @param assumptions The list of logical formulas whose conjunction is assumed to hold during the simplification.
    *                   The assumptions are allowed to contain additional conjunctions.
    * @return A simplified version of `expr`.
    * @example{{{
    *           simplify("a*x^2+b^2 > a*x^3+b*abs(b)".asFormula, "x>1".asFormula :: "b>0".asFormula::Nil) == "a<0".asFormula
    *           simplify("a*x^2+b^2 > a*x^3+b*abs(b)".asFormula, "x>1 && b>0".asFormula::Nil) == "a<0".asFormula
    * }}}
    */
  def simplify(expr: Expression, assumptions: List[Formula]): Expression
  def simplify(expr: Formula, assumptions: List[Formula]): Formula
  def simplify(expr: Term, assumptions: List[Formula]): Term
}

/**
  * Tool for computer algebraic computations.
  * @author Andre Platzer
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.ToolProvider]]
  */
trait AlgebraTool extends ToolInterface {
  /**
    * Computes the quotient and remainder of `term` divided by `div`.
    * @example{{{
    *           quotientRemainder(6*x^2+4*x+8, 2*x, x) == (3*x+2, 8)
    * }}}
    */
  def quotientRemainder(term: Term, div: Term, v: Variable): (Term, Term)

  /**
    * Computes the Gröbner Basis of the given set of polynomials (with respect to some fixed monomial order).
    * @see [[polynomialReduce()]]
    */
  def groebnerBasis(polynomials: List[Term]): List[Term]

  /**
    * Computes the multi-variate polynomial reduction of `polynomial` divided with respect to the
    * set of polynomials `GB`, which is guaranteed to be unique iff `GB` is a Gröbner basis. Returns the list of
    * cofactors and the remainder.
    * @see [[groebnerBasis()]]
    */
  def polynomialReduce(polynomial: Term, GB: List[Term]): (List[Term], Term)
}

/**
  * Tool for computing symbolic derivatives (oracle for tactics).
  * @author Andre Platzer
  */
trait DerivativeTool extends ToolInterface {
  /**
    * Computes the symbolic partial derivative of the given term by `v`.
    * {{{
    *   d(term)
    *   ------
    *     dv
    * }}}
    * @param term The term whose partial derivative is sought.
    * @param v The variable to derive by.
    * @return The partial derivative of `term` by `v`.
    */
  def deriveBy(term: Term, v: Variable): Term
}

object SimulationTool {
  type SimState = Map[NamedSymbol, Number]
  type SimRun = List[SimState]
  type Simulation = List[SimRun]
}

/**
  * Simulation tool.
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.ToolProvider]]
  */
trait SimulationTool extends ToolInterface {
  import SimulationTool._
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
  def simulate(initial: Formula, stateRelation: Formula, steps: Int = 10, n: Int = 1): Simulation

  /**
    * Returns a list of simulated states, where consecutive states in the list satisfy 'stateRelation'. The state
    * relation is a modality-free first-order formula. The simulation starts in the specified initial state.
    * @param initial The initial state: concrete values .
    * @param stateRelation A first-order formula describing the relation between consecutive states. The relationship
    *                      is by name convention: postfix 'pre': prior state; no postfix: posterior state.
    * @param steps The length of the simulation run (i.e., number of states).
    * @return A list (length 'steps') of simulated states.
    */
  def simulateRun(initial: SimState, stateRelation: Formula, steps: Int = 10): SimRun
}
