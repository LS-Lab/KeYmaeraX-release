/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.tools.ext

import org.keymaerax.core.{DifferentialProgram, Expression, Formula, NamedSymbol, Number, ODESystem, Term, Variable}
import org.keymaerax.tools.ToolInterface

/**
 * Tool for computing the symbolic solution of a differential equation system.
 *
 * @author
 *   smitsch
 * @see
 *   [[org.keymaerax.btactics.ToolProvider]]
 */
trait ODESolverTool extends ToolInterface {

  /**
   * Computes the symbolic solution of a differential equation in normal form.
   * @param diffSys
   *   The system of differential equations of the form x' = theta & H.
   * @param diffArg
   *   The name of the differential argument (dx/d diffArg = theta).
   * @param iv
   *   The variables for initial values per derivative.
   * @return
   *   The solution if found; None otherwise The solution should be a
   */
  def odeSolve(diffSys: DifferentialProgram, diffArg: Variable, iv: Map[Variable, Variable]): Option[Formula]
}

/**
 * Tool for computing the solution of an equation system.
 * @author
 *   Andre Platzer
 * @see
 *   [[org.keymaerax.btactics.ToolProvider]]
 */
trait EquationSolverTool extends ToolInterface {

  /**
   * Computes the symbolic solution of an equation system written as a conjunction of equations.
   * @param equations
   *   The system of equations as a conjunction of equations.
   * @param vars
   *   The variables or symbols to solve for. Within reason, it may also be possible to solve for compound expressions
   *   like solve for j(z).
   * @return
   *   The solution if found; None otherwise The solution should be a conjunction of explicit equations for the vars. Or
   *   a disjunction of a conjunction of explicit equations for the vars.
   * @example
   *   {{{
   *   solve("z+1=3&x+5=z-1".asFormula, Variable("z")::Variable("x")::Nil) == Some("z=2&x=-4")
   *   }}}
   */
  def solve(equations: Formula, vars: List[Expression]): Option[Formula]
}

/**
 * Tool for computing the symbolic solution of a partial differential equation system.
 * @author
 *   Andre Platzer
 * @see
 *   [[org.keymaerax.btactics.ToolProvider]]
 */
trait PDESolverTool extends ToolInterface {

  /**
   * Computes the symbolic solution of the inverse characteristic partial differential equation corresponding to an
   * ordinary differential equation.
   * @param diffSys
   *   The system of differential equations of the form x'=theta,y'=eta.
   * @return
   *   A list of solutions for `f` of the inverse characteristic PDE
   *   {{{
   *   theta*df/dx + eta*df/dy = 0
   *   }}}
   *   if found.
   */
  def pdeSolve(diffSys: DifferentialProgram): Iterator[Term]
}

/** Tool for computing Lyapunov functions. */
trait LyapunovSolverTool extends ToolInterface {

  /** Computes a Common Lyapunov Function for the switched system `sys`. */
  def genCLF(sys: List[ODESystem]): Option[Term]

  /** Computes a Lyapunov function for the switched system `sys`. */
  def genMLF(sys: List[ODESystem], trans: List[(Int, Int, Formula)]): List[Term]
}

/**
 * Counterexample generation tool for first-order real arithmetic formulas.
 * @see
 *   [[org.keymaerax.btactics.ToolProvider]]
 */
trait CounterExampleTool extends ToolInterface {

  /**
   * Returns a counterexample for the specified formula.
   * @param formula
   *   The formula of first-order real arithmetic.
   * @return
   *   A counterexample, if found. None otherwise.
   */
  def findCounterExample(formula: Formula): Option[Map[NamedSymbol, Expression]]
}

/**
 * Tool for simplifying logical and/or arithmetical expressions.
 * @author
 *   Andre Platzer
 * @see
 *   [[org.keymaerax.btactics.ToolProvider]]
 * @see
 *   [[[org.keymaerax.btactics.SimplifierV3]]
 */
trait SimplificationTool extends ToolInterface {

  /**
   * Simplifies the given expression `expr`, under the list of assumptions.
   * @param expr
   *   The formula or term to simplify.
   * @param assumptions
   *   The list of logical formulas whose conjunction is assumed to hold during the simplification. The assumptions are
   *   allowed to contain additional conjunctions.
   * @return
   *   A simplified version of `expr`.
   * @example
   *   {{{
   *   simplify("a*x^2+b^2 > a*x^3+b*abs(b)".asFormula, "x>1".asFormula :: "b>0".asFormula::Nil) == "a<0".asFormula
   *   simplify("a*x^2+b^2 > a*x^3+b*abs(b)".asFormula, "x>1 && b>0".asFormula::Nil) == "a<0".asFormula
   *   }}}
   */
  def simplify(expr: Expression, assumptions: List[Formula]): Expression
  def simplify(expr: Formula, assumptions: List[Formula]): Formula
  def simplify(expr: Term, assumptions: List[Formula]): Term
}

/**
 * Tool for computer algebraic computations.
 * @author
 *   Andre Platzer
 * @see
 *   [[org.keymaerax.btactics.ToolProvider]]
 */
trait AlgebraTool extends ToolInterface {

  /**
   * Computes the quotient and remainder of `term` divided by `div`.
   * @param term
   *   the polynomial term to divide, considered as a univariate polynomial in variable `v` with coefficients that may
   *   have other variables.
   * @param div
   *   the polynomial term to divide `term` by, considered as a univariate polynomial in variable `v` with coefficients
   *   that may have other variables.
   * @param v
   *   the variable with respect to which `term` and `div` are regarded as univariate polynomials (with coefficients
   *   that may have other variables).
   * @example
   *   {{{
   *   quotientRemainder("6*x^2+4*x+8".asTerm, "2*x".asTerm, Variable("x")) == (3*x+2, 8)
   *   // because (6*x^2+4*x+8) == (3*x+2) * (2*x) + 8
   *   // so the result of division is 3*x+2 with remainder 8
   *   }}}
   */
  def quotientRemainder(term: Term, div: Term, v: Variable): (Term, Term)

  /**
   * Computes the multivariate polynomial reduction of `polynomial` divided with respect to the set of polynomials `GB`,
   * which is guaranteed to be unique iff `GB` is a Gröbner basis. Returns the list of cofactors and the remainder.
   * Repeatedly divides the leading term of `polynomial` by a corresponding multiple of a polynomial of `GB` while
   * possible. Each individual reduction divides the leading term of `polynomial` by the required multiple of the
   * leading term of the polynomial of `GB` such that those cancel. Let l(p) be the leading monomial of p and lc(p) its
   * leading coefficient. Then each round of reduction of p:=polynomial with leading term `l*X^v` picks a polynomial g
   * in `GB` and turns it into
   * {{{
   *   p := p - l/lc(g) * X^v/l(g) * g
   * }}}
   * alias
   * {{{
   *   p := p - (l/(lc(g) * l(g)))*X^v  * g
   * }}}
   * The former leading monomial `X^v` no longer occurs in the resulting polynomial and `p` got smaller or is now 0. To
   * determine leading terms, polynomial reduction uses the same fixed monomial order that [[groeberBasis()]] uses. The
   * remainders will be unique (independent of the order of divisions) iff `GB` is a [[groeberBasis() Gröbner Basis]].
   * @param polynomial
   *   the multivariate polynomial to divide by the elements of `GB` until saturation.
   * @param GB
   *   the set of multivariate polynomials that `polynomial` will repeatedly be divided by. The result of this algorithm
   *   is particularly insightful (and has unique remainders) if `GB` is a Gröbner Basis.
   * @return
   *   (coeff, rem) where `rem` is the result of multivariate polynomial division of `polynomial` by `GB` and `coeff`
   *   are the respective coefficients of the polynomials in `GB` that explain the result. That is
   *   {{{
   *   polynomial == coeff(1)*GB(1) + coeff(2)*GB(2) + ... + coeff(n)*GB(n) + rem
   *   }}}
   *   alias
   *   {{{
   *   rem == polynomial - coeff(1)*GB(1) - coeff(2)*GB(2) - ... - coeff(n)*GB(n)
   *   }}}
   *   In addition, the remainder `rem` is small in that its leading monomial cannot be divided by leading monomials of
   *   any polynomial in `GB`. The result `rem` is unique when `GB` is a Gröbner Basis.
   * @example
   *   {{{
   *   polynomialReduce("y^3 + 2*x^2*y".asTerm, List("x^2-y".asTerm, "y^2+5".asTerm)) = ((2*y :: 2 + y), -5*y-10)
   *   // because y^3 + 2*x^2*y == (2*y) * (x^2-y) + (2+y) * (y^2+5) + (-5*y-10)
   *   }}}
   * @see
   *   [[groebnerBasis()]]
   */
  def polynomialReduce(polynomial: Term, GB: List[Term]): (List[Term], Term)

  /**
   * Computes the Gröbner Basis of the given set of polynomials (with respect to some fixed monomial order). Gröbner
   * Bases can be made unique for the fixed monomial order, when reduced, modulo scaling by constants.
   * @param polynomials,
   *   the list of polynomial terms to form a Gröbner Basis for.
   * @return
   *   The Gröbner Basis of `polynomials`. The Gröbner Basis spans the same ideal as `polynomials` but has unique
   *   remainders of polynomialReduce.
   * @see
   *   [[polynomialReduce()]]
   * @see
   *   [[https://lfcps.org/orbital/Orbital-doc/api/orbital/math/AlgebraicAlgorithms.html#groebnerBasis(java.util.Set,%20java.util.Comparator)]]
   */
  def groebnerBasis(polynomials: List[Term]): List[Term]
}

/**
 * Tool for computing symbolic derivatives (oracle for tactics).
 * @author
 *   Andre Platzer
 */
trait DerivativeTool extends ToolInterface {

  /**
   * Computes the symbolic partial derivative of the given term by `v`.
   * {{{
   *   d(term)
   *   ------
   *     dv
   * }}}
   * @param term
   *   The term whose partial derivative is sought.
   * @param v
   *   The variable to derive by.
   * @return
   *   The partial derivative of `term` by `v`.
   */
  def deriveBy(term: Term, v: Variable): Term
}

/** Simulation tool types. */
object SimulationTool {
  type SimState = Map[NamedSymbol, Number]
  type SimRun = List[SimState]
  type Simulation = List[SimRun]
}

/**
 * Simulation tool.
 * @see
 *   [[org.keymaerax.btactics.ToolProvider]]
 */
trait SimulationTool extends ToolInterface {
  import SimulationTool._

  /**
   * Returns a list of simulated states, where consecutive states in the list satisfy 'stateRelation'. The state
   * relation is a modality-free first-order formula. The simulation starts in a state where initial holds (first-order
   * formula).
   * @param initial
   *   A first-order formula describing the initial state.
   * @param stateRelation
   *   A first-order formula describing the relation between consecutive states. The relationship is by name convention:
   *   postfix 'pre': prior state; no postfix: posterior state.
   * @param steps
   *   The length of the simulation run (i.e., number of states).
   * @param n
   *   The number of simulations (different initial states) to create.
   * @return
   *   'n' lists (length 'steps') of simulated states.
   */
  def simulate(initial: Formula, stateRelation: Formula, steps: Int = 10, n: Int = 1): Simulation

  /**
   * Returns a list of simulated states, where consecutive states in the list satisfy 'stateRelation'. The state
   * relation is a modality-free first-order formula. The simulation starts in the specified initial state.
   * @param initial
   *   The initial state: concrete values .
   * @param stateRelation
   *   A first-order formula describing the relation between consecutive states. The relationship is by name convention:
   *   postfix 'pre': prior state; no postfix: posterior state.
   * @param steps
   *   The length of the simulation run (i.e., number of states).
   * @return
   *   A list (length 'steps') of simulated states.
   */
  def simulateRun(initial: SimState, stateRelation: Formula, steps: Int = 10): SimRun
}
