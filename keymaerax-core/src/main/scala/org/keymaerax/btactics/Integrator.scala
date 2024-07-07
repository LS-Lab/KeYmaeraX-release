/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.Logging
import org.keymaerax.bellerophon.TacticInapplicableFailure
import org.keymaerax.btactics.helpers.DifferentialHelper._
import org.keymaerax.core.StaticSemantics.freeVars
import org.keymaerax.core._
import org.keymaerax.infrastruct.SubstitutionHelper
import org.keymaerax.tools.Tool
import org.keymaerax.tools.ext.ODESolverTool

/**
 * Solves the initial value problem for systems of differential equations.
 *
 * @author
 *   Nathan Fulton
 */
object Integrator extends Logging {

  /**
   * Integrates the differential equation and returns the solution as a list of equalities for each of the primed
   * variables occuring in the system.
   * @param initialValues
   *   Initial conditions for each of the variables that occur primed in the ODE.
   * @param system
   *   The ODE system. @todo this could be a DifferentialProgram instead because we never use the contraint.
   * @return
   *   The solution as a list of equalities, one for each of the primed variables.
   */
  def apply(initialValues: Map[Variable, Term], diffArg: Term, system: ODESystem): List[Equal] = {
    val sortedOdes = sortAtomicOdes(atomicOdes(system), Variable("kyxtime"))
    val primedVars = sortedOdes.map(ode => ode.xp.x).filter(_ != diffArg)
    val initializedVars = initialValues.keySet
    val timerVars = StaticSemantics.freeVars(diffArg)

    assert(primedVars.forall(initializedVars.contains), "All primed vars should be initialized.")

    sortedOdes.foldLeft[List[Equal]](Nil)((solvedComponents, ode) => {
      if (timerVars.contains(ode.xp.x)) { solvedComponents }
      else if (containsSolvedComponents(ode.e, solvedComponents)) {
        val xPrime = ode.e // as in the RHS of x' = xPrime
        val xPrimeWithoutDependentVariables = replaceSolvedDependentVariables(xPrime, solvedComponents)
        Equal(
          ode.xp.x,
          Plus(
            integrator(
              xPrimeWithoutDependentVariables,
              (
                diffArg,
                SimplifierV3.termSimp(diffArg, SimplifierV3.emptyCtx, SimplifierV3.defaultTaxs)._1,
                StaticSemantics.freeVars(diffArg).toSet,
              ),
              getPrimedVariables(system).toSet,
            ),
            initialValues(ode.xp.x),
          ),
        ) +: solvedComponents
      } else { Equal(ode.xp.x, Plus(Times(ode.e, diffArg), initialValues(ode.xp.x))) +: solvedComponents }
    })
  }

  /**
   * Glue code that implements the [[org.keymaerax.tools.ext.ODESolverTool]] interface using the Integrator.
   *
   * @todo
   *   untested
   */
  def diffSol(diffSys: DifferentialProgram, diffArg: Variable, iv: Map[Variable, Variable]): Option[Formula] = {
    apply(iv, diffArg, ODESystem(diffSys)).foldLeft[Formula](True)((fml, eqn) => And(fml, eqn)) match {
      case True => None
      case And(l, r) =>
        // throw away the initial True
        if (l != True) throw new TacticInapplicableFailure("Expected the left-most component to be a True.")
        Some(r)
    }
  }

  /**
   * Returns true if `t` contains variables that have solutions in `solvedComponents`
   * @param t
   *   The term to analyze.
   * @param solvedComponents
   *   Should be a list of equalities with Variables on the LHS.
   */
  private def containsSolvedComponents(t: Term, solvedComponents: List[Equal]) = {
    assert(solvedComponents.forall(eq => eq.left.isInstanceOf[Variable]))
    val solutions = conditionsToValues(solvedComponents)

    freeVars(t).toSet.exists(solutions.keySet.contains)
  }

  private def replaceSolvedDependentVariables(t: Term, eqns: List[Equal]): Term = {
    val solutions = conditionsToValues(eqns)
    solutions.foldLeft[Term](t)((newT, op) => {
      val v = op._1
      val t = op._2
      logger.debug(s"Replacing $v with $t in $newT")
      SubstitutionHelper.replaceFree(newT)(v, t)
    })
  }

  /**
   * A syntactic integrator for @todo something like sums of terms over polynomials univariable in t.
   *
   * @todo
   *   rename
   * @param term
   *   The term
   * @param time
   *   Time variable, simplified time variable, and free variables of time
   * @param primedVars
   *   Primed variables of the ODE system
   * @return
   *   Integral term dt
   */
  private def integrator(term: Term, time: (Term, Term, Set[Variable]), primedVars: Set[Variable]): Term = {
    val t = time._1
    val tsimp = time._2
    val (simp, _) = SimplifierV3.termSimp(term, SimplifierV3.emptyCtx, SimplifierV3.defaultTaxs)
    val dx = time._3 ++ primedVars
    simp match {
      case e if StaticSemantics.freeVars(e).intersect(dx).isEmpty => Times(e, t)
      case e if e == t || e == tsimp => Divide(Power(e, Number(2)), Number(2))
      case Plus(l, r) => Plus(integrator(l, time, primedVars), integrator(r, time, primedVars))
      case Minus(l, r) => Minus(integrator(l, time, primedVars), integrator(r, time, primedVars))
      case Neg(c) => Neg(integrator(c, time, primedVars))
      case Times(c, x) if StaticSemantics.freeVars(c).intersect(dx).isEmpty => Times(c, integrator(x, time, primedVars))
      case Times(x, c) if StaticSemantics.freeVars(c).intersect(dx).isEmpty => Times(c, integrator(x, time, primedVars))
      case Times(_, _) =>
        throw new IllegalArgumentException("Cannot integrate terms with non-constant multiplication factor")
      case Power(base, exp) if StaticSemantics.freeVars(exp).intersect(dx).isEmpty =>
        exp match {
          case Number(n) if n != -1 => Divide(Power(base, Number(n + 1)), Number(n + 1))
          case Number(n) if n == -1 => throw new IllegalArgumentException("Cannot integrate terms with exponent -1")
          case e => Divide(Power(base, Plus(e, Number(1))), Plus(e, Number(1)))
        }
      case Power(_, exp) if !StaticSemantics.freeVars(exp).intersect(dx).isEmpty =>
        throw new IllegalArgumentException("Cannot integrate terms with non-constant exponents")
      case Divide(num, Number(denom)) => integrator(num, time, primedVars) match {
          case Divide(n, Number(d)) => Divide(n, Number(denom * d))
          case r => Divide(r, Number(denom))
        }
      case Divide(num, denom) if StaticSemantics.freeVars(denom).intersect(dx).isEmpty =>
        Divide(integrator(num, time, primedVars), denom)
      case Divide(num, Power(base, Number(exp))) => integrator(Times(num, Power(base, Number(-exp))), time, primedVars)
      case Divide(num, Power(base, exp)) => integrator(Times(num, Power(base, Neg(exp))), time, primedVars)
      case Divide(_, _) => throw new IllegalArgumentException("Cannot integrate terms with non-constant denominator")
    }
  }
}

class IntegratorODESolverTool extends Tool with ODESolverTool {

  /** @inheritdoc */
  override val name: String = "IntegratorDiffSolutionTool"

  /**
   * Computes the symbolic solution of a differential equation in normal form.
   *
   * @param diffSys
   *   The system of differential equations of the form x' = theta & H.
   * @param diffArg
   *   The name of the differential argument (dx/d diffArg = theta).
   * @param iv
   *   The initial values per derivative.
   * @return
   *   The solution if found; None otherwise
   */
  override def odeSolve(
      diffSys: DifferentialProgram,
      diffArg: Variable,
      iv: Map[Variable, Variable],
  ): Option[Formula] = { Some(Integrator(iv, diffArg, ODESystem(diffSys, True)).reduce[Formula]((l, r) => And(l, r))) }

  /** @inheritdoc */
  override def restart(): Unit = {}

  /** @inheritdoc */
  override def shutdown(): Unit = {}

  /** @inheritdoc */
  override def isInitialized: Boolean = true

  /** @inheritdoc */
  override def cancel(): Boolean = true
}
