/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper._
import StaticSemantics.freeVars
import edu.cmu.cs.ls.keymaerax.tools.{ODESolverTool, Tool, ToolBase}

/**
  * Solves the initial value problem for systems of differential equations.
  *
  * @author Nathan Fulton
  */
object Integrator {
  /**
    * Integrates the differential equation and returns the solution as a list of equalities for each of the primed variables occuring in the system.
    * @param initialValues Initial conditions for each of the variables that occur primed in the ODE.
    * @param system The ODE system. @todo this could be a DifferentialProgram instead because we never use the contraint.
    * @return The solution as a list of equalities, one for each of the primed variables.
    */
  def apply(initialValues: Map[Variable, Term], diffArg: Term, system: ODESystem): List[Equal] = {
    val sortedOdes = sortAtomicOdes(atomicOdes(system), Variable("kyxtime"))
    val primedVars = sortedOdes.map(ode => ode.xp.x).filter(_ != diffArg)
    val initializedVars = initialValues.keySet
    val timerVars = StaticSemantics.freeVars(diffArg)

    assert(primedVars.forall(initializedVars.contains), "All primed vars should be initialized.")

    sortedOdes.foldLeft[List[Equal]](Nil)((solvedComponents, ode) => {
      if (timerVars.contains(ode.xp.x)) {
        solvedComponents
      } else if (containsSolvedComponents(ode.e, solvedComponents)) {
        val xPrime = ode.e //as in the RHS of x' = xPrime
        val xPrimeWithoutDependentVariables = replaceSolvedDependentVariables(xPrime, solvedComponents)
        Equal(ode.xp.x, Plus(integrator(xPrimeWithoutDependentVariables, diffArg, system), initialValues(ode.xp.x))) +: solvedComponents
      }
      else {
        Equal(ode.xp.x, Plus(Times(ode.e, diffArg), initialValues(ode.xp.x))) +: solvedComponents
      }
    })
  }

  /**
    * Glue code that implements the [[edu.cmu.cs.ls.keymaerax.tools.ODESolverTool]] interface using the Integrator.
 *
    * @todo untested
    */
  def diffSol(diffSys: DifferentialProgram, diffArg: Variable, iv: Map[Variable, Variable]): Option[Formula] = {
    apply(iv, diffArg, ODESystem(diffSys)).foldLeft[Formula](True)((fml, eqn) => And(fml, eqn)) match {
      case True => None
      case And(l,r) => {
        //throw away the initial True
        if(l != True) throw new AxiomaticODESolver.AxiomaticODESolverExn("Expected the left-most component to be a True.")
        Some(r)
      }
    }
  }

  /** Returns true if `t` contains variables that have solutions in `solvedComponents`
    * @param solvedComponents Should be a list of equalities with Variables on the LHS. */
  private def containsSolvedComponents(t: Term, solvedComponents: List[Equal]) = {
    assert(solvedComponents.forall(eq => eq.left.isInstanceOf[Variable]))
    val solutions = conditionsToValues(solvedComponents)

    freeVars(t)
      .toSet
      .map((x: NamedSymbol) => x.asInstanceOf[Variable])
      .find((x: Variable) => solutions.keySet.contains(x))
      .nonEmpty
  }

  private def replaceSolvedDependentVariables(t: Term, eqns : List[Equal]): Term = {
    val solutions = conditionsToValues(eqns)
    solutions.foldLeft[Term](t)((newT, op) => {
      val v = op._1
      val t = op._2
      println(s"Replacing ${v} with ${t} in ${newT}")
      SubstitutionHelper.replaceFree(newT)(v, t)
    })
  }

  private def valueFor(v: Variable, equalities: List[Equal]): Option[Equal] = equalities.find(eq => eq.left == v)
  private def hasValue(v: Variable, equalities: List[Equal]) = valueFor(v, equalities).nonEmpty

  /**
    * A syntactic integrator for @todo something like sums of terms over polynomials univariable in t.
    *
    * @todo rename
    * @param term The term
    * @param t Time variable
    * @return Integral term dt
    */
  private def integrator(term: Term, t: Term, system: ODESystem) : Term = {
    val tsimp = SimplifierV2.termSimp(t)._1
    val simp = SimplifierV2.termSimp(term)._1
    simp match {
      case e if e.equals(t) => Divide(Power(e, Number(2)),Number(2))
      case Plus(l, r) => Plus(integrator(l, t, system), integrator(r, t, system))
      case Times(c, x) if (x.equals(t) || x.equals(tsimp)) && StaticSemantics.freeVars(c).intersect(StaticSemantics.freeVars(t)).isEmpty => Times(Divide(c, Number(2)), Power(x, Number(2)))case Times(c, x) if (x.equals(t) || x.equals(tsimp)) && StaticSemantics.freeVars(c).intersect(StaticSemantics.freeVars(t)).isEmpty => Times(Divide(c, Number(2)), Power(x, Number(2)))
      case Times(c, Power(x, exp)) if (x.equals(t) || x.equals(tsimp)) && StaticSemantics.freeVars(exp).intersect(StaticSemantics.freeVars(t)).isEmpty &&
          StaticSemantics.freeVars(c).intersect(StaticSemantics.freeVars(t)).isEmpty => {
        val newExp = exp match {
          case Number(n) => Number(n+1)
          case _ => Plus(exp, Number(1))
        }
        Times(Divide(c, newExp), Power(t, newExp))
      }
      case Times(c:Number, r) => Times(c, integrator(r, t, system))
      case Times(r, c:Number) => Times(c, integrator(r, t, system))
      case Neg(c) => Neg(integrator(c, t, system))
      case Power(base, exp) => exp match {
        case Number(n) =>
          if(n == 1) integrator(base, t, system)
          else       Times(Divide(Number(1), Number(n+1)), integrator(Power(base, Number(n-1)), t, system))
        case _ => throw new Exception("Cannot integrate terms with non-number exponents!")
      }
      case Minus(l, r) => Minus(integrator(l, t, system), integrator(r, t, system))
      case x: Term => {
        val fvs = StaticSemantics.freeVars(x).toSet.filter(_.isInstanceOf[Variable])
        if(!containsPrimedVariables(fvs, system))
          Times(x,t)
        else
          throw new Exception("Expected that recurrences would be solved so that derivatives don't ever mention other primed variables.")
      }
    }
  }
}

class IntegratorODESolverTool extends ToolBase("IntegratorDiffSolutionTool") with ODESolverTool {
  /**
    * Computes the symbolic solution of a differential equation in normal form.
    *
    * @param diffSys The system of differential equations of the form x' = theta & H.
    * @param diffArg The name of the differential argument (dx/d diffArg = theta).
    * @param iv      The initial values per derivative.
    * @return The solution if found; None otherwise
    */
  override def odeSolve(diffSys: DifferentialProgram, diffArg: Variable, iv: Map[Variable, Variable]): Option[Formula] = {
    Some(Integrator(iv, diffArg, ODESystem(diffSys, True)).reduce[Formula]((l,r) => And(l,r)))
  }

  override def init(config: Map[String, String]): Unit = { initialized = true }
  override def restart(): Unit = { initialized = true }
  override def shutdown(): Unit = { initialized = false }
}
