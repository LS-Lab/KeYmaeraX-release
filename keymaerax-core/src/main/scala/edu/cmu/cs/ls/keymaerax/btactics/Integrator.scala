/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._
import DifferentialHelper._
import StaticSemantics.freeVars

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
  def apply(initialValues: Map[Variable, Term], system: ODESystem): List[Equal] = {
    val sortedOdes = sortAtomicOdes(atomicOdes(system))
    val primedVars = sortedOdes.map(ode => ode.xp.x)
    val initializedVars = initialValues.keySet
    val timer = timeVar(system).getOrElse(throw new Exception("System needs a time variable."))

    assert(primedVars.filterNot(x => initializedVars contains x).isEmpty, "All primed vars should be initialized.")

    sortedOdes.foldLeft[List[Equal]](Nil)((solvedComponents, ode) => {
      if(timer == ode.xp.x)
        solvedComponents
      else if(containsSolvedComponents(ode.e, solvedComponents)) {
        val xPrime = ode.e //as in the RHS of x' = xPrime
        val xPrimeWithoutDependentVariables = replaceSolvedDependentVariables(xPrime, solvedComponents)
        Equal(ode.xp.x, Plus(integrator(xPrimeWithoutDependentVariables, timer, system), initialValues(ode.xp.x))) +: solvedComponents
      }
      else {
        Equal(ode.xp.x, Plus(Times(ode.e, timer), initialValues(ode.xp.x))) +: solvedComponents
      }
    })
  }

  /**
    * Glue code that implements the [[edu.cmu.cs.ls.keymaerax.tools.DiffSolutionTool]] interface using the Integrator.
    * @todo untested
    */
  def diffSol(diffSys: DifferentialProgram, diffArg: Variable, iv: Map[Variable, Variable]): Option[Formula] = {
    //Ensure that diffArg is what the Integrator will consider to be the independent variable.
    if(timeVar(diffSys) != diffArg)
      throw new AxiomaticODESolver.AxiomaticODESolverExn(s"Expected ${diffArg.prettyString} to be the time variable of the system ${diffSys.prettyString}")

    apply(iv, ODESystem(diffSys)).foldLeft[Formula](True)((fml, eqn) => And(fml, eqn)) match {
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
  private def integrator(term : Term, t : Variable, system: ODESystem) : Term = term match {
    case Plus(l, r) => Plus(integrator(l, t, system), integrator(r, t, system))
    case Minus(l, r) => Minus(integrator(l, t, system), integrator(r, t, system))
    case Times(c, x) if x.equals(t) && !StaticSemantics.freeVars(c).contains(t) => Times(Divide(c, Number(2)), Power(x, Number(2)))
    case Times(c, Power(x, exp)) if x.equals(t) && !StaticSemantics.freeVars(exp).contains(t) && !StaticSemantics.freeVars(c).contains(t) => {
      val newExp = exp match {
        case Number(n) => Number(n+1)
        case _ => Plus(exp, Number(1))
      }
      Times(Divide(c, newExp), Power(t, newExp))
    }
    case Neg(c) => Neg(integrator(c, t, system))
    case Power(base, exp) => exp match {
      case Number(n) =>
        if(n == 1) integrator(base, t, system)
        else       Times(Divide(Number(1), Number(n+1)), integrator(Power(base, Number(n-1)), t, system))
      case _ => throw new Exception("Cannot integrate terms with non-number exponents!")
    }
    case x: Term => {
      val fvs = StaticSemantics.freeVars(x).toSet.filter(_.isInstanceOf[Variable]).map(_.asInstanceOf[Variable])
      if(!containsPrimedVariables(fvs, system))
        Times(x,t)
      else
        throw new Exception("Expected that recurrences would be solved so that derivatives don't ever mention other primed variables.")
    }
  }
}
