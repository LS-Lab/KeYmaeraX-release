/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import DifferentialHelper._
import Integrator.integrator

/**
  * An Axiomatic ODE solver (second attempt)
  *
  * @see Page 25 in http://arxiv.org/abs/1503.01981 for a high-level sketch.
  * @author Nathan Fulton
  */
object AxiomaticODESolver {
  def tmpmsg(s:String) = println(s) //@todo before deployment, remove this method.

  //implicits for "by" notation and functional application of positions to sequents/formulas.
  import TacticFactory._
  import Augmentors._

  /** The main tactic. */
  def axiomaticSolve(implicit qeTool: QETool) = "axiomaticSolve" by ((pos:Position, s:Sequent) => {
    val odePos = subPosition(pos, 0::Nil)

    addTimeVarIfNecessary(odePos) & //@todo initialize time var so that there's always a t:=0 in front. Then munge positions.
    cutInSoln(qeTool)(pos).*@(TheType())
  })

  //region Setup time variable

  /** The name of the explicit time variables. */
  private val TIMEVAR : String = "kyxtime"

  /** Adds a time variable to the ODE if there isn't one already; otherwise, does nothing.
    *
    * @see [[addTimeVar]] */
  val addTimeVarIfNecessary = "addTimeVarIfNecessary" by ((pos: Position, s:Sequent) => s(pos) match {
      case x:DifferentialProgram if timeVar(x).isEmpty => addTimeVar(pos)
      case x:DifferentialProgram if timeVar(x).nonEmpty => Idioms.nil
      case x:ODESystem if timeVar(x).isEmpty => addTimeVar(pos)
      case x:ODESystem if timeVar(x).nonEmpty => Idioms.nil
      case _ => throw AxiomaticODESolverExn("Expected DifferentialProgram or ODESystem")
  })

  /** Rewrites [{c}]p to [{c, t'=1}]p whenever the system c does not already contain a clock.
    * The positional argument should point to the location of c, NOT the location of the box.
    * This tactic should work at any top-level position and also in any context.
    *
    * @note If we want an initial value for time (kyxtime:=0) then this is the place to add that functionality.
    */
  val addTimeVar = "addTimeVar" by((pos: Position, s:Sequent) => {
    s(pos) match {
      case x:DifferentialProgram if timeVar(x).isEmpty => //ok
      case x:ODESystem if timeVar(x).isEmpty => //ok
      case _ => throw AxiomaticODESolverExn(s"setupTimeVar should only be called on differential programs without an existing time variable but found ${s(pos)} of type ${s(pos).getClass}.")
    }

    val modalityPos = parentPosition(pos)
    if(!s(modalityPos).isInstanceOf[Modal])
      throw AxiomaticODESolverExn("Parent position of setupTimeVar should be a modality.")

    val t = TacticHelper.freshNamedSymbol(Variable(TIMEVAR), s)

    s(modalityPos) match {
      case Box(_,_) => {
        HilbertCalculus.DG(t, Number(0), Number(1))(modalityPos) &
        DebuggingTactics.error("Needs exists monotone") //@todo instantiate \exists t to an assignment [t:=0] or additional antecedent.
      }
      case Diamond(_,_) => throw noDiamondsForNowExn
    }
  })

  //endregion

  //region Cut in solutions

  def cutInSoln(implicit qeTool: QETool) = "cutInSoln" by ((pos: Position, s: Sequent) => {
    assert(s(pos).isInstanceOf[Modal], s"Expected a modality but found ${s(pos).prettyString}")
    val system:ODESystem = s(pos).asInstanceOf[Modal].program match {
      case x:ODESystem => x
      case x:DifferentialProgram => ???
    }

    //@todo constrain to only true initial conditions by passing in Some(ode).
    //@todo I don't think that the extractInitialConditions code picks up a=0 as an initial condtion for x'=v,v'=a. Check this when changing None.
    val initialConditions = s.ante.flatMap(extractInitialConditions(None)).toList

    val nextEqn = sortAtomicOdes(atomicODEs(system))
      .filter(eqn => !isOne(eqn.e))
      .filter(eqn => isUnsolved(eqn.xp.x, system))
      .head

    tmpmsg(s"next equation to integrate and cut: ${nextEqn.prettyString}")

    //@todo switch completely to the new integrator, so that this is a single tactic instead of a saturated tactic.
    val solnToCut =
      Integrator(conditionsToValues(initialConditions), system).find(eq => eq.left == nextEqn.xp.x)
        .getOrElse(throw new Exception(s"Could not get integrated value for ${nextEqn.xp.x} using new integration logic."))
//    val solnToCut = Equal(nextEqn.xp.x, integralOf(nextEqn.xp.x, system, initialConditions))

    tmpmsg(s"Soltuion for ${nextEqn.prettyString} is ${solnToCut}")

    //@note we have to cute one at a time instead of just constructing a single tactic because solutions need to be added
    //to the domain constraint for recurrences to work. IMO we should probably go for a different implementation of
    //integral and recurrence so that saturating this tactic isn't necessary, and we can just do it all in one shot.
    s(pos) match {
      case Box(ode, postcond) => {
        DifferentialTactics.diffCut(solnToCut)(pos) <(
          Idioms.nil,
          DebuggingTactics.debug("Doing diffInd on ", true) & DifferentialTactics.diffInd(qeTool)(pos) & DebuggingTactics.assertProved
        )
      }
      case Diamond(ode, postcond) => throw noDiamondsForNowExn
    }
  })

  /**
    * @param ode
    * @return The list of atomic differential equations occurring in the differential program.
    * @author Nathan Fulton
    */
  private def odeConstraints(ode : Program) : List[Formula] = ode match {
    case AtomicODE(x,e)                   => Nil
    case ODESystem(ode, constraint)       => constraint :: Nil
    case DifferentialProduct(left, right) => odeConstraints(left) ++ odeConstraints(right)
    case _                                => throw AxiomaticODESolverExn("Expected AtomicODE, ODESystem, or DifferentialProduct.") //@todo what about other differential programs?
  }

  /**
    * @param ode
    * @return The list of atomic differential equations occurring in the differential program.
    * @author Nathan Fulton
    */
  def atomicODEs(ode : Program) : List[AtomicODE] = ode match {
    case AtomicODE(x, e)                  => AtomicODE(x,e) :: Nil
    case ODESystem(ode, constraint)       => atomicODEs(ode)
    case DifferentialProduct(left, right) => atomicODEs(left) ++ atomicODEs(right)
    case _                                => throw AxiomaticODESolverExn("Expected AtomicODE, ODESystem, or DifferentialProduct.") //@todo what about other differential programs?
  }

  /**
    *
    * @param v A variable occuring in the odes program.
    * @param system An ode system.
    * @return true if the program does not already contain an = constraint (a.k.a. sol'n) for v in the evolution domain.
    */
  def isUnsolved(v : Variable, system : ODESystem) = {
    val odes = atomicODEs(system.ode)
    if(odes.find(_.xp.x.equals(v)).isEmpty) false //Variables that don't occur in the ODE are trivially already solved.
    else if(timeVar(system.ode).equals(v)) false //Don't need to solve for the time var.
    //In non-special cases, check for a = evolution domain constraint in the ode.
    else {
      val vConstraints = odeConstraints(system).flatMap(decomposeAnds).find(_ match {
        case Equal(l, r) => l.equals(v)
        case _ => false
      })
      vConstraints.isEmpty
    }
  }

  //endregion

  //region Simple integrator

  /**
    * If v' = term occurs in the system of ODEs, then this function computes the integral of term.
    * Assumes that the ODEs have a time variable, that a formula of the form v=f occurs in the initialConditions formulas,
    * and that the system of odes is blah blah.
    *
    * @param v
    * @param system
    * @param initialConditions
    * @return Integral of f assuming v' = f occurs in ODEs.
    */
  def integralOf(v : Variable, system : ODESystem, initialConditions : List[Formula]) : Term = {
    val termToIntegrate = resolveRecurrences(v, system, initialConditions)
    println("Integrating term " + termToIntegrate + s" (after resolving recurrences for the equational definition of ${v.prettyString}' in the ode ${system.prettyString}")

    val t = timeVar(system) match {
      case Some(t) => t
      case None    => throw new Exception("Could not find time variable in ODEs")
    }

    val v_0 : Term = conditionsToValues(initialConditions).get(v) match {
      case Some(x) => x
      case None => throw new Exception("Could not find initial condition for " + v.name)
    }

    Plus(integrator(termToIntegrate, t, system), v_0)
  }



  /**
    * Given x' = f, replaces all variables in f with their recurrences or initial conditions.
    *
    * @param v A variable s.t. v' = f occurs in the ODEs.
    * @param system ODE(s) with a time variable (some x s.t. x' = 1).
    * @param initialConditions Any initial conditions for the ODE.
    * @return f with all variables replaced by their recurrences or initial conditions.
    */
  def resolveRecurrences(v : Variable, system : ODESystem, initialConditions : List[Formula]) : Term = {
    val odes         = atomicODEs(system)

    val time : Variable = timeVar(system) match {
      case Some(theTimeVar) => theTimeVar
      case None             => throw new Exception(s"A time variable should exist prior to calling resolveRecurrences, but none exists in ${system.prettyString}")
    }

    //The assertion message is not technically true becuase the solution would just be zero.
    //But if the variable requested is not in the ODE, it's most likely this indicates a programming error rather than
    //an honest inquiry.
    assert(odes.find(ode => ode.xp.x.equals(v)).isDefined, "Cannot solve for a variable that does not occur in the ODE")

    val primedVariables : Set[Variable] = odes.map(_.xp.x).toSet

    //Compute the free variables in the ode corresponding to v'.
    val ode = odes.find(_.xp.x.equals(v)).getOrElse(throw new Exception("Could not find ODE associated with " + v))
    val varsInOde = StaticSemantics.freeVars(ode.e).toSet.map((x : NamedSymbol) => {
      assert(x.isInstanceOf[Variable], "Only variables should occur as the child of the LHS of an ODE")
      x.asInstanceOf[Variable]
    })

    //Variables that occur in the term associated with v' and also occur primed in the ODE.
    val recurrenceVars : Set[Variable] = (varsInOde intersect primedVariables) //for lack of a better name.

    //Variables that occur in the term associated with v' but do not occur primed in the ODE.
    val nonRecurringVars : Set[Variable] = varsInOde -- recurrenceVars

    if(recurrenceVars.isEmpty) {
      // If x' = a where a is not a variable occurring in the system of odes, then the solution is
      // x = at + x_0 where t is the time variable and x_0 is the value in initialValues associated with
      val f_initValuesResolved = nonRecurringVars.foldLeft[Term](ode.e)((currTerm, x) => {
        val x_0 = initValue(initialConditions, x)
        assert(x_0.isDefined, "Need an initial condition for non-recurring variable " + x + " while solve for " + v)
        SubstitutionHelper.replaceFree(currTerm)(x, x_0.get)
      })

      f_initValuesResolved
    }
    else {
      //Replace all instance of primed variables in the term assocaited with v'
      val f_substRecurrences = recurrenceVars.foldLeft[Term](ode.e)((currTerm, x) => {
        val xSoln = recurrence(ode, initialConditions, x)
        assert(xSoln.isDefined, "Need a solution for recurring variable " + x + " while solving for " + v)
        SubstitutionHelper.replaceFree(currTerm)(x, xSoln.get)
      })
      val f_substInitValues = nonRecurringVars.foldLeft[Term](f_substRecurrences)((currTerm, x) => {
        val x_0 = initValue(initialConditions, x)
        assert(x_0.isDefined, "Need an initial condition for non-recurring variable " + x + " while solve for " + v)
        SubstitutionHelper.replaceFree(currTerm)(x, x_0.get)
      })
      f_substInitValues
    }
  }

  /**
    * @param program (An system of) odes.
    * @param initialConstraints Formulas describing initial values.
    * @param x A variable that occurs on the left hand side of some ode.
    * @return Some(term) if x = term occurs in either the ev.dom. constraint or the initial constraints. Otherwise, None.
    */
  private def recurrence(program : DifferentialProgram, initialConstraints : List[Formula], x : Variable) : Option[Term] = {
    val odeConditions = conditionsToValues(flattenAnds(odeConstraints(program)))
    val initialConditions = conditionsToValues(flattenAnds(initialConstraints))
    if(odeConditions.contains(x)) odeConditions.get(x)
    else if(initialConditions.contains(x)) initialConditions.get(x)
    else None
  }

  //endregion

  //region Misc.

  /** Exceptions thrown by the axiomatic ODE solver. */
  case class AxiomaticODESolverExn(msg: String) extends Exception(msg)
  val noDiamondsForNowExn = AxiomaticODESolverExn("No diamonds for now.")

//  def childPosition(pos: Position) =
//    if(pos.isAnte) AntePosition(pos.checkAnte.top, pos.inExpr.child)
//    else SuccPosition(pos.checkSucc.top, pos.inExpr.child)

  def parentPosition(pos: Position): Position =
    if(pos.isAnte) AntePosition(pos.checkAnte.top, pos.inExpr.parent)
    else SuccPosition(pos.checkSucc.top, pos.inExpr.parent)

  def subPosition(pos: Position, sub: PosInExpr): Position =
    if(pos.isAnte) AntePosition(pos.checkAnte.top, pos.inExpr + sub)
    else SuccPosition(pos.checkSucc.top, pos.inExpr + sub)
  def subPosition(pos: Position, sub: List[Int]): Position = subPosition(pos, PosInExpr(sub))

  //endregion
}

/*
Todo list:
 1. Implement differential ghosts and inverse differential ghosts.
 2. Add t' = 1 if it's not already present
 3. Re-order the ODE so that it's in the correct dependency ordering.
 ...
 */