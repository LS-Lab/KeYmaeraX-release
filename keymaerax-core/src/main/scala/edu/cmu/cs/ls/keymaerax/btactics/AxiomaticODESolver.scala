/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import TacticFactory._
import Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
  * An Axiomatic ODE solver.
  * Current Limitations:
  *   * Only works in top-level succedent positions. I think this is only
  *     a limitation imposed by the differential tactics used herein.
  *   * Initial conditions must already exist. Stefan has a work-around
  *     that ghosts in initial conditions already in the diffSolve tactic.
  *   * Brittle when the initial ODE already has a domain constraint.
  *
  * @see Page 25 in http://arxiv.org/abs/1503.01981 for a high-level sketch.
  * @author Nathan Fulton
  */
object AxiomaticODESolver {
  private val ODE_DEBUGGER = false

  /** The name of the explicit time variables. */
  private val TIMEVAR: Variable = "kyxtime".asVariable

  /** Temporary messages that aren't even necessarily useful to have in verbose ODE debugger mode. */
  private def tmpmsg(s:String) = if(ODE_DEBUGGER) println(s)

  //region The main tactic

  def apply() = axiomaticSolve()

  def axiomaticSolve() = "AxiomaticODESolver" by ((pos:Position, s:Sequent) => {
    val odePos = subPosition(pos, 0::Nil)
    val ode = s.apply(pos).asInstanceOf[Modal].program.asInstanceOf[ODESystem].ode
    val sizeOfTimeExplicitOde = odeSize(ode) + 1

    //The position of the [kyxtime:=...;] assignment after using the DS& axiom.
    val timeAssignmentPos = subPosition(pos, PosInExpr(0::1::1::Nil))
    val isAssignment: Expression => Boolean = { case Box(Assign(_,_), _) => true case _ => false }

    addTimeVarIfNecessary(odePos) &
    DebuggingTactics.debug("AFTER time var", ODE_DEBUGGER) &
    odeSolverPreconds(pos) &
    DebuggingTactics.debug("AFTER precondition check", ODE_DEBUGGER) &
    (cutInSoln(pos) & DebuggingTactics.debug("Cut in a sol'n", ODE_DEBUGGER)).* &
    DebuggingTactics.debug("AFTER cutting in all soln's", ODE_DEBUGGER) &
    (s.sub(pos) match {
      case Some(Box(_,_)) => HilbertCalculus.DW(pos)
      case Some(Diamond(_,_)) => TactixLibrary.useAt("DWd2 diamond differential weakening")(pos)
    }) &
    DebuggingTactics.debug("AFTER DW", ODE_DEBUGGER) &
    simplifyPostCondition(odeSize(ode))(pos ++ PosInExpr(1::Nil)) &
    DebuggingTactics.debug("AFTER simplifying post-condition", ODE_DEBUGGER) &
    (inverseDiffCut(pos) & DebuggingTactics.debug("did an inverse diff cut", ODE_DEBUGGER)).* &
    DebuggingTactics.debug("AFTER all inverse diff cuts", ODE_DEBUGGER) &
    RepeatTactic(inverseDiffGhost(pos), sizeOfTimeExplicitOde - 1) &
    DebuggingTactics.assert((s,p) => odeSize(s.apply(p)) == 1, "ODE should only have time.")(pos) &
    DebuggingTactics.debug("AFTER all inverse diff ghosts", ODE_DEBUGGER) &
    (s.sub(pos) match {
      case Some(Box(_,_)) => HilbertCalculus.useAt("DS& differential equation solution")(pos)
      case Some(Diamond(_,_)) => HilbertCalculus.useAt("Dsol& differential equation solution")(pos)
    }) &
    DebuggingTactics.debug("AFTER DS&", ODE_DEBUGGER) &
    (HilbertCalculus.assignb(timeAssignmentPos) | HilbertCalculus.assignd(timeAssignmentPos) | Idioms.nil) &
    DebuggingTactics.debug("AFTER box assignment on time", ODE_DEBUGGER) &
    TactixLibrary.exhaustiveEqL2R(hide=true)('Llast)*sizeOfTimeExplicitOde &
    // boxes can simplify a little further (could simplify even more -> simplification tactic)
    Idioms.?(DebuggingTactics.assert((s: Sequent, p: Position) => s.sub(p) match {
               case Some(Equal(timeVar, _)) => true
               case _ => false }, "Cannot simplify, don't know kyxtime value")('Llast) &
             TactixLibrary.exhaustiveEqL2R(hide=true)('Llast)) &
    DebuggingTactics.debug("AFTER rewriting initial equalities", ODE_DEBUGGER) &
    //@note do not simplify 0<=s<=t_, result can be surprising
    SimplifierV2.simpTac(pos ++ PosInExpr(0::1::0::0::1::Nil)) &
    SimplifierV2.simpTac(pos ++ PosInExpr(0::1::1::Nil)) &
    DebuggingTactics.debug("AFTER final simplification", ODE_DEBUGGER)
  })

  //endregion

  //region Preconditions

  val odeSolverPreconds =  TacticFactory.anon ((pos: Position, s: Sequent) => {
    val ode: DifferentialProgram = s.sub(pos) match {
      case Some(Box(ODESystem(o, _), _)) => o
      case Some(Diamond(ODESystem(o, _), _)) => o
      case sub => throw BelleUserGeneratedError("Expected [] or <> modality at position " + pos + ", but got " + sub)
    }

    if(!isCanonicallyLinear(ode))
      DebuggingTactics.error("Expected ODE to be linear and in correct order.")
    else
      StaticSemantics.boundVars(ode).symbols.filter(_.isInstanceOf[DifferentialSymbol]).map({case DifferentialSymbol(v) => v}).
        foldLeft[BelleExpr](Idioms.nil)((a, b) => a & (TactixLibrary.discreteGhost(b)(pos) & DLBySubst.assignEquality(pos)))
  })

  //endregion

  //region Setup time variable

  /** Adds a time variable to the ODE if there isn't one already; otherwise, does nothing.
    *
    * @see [[addTimeVar]] */
  val addTimeVarIfNecessary = TacticFactory.anon ((pos: Position, s:Sequent) => s.apply(pos) match {
      case x:DifferentialProgram => addTimeVar(pos)
      case x:ODESystem => addTimeVar(pos)
      case _ => throw AxiomaticODESolverExn(s"Expected DifferentialProgram or ODESystem but found ${s.apply(pos).getClass}")
  })

  /** Rewrites [{c}]p to [{c, t'=1}]p whenever the system c does not already contain a clock.
    * The positional argument should point to the location of c, NOT the location of the box.
    * This tactic should work at any top-level position and also in any context.
    *
    * @note If we want an initial value for time (kyxtime:=0) then this is the place to add that functionality.
    */
  val addTimeVar = TacticFactory.anon ((pos: Position, s:Sequent) => {
    s.sub(pos) match {
      case Some(x: DifferentialProgram) => //ok
      case Some(x: ODESystem) => //ok
      case _ => throw AxiomaticODESolverExn(s"setupTimeVar should only be called on differential programs without an existing time variable but found ${s.apply(pos)} of type ${s.apply(pos).getClass}.")
    }

    val t = TacticHelper.freshNamedSymbol(TIMEVAR, s)
    val modalityPos = parentPosition(pos)

    s.sub(modalityPos) match {
      case Some(Box(_,_)) =>
        HilbertCalculus.DGC(t, Number(1))(modalityPos) &
        DLBySubst.assignbExists(Number(0))(modalityPos) &
        DLBySubst.assignEquality(modalityPos)
      case Some(Diamond(_,_)) =>
        HilbertCalculus.DGCd(t, Number(1))(modalityPos) &
        TactixLibrary.allR(modalityPos)
      case _ => throw AxiomaticODESolverExn("Parent position of setupTimeVar should be a modality.")
    }
  })

  //endregion

  //region Cut in solutions

  val cutInSoln = "cutInSoln" by ((pos: Position, s: Sequent) => {
    assert(s.apply(pos).isInstanceOf[Modal], s"Expected a modality but found ${s.apply(pos).prettyString}")
    val system:ODESystem = s.sub(pos) match {
      case Some(Box(x:ODESystem, _)) => x
      case Some(Diamond(x:ODESystem, _)) => x
      case _ => ???
    }

    //@todo constrain to only true initial conditions by passing in Some(ode).
    //@todo I don't think that the extractInitialConditions code picks up a=0 as an initial condtion for x'=v,v'=a. Check this when changing None.
    val initialConditions = s.ante.flatMap(extractInitialConditions(None)).toList

    val nextEqn = sortAtomicOdes(atomicOdes(system))
      .filter(eqn => eqn.xp.x != TIMEVAR)
      .filter(eqn => isUnsolved(eqn.xp.x, system))
      .head

    tmpmsg(s"next equation to integrate and cut: ${nextEqn.prettyString}")

    //@todo switch completely to the new integrator, so that this is a single tactic instead of a saturated tactic.
    val solnToCut =
      Integrator(conditionsToValues(initialConditions), Minus(TIMEVAR, Variable(TIMEVAR.name, Some(0))), system).find(eq => eq.left == nextEqn.xp.x)
        .getOrElse(throw new Exception(s"Could not get integrated value for ${nextEqn.xp.x} using new integration logic."))

    tmpmsg(s"Solution for ${nextEqn.prettyString} is $solnToCut")

    //@note we have to cut one at a time instead of just constructing a single tactic because solutions need to be added
    //to the domain constraint for recurrences to work. IMO we should probably go for a different implementation of
    //integral and recurrence so that saturating this tactic isn't necessary, and we can just do it all in one shot.
    DifferentialTactics.diffCut(solnToCut)(pos) <(
      Idioms.nil,
      DebuggingTactics.debug("Doing diffInd on ", ODE_DEBUGGER) & DifferentialTactics.diffInd()(pos) & DebuggingTactics.done
      )
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
    *
    * @param v A variable occuring in the odes program.
    * @param system An ode system.
    * @return true if the program does not already contain an = constraint (a.k.a. sol'n) for v in the evolution domain.
    */
  def isUnsolved(v : Variable, system : ODESystem) = {
    val odes = atomicOdes(system.ode)
    if(odes.find(_.xp.x.equals(v)).isEmpty) false //Variables that don't occur in the ODE are trivially already solved.
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

  //region diffCut lower bound on time

  /** Adds t>=0 to the differential equation's domain constraint.
    * @todo Why is this necessary? It's not included in the paper proof. */
  val cutInTimeLB = "cutInTimeLB" by ((pos: Position, s: Sequent) => {
    assert(s.apply(pos).isInstanceOf[Modal], s"Expected modality at position ${pos} of ${s.prettyString}")
    assert(s.apply(pos).asInstanceOf[Modal].program.isInstanceOf[ODESystem], s"Expected modality to contain ODE System but it did not in ${s(pos)}")

    val system = s.apply(pos).asInstanceOf[Modal].program.asInstanceOf[ODESystem]

    val lowerBound = Number(0) //@todo check that this is actually the lower bound. Lower bound could be symbolic.
    val timer = TIMEVAR

    //@todo this won't work in the case where we cut in our own time until Stefan's code for isntantiating exisentials is added in...
    s.apply(pos).asInstanceOf[Modal] match {
      case Box(_,_) => TactixLibrary.diffCut(GreaterEqual(timer, lowerBound))(pos) <(Idioms.nil, TactixLibrary.diffInd()(pos) & DebuggingTactics.done)
      case Diamond(_,_) => throw noDiamondsForNowExn
    }
  })

  //endregion

  //region Simplify post-condition

  def simplifyPostCondition(odeSize: Int) = "simplifyPostCondition" by ((pos: Position, seq: Sequent) => {
    val rewrite = TactixLibrary.proveBy("(q_(||) -> p_(f(x_))) -> (q_(||) & x_=f(x_) -> p_(x_))".asFormula,
      TactixLibrary.implyR(1)*2 & TactixLibrary.andL(-2) & TactixLibrary.eqL2R(-3)(1) & TactixLibrary.prop)
    TactixLibrary.useAt(rewrite, PosInExpr(1::Nil))(pos)*odeSize & TactixLibrary.useAt(DerivedAxioms.trueImplies)(pos) &
    SimplifierV2.simpTac(pos)
  })

  //endregion

  //region Inverse diff cuts

  private val inverseDiffCut = "inverseDiffCut" by ((pos: Position, s: Sequent) => {
    val idc: BelleExpr = s.sub(pos) match {
      //@note evolution domain constraints are of the form true&solution or ...&solution
      case Some(f@Box(ODESystem(ode, And(_, constraint)), p)) if isPartOfSoln(ode, constraint) =>
        HilbertCalculus.useExpansionAt("DC differential cut")(pos)
      case Some(f@Diamond(ODESystem(ode, And(_, constraint)), p)) if isPartOfSoln(ode, constraint) =>
        HilbertCalculus.useExpansionAt("DCd diamond differential cut")(pos)
    }

    idc <(
      Idioms.nil, /* Branch with no ev dom contraint */
      DifferentialTactics.diffInd()(1) & DebuggingTactics.done /* Show precond of diff cut */
      )
  })

  /** Returns true iff f is part of the cut-in solution for the ODE. */
  private def isPartOfSoln(ode: DifferentialProgram, f: Formula): Boolean = f match {
    case Equal(t1, t2) => atomicOdes(ode).exists(a => a.xp.x == t1 || a.xp.x == t2)
    case _ => false
  }

  //endregion

  //region Inverse diff ghosts

  /**
    * Removes the left-most DE from a system of ODEs:
    * {{{
    *   [v'=a,t'=1 & q]p
    *   ---------------------- inserverDiffGhost
    *   [x'=v,v'=a,t'=1 & q]p
    * }}}
    */
  val inverseDiffGhost = "inverseDiffGhost" by ((pos: Position, s: Sequent) => {
    /* Note: Constructing our own substitution because the default substitution seems to get at least g(||) wrong. */
    def subst(y_DE: AtomicODE, c: DifferentialProgram, q: Formula, p: Formula)(r: RenUSubst) = {
      if(ODE_DEBUGGER) println("[inverseDiffGhost] input to subst:    " + r)
      val (y, a, b) = DifferentialHelper.parseGhost(y_DE)
      val renaming = RenUSubst(URename("y_".asVariable, y))
      val result = renaming ++
        RenUSubst(USubst(
          "a(|y_|)".asTerm    ~> renaming(a) ::
          "b(|y_|)".asTerm    ~> renaming(b) ::
          "q(|y_|)".asFormula ~> q ::
          DifferentialProgramConst("c", Except("y_".asVariable)) ~> c ::
          "p(|y_|)".asFormula ~> p ::
          Nil))

      if(ODE_DEBUGGER) println("[inverseDiffGhost] output from subst: " + result)
      result
    }

    s.sub(pos) match {
      case Some(f@Box(ODESystem(ode@DifferentialProduct(y_DE: AtomicODE, c), q), p)) =>
        val axiomName = "DG inverse differential ghost implicational"
        //Cut in the right-hand side of the equivalence in the [[axiomName]] axiom, prove it, and then performing rewriting.
        TactixLibrary.cutAt(Forall(y_DE.xp.x::Nil, f))(pos) <(
          DebuggingTactics.debug(s"[inverseDiffGhost] Trying to eliminate $y_DE from the ODE via an application of $axiomName.", ODE_DEBUGGER) &
          HilbertCalculus.useExpansionAt(axiomName)(pos)
          ,
          TactixLibrary.implyR(pos) & HilbertCalculus.useAt("all eliminate")('Llast) & TactixLibrary.close & DebuggingTactics.done
          ) &
          DebuggingTactics.assertProvableSize(1) &
          DebuggingTactics.debug(s"[inverseDiffGhost] Finished trying to eliminate $y_DE from the ODE.", ODE_DEBUGGER) &
          DebuggingTactics.assert((s,p) => odeSize(s.apply(p)) == odeSize(ode)-1, "[inverseDiffGhost] Size of ODE should have decreased by one after an inverse diff ghost step.")(pos)
      case Some(f@Diamond(ODESystem(ode@DifferentialProduct(y_DE: AtomicODE, c), q), p)) =>
        val axiomName = "DGd diamond differential ghost"
        //Cut in the right-hand side of the equivalence in the [[axiomName]] axiom, prove it, and then performing rewriting.
        FOQuantifierTactics.universalGen(Some(y_DE.xp.x), y_DE.xp.x)(pos) &
        TactixLibrary.cutAt(Diamond(ODESystem(c, q), p))(pos) <(
          TactixLibrary.skip
          ,
          DebuggingTactics.debug(s"[inverseDiffGhost] Trying to eliminate $y_DE from the ODE via an application of $axiomName.", ODE_DEBUGGER) &
          TactixLibrary.cohideR('Rlast) & TactixLibrary.equivifyR(1) & TactixLibrary.useAt(",d commute")(1, 1::0::Nil) & DebuggingTactics.print("Foo") &
            TactixLibrary.byUS("DGd diamond differential ghost"/*, subst(y_DE, c, q, p)*/) & TactixLibrary.done
        ) &
          DebuggingTactics.assertProvableSize(1) &
          DebuggingTactics.debug(s"[inverseDiffGhost] Finished trying to eliminate $y_DE from the ODE.", ODE_DEBUGGER) &
          DebuggingTactics.assert((s,p) => odeSize(s.apply(p)) == odeSize(ode)-1, "[inverseDiffGhost] Size of ODE should have decreased by one after an inverse diff ghost step.")(pos)
    }
  })

  private def odeSize(e: Expression): Int = odeSize(e.asInstanceOf[Modal].program.asInstanceOf[ODESystem].ode)
  private def odeSize(ode: DifferentialProgram): Int = ode match {
    case x:DifferentialProgramConst => 1
    case x:AtomicODE => 1
    case x:DifferentialProduct => odeSize(x.left) + odeSize(x.right)
  }

  //endregion

  //region Misc.

  /** Exceptions thrown by the axiomatic ODE solver. */
  case class AxiomaticODESolverExn(msg: String) extends Exception(msg)
  val noDiamondsForNowExn = AxiomaticODESolverExn("No diamonds for now.")

  def parentPosition(pos: Position): Position =
    if(pos.isAnte) AntePosition(pos.checkAnte.top, pos.inExpr.parent)
    else SuccPosition(pos.checkSucc.top, pos.inExpr.parent)

  def subPosition(pos: Position, sub: PosInExpr): Position =
    if(pos.isAnte) AntePosition(pos.checkAnte.top, pos.inExpr ++ sub)
    else SuccPosition(pos.checkSucc.top, pos.inExpr ++ sub)
  def subPosition(pos: Position, sub: List[Int]): Position = subPosition(pos, PosInExpr(sub))

  //endregion
}
