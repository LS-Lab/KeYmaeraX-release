/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import TacticFactory._
import Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
  * An Axiomatic ODE solver.
  * Current Limitations:
  *   * Only works in succedent positions (top-level for diamonds). I think this is only
  *     a limitation imposed by the differential tactics used herein.
  *   * Brittle when the initial ODE already has a domain constraint.
  *
  * @see Page 25 in http://arxiv.org/abs/1503.01981 for a high-level sketch.
  * @author Nathan Fulton
  * @author Stefan Mitsch
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
    val ode = s.apply(pos).asInstanceOf[Modal].program.asInstanceOf[ODESystem].ode
    val osize = odeSize(ode)

    //The position of the ODE after introducing all [x_0:=x;] assignments
    val odePosAfterInitialVals = pos ++ PosInExpr(List.fill(osize+2)(1))
    //The position of the [kyxtime:=...;] assignment after using the DS& axiom.
    val timeAssignmentPos = odePosAfterInitialVals ++ PosInExpr(0::1::1::Nil)

    addTimeVar(pos) &
    DebuggingTactics.debug("AFTER time var", ODE_DEBUGGER) &
    odeSolverPreconds(pos ++ PosInExpr(1::Nil)) &
    DebuggingTactics.debug("AFTER precondition check", ODE_DEBUGGER) &
    (cutInSoln(osize)(odePosAfterInitialVals) & DebuggingTactics.debug("Cut in a sol'n", ODE_DEBUGGER))*osize &
    DebuggingTactics.debug("AFTER cutting in all soln's", ODE_DEBUGGER) &
    (s.sub(pos) match {
      case Some(Box(_,_)) if pos.isSucc => HilbertCalculus.DW(odePosAfterInitialVals)
      case Some(Box(_,_)) if pos.isAnte => HilbertCalculus.useAt(DerivedAxioms.DWeakeningAnd, PosInExpr(0::Nil))(odePosAfterInitialVals)
      case Some(Diamond(_,_)) => TactixLibrary.useAt("DWd2 diamond differential weakening")(odePosAfterInitialVals)
    }) &
    DebuggingTactics.debug("AFTER DW", ODE_DEBUGGER) &
    simplifyPostCondition(osize)(odePosAfterInitialVals ++ PosInExpr(1::Nil)) &
    DebuggingTactics.debug("AFTER simplifying post-condition", ODE_DEBUGGER) &
    (inverseDiffCut(odePosAfterInitialVals) & DebuggingTactics.debug("did an inverse diff cut", ODE_DEBUGGER)).* &
    DebuggingTactics.debug("AFTER all inverse diff cuts", ODE_DEBUGGER) &
    RepeatTactic(inverseDiffGhost(odePosAfterInitialVals), osize) &
    DebuggingTactics.assert((s,p) => odeSize(s.apply(p)) == 1, "ODE should only have time.")(odePosAfterInitialVals) &
    DebuggingTactics.debug("AFTER all inverse diff ghosts", ODE_DEBUGGER) &
    (s.sub(pos) match {
      case Some(Box(_,_)) => HilbertCalculus.useAt("DS& differential equation solution")(odePosAfterInitialVals)
      case Some(Diamond(_,_)) => HilbertCalculus.useAt("Dsol& differential equation solution")(odePosAfterInitialVals)
    }) &
    DebuggingTactics.debug("AFTER DS&", ODE_DEBUGGER) &
    (HilbertCalculus.assignb(timeAssignmentPos) | HilbertCalculus.assignd(timeAssignmentPos) | Idioms.nil) &
    DebuggingTactics.debug("AFTER box assignment on time", ODE_DEBUGGER) &
    HilbertCalculus.assignb(pos)*(osize+2) & // all initial vals + time_0=time + time=0
    DebuggingTactics.debug("AFTER inserting initial values", ODE_DEBUGGER) &
    //@note do not simplify 0<=s<=t_ -> evolution domain (easier to recognize if we don't change evolution domain)
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

    if (!isCanonicallyLinear(ode)) DebuggingTactics.error("Expected ODE to be linear and in correct order.")
    else
      StaticSemantics.boundVars(ode).symbols.filter(_.isInstanceOf[DifferentialSymbol]).map({case DifferentialSymbol(v) => v}).
        foldLeft[BelleExpr](Idioms.nil)((a, b) => a & TactixLibrary.discreteGhost(b)(pos))
  })

  //endregion

  //region Setup time variable

  /** Rewrites [{c}]p to [{c, t'=1}]p.
    * The positional argument should point to the location of c, NOT the location of the box.
    * This tactic should work at any top-level position and also in any context.
    *
    * @note If we want an initial value for time (kyxtime:=0) then this is the place to add that functionality.
    */
  val addTimeVar = TacticFactory.anon ((pos: Position, s:Sequent) => {
    s.sub(pos ++ PosInExpr(0::Nil)) match {
      case Some(x: DifferentialProgram) => //ok
      case Some(x: ODESystem) => //ok
      case _ => throw AxiomaticODESolverExn(s"setupTimeVar should only be called on differential programs without an existing time variable but found ${s.apply(pos)} of type ${s.apply(pos).getClass}.")
    }

    val t = TacticHelper.freshNamedSymbol(TIMEVAR, s)

    s.sub(pos) match {
      case Some(Box(_,_)) if pos.isSucc => HilbertCalculus.DGC(t, Number(1))(pos) & DLBySubst.assignbExists(Number(0))(pos)
      case Some(Box(_,_)) if pos.isAnte => HilbertCalculus.DGCa(t, Number(1))(pos) & DLBySubst.assignbAll(Number(0))(pos)
      case Some(Diamond(_,_)) => HilbertCalculus.DGCde(t, Number(1))(pos) & DLBySubst.assignbExists(Number(0))(pos)
      case _ => throw AxiomaticODESolverExn("Parent position of setupTimeVar should be a modality.")
    }
  })

  //endregion

  //region Cut in solutions

  def cutInSoln(odeSize: Int) = "cutInSoln" by ((pos: Position, s: Sequent) => {
    val system:ODESystem = s.sub(pos) match {
      case Some(Box(x: ODESystem, _)) => x
      case Some(Diamond(x: ODESystem, _)) => x
    }

    def extract(f: Formula, p: PosInExpr, n: Int): List[(Variable, Term)] =
      if (n == 0) Nil
      else extract(f, p.parent, n-1) :+ (f.sub(p) match { case Some(Box(Assign(v, t: Variable), _)) => t -> v })

    val initialConditions: Map[Variable, Term] = extract(s(pos.top), pos.inExpr.parent, odeSize+1).toMap

    val nextEqn = sortAtomicOdes(atomicOdes(system))
      .filter(_.xp.x != TIMEVAR)
      .filterNot(eqn => isSolved(eqn.xp.x, system))
      .head

    tmpmsg(s"next equation to integrate and cut: ${nextEqn.prettyString}")

    //@todo switch completely to the new integrator, so that this is a single tactic instead of a saturated tactic.
    val solnToCut =
      Integrator(initialConditions, Minus(TIMEVAR, Variable(TIMEVAR.name, Some(0))), system).find(eq => eq.left == nextEqn.xp.x)
        .getOrElse(throw new Exception(s"Could not get integrated value for ${nextEqn.xp.x} using new integration logic."))

    tmpmsg(s"Solution for ${nextEqn.prettyString} is $solnToCut")

    val diffIndPos = if (pos.isSucc) pos.top else SuccPosition.base0(s.succ.size).top

    //@note we have to cut one at a time instead of just constructing a single tactic because solutions need to be added
    //to the domain constraint for recurrences to work. IMO we should probably go for a different implementation of
    //integral and recurrence so that saturating this tactic isn't necessary, and we can just do it all in one shot.
    DifferentialTactics.diffCut(solnToCut)(pos) <(
      Idioms.nil,
      //@todo need to normalize (otherwise no constified initial conditions), but normalize is probably too much when there are other formulas around (normalize at pos)
      DebuggingTactics.debug("Normalizing", ODE_DEBUGGER) & TactixLibrary.normalize &
        DebuggingTactics.debug("diffInd", ODE_DEBUGGER) & DifferentialTactics.diffInd()(diffIndPos) & DebuggingTactics.done
      )
  })

  /**
    *
    * @param v A variable occuring in the odes program.
    * @param system An ode system.
    * @return true if the program does not already contain an = constraint (a.k.a. sol'n) for v in the evolution domain.
    */
  def isSolved(v: Variable, system: ODESystem): Boolean = {
    //Variables that don't occur in the ODE are trivially already solved
    //An occurring variable is solved when an evolution domain constraint of the form 'a = ...' exists
    !atomicOdes(system.ode).exists(_.xp.x == v) ||
      decomposeAnds(system.constraint).exists({ case Equal(l, r) => l == v case _ => false })
  }

  //endregion

  //region Simplify post-condition

  def simplifyPostCondition(odeSize: Int) = "simplifyPostCondition" by ((pos: Position, seq: Sequent) => {
    val rewrite: Provable =
      if (pos.isSucc) TactixLibrary.proveBy("(q_(f(x_)) -> p_(f(x_))) -> (q_(x_) & x_=f(x_) -> p_(x_))".asFormula,
        TactixLibrary.implyR(1) * 2 & TactixLibrary.andL(-2) & TactixLibrary.eqL2R(-3)(1) & TactixLibrary.eqL2R(-3)(-2) & TactixLibrary.prop & TactixLibrary.done)
      else TactixLibrary.proveBy("(q_(x_) & x_=f(x_)) & p_(x_) -> q_(f(x_)) & p_(f(x_))".asFormula,
        TactixLibrary.implyR(1) & TactixLibrary.andL(-1) * 2 & TactixLibrary.andR(1) & OnAll(TactixLibrary.eqR2L(-3)(1) & TactixLibrary.closeId))

    //@note compute substitution fresh on each step, single pass unification match does not work because q_(x_) before x_=f
    ("simplifyPostConditionStep" by ((pp: Position, ss: Sequent) => {
      val subst = if (pos.isSucc) (us: Option[TactixLibrary.Subst]) => ss.sub(pp) match {
        case Some(Imply(And(q, Equal(x, f)), p)) => RenUSubst(
          ("x_".asVariable, x) ::
            ("q_(.)".asFormula, q.replaceFree(x, DotTerm())) ::
            ("p_(.)".asFormula, p.replaceFree(x, DotTerm())) ::
            ("f(.)".asTerm, f.replaceFree(x, DotTerm())) ::
            Nil)
      } else (us: Option[TactixLibrary.Subst]) => ss.sub(pp) match {
        case Some(And(And(q, Equal(x, f)), p)) => RenUSubst(
          ("x_".asVariable, x) ::
            ("q_(.)".asFormula, q.replaceFree(x, DotTerm())) ::
            ("p_(.)".asFormula, p.replaceFree(x, DotTerm())) ::
            ("f(.)".asTerm, f.replaceFree(x, DotTerm())) ::
            Nil)
      }
      TactixLibrary.useAt("ANON", rewrite, if (pp.isSucc) PosInExpr(1::Nil) else PosInExpr(0::Nil), subst)(pp)
    }))(pos)*odeSize & SimplifierV2.simpTac(pos)
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
      //@todo need to normalize (constify initial conditions), but normalize might be too much if other formulas are around
      DebuggingTactics.debug("inverse normalize", ODE_DEBUGGER) & TactixLibrary.normalize &
        DebuggingTactics.debug("inverse diffInd", ODE_DEBUGGER) & DifferentialTactics.diffInd()(1) & DebuggingTactics.done /* Show precond of diff cut */
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
    def checkResult(ode: DifferentialProgram, y_DE: AtomicDifferentialProgram) = DebuggingTactics.assertProvableSize(1) &
      DebuggingTactics.debug(s"[inverseDiffGhost] Finished trying to eliminate $y_DE from the ODE.", ODE_DEBUGGER) &
      DebuggingTactics.assert((s,p) => odeSize(s.apply(p)) == odeSize(ode)-1, "[inverseDiffGhost] Size of ODE should have decreased by one after an inverse diff ghost step.")(pos)

    s.sub(pos) match {
      case Some(f@Box(ODESystem(ode@DifferentialProduct(y_DE: AtomicODE, c), q), p)) if pos.isSucc =>
        val axiomName = "DG inverse differential ghost implicational"
        //Cut in the right-hand side of the equivalence in the [[axiomName]] axiom, prove it, and then performing rewriting.
        TactixLibrary.cutAt(Forall(y_DE.xp.x::Nil, f))(pos) <(
          DebuggingTactics.debug(s"[inverseDiffGhost] Trying to eliminate $y_DE from the ODE via an application of $axiomName.", ODE_DEBUGGER) &
          HilbertCalculus.useExpansionAt(axiomName)(pos)
          ,
          HilbertCalculus.useAt("all eliminate")(pos.topLevel ++ PosInExpr(0 +: pos.inExpr.pos)) & TactixLibrary.useAt(DerivedAxioms.implySelf)(pos.top) & TactixLibrary.closeT & DebuggingTactics.done
          ) & checkResult(ode, y_DE)
      case Some(Box(ODESystem(ode@DifferentialProduct(y_DE: AtomicODE, c), q), p)) if pos.isAnte =>
        //@note must substitute manually since DifferentialProduct reassociates (see cutAt) and therefore unification won't match
        val subst = (us: Option[TactixLibrary.Subst]) =>
          RenUSubst(
            ("y_".asTerm, y_DE.xp.x) ::
            ("b(|y_|)".asTerm, y_DE.e) ::
            ("q(|y_|)".asFormula, q) ::
            (DifferentialProgramConst("c", Except("y_".asVariable)), c) ::
            ("p(|y_|)".asFormula, p) ::
            Nil)

        //Cut in the right-hand side of the equivalence in the [[axiomName]] axiom, prove it, and then performing rewriting.
        HilbertCalculus.useAt(", commute", PosInExpr(1::Nil))(pos) &
        TactixLibrary.cutAt(Exists(y_DE.xp.x::Nil, Box(ODESystem(DifferentialProduct(c, y_DE), q), p)))(pos) <(
          HilbertCalculus.useAt("DG differential ghost constant", PosInExpr(1::Nil), subst)(pos)
          ,
          TactixLibrary.cohideR('Rlast) & TactixLibrary.CMon(pos.inExpr) & TactixLibrary.implyR(1) &
            TactixLibrary.existsR(y_DE.xp.x)(1) & TactixLibrary.closeId
          ) & checkResult(ode, y_DE)
      case Some(f@Diamond(ODESystem(ode@DifferentialProduct(y_DE: AtomicODE, c), q), p)) =>
        val axiomName = "DGd diamond differential ghost"
        //Cut in the right-hand side of the equivalence in the [[axiomName]] axiom, prove it, and then performing rewriting.
        FOQuantifierTactics.universalGen(Some(y_DE.xp.x), y_DE.xp.x)(pos) &
        TactixLibrary.cutAt(Diamond(ODESystem(c, q), p))(pos) <(
          TactixLibrary.skip
          ,
          DebuggingTactics.debug(s"[inverseDiffGhost] Trying to eliminate $y_DE from the ODE via an application of $axiomName.", ODE_DEBUGGER) &
          TactixLibrary.cohideR('Rlast) & TactixLibrary.equivifyR(1) &
            TactixLibrary.useAt(",d commute")(1, pos.inExpr ++ PosInExpr(1::0::Nil)) &
            TactixLibrary.CE(pos.inExpr) & TactixLibrary.byUS("DGd diamond differential ghost") & TactixLibrary.done
        ) & checkResult(ode, y_DE)
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

  //endregion
}
