/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon._
import org.keymaerax.core._
import TacticFactory._
import org.keymaerax.infrastruct.Augmentors._
import org.keymaerax.btactics.AnonymousLemmas._
import org.keymaerax.btactics.helpers.DifferentialHelper._
import org.keymaerax.btactics.TactixLibrary._
import org.keymaerax.infrastruct._
import org.keymaerax.parser.Declaration
import org.keymaerax.parser.StringConverter._
import org.keymaerax.pt.ElidingProvable

import scala.annotation.tailrec
import scala.collection.immutable._

/**
 * An Axiomatic ODE solver. Current limitations:
 *   - No support for explicit-form diamond ODEs/box ODEs in context: `<{x'=0*x+1}>P, ![{x'=0*x+1}]P`
 *
 * @see
 *   Page 25 in http://arxiv.org/abs/1503.01981 for a high-level sketch.
 * @author
 *   Nathan Fulton
 * @author
 *   Stefan Mitsch
 */
object AxiomaticODESolver {
  private val ODE_DEBUGGER = false

  private val namespace = "odesolver"

  private lazy val simplifier = SimplifierV3.simpTac()

  /** Simplifier that does not simplify dependent formulas F->(F<->true) to true */
  private lazy val postCondSimplifier = SimplifierV3.simpTac(Nil,
    SimplifierV3.composeIndex(SimplifierV3.baseIndexWithoutDepFmlSimp, SimplifierV3.boolIndex, SimplifierV3.cmpIndex),
    SimplifierV3.defaultTaxs)

  /** The name of the explicit time variables. */
  //WARNING global mutable state. Changed by addTimeVar. Do not run 2 AxiomaticODESolvers sequentially!
  private var TIMEVAR: Variable = "kyxtime".asVariable

  /** The name of the ODE duration variable. */
  private lazy val DURATION: Variable = "t_".asVariable

  /** The name of the evolution domain time variable 0<=s_<=t_ */
  private lazy val EVOL_DOM_TIME: Variable = "s_".asVariable

  //region The main tactic

  def apply(): DependentPositionTactic = axiomaticSolve()

  /** [[DifferentialEquationCalculus.solve]] and [[DifferentialEquationCalculus.solveEnd]]. */
  private[btactics] def axiomaticSolve(instEnd: Boolean = false): DependentPositionTactic =
  // name was (if (instEnd) "solveEnd" else "solve")
      anon ((pos: Position, s: Sequent) => {
    s.sub(pos) match {
      case Some(Diamond(ODESystem(_, True), _)) =>
        useAt(Ax.diamond, PosInExpr(1::Nil))(pos) &
        boxAxiomaticSolve(instEnd)(pos ++ PosInExpr(0::Nil)) &
        pushNegation(pos) &
        simplifier(pos)
      case Some(Diamond(ODESystem(_, _), _)) =>
        useAt(Ax.diamond, PosInExpr(1::Nil))(pos) &
        boxAxiomaticSolve(instEnd)(pos ++ PosInExpr(0::Nil)) &
        pushNegation(pos) &
        // pushNegation may turn disjunction into implication
        (anon ((p: Position, s: Sequent) => s.sub(p) match {
          case Some(Or(_, _)) => useAt(Ax.PC10, PosInExpr(1::Nil))(p)
          case Some(Imply(_, _)) => useAt(Ax.implyExpand)(p) & useAt(Ax.PC10, PosInExpr(1::Nil))(p)
          case _ => skip
        }))(pos ++ PosInExpr(0::1::1::Nil)) &
        simplifier(pos)
      case _ => boxAxiomaticSolve(instEnd)(pos)
    }
  })

  /** Normalize into expected shape for diamond solve, after solving dual box ODE. */
  private def pushNegation: DependentPositionTactic = anon ((pos: Position, s: Sequent) => {
    s.sub(pos) match {
      case Some(Not(Not(_))) => useAt(Ax.doubleNegation)(pos)
      case Some(Not(Forall(x, p))) if  StaticSemantics.boundVars(p).intersect(x.toSet).isEmpty => useAt(Ax.notAll)(pos) & pushNegation(pos ++ PosInExpr(0::Nil))
      case Some(Not(Forall(x, p))) if !StaticSemantics.boundVars(p).intersect(x.toSet).isEmpty =>
        x.map(DLBySubst.stutter(_)(pos ++ PosInExpr(0::0::Nil))).reduce[BelleExpr](_ & _) & // stutter
        useAt(Ax.notAll)(pos) &
        assignb(pos ++ PosInExpr(0::0::Nil))*x.size & // unstutter
        pushNegation(pos ++ PosInExpr(0::Nil))
      case Some(Not(Exists(x, p))) if  StaticSemantics.boundVars(p).intersect(x.toSet).isEmpty => useAt(Ax.notExists)(pos) & pushNegation(pos ++ PosInExpr(0::Nil))
      case Some(Not(Exists(x, p))) if !StaticSemantics.boundVars(p).intersect(x.toSet).isEmpty =>
        x.map(DLBySubst.stutter(_)(pos ++ PosInExpr(0::0::Nil))).reduce[BelleExpr](_ & _) & // stutter
        useAt(Ax.notExists)(pos) &
        assignb(pos ++ PosInExpr(0::0::Nil))*x.size & // unstutter
        pushNegation(pos ++ PosInExpr(0::Nil))
      case Some(Not(Imply(_, _))) => useAt(Ax.notImply)(pos) &
        pushNegation(pos ++ PosInExpr(0::Nil)) & pushNegation(pos ++ PosInExpr(1::Nil))
      case Some(Not(And(_, _))) => useAt(Ax.notAnd)(pos) &
        pushNegation(pos ++ PosInExpr(0::Nil)) & pushNegation(pos ++ PosInExpr(1::Nil)) &
        // heuristic: turn !p|q into -> to create more natural assign equality look \forall x (x=y -> q(x)) instead of \forall x (x!=y | q(x))
        (anon ((p: Position, s: Sequent) => s.sub(p) match {
          case Some(Or(Not(Equal(_, _)), q)) if !q.isInstanceOf[Not] => useAt(Ax.implyExpand, PosInExpr(1::Nil))(p)
          case _ => skip
        }))(pos)
      case Some(Not(Or(_, _))) => useAt(Ax.notOr)(pos) &
        pushNegation(pos ++ PosInExpr(0::Nil)) & pushNegation(pos ++ PosInExpr(1::Nil))
      case _ => skip
    }
  })

  /** Axiomatic solver for box ODEs. */
  private def boxAxiomaticSolve(instEnd: Boolean = false): DependentPositionTactic = anon ((pos: Position, s: Sequent) => {
    val (ode, q, post) = s.sub(pos) match {
      case Some(Box(ODESystem(o, qq), pp)) => (o, qq, pp)
      case Some(f) => throw new TacticInapplicableFailure("Position " + pos + " does not point to a differential equation, but to " + f.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a differential equation")
    }

    val osize = odeSize(ode)

    val ord = dfs(ode) match {
      case None => throw new TacticInapplicableFailure("ODE not known to have polynomial solutions. Differential equations with cyclic dependencies need invariants instead of solve().")
      case Some(ord) => ord
    }

    //The position of the ODE after introducing all [x_0:=x;] assignments
    val odePosAfterInitialVals = pos ++ PosInExpr(List.fill(osize + 2)(1))
    //The position of the [kyxtime:=...;] assignment after using the DS& axiom.
    val timeAssignmentPos = odePosAfterInitialVals ++ PosInExpr(0 :: 1 :: 1 :: Nil)

    val polarity = (if (pos.isSucc) 1 else -1) * FormulaTools.polarityAt(s(pos.top), pos.inExpr)

    val renameDuration =
      if (StaticSemantics.symbols(s(pos.top)).contains(DURATION) && StaticSemanticsTools.boundAt(s(pos.top), pos.inExpr).contains(DURATION)) {
        @tailrec
        def findDurationBoundPos(seed: Position): Option[Position] = s.sub(seed) match {
          case Some(Forall(v, _)) if v.contains(DURATION) => Some(seed)
          case Some(Exists(v, _)) if v.contains(DURATION) => Some(seed)
          case Some(Box(Assign(v, _), _)) if v == DURATION => Some(seed)
          case Some(Box(AssignAny(v), _)) if v == DURATION => Some(seed)
          case Some(Diamond(Assign(v, _), _)) if v == DURATION => Some(seed)
          case Some(Diamond(AssignAny(v), _)) if v == DURATION => Some(seed)
          case _ => seed.parent match {
            case Some(parent) => findDurationBoundPos(parent)
            case None => None //@note not reachable since tested for symbols(s(pos.top).contains(DURATION)
          }
        }
        findDurationBoundPos(pos) match {
          case Some(dpos) => boundRename(DURATION, TacticHelper.freshNamedSymbol(DURATION, s))(dpos)
          case None => skip
        }
      } else nil

    val assumptions = if (pos.isAnte) s.ante.patch(pos.index0, Nil, 1) else s.ante
    val odeVars = StaticSemantics.boundVars(ode).toSet + DURATION + EVOL_DOM_TIME
    val consts = assumptions.filter(_.isFOL).flatMap(FormulaTools.conjuncts).
      filter(StaticSemantics.freeVars(_).intersect(odeVars).toSet.isEmpty).
      // filter quantified, avoid substitution clash in dI on formulas of the shape (\forall x x>0)'
      filter({ case _: Quantified => false case _ => true}).
      // keep only relevant (occur in RHS of ODE, evolution domain, or postcondition)
      filter(StaticSemantics.symbols(_).intersect(StaticSemantics.symbols(ode) ++ StaticSemantics.symbols(q) ++ StaticSemantics.symbols(post)).nonEmpty).
      map(SimplifierV3.simpWithDischarge(IndexedSeq[Formula](), _, SimplifierV3.defaultFaxs, SimplifierV3.defaultTaxs)._1).
      filterNot(f => f==True || f==False). //@todo improve DI
      reduceOption(And).getOrElse(True)

    //@note do not simplify dependent formulas in postcondition, since diamond solver relies on duplicated formulas
    val simpSol = postCondSimplifier(pos ++ (if (q == True) PosInExpr(0 :: 1 :: Nil) else PosInExpr(0 :: 1 :: 1 :: Nil)))
    val simpEvolDom =
      if (q == True) TactixLibrary.skip //evolution domain constraint is trivial, so simplification is not necessary.
      else if (instEnd) simplifier(pos ++ PosInExpr(0 :: Nil))
      else simplifier(pos ++ PosInExpr(0::1::0::0::1::Nil))

    lazy val allExtract1 = remember("\\forall x_ (p_(x_) -> q_()) -> (\\forall x_ p_(x_) -> q_())".asFormula,
      implyR(1)*2 & allL(-1) & allL(-2) & prop & done, namespace)
    lazy val allExtract2 = remember("\\forall x_ (p_(x_) -> r_(x_)&q_()) -> \\forall x_ (p_(x_)->r_(x_)) ".asFormula,
      implyR(1) & allR(1) & allL(-1) & prop & done, namespace)
    lazy val allExtract3 = remember("p_() & \\forall x_ (r_(x_) -> q_(x_)) -> \\forall x_ (r_(x_) -> q_(x_) & p_())".asFormula,
      implyR(1) & andL(-1) & allR(1) & allL(-2) & prop & done, namespace)

    lazy val imply2 = remember("(p_()->s_()&r_()) -> (p_()->(q_()->r_())->s_())".asFormula, prop & done, namespace)

    //@todo preserve consts when solving in context (requires closing const as last step of DI in context - let fails otherwise)
    val simpConsts: DependentPositionTactic = anon ((pp: Position, ss: Sequent) =>
      if (consts != True && pos.isTopLevel) ss.sub(pp) match {
        case Some(False) => TactixLibrary.skip
        case Some(_) =>
          val constsPos = if (q == True) PosInExpr(0::1::0::0::1::Nil) else PosInExpr(0::1::0::0::1::1::Nil)
          s.sub(pos) match {
            case Some(Box(ODESystem(_, qq), _)) if polarity > 0 =>
              if (qq == True) useAt(allExtract1)(pos ++ PosInExpr(0::1::0::Nil)) &
                useAt(imply2, PosInExpr(1::Nil))(pos ++ PosInExpr(0::Nil)) &
                useAt(allExtract3, PosInExpr(1::Nil))(pos) &
                //@todo pos is top level, prove that consts are true in context
                andR(pos) <(prop & done, skip)
              else skip//useAt(allExtract2)(pos ++ PosInExpr(0::1::0::Nil))
            case Some(Box(ODESystem(_, qq), _)) if polarity < 0 => skip //@todo
            case Some(e) => throw new TacticInapplicableFailure("simpConsts only applicable to box ODEs, but got " + e.prettyString)
            case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + s.prettyString)
          }
        case None => throw new IllFormedTacticApplicationException("Position " + pp + " does not point to a valid position in sequent " + ss.prettyString)
      } else TactixLibrary.skip)

    val cutConsts = consts != True && pos.isTopLevel && polarity >= 0

    DebuggingTactics.debug("SOLVE Start", ODE_DEBUGGER) &
      renameDuration &
      DebuggingTactics.debug("Renamed duration", ODE_DEBUGGER) &
      //@todo support the cases we now skip
      (if (cutConsts) DifferentialTactics.diffCut(consts)(pos) <(skip, V(Symbol("Rlast")) & prop &
        DebuggingTactics.done("Expected to prove constants invariant"))
       else TactixLibrary.skip) &
      DebuggingTactics.debug("AFTER preserving consts", ODE_DEBUGGER) &
      addTimeVar(pos) &
      DebuggingTactics.debug("AFTER time var", ODE_DEBUGGER) &
      odeSolverPreconds(ord)(pos ++ PosInExpr(1 :: Nil)) &
      DebuggingTactics.debug("AFTER precondition check", ODE_DEBUGGER) &
      (cutInSoln(osize)(odePosAfterInitialVals) & DebuggingTactics.debug("Cut in a sol'n", ODE_DEBUGGER)) &
      DebuggingTactics.debug("AFTER cutting in all soln's", ODE_DEBUGGER) &
      simplifyEvolutionDomain(osize)(odePosAfterInitialVals ++ PosInExpr(0 :: 1 :: Nil)) &
      DebuggingTactics.debug("AFTER simplifying evolution domain constraint", ODE_DEBUGGER) &
      (if (polarity > 0) HilbertCalculus.DW(odePosAfterInitialVals)
       else if (polarity < 0) HilbertCalculus.useAt(Ax.DWeakenAnd, PosInExpr(0 :: Nil))(odePosAfterInitialVals)
       else throw new TacticInapplicableFailure("Unable to DW: unknown ODE polarity.")
      ) &
      DebuggingTactics.debug("AFTER DW", ODE_DEBUGGER) &
      simplifyPostCondition(osize)(odePosAfterInitialVals ++ PosInExpr(1 :: Nil)) &
      DebuggingTactics.debug("AFTER simplifying post-condition", ODE_DEBUGGER) &
      //@todo box ODE in succedent: could shortcut with diffWeaken (but user-definable if used or not)
      (inverseDiffCut(osize)(odePosAfterInitialVals) & DebuggingTactics.debug("did an inverse diff cut", ODE_DEBUGGER))*(osize + (if (cutConsts) 1 else 0)) &
      DebuggingTactics.debug("AFTER all inverse diff cuts", ODE_DEBUGGER) &
      simplifier(odePosAfterInitialVals ++ PosInExpr(0 :: 1 :: Nil)) &
      DebuggingTactics.debug("AFTER simplifying evolution domain 2", ODE_DEBUGGER) &
      RepeatTactic(DifferentialTactics.inverseDiffGhost(odePosAfterInitialVals), osize) &
      DebuggingTactics.assert((s, p) => odeSize(s.apply(p)) == 1, "ODE should only have time.")(odePosAfterInitialVals) &
      DebuggingTactics.debug("AFTER all inverse diff ghosts", ODE_DEBUGGER) &
      HilbertCalculus.useAt(Ax.DS)(odePosAfterInitialVals) &
      DebuggingTactics.debug("AFTER DS&", ODE_DEBUGGER) &
      (HilbertCalculus.assignb(timeAssignmentPos) | HilbertCalculus.assignd(timeAssignmentPos) | Idioms.nil) &
      DebuggingTactics.debug("AFTER box assignment on time", ODE_DEBUGGER) &
      HilbertCalculus.assignb(pos) * (osize + 2) & // all initial vals + time_0=time + time=0
      DebuggingTactics.debug("AFTER inserting initial values", ODE_DEBUGGER) &
      simpConsts(pos ++ PosInExpr(0::1::0::0::1::Nil)) &
      DebuggingTactics.debug("AFTER simplifying consts", ODE_DEBUGGER) &
      (if (q == True && consts == True) TactixLibrary.useAt(Ax.implyTrue)(pos ++ PosInExpr(0 :: 1 :: 0 :: 0 :: Nil)) &
        TactixLibrary.useAt(Ax.allV)(pos ++ PosInExpr(0 :: 1 :: 0 :: Nil)) &
        (TactixLibrary.useAt(Ax.trueImply)(pos ++ PosInExpr(0 :: 1 :: Nil))
          | TactixLibrary.useAt(Ax.trueAnd)(pos ++ PosInExpr(0 :: 1 :: Nil)))
      else if (instEnd && q != True) TactixLibrary.allL(DURATION)(pos ++ PosInExpr(0 :: 1 :: 0 :: Nil)) &
        TactixLibrary.useAt(Ax.flipLessEqual)(pos ++ PosInExpr(0 :: 1 :: 0 :: 0 :: 0 :: Nil))
      else TactixLibrary.skip) &
      DebuggingTactics.debug("AFTER handling evolution domain", ODE_DEBUGGER) &
      simpSol & simpEvolDom &
      DebuggingTactics.debug("AFTER final simplification", ODE_DEBUGGER)
  })

  //endregion

  //region Preconditions

  class Cycle extends Exception {}

  private def myFreeVars(term:Term): SetLattice[Variable] = {
    term match {
      /* Hack: ODE solving actually works ok sometimes if semantically free variables are treated as free.
       * If we have something in the linear form expected by DG, then leave it around and see if it solves.
       * some of the case studies use this. */
      case Plus(Times(Number(n),_), e) if n == 0 => StaticSemantics.freeVars(e)
      case e => StaticSemantics.freeVars(e)
    }
  }

  private def dfsLoop(odes: List[AtomicODE], visited: Set[Variable], active: Set[Variable],
                      curr: Variable, acc: List[Variable]): Option[(Set[Variable], List[Variable])] = {
    if (visited.contains(curr)) {
      None
    } else if (acc.contains(curr)) {
      Some(visited + curr, acc)
    } else {
      val currRhs = odes.find(_.xp.x == curr).get.e
      val incoming = odes.filter(ode => myFreeVars(currRhs).contains(ode.xp.x)).map(_.xp.x)
      if (incoming.exists(active.contains)) throw new Cycle
      val (vis, sorted) = incoming.foldLeft[(Set[Variable], List[Variable])]((visited + curr, acc))({case ((vis2, acc2), x) =>
        dfsLoop(odes, vis2, active + curr, x, acc2) match {
          case Some(xx)  => xx
          case _  => (vis2, acc2)
        }
      })
      Some(vis, curr :: sorted)
    }
  }

  def alist(ode: DifferentialProgram): Option[List[AtomicODE] ]= {
    ode match {
      case _: DifferentialProgramConst => None
      case DifferentialProduct(ode1, ode2) =>
        (alist(ode1), alist(ode2)) match {
          case ((_, None)) => None
          case ((None, _)) => None
          case (Some(x), Some(y)) => Some(x ++ y)
        }
      case ode: AtomicODE => Some(List(ode))
    }
  }
  def ofAtoms(atoms:List[AtomicODE]):DifferentialProgram = {
    atoms match {
      case Nil => ???
      case ode::Nil => ode
      case ode::rest => DifferentialProduct(ode, ofAtoms(rest))
    }
  }

  private def dfsOuterLoop(odes: List[AtomicODE], visited: Set[Variable], acc: List[Variable]): Option[(Set[Variable], List[Variable])] = {
    if (visited.size == odes.size) {
      Some(visited, acc)
    } else {
      val curr = odes.find(ode => !visited.contains(ode.xp.x)).get.xp.x
      dfsLoop(odes, Set(), Set(curr), curr, acc) match {
        case None => None
        case Some((vis, a)) => dfsOuterLoop(odes, vis ++ visited, a)
      }
    }
  }

  //@todo performance bottleneck
  def dfs(ode: DifferentialProgram): Option[List[Variable]] = {
    try {
      alist(ode) match {
        case Some(atomics) => dfsOuterLoop(atomics, Set(),  Nil).map(_._2) match {
          case None => None
          case Some(vs) =>
            // ODE solving tactic expects kyxtime variable to stay at the end. Let's keep it that way since it never depends on other variables
            if (vs.exists(_.name == "kyxtime")) Some(vs.filter(_.name != "kyxtime") ++ vs.filter(_.name == "kyxtime").sortBy(_.index))
            else Some(vs)
        }
        case None => None
      }
    } catch  {
      case _: Cycle => None
    }
  }

  def sortSubst(dom:Formula, post:Formula, context:DifferentialProgram, ode1:DifferentialProgram, ode2:DifferentialProgram):USubst = USubst(List(
    SubstitutionPair(DifferentialProgramConst("c_"), context),
    SubstitutionPair(DifferentialProgramConst("d_"), ode1),
    SubstitutionPair(DifferentialProgramConst("e_"), ode2),
    SubstitutionPair(UnitPredicational("q", AnyArg), dom),
    SubstitutionPair(UnitPredicational("p", AnyArg), post)))

  def sortAxiomInst(dom:Formula, post:Formula, context:DifferentialProgram, ode1:DifferentialProgram, ode2:DifferentialProgram):Provable = {
    Provable.axioms(", sort")(sortSubst(dom, post, context, ode1,ode2))
  }

  def commSubst(dom:Formula, post:Formula, ode1:DifferentialProgram, ode2:DifferentialProgram):USubst = USubst(List(
    SubstitutionPair(DifferentialProgramConst("c"), ode1),
    SubstitutionPair(DifferentialProgramConst("d"), ode2),
    SubstitutionPair(UnitPredicational("q", AnyArg), dom),
    SubstitutionPair(UnitPredicational("p", AnyArg), post)))

  def commAxiomInst(dom:Formula, post:Formula, ode1:DifferentialProgram, ode2:DifferentialProgram):Provable = {
    Provable.axioms(", commute")(commSubst(dom, post, ode1, ode2))
  }

  def splitODEAt(ode:DifferentialProgram, v:Variable):(List[AtomicODE], List[AtomicODE], List[AtomicODE]) = {
    ode match {
      case DifferentialProduct(AtomicODE(DifferentialSymbol(v2),e), tail) => {
        if (v == v2) {
          (Nil, List(AtomicODE(DifferentialSymbol(v2),e)), alist(tail).get)
        } else {
          splitODEAt(tail, v) match {
            /* If variable already found, add ourselves to the context */
            case (l1, o::l2, l3) => (AtomicODE(DifferentialSymbol(v2),e)::l1, o::l2, l3)
            /* If variable not yet found, add ourselves to the tail */
            case (Nil, Nil, l3) => (Nil, Nil, AtomicODE(DifferentialSymbol(v2),e)::l3)
            /* Should never happen */
            case _ => ???
          }
        }
      }
      case AtomicODE(DifferentialSymbol(v2), e) => {
        if (v == v2) {
          (Nil, List(AtomicODE(DifferentialSymbol(v2), e)), Nil)
        } else {
          (Nil, Nil, List(AtomicODE(DifferentialSymbol(v2), e)))
        }
      }
    }
  }

  /* Produces a tactic that transforms  [ODE & Q]P (at pos) into [sorted_ode & Q]P
  * This works in selection-sort style: At step i, pull the variable whose final position should be i to the end of ODE*/
  def selectionSort(dom:Formula, post:Formula, ode: DifferentialProgram, goal: List[Variable], pos:Position):BelleExpr = {
    val insts =
      goal.foldLeft((ode, TactixLibrary.nil, Nil:List[Provable]))({ case ((ode, e,insts), v) =>
        val (l1, l2, l3) = splitODEAt(ode, v)
        // Already at end - no commuting necessary
        if(l3.isEmpty) {
          (ode, e, insts)
        // Currently at beginning: use regular ODE commute axiom, not contextual ODE commute
        } else if(l1.isEmpty) {
          val (ode2, ode3) = (ofAtoms(l2), ofAtoms(l3))
          val pr = commAxiomInst(dom, post, ode2,ode3)
          val newOde = DifferentialProduct(ode3, ode2)
          (newOde, e, pr::insts)
        // Neither at beginning nor end: use contextual ODE commute axiom.
        } else {
          val (ode1, ode2, ode3) = (ofAtoms(l1), ofAtoms(l2), ofAtoms(l3))
          val pr = sortAxiomInst(dom, post, ode1,ode2,ode3)
          val newOde = DifferentialProduct(ode1, DifferentialProduct(ode3, ode2))
          (newOde, e, pr::insts)
        }
      })._3
    // The above gives us a chain of equivalences on ODES: piece the chain together.
    insts.map(pr => HilbertCalculus.useAt(ElidingProvable(pr, Declaration(Map.empty)), PosInExpr(0::Nil))(pos)).foldLeft[BelleExpr](TactixLibrary.nil)((acc, e) => e & acc)
  }

  /* Produces a tactic that permutes ODE into canonical ordering or a tacatic that errors if ode contains cycles */
  def makeCanonical(ode: DifferentialProgram, ord: List[Variable], dom: Formula, post: Formula, pos: Position): BelleExpr = {
    DebuggingTactics.debug("Sorting to " + ord.mkString("::"), ODE_DEBUGGER) & selectionSort(dom, post, ode, ord, pos)
  }

  def odeSolverPreconds(ord: List[Variable]): DependentPositionTactic =  TacticFactory.anon ((pos: Position, s: Sequent) => {
    val (ode: DifferentialProgram, dom: Formula, post: Formula) = s.sub(pos) match {
      case Some(Box(ODESystem(o, q), p)) => (o, q, p)
      case Some(sub) => throw new TacticInapplicableFailure("Expected [] or <> modality at position " + pos + ", but got " + sub.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + s.prettyString)
    }

    val bv = StaticSemantics.boundVars(ode).symbols.filter(_.isInstanceOf[DifferentialSymbol]).map({case DifferentialSymbol(v) => v})
    val timeExtendedOrd = bv.find(_.name == TIMEVAR.name) match {
      case None => ord
      case Some(v) => ord :+ v
    }

    DebuggingTactics.debug("Before Canonicalization") &
    makeCanonical(ode, timeExtendedOrd, dom, post, pos) &
    DebuggingTactics.debug("After Canonicalization") &
    bv.foldLeft[BelleExpr](Idioms.nil)((a, b) => a & DLBySubst.discreteGhost(b, None, assignInContext=false)(pos))
  })

  //endregion

  //region Setup time variable

  /** Rewrites `[{c}]p` to `[{c, t'=1}]p`.
    * The positional argument should point to the location of c, NOT the location of the box.
    * This tactic should work at any top-level position and also in any context.
    *
    * @note If we want an initial value for time (`kyxtime:=0`) then this is the place to add that functionality.
    */
  val addTimeVar: DependentPositionTactic = TacticFactory.anon ((pos: Position, s:Sequent) => {
    s.sub(pos ++ PosInExpr(0::Nil)) match {
      case Some(_: DifferentialProgram) => //ok
      case Some(_: ODESystem) => //ok
      case _ => throw new TacticInapplicableFailure(s"setupTimeVar should only be called on differential programs without an existing time variable but found ${s.apply(pos)} of type ${s.apply(pos).getClass}.")
    }

    val t = TacticHelper.freshNamedSymbol(TIMEVAR, s)
    TIMEVAR = t //WARNING global state

    val polarity = (if (pos.isSucc) 1 else -1) * FormulaTools.polarityAt(s(pos.top), pos.inExpr)

    if (polarity > 0) HilbertCalculus.DGC(t, Number(1))(pos) & DLBySubst.assignbExists(Number(0))(pos)
    else if (polarity < 0) HilbertCalculus.DGCa(t, Number(1))(pos) & DLBySubst.assignbAll(Number(0))(pos)
    else throw new TacticInapplicableFailure("Parent position of setupTimeVar should be a modality in known polarity.")
  })

  //endregion

  //region Cut in solutions

  // was solDC
  def cutInSoln(odeSize: Int, diffArg:Term = Variable("kyxtime")): DependentPositionTactic = anon ((pos: Position, s: Sequent) => {
    val system: ODESystem = s.sub(pos) match {
      case Some(Box(x: ODESystem, _)) => x
      case Some(e) => throw new TacticInapplicableFailure("solDC only applicable to box ODEs, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + s.prettyString)
    }

    def extract(f: Formula, p: PosInExpr, n: Int): List[(Variable, Term)] =
      if (n == 0) Nil
      else extract(f, p.parent, n-1) :+ (f.sub(p) match {
        case Some(Box(Assign(v, t: Variable), _)) => t -> v
        case Some(e) => throw new TacticInapplicableFailure("solDC.extract only applicable to box assignments, but got " + e.prettyString)
        case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in formula " + f.prettyString)
      })

    val initialConditions: Map[Variable, Term] = extract(s(pos.top), pos.inExpr.parent, odeSize+1).toMap

    val initIdx = TIMEVAR.index.getOrElse(-1) + 1

    //@note we have to cut one at a time instead of just constructing a single tactic because solutions need to be added
    //to the domain constraint for recurrences to work. IMO we should probably go for a different implementation of
    //integral and recurrence so that saturating this tactic isn't necessary, and we can just do it all in one shot.

    val solutions = try {
      Integrator(initialConditions, Minus(TIMEVAR, Variable(TIMEVAR.name, Some(initIdx))), system)
    } catch {
      case ex: IllegalArgumentException => throw new TacticInapplicableFailure("Unable to obtain symbolic solution with builtin integrator", ex)
    }

    val sortedDifferentials = sortAtomicOdes(atomicOdes(system), diffArg).filter(_.xp.x != TIMEVAR).map(_.xp.x)
    val sortedSolutions = solutions.sortWith({case (Equal(a, _), Equal(b, _)) => sortedDifferentials.indexOf(a) < sortedDifferentials.indexOf(b)})

    sortedSolutions.foldRight[BelleExpr](nil)((soln, tactic) => cutAndProveFml(soln, odeSize+1)(pos) & tactic)
  })

  /** Augment ODE with formula `cut`, consider context of size `contextSize` when proving with DI. */
  def cutAndProveFml(cut: Formula, contextSize: Int = 0): DependentPositionTactic = anon ((pos: Position, s: Sequent) => {
    val polarity = (if (pos.isSucc) 1 else -1) * FormulaTools.polarityAt(s(pos.top), pos.inExpr)
    val withInitialsPos = pos.topLevel ++ PosInExpr(pos.inExpr.pos.dropRight(contextSize))

    val fact = s.sub(withInitialsPos) match {
      case Some(fml: Formula) if polarity > 0 =>
        val odePos = PosInExpr(pos.inExpr.pos.takeRight(contextSize))
        val (ctx, modal: Modal) = Context.at(fml, odePos)
        val ODESystem(_, e) = modal.program
        TactixLibrary.proveBy(Imply(ctx(modal.replaceAt(PosInExpr(0::1::Nil), And(e, cut))), fml),
          TactixLibrary.implyR(1) & TactixLibrary.dC(cut)(if (polarity > 0) 1 else -1, odePos) <(
            TactixLibrary.close
            ,
            TactixLibrary.cohideR(Symbol("Rlast")) &
              DebuggingTactics.debug("Normalizing", ODE_DEBUGGER) & TactixLibrary.assignb(1)*contextSize &
              DebuggingTactics.debug("diffInd", ODE_DEBUGGER) & DifferentialTactics.diffInd()(1) & DebuggingTactics.done
          )
        )
      case Some(fml: Formula) if polarity < 0 =>
        val odePos = PosInExpr(pos.inExpr.pos.takeRight(contextSize))
        val (ctx, modal: Modal) = Context.at(fml, odePos)
        val ODESystem(_, e) = modal.program
        TactixLibrary.proveBy(Imply(fml, ctx(modal.replaceAt(PosInExpr(0::1::Nil), And(e, cut)))),
          CMon(odePos) & useAt(Ax.DR, PosInExpr(1::Nil))(1) &
            DW(1) & G(1) & implyR(1) & andL(-1) & close(-1, 1))
      case Some(fml: Formula) if polarity == 0 => throw new TacticInapplicableFailure("cutAndProveFml only applicable in positive or negative polarity contexts")
      case Some(e) => throw new TacticInapplicableFailure("cutAndProveFml only applicable to box ODEs, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + s.prettyString)
    }

    TactixLibrary.useAt(fact, PosInExpr((if (polarity > 0) 1 else 0 )::Nil))(withInitialsPos)
  })

  /**
    *
    * @param v A variable occurring in the odes program.
    * @param system An ode system.
    * @return true if the program does not already contain an = constraint (a.k.a. sol'n) for v in the evolution domain.
    */
  def isSolved(v: Variable, system: ODESystem): Boolean = {
    //Variables that don't occur in the ODE are trivially already solved
    //An occurring variable is solved when an evolution domain constraint of the form 'a = ...' exists
    !atomicOdes(system.ode).exists(_.xp.x == v) ||
      FormulaTools.conjuncts(system.constraint).exists({ case Equal(l, _) => l == v case _ => false })
  }

  //endregion

  //region Simplify post-condition and evolution domain constraint

  // was "domSimplify"
  private def simplifyEvolutionDomain(odeSize: Int) = anon ((pos: Position, _: Sequent) => {
    lazy val simplFact = remember(
      "p_(f(x_)) & x_=f(x_) <-> p_(x_) & x_=f(x_)".asFormula, TactixLibrary.equivR(1) <(
        TactixLibrary.andL(-1) & TactixLibrary.andR(1) < (TactixLibrary.eqL2R(-2)(1) & TactixLibrary.id, TactixLibrary.id),
        TactixLibrary.andL(-1) & TactixLibrary.andR(1) < (TactixLibrary.eqR2L(-2)(1) & TactixLibrary.id, TactixLibrary.id)
        ), namespace)

    // was domSimplifyStep
    val step = anon ((pp: Position, ss: Sequent) => {
      val subst = (_: Option[TactixLibrary.Subst]) => ss.sub(pp) match {
        case Some(And(p, Equal(x, f))) => RenUSubst(
          ("x_".asVariable, x) ::
            ("p_(.)".asFormula, p.replaceFree(x, DotTerm())) ::
            ("f(.)".asTerm, f.replaceFree(x, DotTerm())) ::
            Nil)
        case Some(e) => throw new TacticInapplicableFailure("domSimplifyStep only applicable to conjunctions, but got " + e.prettyString)
        case None => throw new IllFormedTacticApplicationException("Position " + pp + " does not point to a valid position in sequent " + ss.prettyString)
      }
      TactixLibrary.useAt(simplFact, PosInExpr(1::Nil), subst)(pp)
    })

    (0 until odeSize).map(List.fill(_)(0)).map(i => step(pos ++ PosInExpr(i))).reduceRight[BelleExpr](_ & _)
  })

  // was postSimplify
  def simplifyPostCondition(odeSize: Int): DependentPositionTactic = anon ((pos: Position, seq: Sequent) => {
    val polarity = (if (pos.isSucc) 1 else -1) * FormulaTools.polarityAt(seq(pos.top), pos.inExpr)

    lazy val rewrite1 = remember("(q_(f(x_)) -> p_(f(x_))) -> (q_(x_) & x_=f(x_) -> p_(x_))".asFormula,
      TactixLibrary.implyR(1) * 2 & TactixLibrary.andL(-2) & TactixLibrary.eqL2R(-3)(1) &
        TactixLibrary.eqL2R(-3)(-2) & TactixLibrary.prop & TactixLibrary.done, namespace)
    lazy val rewrite2 = remember("(q_(x_) & x_=f(x_)) & p_(x_) -> q_(f(x_)) & p_(f(x_))".asFormula,
      TactixLibrary.implyR(1) & TactixLibrary.andL(-1) * 2 & TactixLibrary.andR(1) &
        OnAll(TactixLibrary.eqR2L(-3)(1) & TactixLibrary.id), namespace)
    lazy val rewrite3 = remember("p_() -> (q_() -> p_())".asFormula, TactixLibrary.prop, namespace)

    //@note compute substitution fresh on each step, single pass unification match does not work because q_(x_) before x_=f
    // was "postSimplifyStep"
    (anon ((pp: Position, ss: Sequent) => {
      val (xx, subst, rewrite) = ss.sub(pp) match {
        case Some(Imply(And(q, Equal(x: Variable, f)), p)) => (x, (_: Option[TactixLibrary.Subst]) => RenUSubst(
          ("x_".asVariable, x) ::
            ("q_(.)".asFormula, q.replaceFree(x, DotTerm())) ::
            ("p_(.)".asFormula, Box(Assign(x, DotTerm()), p).replaceAll(x, "x_".asVariable)) ::
            ("f(.)".asTerm, f.replaceFree(x, DotTerm())) ::
            Nil), rewrite1)
        case Some(And(And(q, Equal(x: Variable, f)), p)) => (x, (_: Option[TactixLibrary.Subst]) => RenUSubst(
          ("x_".asVariable, x) ::
            ("q_(.)".asFormula, q.replaceFree(x, DotTerm())) ::
            ("p_(.)".asFormula, Box(Assign(x, DotTerm()), p).replaceAll(x, "x_".asVariable)) ::
            ("f(.)".asTerm, f.replaceFree(x, DotTerm())) ::
            Nil), rewrite2)
        case Some(e) => throw new TacticInapplicableFailure("postSimplifyStep not applicable at " + e.prettyString)
        case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
      }

      DLBySubst.stutter(xx)(pp ++ PosInExpr(1::Nil)) &
      TactixLibrary.useAt(rewrite, if (polarity >= 0) PosInExpr(1::Nil) else PosInExpr(0::Nil), subst)(pp) &
      TactixLibrary.assignb(pp ++ PosInExpr(1::Nil))
    }))(pos)*odeSize &
      (if (polarity > 0) TactixLibrary.useAt(rewrite3, PosInExpr(1::Nil))(pos)
       else TactixLibrary.skip) & postCondSimplifier(pos) //@note do not simplify dependent formulas in postcondition, since diamond solver relies on duplicated formulas
  })

  //endregion

  //region Inverse diff cuts

  //@todo @see DifferentialTactics.inverseDiffCut duplication?
  // was "dCi2"
  private def inverseDiffCut(odeSize: Int): DependentPositionTactic = anon ((pos: Position, s: Sequent) => {
    val polarity = (if (pos.isSucc) 1 else -1) * FormulaTools.polarityAt(s(pos.top), pos.inExpr)
    val withInitialsPos = pos.topLevel ++ PosInExpr(pos.inExpr.pos.dropRight(odeSize+1))
    val fact = s.sub(withInitialsPos) match {
      case Some(fml: Formula) if polarity > 0 =>
        val odePos = PosInExpr(pos.inExpr.pos.takeRight(odeSize+1))
        val (ctx, modal: Modal) = Context.at(fml, odePos)
        val ODESystem(_, And(e, soln)) = modal.program
        TactixLibrary.proveBy(Imply(ctx(modal.replaceAt(PosInExpr(0::1::Nil), e)), fml),
          CMon(odePos) & useAt(Ax.DR, PosInExpr(1::Nil))(1) &
            DW(1) & G(1) & implyR(1) & andL(-1) & close(-1, 1))
      case Some(fml: Formula) if polarity < 0 =>
        val odePos = PosInExpr(pos.inExpr.pos.takeRight(odeSize+1))
        val (ctx, modal: Modal) = Context.at(fml, odePos)
        val ODESystem(_, And(e, soln)) = modal.program
        TactixLibrary.proveBy(Imply(fml, ctx(modal.replaceAt(PosInExpr(0::1::Nil), e))),
          TactixLibrary.implyR(1) & TactixLibrary.dC(soln)(if (polarity > 0) -1 else 1, odePos) <(
            TactixLibrary.close
            ,
            TactixLibrary.cohideR(Symbol("Rlast")) &
            DebuggingTactics.debug("Normalizing", ODE_DEBUGGER) & TactixLibrary.assignb(1)*(odeSize+1) &
            DebuggingTactics.debug("diffInd", ODE_DEBUGGER) & DifferentialTactics.diffInd()(1) & DebuggingTactics.done
            )
        )
      case Some(fml: Formula) if polarity == 0 => throw new TacticInapplicableFailure("dCi2 only applicable in negative or positive polarity contexts")
      case Some(e) => throw new TacticInapplicableFailure("dCi2 only applicable to formulas, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + withInitialsPos + " does not point to a valid position in sequent " + s.prettyString)
    }

    TactixLibrary.useAt(fact, PosInExpr((if (polarity > 0) 1 else 0)::Nil))(withInitialsPos)
  })

  //endregion

  private def odeSize(e: Expression): Int = odeSize(e.asInstanceOf[Modal].program.asInstanceOf[ODESystem].ode)
  private def odeSize(ode: DifferentialProgram): Int = ode match {
    case _: DifferentialProgramConst => 1
    case _: AtomicODE => 1
    case x: DifferentialProduct => odeSize(x.left) + odeSize(x.right)
  }
}
