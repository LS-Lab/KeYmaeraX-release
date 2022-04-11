package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TacticHelper.timed
import TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfoAugmentors.ProvableInfoAugmentor
import edu.cmu.cs.ls.keymaerax.core.{Close, Cut, EquivLeft, NotLeft}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.{Logging, core}
import edu.cmu.cs.ls.keymaerax.infrastruct.{AntePosition, FormulaTools, PosInExpr, Position, RenUSubst, SuccPosition, UnificationMatchUSubstAboveURen}
import edu.cmu.cs.ls.keymaerax.btactics.macros.{AxiomInfo, Tactic, TacticInfo}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.annotation.tailrec
import scala.collection.immutable.{::, List, Nil}
import scala.util.Try

/**
 * [[PropositionalTactics]] provides tactics for propositional reasoning.
 */
private[keymaerax] object PropositionalTactics extends Logging {
  /**
   * Inverse of [[SequentCalculus.implyR]].
   * @author Nathan Fulton
   * @author Stefan Mitsch
   * @see [[SequentCalculus.implyR]]
   */
  private[btactics] lazy val implyRi: AppliedBuiltinTwoPositionTactic = implyRi()(AntePos(0), SuccPos(0))
  private[btactics] def implyRi(keep: Boolean = false): BuiltInTwoPositionTactic = anon ((p: ProvableSig, a: Position, s: Position) => {
    assert(p.subgoals.length == 1, "Assuming one subgoal.")
    val sequent = p.subgoals.head
    require(a.isIndexDefined(sequent) && s.isIndexDefined(sequent),
      "Ante position " + a + " or succ position " + s + " is out of bounds; provable has ante size " +
        sequent.ante.length + " and succ size " + sequent.succ.length)
    val left = sequent.ante(a.checkAnte.top.getIndex)
    val impl = p(CutRight(left, s.checkSucc.top), 0)(Close(a.checkAnte.top, s.checkSucc.top), 0)
    if (keep) impl else impl(core.HideLeft(a.checkAnte.top), 0)
  })

  /**
   * Inverse of [[ProofRuleTactics.orR]].
   *
   * @author Stefan Mitsch
   * @see [[ProofRuleTactics.orR]]
   */
  private[btactics] lazy val orRi: AppliedBuiltinTwoPositionTactic = orRi(keepLeft=false)(SuccPosition.base0(0), SuccPosition.base0(1))
  private[btactics] def orRi(keepLeft: Boolean): BuiltInTwoPositionTactic = anon { (pr: ProvableSig, pos1: Position, pos2: Position) => {
    require(pos1 != pos2, "Two distinct positions required")
    val sequent = pr.subgoals.head
    require(sequent.succ.length > pos1.index0 && sequent.succ.length > pos2.index0,
      "Position " + pos1 + " or position " + pos2 + " is out of bounds; provable has succ size " + sequent.succ.length)
    val left = sequent.succ(pos1.index0)
    val right = sequent.succ(pos2.index0)
    val cutUsePos = AntePos(sequent.ante.length)

    //    cut(Or(left, right)) <(
    //      /* use */ orL(cutUsePos) & OnAll(TactixLibrary.close),
    //      /* show */
    //        if (pos1.getIndex > pos2.getIndex) (assertE(left, "")(pos1) & hideR(pos1) & assertE(right, "")(pos2) & hideR(pos2))
    //        else (assertE(right, "")(pos2) & hideR(pos2) & assertE(left, "")(pos1) & hideR(pos1))
    //      )
    //    }
    val cutPr = pr(Cut(Or(left, right)), 0)
    (if (pos1.index0 > pos2.index0) cutPr(HideRight(pos1.checkSucc.checkTop), 1)(HideRight(pos2.checkSucc.checkTop), 1)
     else cutPr(HideRight(pos2.checkSucc.checkTop), 1)(HideRight(pos1.checkSucc.checkTop), 1))(
      OrLeft(cutUsePos), 0)(
      Close(cutUsePos, pos2.checkSucc.checkTop), 2)(
      Close(cutUsePos, pos1.checkSucc.checkTop), 0)
  }}

  /**
   * Inverse of [[ProofRuleTactics.andL]].
 *
   * @author Stefan Mitsch
   * @see [[ProofRuleTactics.andL]]
   */
  private[btactics] lazy val andLi: AppliedBuiltinTwoPositionTactic = andLi(keepLeft=false)(AntePosition.base0(0), AntePosition.base0(1))
  private[btactics] def andLi(keepLeft: Boolean): BuiltInTwoPositionTactic = anon { (pr: ProvableSig, pos1: Position, pos2: Position) => {
    require(pos1 != pos2, "Two distinct positions required")
    val sequent = pr.subgoals.head
    require(sequent.ante.length > pos1.index0 && sequent.ante.length > pos2.index0,
      "Position " + pos1 + " or position " + pos2 + " is out of bounds; provable has ante size " + sequent.ante.length)
    val left = sequent.ante(pos1.index0)
    val right = sequent.ante(pos2.index0)
    val cutUsePos = SuccPos(sequent.succ.length)

    //    cut(And(left, right)) <(
    //      /* use */
    //      if (pos1.index0 > pos2.index0) assertE(left, "")(pos1) & (if (keepLeft) skip else hideL(pos1)) & assertE(right, "")(pos2) & hideL(pos2)
    //      else assertE(right, "")(pos2) & hideL(pos2) & assertE(left, "")(pos1) & (if (keepLeft) skip else hideL(pos1)),
    //      /* show */ andR(cutUsePos) & OnAll(TactixLibrary.close)
    //    )}
    val cutPr = pr(Cut(And(left, right)), 0)
    (if (pos1.index0 > pos2.index0) {
      (if (keepLeft) cutPr else cutPr(HideLeft(pos1.checkAnte.checkTop), 0))(HideLeft(pos2.checkAnte.checkTop), 0)
    } else {
      val pos2Hidden = cutPr(HideLeft(pos2.checkAnte.checkTop), 0)
      if (keepLeft) pos2Hidden else pos2Hidden(HideLeft(pos1.checkAnte.checkTop), 0)
    })(AndRight(cutUsePos), 1)(
      Close(pos2.checkAnte.checkTop, cutUsePos), 2)(
      Close(pos1.checkAnte.checkTop, cutUsePos), 1)
  }}

  /**
   * Returns a tactic for propositional CE with purely propositional unpeeling. Useful when unpeeled fact is not
   * an equivalence, as needed by CE. May perform better than CE for small contexts.
 *
   * @see [[UnifyUSCalculus.CMon(Context)]]
   * @see [[UnifyUSCalculus.CE(Context)]]
   * @example {{{
   *                  z=1 |- z>0
   *         --------------------------propCE(PosInExpr(1::Nil))
   *           x>0 -> z=1 |- x>0 -> z>0
   * }}}
   * @param at Points to the position to unpeel.
   * @return The tactic.
   */
  def propCMon(at: PosInExpr): BuiltInTactic = anon { provable: ProvableSig =>
    ProofRuleTactics.requireOneSubgoal(provable, "propCMon")
    val sequent = provable.subgoals.head
    require(sequent.ante.length == 1 && sequent.succ.length == 1 &&
      Try(sequent.ante.head.at(at)._1 == sequent.succ.head.at(at)._1).toOption.getOrElse(false), s"Propositional CMon requires single antecedent " +
      s"and single succedent formula with matching context to $at, but got $sequent" +
      Try(sequent.ante.head.at(at)._1 -> sequent.succ.head.at(at)._1).toOption.map({ case (a, b) => s"\n${a.ctx} != ${b.ctx}" }).getOrElse(s"\n($at points to non-existing position in sequent)"))

    // we know that we have the same operator in antecedent and succedent with the same lhs -> we know that one
    // will branch and one of these branches will close by identity. on the other branch, we have to hide
    // list all cases explicitly, hide appropriate formulas in order to not blow up branching
    if (at.pos.length <= 0) provable
    else ((sequent.succ.headOption match {
      case Some(_: Not) => (provable
        (NotLeft(AntePos(0)), 0)
        (NotRight(SuccPos(0)), 0)
        )
      case Some(And(lhs, rhs)) => (provable
        (AndLeft(AntePos(0)), 0)
        (AndRight(SuccPos(0)), 0)
        ((pr: ProvableSig) => if (pr.subgoals.head(AntePos(1)) == rhs) pr(Close(AntePos(1), SuccPos(0)), 0) else pr(HideLeft(AntePos(0)), 0), 1)
        ((pr: ProvableSig) => if (pr.subgoals.head(AntePos(0)) == lhs) pr(Close(AntePos(0), SuccPos(0)), 0) else pr(HideLeft(AntePos(1)), 0), 0)
        )
      case Some(Or(lhs, rhs)) => (provable
        (OrRight(SuccPos(0)), 0)
        (OrLeft(AntePos(0)), 0)
        ((pr: ProvableSig) => if (pr.subgoals.head(AntePos(0)) == rhs) pr(Close(AntePos(0), SuccPos(1)), 0) else pr(HideRight(SuccPos(0)), 0), 1)
        ((pr: ProvableSig) => if (pr.subgoals.head(AntePos(0)) == lhs) pr(Close(AntePos(0), SuccPos(0)), 0) else pr(HideRight(SuccPos(1)), 0), 0)
        )
      case Some(Imply(lhs, rhs)) => (provable
        (ImplyRight(SuccPos(0)), 0)
        (ImplyLeft(AntePos(0)), 0)
        ((pr: ProvableSig) => if (pr.subgoals.head(AntePos(0)) == rhs) pr(Close(AntePos(0), SuccPos(0)), 0) else pr(HideLeft(AntePos(1) /* 'Llast */), 0), 1)
        ((pr: ProvableSig) => if (pr.subgoals.head(SuccPos(1)) == lhs) pr(Close(AntePos(0), SuccPos(1)), 0) else pr(HideRight(SuccPos(0)), 0), 0)
        )
      case Some(_: Box) =>
        import edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfoAugmentors._
        provable(US(Ax.monbaxiom.provable).result _, 0)
      case Some(_: Diamond) =>
        import edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfoAugmentors._
        provable(US(Ax.mondrule.provable).result _, 0)
      case Some(_: Forall) => (provable
        (FOQuantifierTactics.allSkolemize(SuccPos(0)).computeResult _, 0)
        (FOQuantifierTactics.allInstantiate(None, None)(AntePos(0)).computeResult _, 0)
        )
      case Some(_: Exists) => (provable
        (FOQuantifierTactics.existsSkolemize(AntePos(0)).computeResult _, 0)
        (FOQuantifierTactics.existsInstantiate(None, None)(SuccPos(0)).computeResult _, 0)
        )
      case Some(e) => throw new TacticInapplicableFailure("Prop. CMon not applicable to " + e.prettyString)
      // redundant to exception raised by .at(...) in contract above
      case None => throw new IllFormedTacticApplicationException("Prop. CMon: no more formulas left to descend into " + at.prettyString)
    })
      (propCMon(at.child).result _, 0)
      )
  }

  /** @see [[SequentCalculus.modusPonens()]] */
  private[btactics] def modusPonens(assumption: AntePos, implication: AntePos): BuiltInTactic = anon { pr: ProvableSig =>
    ProofRuleTactics.requireOneSubgoal(pr, "modusPonens")
    val seq = pr.subgoals.head
    val p = AntePos(assumption.getIndex - (if (assumption.getIndex > implication.getIndex) 1 else 0))
    (pr(ImplyLeft(implication), 0)
      (closeId(p, SuccPos(seq.succ.length)).computeResult _, 0)
      )
  }

  /** Automated modus ponens for p->q ==> ; tries to automatically prove p from the rest of the assumptions. */
  @Tactic()
  private[btactics] val autoMP: DependentPositionTactic = anon { (pos: Position, seq: Sequent) => seq(pos.checkAnte.checkTop) match {
      case Imply(p, _) =>
        val pi = seq.ante.indexWhere(_ == p)
        if (pi >= 0) modusPonens(AntePos(pi), pos.checkAnte.checkTop)
        else {
          //@todo usually includes too many assumptions
          val notsuccs = seq.succ.map(Not).map(SimplifierV3.formulaSimp(_, scala.collection.immutable.HashSet.empty, SimplifierV3.defaultFaxs, SimplifierV3.defaultTaxs)._1)
          val antes = seq.ante.patch(pos.index0, List.empty, 1)
          val assms = (notsuccs ++ antes).reduceRightOption(And).getOrElse(True)
          val mpShow = Sequent(scala.collection.immutable.IndexedSeq(), scala.collection.immutable.IndexedSeq(Imply(assms, p)))
          //@todo tactic with timeouts results in proof repeatability issues
          val mpLemma = proveBy(mpShow, SaturateTactic(implyR('R) | andL('L)) & EqualityTactics.expandAll & PropositionalTactics.prop &
            Idioms.doIf(_.subgoals.size <= 4)(OnAll(QEX(None, Some(Number(2))))))

          if (mpLemma.isProved) {
            cut(p) < (
              modusPonens(AntePos(seq.ante.size), pos.checkAnte.checkTop) & SaturateTactic(hideL('L, p)),
              useAt(mpLemma, PosInExpr(1 :: Nil))('Rlast) & PropositionalTactics.prop & done)
          } else throw new TacticInapplicableFailure("Failed to prove assumptions")
        }
      case _ => throw new TacticInapplicableFailure("Applicable only to implications at top-level in the antecedent")
    }
  }
  private[btactics] val autoMPInfo: TacticInfo = TacticInfo("autoMP")

  /**
   * Converts a sequent into a single formula.
   * Example:
   * {{{
   *   A, B |- S, T, U
   * }}}
   * is converted into:
   * {{{
   *   (A ^ B) -> (S \/ T \/ U)
   * }}}
   */
  @Tactic()
  val toSingleFormula: BuiltInTactic  = anon { pr: ProvableSig =>
    ProofRuleTactics.requireOneSubgoal(pr, "toSingleFormula")
    val sequent = pr.subgoals.head
    if (sequent.ante.isEmpty && sequent.succ.isEmpty) {
      (pr(Cut(sequent.toFormula), 0)
        /* show */
        (CoHideRight(SuccPos(sequent.succ.length)), 1)
        /* use */
        (ImplyLeft(AntePos(0)), 0)
        (CloseFalse(AntePos(0)), 2)
        (CloseTrue(SuccPos(0)), 0)
        )
    } else if (sequent.ante.isEmpty && sequent.succ.size == 1) {
      pr
    } else {
      (pr(Cut(sequent.toFormula), 0)
        /* show */
        (CoHideRight(SuccPos(sequent.succ.length)), 1)
        /* use */
        (ImplyLeft(AntePos(sequent.ante.length)), 0) // creates subgoals 0+2
        /* ImplyLeft show */
        (List.fill(sequent.ante.size)(HideLeft(AntePos(0))).foldLeft(_: ProvableSig)({ (pr, r) => pr(r, 0) }), 2) // hideL(-1)*sequent.ante.size
        (List.fill(sequent.succ.size - 1)(OrLeft(AntePos(0))).zipWithIndex.foldLeft(_: ProvableSig)({ case (pr, (r, i)) => // (orL(-1) <(close, skip))*(sequent.succ.size-1) & onAll(close)
          (pr(r, 0)
            (Close(AntePos(0), SuccPos(i)), 0)
            )
        }), 2)
        (if (sequent.succ.nonEmpty) Close(AntePos(0), SuccPos(sequent.succ.length-1)) else CloseFalse(AntePos(0)), 2)
        /* ImplyLeft use */
        (List.fill(sequent.succ.size)(HideRight(SuccPos(0))).foldLeft(_: ProvableSig)({ (pr, r) => pr(r, 0) }), 0) // hideR(1)*sequent.succ.size
        (List.fill(sequent.ante.size - 1)(AndRight(SuccPos(0))).zipWithIndex.foldLeft(_: ProvableSig)({ case (pr, (r, i)) => // (andR(1) <(close, skip))*(sequent.ante.size-1) & onAll(close)
          (pr(r, 0)
            (Close(AntePos(i), SuccPos(0)), 0)
            )
        }), 0)
        (if (sequent.ante.nonEmpty) Close(AntePos(sequent.ante.length-1), SuccPos(0)) else CloseTrue(SuccPos(0)), 0)
        )
    }
  }

  /** Forward propositional tactic for internal use (does not create branch labels). */
  val prop: BuiltInTactic = prop(alphaRules, betaRules)(List.empty, List.empty)

  /** Returns the alpha rules for `fml`, applied at position `p`. */
  def alphaRules(fml: Formula, p: SeqPos): List[PositionRule] = (fml, p) match {
    case (_: Or,    sp: SuccPos) => List(OrRight(sp))
    case (_: Imply, sp: SuccPos) => List(ImplyRight(sp))
    case (_: Not,   sp: SuccPos) => List(NotRight(sp))
    case (_: And,   ap: AntePos) => List(AndLeft(ap))
    case (_: Not,   ap: AntePos) => List(NotLeft(ap))
    case (True,     sp: SuccPos) => List(CloseTrue(sp))
    case (False,    ap: AntePos) => List(CloseFalse(ap))
    case _ => Nil
  }

  /** Returns the beta rules for `fml`, applied at position `p`. */
  def betaRules(fml: Formula, p: SeqPos): List[PositionRule] = (fml, p) match {
    case (_: And,   sp: SuccPos) => List(AndRight(sp))
    case (_: Equiv, sp: SuccPos) => List(EquivRight(sp))
    case (_: Or,    ap: AntePos) => List(OrLeft(ap))
    case (_: Imply, ap: AntePos) => List(ImplyLeft(ap))
    case (_: Equiv, ap: AntePos) => List(EquivLeft(ap))
    case _ => Nil
  }

  /** Forward propositional tactic implementation with work stacks `alpha` and `beta`, and configuration */
  def prop(alphaRules: (Formula, SeqPos) => List[PositionRule], betaRules: (Formula, SeqPos) => List[PositionRule])
          (alpha: List[PositionRule], beta: List[PositionRule]): BuiltInTactic = anon { provable: ProvableSig =>
    ProofRuleTactics.requireOneSubgoal(provable, "PropositionalTactics.prop")

    /** Repositions the beta rules in `r` a position up (to index-1) if they are after position `p`. */
    def repositionBeta(r: List[PositionRule], p: SeqPos): List[PositionRule] = r.map({
      case AndRight(rp)   if p.isSucc && rp.getIndex > p.getIndex => AndRight(rp.copy(rp.getIndex-1))
      case EquivRight(rp) if p.isSucc && rp.getIndex > p.getIndex => EquivRight(rp.copy(rp.getIndex-1))
      case OrLeft(rp)     if p.isAnte && rp.getIndex > p.getIndex => OrLeft(rp.copy(rp.getIndex-1))
      case ImplyLeft(rp)  if p.isAnte && rp.getIndex > p.getIndex => ImplyLeft(rp.copy(rp.getIndex-1))
      case EquivLeft(rp)  if p.isAnte && rp.getIndex > p.getIndex => EquivLeft(rp.copy(rp.getIndex-1))
      case r => r
    })

    val s = provable.subgoals.head
    s.ante.intersect(s.succ).toList.headOption match {
      case Some(f) => provable(Close(AntePos(s.ante.indexOf(f)), SuccPos(s.succ.indexOf(f))), 0)
      case None => alpha match {
        case rule :: tail =>
          val pos = rule.pos
          s(pos) match {
            case And(l, r) =>
              assert(pos.isAnte)
              provable(rule, 0)(prop(alphaRules, betaRules)(
                alphaRules(r, AntePos(s.ante.length)) ++ alphaRules(l, AntePos(s.ante.length-1)) ++ tail,
                betaRules(r, AntePos(s.ante.length)) ++ betaRules(l, AntePos(s.ante.length-1)) ++ repositionBeta(beta, pos)
              ).result _, 0)
            case Or(l, r) =>
              assert(pos.isSucc)
              provable(rule, 0)(prop(alphaRules, betaRules)(
                alphaRules(r, SuccPos(s.succ.length)) ++ alphaRules(l, SuccPos(s.succ.length-1)) ++ tail,
                betaRules(r, SuccPos(s.succ.length)) ++ betaRules(l, SuccPos(s.succ.length-1)) ++ repositionBeta(beta, pos)
              ).result _, 0)
            case Imply(l, r) =>
              assert(pos.isSucc)
              provable(rule, 0)(prop(alphaRules, betaRules)(
                alphaRules(r, SuccPos(s.succ.length-1)) ++ alphaRules(l, AntePos(s.ante.length)) ++ tail,
                betaRules(r, SuccPos(s.succ.length-1)) ++ betaRules(l, AntePos(s.ante.length)) ++ repositionBeta(beta, pos)
              ).result _, 0)
            case Not(f) =>
              val p = if (pos.isSucc) AntePos(s.ante.length) else SuccPos(s.succ.length)
              provable(rule, 0)(prop(alphaRules, betaRules)(alphaRules(f, p) ++ tail, betaRules(f, p) ++ repositionBeta(beta, pos)).result _, 0)
            case True =>
              assert(pos.isSucc)
              provable(rule, 0)
            case False =>
              assert(pos.isAnte)
              provable(rule, 0)
          }
        case Nil => beta match {
          case rule :: tail =>
            val pos = rule.pos
            s(pos) match {
              case And(l, r) =>
                assert(pos.isSucc)
                val propLeft = prop(alphaRules, betaRules)(alphaRules(l, pos), betaRules(l, pos) ++ tail)
                val propRight = prop(alphaRules, betaRules)(alphaRules(r, pos), betaRules(r, pos) ++ tail)
                provable(rule, 0)(propRight.result _, 1)(propLeft.result _, 0)
              case Or(l, r) =>
                assert(pos.isAnte)
                val propLeft = prop(alphaRules, betaRules)(alphaRules(l, pos), betaRules(l, pos) ++ tail)
                val propRight = prop(alphaRules, betaRules)(alphaRules(r, pos), betaRules(r, pos) ++ tail)
                provable(rule, 0)(propRight.result _, 1)(propLeft.result _, 0)
              case Imply(l, r) =>
                assert(pos.isAnte)
                val propLeft = prop(alphaRules, betaRules)(alphaRules(l, SuccPos(s.succ.length)), betaRules(l, SuccPos(s.succ.length)) ++ tail)
                val propRight = prop(alphaRules, betaRules)(alphaRules(r, pos), betaRules(r, pos) ++ tail)
                provable(rule, 0)(propRight.result _, 1)(propLeft.result _, 0)
              case Equiv(l, r) =>
                if (pos.isSucc) {
                  //@see [[EquivRight]]
                  val propLeft = prop(alphaRules, betaRules)(
                    alphaRules(r, SuccPos(s.succ.length-1)) ++ alphaRules(l, AntePos(s.ante.length)),
                    betaRules(r, SuccPos(s.succ.length-1)) ++ betaRules(l, AntePos(s.ante.length)) ++ tail
                  )
                  val propRight = prop(alphaRules, betaRules)(
                    alphaRules(l, SuccPos(s.succ.length-1)) ++ alphaRules(r, AntePos(s.ante.length)),
                    betaRules(l, SuccPos(s.succ.length-1)) ++ betaRules(r, AntePos(s.ante.length)) ++ tail
                  )
                  provable(rule, 0)(propRight.result _, 1)(propLeft.result _, 0)
                } else {
                  //@see [[EquivLeft]]
                  val propLeft = prop(alphaRules, betaRules)(List(AndLeft(pos.asInstanceOf[AntePos])), tail)
                  val propRight = prop(alphaRules, betaRules)(List(AndLeft(pos.asInstanceOf[AntePos])), tail)
                  provable(rule, 0)(propRight.result _, 1)(propLeft.result _, 0)
                }
            }
          case Nil =>
            val alpha =
              s.succ.zipWithIndex.flatMap({ case (fml, i) => alphaRules(fml, SuccPos(i)) }).reverse ++
              s.ante.zipWithIndex.flatMap({ case (fml, i) => alphaRules(fml, AntePos(i)) }).reverse
            val beta =
              s.succ.zipWithIndex.flatMap({ case (fml, i) => betaRules(fml, SuccPos(i)) }).reverse ++
              s.ante.zipWithIndex.flatMap({ case (fml, i) => betaRules(fml, AntePos(i)) }).reverse
            if (alpha.nonEmpty || beta.nonEmpty) prop(alphaRules, betaRules)(alpha.toList, beta.toList).result(provable)
            else provable
        }
      }
    }
  }

  //region Equivalence Rewriting

  /**
    * Performs equivalence rewriting in either direction at any top-level position in a sequent,
    * leaving the original equivalence in place. Instantiates Forall-quantified equivalences so that they match
    * the target position when necessary. If the quantified variable is not mentioned in the targetPos, then the quantified
    * name is used.
    *
    * @todo these examples might be incorrect, and the description above might be incorrect. Correct explanation is "does whatever unification does", actually.
    *       Although we might want to change that to not use unification...
    *
    * Examples:
    * {{{
    *   \forall x. p(x) <-> q() |- p(x)
    *   --------------------------------- equivRewriting(-1,1)
    *   \forall x. p(x) <-> q() |- q()
    *
    *   \forall x. p(x) <-> q() |- q()
    *   --------------------------------- equivRewriting(-1,1)
    *   \forall x. p(x) <-> q() |- p(z)
    *
    *   \forall x. p(x) <-> q(z), p(x) |-
    *   --------------------------------- equivRewriting(-1,-2)
    *   \forall x. p(x) <-> q(z), q(z) |-
    *
    *   \forall x. p(x) <-> q(z), q(z) |-
    *   --------------------------------- equivRewriting(-1,-2)
    *   \forall x. p(x) <-> q(z), p(z) |-
    *
    *   \forall x. p(x) <-> q(z), q(z) |-
    *   --------------------------------- equivRewriting(-1,-2)
    *   \forall x. p(x) <-> q(z), p(x) |-
    * }}}
    */
  @Tactic("equivRewriting", conclusion = "Γ, ∀X p(X) <-> q(X) |- p(Z), Δ", premises = "Γ, ∀X p(X) <-> q(X) |- q(Z), Δ")
  val equivRewriting: BuiltInTwoPositionTactic =  anon ((p: ProvableSig, equivPos: Position, targetPos: Position) => {
    assert(p.subgoals.length == 1, "Assuming one subgoal.")
    val target = p.subgoals(0)(targetPos).asInstanceOf[Formula]
    p.subgoals(0)(equivPos) match {
      case Equiv(_,_) => instantiatedEquivRewritingImpl(p, equivPos, targetPos)
      case fa: Forall =>
        /*
         * Game plan:
         *   1. Compute the instantiation of p(equivPos) that matches p(targetPos)
         *   2. Cut in a new quantified equivalence
         *   3. Perform instantiations on this new quantified equivalence.
         *   4. perform instantiatedEquivRewritingImpl using the newly instantiated equivalence
         *   5. Hide the instantiated equivalence OR the original assumption.
         */

        // step 1
        val instantiation = computeInstantiation(fa, target)

        val cutPos = AntePos(p.subgoals.head.ante.length) //Position of equivalence to instantiate.

        // step 2: input is p and output is postCut
        (p(Cut(fa), 0)
          (closeId(equivPos.checkAnte.top, SuccPos(p.subgoals.head.succ.length)).computeResult _, 1)
          // step 3: input is postCut and output is instantiatedEquivalence
          (vars(fa).map(x => FOQuantifierTactics.allInstantiate(Some(x), Some(instantiation(x)))(cutPos)).
            foldLeft(_: ProvableSig)({ case (pr, r) => pr(r.computeResult _, 0)  }), 0)
          // step 4
          (instantiatedEquivRewritingImpl(_, cutPos, targetPos), 0)
          // step 5
          (if (targetPos.isAnte) HideLeft(targetPos.checkAnte.top) else HideLeft(cutPos), 0)
          )
    }
  })

  private def computeInstantiation(fa: Forall, target: Formula): RenUSubst = {
    val equiv = bodyOf(fa)

    //@note it's important to only use the renaming; otherwise unification is too clever and comes up with predicate substitutions that cannot be achieved by instantiation alone.
    val leftRenaming: Option[RenUSubst] = try {
      val renaming = new UnificationMatchUSubstAboveURen().apply(equiv.left, target).renaming
      if (renaming.isEmpty) None
      else Some(renaming)
    } catch {
      case _: UnificationException => None
    }

    val rightRenaming: Option[RenUSubst] = try {
      val renaming = new UnificationMatchUSubstAboveURen().apply(equiv.right, target).renaming
      if (renaming.isEmpty) None
      else Some(renaming)
    } catch {
      case _: UnificationException => None
    }

    //First try to left-unify, then try to right-unify. I.e., default to left-rewriting when bot hare available.
    //@note This is also the default behavior of instantiatedEquivRewriting, and the two should be consistent on defaults.
    (leftRenaming, rightRenaming) match {
      case (Some(subst), _)  => logger.trace(s"Unified ${equiv.right} with $target under $subst"); subst
      case (None, Some(subst)) => logger.trace(s"Unified ${equiv.left} with $target under $subst"); subst
      case _ => RenUSubst(Nil) //Try to go ahead with an empty renaming since it will work more often than not.
    }
  }
  private def vars(fa: Forall): Seq[Variable] = fa.vars ++ (fa.child match {
    case child: Forall => vars(child)
    case e:Equiv => Nil
    case _ => throw new Exception("Expted equiv.")
  })
  @tailrec
  private def bodyOf(fa: Forall): Equiv = fa.child match {
    case child:Forall => bodyOf(child)
    case child:Equiv  => child
    case _            => throw new Exception(s"Expected a universally quantified equivalence but found ${fa.child.getClass}")
  }


  /**
    * Performs equivalence rewriting in either direction at any top-level position in a sequent,
    * leaving the original equivalence in place.
    *
    * Examples:
    * {{{
    *   P<->Q |- Q
    *   ----------- equivRewriting(-1, 1)
    *   P<->Q |- P
    * }}}
    *
    * {{{
    *   P<->Q, Q |-
    *   ------------ equivRewriting(-1, 1)
    *   P<->Q, P |-
    * }}}
    *
    * {{{
    *   P<->Q, P |-
    *   ------------ equivRewriting(-1, 1)
    *   P<->Q, Q |-
    * }}}
    */
  private def instantiatedEquivRewritingImpl(p: ProvableSig, equivPos: Position, targetPos: Position): ProvableSig = {
    assert(p.subgoals.length == 1, "Assuming one subgoal.")

    //@note equivalence == target <-> other.
    val equivalence: Equiv = p.subgoals.head(equivPos.checkAnte) match {
      case e:Equiv => e
      case f:Formula => throw new Exception(s"Expected an Equiv but found ${f.prettyString}")
      case e@_ => throw new Exception(s"Expected an Equiv formula but found ${e.prettyString}")
    }
    val targetValue : Formula = p.subgoals.head(targetPos.top)
    val otherValue : Formula = if(equivalence.left == targetValue) equivalence.right else equivalence.left

    val newEquivPos = AntePos(p.subgoals.head.ante.length)

    //First constraint a sequent that we can close as long as we know which positions to target with CloseId
    val postCut =
      p.apply(Cut(equivalence), 0)
        .apply(Close(equivPos.checkAnte.top, SuccPos(p.subgoals.head.succ.length)), 1)
        .apply(EquivLeft(newEquivPos), 0)
        .apply(AndLeft(newEquivPos), 0)
        .apply(AndLeft(newEquivPos), 1)

    if(targetPos.isAnte) {
      /*
       * Positive subgoal (A&B) is the result branch. Cleanup as follows:
       *    1. Ante reduces from
       *          G, {target, other} |- D
       *       to
       *          G', other |- D
       *       where G' is G with targetPos hidden, and {target, other} could occur in either direction.
       *       I.e., we just hid both the original targetPos and the new targetPos that came from breaking up the And.
       */
      val positiveSubgoalCleanup = {
        val redundantTargetPosition =
          if (postCut.subgoals(0).ante.last == targetValue) AntePos(postCut.subgoals(0).ante.length - 1)
          else AntePos(postCut.subgoals(0).ante.length - 2)

        postCut
          .apply(HideLeft(redundantTargetPosition), 0)
          .apply(HideLeft(targetPos.checkAnte.top), 0)
      }

      /*
       * Negative subgoal (!A&!B) closes:
       *   1. Identify location of negated other of equivalence
       *   2.
       */
      val negatedTargetPos =
        if(positiveSubgoalCleanup.subgoals(1).ante.last == Not(targetValue))
          AntePos(positiveSubgoalCleanup.subgoals(1).ante.length - 1)
        else
          AntePos(positiveSubgoalCleanup.subgoals(1).ante.length - 2)
      val unNegatedTargetPos = SuccPos(positiveSubgoalCleanup.subgoals(1).succ.length)

      positiveSubgoalCleanup
        .apply(NotLeft(negatedTargetPos), 1)
        .apply(Close(targetPos.checkAnte.top, unNegatedTargetPos), 1)
    }
    else { //targetPos is in the succedent.
      val anteTargetPos =
        if (postCut.subgoals(0).ante.last == targetValue) AntePos(postCut.subgoals(0).ante.length - 1)
        else AntePos(postCut.subgoals(0).ante.length - 2)

      val negatedOtherPos =
        if (postCut.subgoals(1).ante.last == Not(otherValue)) AntePos(postCut.subgoals(1).ante.length - 1)
        else AntePos(postCut.subgoals(1).ante.length - 2)

      postCut
        .apply(Close(anteTargetPos, targetPos.checkSucc.top), 0)
        .apply(HideRight(targetPos.checkSucc.top), 0) //@note these are not position 0 instead of position 1 because the other goal has now closed.
        .apply(NotLeft(negatedOtherPos), 0)
        .apply(HideLeft(AntePos(postCut.subgoals(1).ante.length-2)), 0)
    }
  }
  @Tactic("instantiatedEquivRewriting")
  val instantiatedEquivRewriting: BuiltInTwoPositionTactic = anon ((p: ProvableSig, equivPos: Position, targetPos: Position) => instantiatedEquivRewritingImpl(p, equivPos, targetPos))

  //endregion

  /** Proves equivalence of `p` and `q` by axiom `ax` after applying `trafos`. */
  private def equivByAx(p: Formula, q: Formula, ax: AxiomInfo,
                   trafos: List[ProvableSig=>ProvableSig] = List.empty): (Formula, ProvableSig) = {
    (q, trafos.foldLeft(ProvableSig.startProof(Equiv(p, q)))({
      case (p, t) =>
        val Equiv(l, r) = p.conclusion.succ.head
        if (l != r) t(p)
        else p
    })(byUS(ax.provable).result _, 0))
  }

  /**
   * Negation normal form with proof.
   * @see [[FormulaTools.negationNormalForm]]
   */
  def negationNormalForm(fml: Formula): (Formula, ProvableSig) = fml match {
    case p: AtomicFormula => (p, ProvableSig.startProof(Equiv(p, p))(byUS(Ax.equivReflexive.provable).result _, 0))
    case Not(g:AtomicFormula) => g match {
      case Equal(a, b)        => equivByAx(fml, NotEqual(a, b),     Ax.notEqual)
      case NotEqual(a, b)     => equivByAx(fml, Equal(a, b),        Ax.notNotEqual)
      case Greater(a, b)      => equivByAx(fml, LessEqual(a, b),    Ax.notGreater)
      case GreaterEqual(a, b) => equivByAx(fml, Less(a, b),         Ax.notGreaterEqual)
      case Less(a, b)         => equivByAx(fml, GreaterEqual(a, b), Ax.notLess)
      case LessEqual(a, b)    => equivByAx(fml, Greater(a, b),      Ax.notLessEqual)
      case True      => (False, ProvableSig.startProof(Equiv(fml, False))(PropositionalTactics.prop.result _, 0))
      case False     => (True,  ProvableSig.startProof(Equiv(fml, True))(PropositionalTactics.prop.result _, 0))
      case _: PredOf => (fml,   ProvableSig.startProof(Equiv(fml, fml))(byUS(Ax.equivReflexive.provable).result _, 0))
      case _ => throw new IllegalArgumentException("negationNormalForm of formula " + fml + " not implemented")
    }
    case Not(g: CompositeFormula) => g match {
      case Not(p) =>
        val pr = negationNormalForm(p)
        equivByAx(fml, pr._1, Ax.doubleNegation, List(
          useAt(pr._2, PosInExpr(List(1)))(SuccPosition.base0(0, PosInExpr(List(1)))).computeResult))
      case And(p, q) =>
        val pr = negationNormalForm(Not(p))
        val qr = negationNormalForm(Not(q))
        equivByAx(fml, Or(pr._1, qr._1), Ax.notAnd, List(
          useAt(pr._2, PosInExpr(List(1)))(SuccPosition.base0(0, PosInExpr(List(1, 0)))).computeResult,
          useAt(qr._2, PosInExpr(List(1)))(SuccPosition.base0(0, PosInExpr(List(1, 1)))).computeResult))
      case Or(p, q) =>
        val pr = negationNormalForm(Not(p))
        val qr = negationNormalForm(Not(q))
        equivByAx(fml, And(pr._1, qr._1), Ax.notOr, List(
          useAt(pr._2, PosInExpr(List(1)))(SuccPosition.base0(0, PosInExpr(List(1, 0)))).computeResult,
          useAt(qr._2, PosInExpr(List(1)))(SuccPosition.base0(0, PosInExpr(List(1, 1)))).computeResult))
      case Imply(p, q) =>
        val pr = negationNormalForm(p)
        val qr = negationNormalForm(Not(q))
        equivByAx(fml, And(pr._1, qr._1), Ax.notImply, List(
          useAt(pr._2, PosInExpr(List(1)))(SuccPosition.base0(0, PosInExpr(List(1, 0)))).computeResult,
          useAt(qr._2, PosInExpr(List(1)))(SuccPosition.base0(0, PosInExpr(List(1, 1)))).computeResult))
      case Equiv(p, q) =>
        val pr = negationNormalForm(p)
        val npr = negationNormalForm(Not(p))
        val qr = negationNormalForm(q)
        val nqr = negationNormalForm(Not(q))
        equivByAx(fml, Or(And(pr._1, nqr._1), And(npr._1, qr._1)), Ax.notEquiv, List(
          useAt(pr._2,  PosInExpr(List(1)))(SuccPosition.base0(0, PosInExpr(List(1, 0, 0)))).computeResult,
          useAt(nqr._2, PosInExpr(List(1)))(SuccPosition.base0(0, PosInExpr(List(1, 0, 1)))).computeResult,
          useAt(npr._2, PosInExpr(List(1)))(SuccPosition.base0(0, PosInExpr(List(1, 1, 0)))).computeResult,
          useAt(qr._2,  PosInExpr(List(1)))(SuccPosition.base0(0, PosInExpr(List(1, 1, 1)))).computeResult))
      case Forall(vs, p) =>
        val pr = negationNormalForm(Not(p))
        equivByAx(fml, Exists(vs, pr._1), Ax.notAll, List(
          useAt(pr._2,  PosInExpr(List(1)))(SuccPosition.base0(0, PosInExpr(List(1, 0)))).computeResult))
      case Exists(vs, p) =>
        val pr = negationNormalForm(Not(p))
        equivByAx(fml, Forall(vs, pr._1), Ax.notExists, List(
          useAt(pr._2,  PosInExpr(List(1)))(SuccPosition.base0(0, PosInExpr(List(1, 0)))).computeResult))
      case Box(prg, p) =>
        val pr = negationNormalForm(Not(p))
        equivByAx(fml, Diamond(prg, pr._1), Ax.notBox, List(
          useAt(pr._2,  PosInExpr(List(1)))(SuccPosition.base0(0, PosInExpr(List(1, 1)))).computeResult))
      case Diamond(prg, p) =>
        val pr = negationNormalForm(Not(p))
        equivByAx(fml, Box(prg, pr._1), Ax.notDiamond, List(
          useAt(pr._2,  PosInExpr(List(1)))(SuccPosition.base0(0, PosInExpr(List(1, 1)))).computeResult))
      case _ => throw new IllegalArgumentException("negationNormalForm of formula " + fml + " not implemented")
    }
    case Imply(p, q) =>
      val pr = negationNormalForm(Not(p))
      val qr = negationNormalForm(q)
      equivByAx(fml, Or(pr._1, qr._1), Ax.implyExpand, List(
        useAt(pr._2, PosInExpr(List(1)))(SuccPosition.base0(0, PosInExpr(List(1, 0)))).computeResult,
        useAt(qr._2, PosInExpr(List(1)))(SuccPosition.base0(0, PosInExpr(List(1, 1)))).computeResult))
    case Equiv(p, q) =>
      val pr = negationNormalForm(p)
      val npr = negationNormalForm(Not(p))
      val qr = negationNormalForm(q)
      val nqr = negationNormalForm(Not(q))
      equivByAx(fml, Or(And(pr._1, qr._1), And(npr._1, nqr._1)), Ax.equivExpandAnd, List(
        useAt(pr._2,  PosInExpr(List(1)))(SuccPosition.base0(0, PosInExpr(List(1, 0, 0)))).computeResult,
        useAt(qr._2,  PosInExpr(List(1)))(SuccPosition.base0(0, PosInExpr(List(1, 0, 1)))).computeResult,
        useAt(npr._2, PosInExpr(List(1)))(SuccPosition.base0(0, PosInExpr(List(1, 1, 0)))).computeResult,
        useAt(nqr._2, PosInExpr(List(1)))(SuccPosition.base0(0, PosInExpr(List(1, 1, 1)))).computeResult))
    case f: BinaryCompositeFormula =>
      val ar = negationNormalForm(f.left)
      val br = negationNormalForm(f.right)
      equivByAx(f, f.reapply(ar._1, br._1), Ax.equivReflexive, List(
        useAt(ar._2, PosInExpr(List(1)))(SuccPosition.base0(0, PosInExpr(List(1, 0)))).computeResult,
        useAt(br._2, PosInExpr(List(1)))(SuccPosition.base0(0, PosInExpr(List(1, 1)))).computeResult))
    case f: Quantified             =>
      val ar = negationNormalForm(f.child)
      equivByAx(f, f.reapply(f.vars, ar._1), Ax.equivReflexive, List(
        useAt(ar._2, PosInExpr(List(1)))(SuccPosition.base0(0, PosInExpr(List(1, 0)))).computeResult))
    case f: Modal                  =>
      val ar = negationNormalForm(f.child)
      equivByAx(f, f.reapply(f.program, ar._1), Ax.equivReflexive, List(
        useAt(ar._2, PosInExpr(List(1)))(SuccPosition.base0(0, PosInExpr(List(1, 0)))).computeResult))
    case _ => throw new IllegalArgumentException("negationNormalForm of formula " + fml + " not implemented")
  }

  /** Performs a right-associate proof step. */
  private def rightAssociateStep(l: Formula, r: Formula,
                                 split: Formula=>List[Formula], merge: (Formula, Formula)=>Formula,
                                 prop: BuiltInTactic): (Formula, ProvableSig) = {
    val components = split(l) ++ split(r)
    val result = components.map(rightAssociate)
    val resultFml = result.map(_._1).reduceRight(merge)
    val resultAppliedSubproofs = (ProvableSig.startProof(Equiv(merge(l, r), resultFml))
      (applySubproofs(result.map(_._2), PosInExpr(List(1)))(SuccPosition.base0(0, PosInExpr(List(1)))).computeResult _, 0)
      (applyTacticAbbrv(prop, prop, result.map(_._1)).result _, 0)
      )
    (resultFml, resultAppliedSubproofs)
  }

  /** Propositional reasoning for only disjunctions. */
  private val propOr = prop(
    { case (_: Or, sp: SuccPos) => List(OrRight(sp)) case _ => List.empty },
    { case (_: Or, ap: AntePos) => List(OrLeft(ap))  case _ => List.empty })(List.empty, List.empty)

  /** Propositional reasoning for only conjunctions. */
  private val propAnd = prop(
    { case (_: And, ap: AntePos) => List(AndLeft(ap))  case _ => List.empty },
    { case (_: And, sp: SuccPos) => List(AndRight(sp)) case _ => List.empty })(List.empty, List.empty)

  /** Propositional reasoning for only conjunctions and disjunctions. */
  private val propAndOr = prop(
    { case (_: And, ap: AntePos) => List(AndLeft(ap))  case (_: Or, sp: SuccPos) => List(OrRight(sp)) case _ => List.empty },
    { case (_: And, sp: SuccPos) => List(AndRight(sp)) case (_: Or, ap: AntePos) => List(OrLeft(ap))  case _ => List.empty })(List.empty, List.empty)

  private val andOrAlpha = prop(
    { case (_: And, ap: AntePos) => List(AndLeft(ap))  case (_: Or, sp: SuccPos) => List(OrRight(sp)) case _ => List.empty },
    { case _ => List.empty })(List.empty, List.empty)

  /** Propositional reasoning for only conjunctions and disjunctions, and applies alpha rules only when right-hand side equal to `p`. */
  private def propOrAnd(p: Formula) = PropositionalTactics.prop(
    { case (_: Or, sp: SuccPos) => List(OrRight(sp)) case (And(_, pp), ap: AntePos) if pp == p => List(AndLeft(ap)) case _ => List.empty },
    { case (_: Or, ap: AntePos) => List(OrLeft(ap)) case (And(_, pp), sp: SuccPos) if pp == p => List(AndRight(sp)) case _ => List.empty })(List.empty, List.empty)

  /** Reassociates `fml` to default right-associativity.
   * @see [[FormulaTools.reassociate]]
   */
  def rightAssociate(fml: Formula): (Formula, ProvableSig) = fml match {
    case Or(l, r) => rightAssociateStep(l, r, FormulaTools.disjuncts, Or, propOr)
    case And(l, r) => rightAssociateStep(l, r, FormulaTools.conjuncts, And, propAnd)
    case _ => (fml, ProvableSig.startProof(Equiv(fml, fml))(UnifyUSCalculus.byUS(Ax.equivReflexive.provable).result _, 0))
  }

  /** Reassociates the formula at position `pos` to default right-associativity. */
  @Tactic()
  def rightAssociate: BuiltInPositionTactic = anon { (p: ProvableSig, pos: Position) =>
    ProofRuleTactics.requireOneSubgoal(p, "PropositionalTactics.rightAssociate")
    p.subgoals.head.sub(pos) match {
      case Some(f: Formula) =>
        val (_, rmp) = rightAssociate(f)
        useAt(rmp)(pos).computeResult(p)
      case f => throw new TacticInapplicableFailure("Expected a formula at position " + pos.prettyString + ", but got " + f.map(_.prettyString))
    }
  }

  /** Apply sub-proofs at a right-associated goal. */
  private def applySubproofs(subProofs: List[ProvableSig], key: PosInExpr): BuiltInPositionTactic = anon { (pr: ProvableSig, pos: Position) =>
    subProofs.zipWithIndex.foldRight(pr)({ case ((pi, i), po) =>
      val Equiv(lp, rp) = pi.conclusion.succ.head
      val subPos = if (i < subProofs.size-1) PosInExpr(List.fill(i)(1) :+ 0) else PosInExpr(List.fill(i)(1))
      if (lp != rp) po(useAt(pi, key)(pos ++ subPos).computeResult _, 0)
      else po
    })
  }

  /** Applies tactic `t` on the subgoals resulting from splitting the equivalence in the only subgoal of `pr`
   * after abbreviating the formulas in `ps` to uninterpreted predicates. */
  private def applyTacticAbbrv(l: BuiltInTactic, r: BuiltInTactic, ps: List[Formula]): BuiltInTactic = anon { (pr: ProvableSig) =>
    assert(pr.subgoals.size == 1 && pr.subgoals.head.succ.size == 1 && pr.subgoals.head.succ.head.isInstanceOf[Equiv])
    val subst = USubst(ps.zipWithIndex.map({ case (p, i) =>
      SubstitutionPair(PredOf(Function("p_", Some(i), Unit, Bool, interpreted=false), Nothing), p)
    }))
    (ProvableSig.startProof(subst.subsDefsInput.foldLeft(pr.subgoals.head.succ.head)({ case (p, s) => p.replaceAll(s.repl, s.what) }))
      (EquivRight(SuccPos(0)), 0)
      (r.result _, 1)
      (l.result _, 0)
      (subst)
      )
  }

  /** Distributes disjunctions over conjunctions in `fml`. */
  def orDistAnd(fml: Formula): (Formula, ProvableSig) = fml match {
    case _: Or =>
      val (conjunctions, others) = FormulaTools.disjuncts(fml).partition(_.isInstanceOf[And])
      assert(others.forall({ case _: AtomicFormula => true case Not(f) => f.isInstanceOf[AtomicFormula] case _ => false}))
      val inner = conjunctions.map(orDistAnd) ++ others.map(p => (p, ProvableSig.startProof(Equiv(p, p))(byUS(Ax.equivReflexive.provable).result _, 0)))
      val result = inner.map(_._1).reduceRight(Or)
      val innerDisjuncts = inner.map(_._1).map(FormulaTools.disjuncts)
      val resultProof = timed(ProvableSig.startProof(Equiv(fml, result))
        (applySubproofs(inner.map(_._2), PosInExpr(List(1)))(SuccPosition.base0(0, PosInExpr(List(1)))).computeResult _, 0)
        (applyTacticAbbrv(propOr, propOr, innerDisjuncts.flatten).result _, 0)
        , "applySubproofs")
      assert(resultProof.isProved)
      (result, resultProof)
    case _: And =>
      val (disjunctions, others) = FormulaTools.conjuncts(fml).partition(_.isInstanceOf[Or])
      assert(others.forall({ case _: AtomicFormula => true case Not(f) => f.isInstanceOf[AtomicFormula] case _ => false}))
      if (disjunctions.nonEmpty) {
        val inner = disjunctions.map(orDistAnd)
        val innerDisjuncts = inner.map(_._1).map(FormulaTools.disjuncts)
        val c = FormulaTools.combinations(innerDisjuncts).map(_.reduceRight(And))

        if (others.nonEmpty) {
          val o = others.reduceRight(And)
          val result = c.map(And(_, o)).reduceRight(Or)

          val dand = disjunctions.reduceRight(And)
          val dAndO = And(dand, o)
          val cor = c.reduceRight(Or)
          val cOrO = And(cor, o)

          // branch on disjunctions left (original formula) and close by assumption
          val revA = anon { (pr: ProvableSig) =>
            ProofRuleTactics.requireOneSubgoal(pr, "")
            val r = pr(andOrAlpha.result _, 0)
            if (r.isProved) r
            else {
              val ror = r(propOr.result _, 0)
              val ralpha = ror.subgoals.indices.foldLeft(ror)({ case (p, i) => p(andOrAlpha.result _, i) })
              ralpha.subgoals.indices.foldRight(ralpha)({ case (i, p) =>
                val s = p.subgoals(i)
                val j = s.succ.indexOf(s.ante.reduceRight(And))
                p(cohideOnlyR(SuccPos(j)).computeResult _, i)(propAnd.result _, i)
              })
            }
          }

          // branch on conjunctions right (orDistAnd formula) and close by contradiction, simplifier uses !p -> (p <-> false)
          val revB = anon { (pr: ProvableSig) =>
            ProofRuleTactics.requireOneSubgoal(pr, "")
            val r = pr(andOrAlpha.result _, 0)
            if (r.isProved) r
            else {
              val rand = r(propAnd.result _, 0)
              val ralpha = rand.subgoals.indices.foldLeft(rand)({ case (p, i) => p(andOrAlpha.result _, i) })
              ralpha.subgoals.indices.foldRight(ralpha)({ case (i, p) =>
                p.subgoals(i).succ.indices.foldRight(p)({
                  case (j, pi) => pi(useAt(Ax.doubleNegation, PosInExpr(List(1)))(SuccPos(j)).computeResult _, i)(NotRight(SuccPos(j)), i)
                })(SimplifierV3.simplify(AntePos(0)).computeResult _, i)(CloseFalse(AntePos(0)), i)
              })
            }
          }

          val orDistAndRevProof = timed(ProvableSig.startProof(Equiv(dand, cor))
            (applySubproofs(inner.map(_._2), PosInExpr(List(0)))(SuccPosition.base0(0, PosInExpr(List(0)))).computeResult _, 0)
            (applyTacticAbbrv(revA, revB, innerDisjuncts.flatten).result _, 0)
            , "orDistAndReverse")
          assert(orDistAndRevProof.isProved, "Expected proved orDistAndRev proof, but got open goals")

          val combineProof = timed(ProvableSig.startProof(Equiv(cOrO, dAndO))
            (EquivRight(SuccPos(0)), 0)
            (AndLeft(AntePos(0)), 1)
            (AndRight(SuccPos(0)), 1)
            (Close(AntePos(1), SuccPos(0)), 2)
            (useAt(orDistAndRevProof, PosInExpr(List(1)))(SuccPos(0)).computeResult _, 1)
            (Close(AntePos(0), SuccPos(0)), 1)
            (AndLeft(AntePos(0)), 0)
            (AndRight(SuccPos(0)), 0)
            (Close(AntePos(1), SuccPos(0)), 1)
            (useAt(orDistAndRevProof, PosInExpr(List(1)))(AntePos(0)).computeResult _, 0)
            (Close(AntePos(0), SuccPos(0)), 0)
            , "combineProof")
          assert(combineProof.isProved)

          val mixOProof = timed(ProvableSig.startProof(Equiv(result, cOrO))
            (applyTacticAbbrv(propOrAnd(o), propOrAnd(o), innerDisjuncts.flatten).result _, 0)
            , "mixOProof")
          assert(mixOProof.isProved)

          val resultProof = timed(ProvableSig.startProof(Equiv(fml, result))
            (useAt(mixOProof)(SuccPosition.base0(0, PosInExpr(List(1)))).computeResult _, 0)
            (useAt(combineProof)(SuccPosition.base0(0, PosInExpr(List(1)))).computeResult _, 0)
            (applyTacticAbbrv(propAnd, propAnd, innerDisjuncts.flatten).result _, 0)
            , "resultProof")
          assert(resultProof.isProved)

          (result, resultProof)
        } else {
          val result = c.reduceRight(Or)
          val rearranged = disjunctions.reduceRight(And)
          val disjuncts = disjunctions.flatMap(FormulaTools.disjuncts)
          val combineProof = timed(ProvableSig.startProof(Equiv(result, rearranged))
            (applyTacticAbbrv(propAndOr, propAndOr, disjuncts).result _, 0)
            , "combineProof (2)")
          assert(combineProof.isProved)

          val resultProof = timed(ProvableSig.startProof(Equiv(fml, result))
            (useAt(combineProof)(SuccPosition.base0(0, PosInExpr(List(1)))).computeResult _, 0)
            (applyTacticAbbrv(propAnd, propAnd, disjuncts).result _, 0)
            , "resultProof (2)")
          assert(resultProof.isProved)

          (result, resultProof)
        }
      } else {
        (fml, ProvableSig.startProof(Equiv(fml, fml))(byUS(Ax.equivReflexive.provable).result _, 0))
      }
    case f =>
      assert(f match { case _: AtomicFormula => true case Not(f) => f.isInstanceOf[AtomicFormula] case _ => false})
      (f, ProvableSig.startProof(Equiv(f, f))(byUS(Ax.equivReflexive.provable).result _, 0))
  }

  /** Turns `fml` into disjunctive normal form. */
  def disjunctiveNormalForm(fml: Formula): (Formula, ProvableSig) = {
    val nnf = PropositionalTactics.negationNormalForm(fml)
    assert(nnf._2.isProved, "Expected proved negation normal form transformation, but got open goals")
    val d = orDistAnd(nnf._1)
    assert(d._2.isProved, "Expected proved orDistAnd proof, but got open goals")
    val r = rightAssociate(d._1)
    val rproof = (ProvableSig.startProof(Equiv(fml, r._1))
      (useAt(r._2, PosInExpr(List(1)))(SuccPosition.base0(0, PosInExpr(List(1)))).computeResult _, 0)
      (useAt(d._2, PosInExpr(List(1)))(SuccPosition.base0(0, PosInExpr(List(1)))).computeResult _, 0)
      (byUS(nnf._2).result _, 0)
      )
    assert(rproof.isProved, "Expected proved disjunctive normal form proof, but got open goals")
    (r._1, rproof)
  }
}
