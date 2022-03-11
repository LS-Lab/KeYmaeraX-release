package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import TacticFactory._
import edu.cmu.cs.ls.keymaerax.core.{Close, Cut, EquivLeft, NotLeft}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.{Logging, core}
import edu.cmu.cs.ls.keymaerax.infrastruct.{AntePosition, PosInExpr, Position, RenUSubst, SuccPosition, UnificationMatchUSubstAboveURen}
import edu.cmu.cs.ls.keymaerax.btactics.macros.{Tactic, TacticInfo}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.annotation.tailrec
import scala.collection.immutable.{::, List, Nil}
import scala.util.Try

/**
 * [[PropositionalTactics]] provides tactics for propositional reasoning.
 */
private object PropositionalTactics extends Logging {
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
  val prop: BuiltInTactic = prop(List.empty, List.empty)
  private def prop(alpha: List[PositionRule], beta: List[PositionRule]): BuiltInTactic = anon { provable: ProvableSig =>
    ProofRuleTactics.requireOneSubgoal(provable, "PropositionalTactics.prop")

    /** Returns the alpha rules for `fml`, applied at position `p`. */
    def alphaRule(fml: Formula, p: SeqPos): List[PositionRule] = (fml, p) match {
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
    def betaRule(fml: Formula, p: SeqPos): List[PositionRule] = (fml, p) match {
      case (_: And,   sp: SuccPos) => List(AndRight(sp))
      case (_: Equiv, sp: SuccPos) => List(EquivRight(sp))
      case (_: Or,    ap: AntePos) => List(OrLeft(ap))
      case (_: Imply, ap: AntePos) => List(ImplyLeft(ap))
      case (_: Equiv, ap: AntePos) => List(EquivLeft(ap))
      case _ => Nil
    }

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
              provable(rule, 0)(prop(
                alphaRule(r, AntePos(s.ante.length)) ++ alphaRule(l, AntePos(s.ante.length-1)) ++ tail,
                betaRule(r, AntePos(s.ante.length)) ++ betaRule(l, AntePos(s.ante.length-1)) ++ repositionBeta(beta, pos)
              ).result _, 0)
            case Or(l, r) =>
              assert(pos.isSucc)
              provable(rule, 0)(prop(
                alphaRule(r, SuccPos(s.succ.length)) ++ alphaRule(l, SuccPos(s.succ.length-1)) ++ tail,
                betaRule(r, SuccPos(s.succ.length)) ++ betaRule(l, SuccPos(s.succ.length-1)) ++ repositionBeta(beta, pos)
              ).result _, 0)
            case Imply(l, r) =>
              assert(pos.isSucc)
              provable(rule, 0)(prop(
                alphaRule(r, SuccPos(s.succ.length-1)) ++ alphaRule(l, AntePos(s.ante.length)) ++ tail,
                betaRule(r, SuccPos(s.succ.length-1)) ++ betaRule(l, AntePos(s.ante.length)) ++ repositionBeta(beta, pos)
              ).result _, 0)
            case Not(f) =>
              val p = if (pos.isSucc) AntePos(s.ante.length) else SuccPos(s.succ.length)
              provable(rule, 0)(prop(alphaRule(f, p) ++ tail, betaRule(f, p) ++ repositionBeta(beta, pos)).result _, 0)
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
                val propLeft = prop(alphaRule(l, pos), betaRule(l, pos) ++ tail)
                val propRight = prop(alphaRule(r, pos), betaRule(r, pos) ++ tail)
                provable(rule, 0)(propRight.result _, 1)(propLeft.result _, 0)
              case Or(l, r) =>
                assert(pos.isAnte)
                val propLeft = prop(alphaRule(l, pos), betaRule(l, pos) ++ tail)
                val propRight = prop(alphaRule(r, pos), betaRule(r, pos) ++ tail)
                provable(rule, 0)(propRight.result _, 1)(propLeft.result _, 0)
              case Imply(l, r) =>
                assert(pos.isAnte)
                val propLeft = prop(alphaRule(l, SuccPos(s.succ.length)), betaRule(l, SuccPos(s.succ.length)) ++ tail)
                val propRight = prop(alphaRule(r, pos), betaRule(r, pos) ++ tail)
                provable(rule, 0)(propRight.result _, 1)(propLeft.result _, 0)
              case Equiv(l, r) =>
                if (pos.isSucc) {
                  //@see [[EquivRight]]
                  val propLeft = prop(
                    alphaRule(r, SuccPos(s.succ.length-1)) ++ alphaRule(l, AntePos(s.ante.length)),
                    betaRule(r, SuccPos(s.succ.length-1)) ++ betaRule(l, AntePos(s.ante.length)) ++ tail
                  )
                  val propRight = prop(
                    alphaRule(l, SuccPos(s.succ.length-1)) ++ alphaRule(r, AntePos(s.ante.length)),
                    betaRule(l, SuccPos(s.succ.length-1)) ++ betaRule(r, AntePos(s.ante.length)) ++ tail
                  )
                  provable(rule, 0)(propRight.result _, 1)(propLeft.result _, 0)
                } else {
                  //@see [[EquivLeft]]
                  val propLeft = prop(List(AndLeft(pos.asInstanceOf[AntePos])), tail)
                  val propRight = prop(List(AndLeft(pos.asInstanceOf[AntePos])), tail)
                  provable(rule, 0)(propRight.result _, 1)(propLeft.result _, 0)
                }
            }
          case Nil =>
            val alpha =
              s.succ.zipWithIndex.flatMap({ case (fml, i) => alphaRule(fml, SuccPos(i)) }).reverse ++
              s.ante.zipWithIndex.flatMap({ case (fml, i) => alphaRule(fml, AntePos(i)) }).reverse
            val beta =
              s.succ.zipWithIndex.flatMap({ case (fml, i) => betaRule(fml, SuccPos(i)) }).reverse ++
              s.ante.zipWithIndex.flatMap({ case (fml, i) => betaRule(fml, AntePos(i)) }).reverse
            if (alpha.nonEmpty || beta.nonEmpty) prop(alpha.toList, beta.toList).result(provable)
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

}
