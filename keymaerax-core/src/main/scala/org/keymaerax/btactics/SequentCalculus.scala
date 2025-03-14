/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon.*
import org.keymaerax.btactics.ProofRuleTactics.requireOneSubgoal
import org.keymaerax.btactics.TacticFactory.*
import org.keymaerax.btactics.TactixLibrary.exhaustiveEqL2R
import org.keymaerax.btactics.UnifyUSCalculus.{uniformRename, useAt}
import org.keymaerax.btactics.macros.{
  DisplayLevel,
  FormulaArg,
  InputPositionTacticInfo,
  InputTacticInfo,
  OptionArg,
  PlainTacticInfo,
  PositionTacticInfo,
  StringArg,
  TacticConstructor0,
  TacticConstructor1,
  TacticConstructor2,
  TermArg,
  TwoPositionTacticInfo,
  VariableArg,
}
import org.keymaerax.core
import org.keymaerax.core.*
import org.keymaerax.core.btactics.annotations.Derivation
import org.keymaerax.infrastruct.Augmentors.*
import org.keymaerax.infrastruct.{AntePosition, PosInExpr, Position, SuccPosition}
import org.keymaerax.pt.ProvableSig

import scala.annotation.nowarn

/**
 * Sequent Calculus for propositional and first-order logic.
 * @author
 *   Andre Platzer
 * @author
 *   Stefan Mitsch
 * @see
 *   Andre Platzer. [[https://doi.org/10.1007/s10817-008-9103-8 Differential dynamic logic for hybrid systems]]. Journal
 *   of Automated Reasoning, 41(2), pages 143-189, 2008.
 * @see
 *   Andre Platzer. [[https://doi.org/10.1007/978-3-319-63588-0 Logical Foundations of Cyber-Physical Systems]].
 *   Springer, 2018.
 * @see
 *   [[org.keymaerax.core.Rule]]
 * @see
 *   [[TactixLibrary]]
 * @Tactic
 *   complete
 */
@nowarn("msg=match may not be exhaustive")
@nowarn("cat=deprecation&origin=org.keymaerax.btactics.ProofRuleTactics.closeTrue")
@nowarn("cat=deprecation&origin=org.keymaerax.btactics.ProofRuleTactics.closeFalse")
object SequentCalculus {
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Propositional tactics

  /** Hide/weaken whether left or right */
  val hide: BuiltInPositionTactic = "hide".by { (pr: ProvableSig, pos: Position) =>
    pos match {
      case p: AntePosition => SequentCalculus.hideL(p).computeResult(pr)
      case p: SuccPosition => SequentCalculus.hideR(p).computeResult(pr)
    }
  }

  @Derivation
  val hideInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "hide",
    displayName = Some("W"),
    displayNameLong = Some("Weaken"),
    displayPremises = "Γ |- Δ",
    displayConclusion = "Γ |- P, Δ",
    constructor = TacticConstructor0.create()(() => hide),
  )

  /** Hide/weaken left: weaken a formula to drop it from the antecedent ([[org.keymaerax.core.HideLeft HideLeft]]) */
  val hideL: CoreLeftTactic = "hideL".coreby { (pr: ProvableSig, pos: AntePosition) => pr(HideLeft(pos.checkTop), 0) }

  @Derivation
  val hideLInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "hideL",
    displayName = Some("WL"),
    displayNameLong = Some("Weaken Left"),
    displayPremises = "Γ |- Δ",
    displayConclusion = "Γ, P |- Δ",
    constructor = TacticConstructor0.create()(() => hideL),
  )

  /** Hide/weaken right: weaken a formula to drop it from the succcedent ([[org.keymaerax.core.HideRight HideRight]]) */
  val hideR: CoreRightTactic = "hideR".coreby { (pr: ProvableSig, pos: SuccPosition) => pr(HideRight(pos.checkTop), 0) }

  @Derivation
  val hideRInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "hideR",
    displayName = Some("WR"),
    displayNameLong = Some("Weaken Right"),
    displayPremises = "Γ |- Δ",
    displayConclusion = "Γ |- P, Δ",
    constructor = TacticConstructor0.create()(() => hideR),
  )

  /** CoHide/weaken left: drop all other formulas from the sequent ([[org.keymaerax.core.CoHideLeft CoHideLeft]]) */
  val cohideL: CoreLeftTactic = "cohideL".coreby { (pr: ProvableSig, pos: AntePosition) =>
    pr(CoHideLeft(pos.checkTop), 0)
  }

  @Derivation
  val cohideLInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "cohideL",
    displayName = Some("WL"),
    displayNameLong = Some("Co-Weaken Left"),
    displayPremises = "P |- ",
    displayConclusion = "Γ, P |- Δ",
    constructor = TacticConstructor0.create()(() => cohideL),
  )

  /** CoHide/weaken right: drop all other formulas from the sequent ([[org.keymaerax.core.CoHideRight CoHideRight]]) */
  val cohideR: CoreRightTactic = "cohideR".coreby { (pr: ProvableSig, pos: SuccPosition) =>
    pr(CoHideRight(pos.checkTop), 0)
  }

  @Derivation
  val cohideRInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "cohideR",
    displayName = Some("WR"),
    displayNameLong = Some("Co-Weaken Right"),
    displayPremises = "|- P",
    displayConclusion = "Γ |- P, Δ",
    constructor = TacticConstructor0.create()(() => cohideR),
  )

  /**
   * CoHide/coweaken whether left or right: drop all other formulas from the sequent ([[org.keymaerax.core.CoHideLeft
   * CoHideLeft]])
   */
  val cohide: BuiltInPositionTactic = "cohide".by { (pr: ProvableSig, pos: Position) =>
    pos match {
      case p: AntePosition => SequentCalculus.cohideL(p).computeResult(pr)
      case p: SuccPosition => SequentCalculus.cohideR(p).computeResult(pr)
    }
  }

  @Derivation
  val cohideInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "cohide",
    displayName = Some("W"),
    displayNameLong = Some("Co-Weaken"),
    displayPremises = "|- P",
    displayConclusion = "Γ |- P, Δ",
    constructor = TacticConstructor0.create()(() => cohide),
  )

  /**
   * CoHide2/coweaken2 both left and right: drop all other formulas from the sequent ([[org.keymaerax.core.CoHide2
   * CoHide2]])
   */
  val cohide2: BuiltInTwoPositionTactic = "coHide2".by { (pr: ProvableSig, ante: Position, succ: Position) =>
    require(ante.isAnte && succ.isSucc, "Expects an antecedent and a succedent position.")
    pr(CoHide2(ante.checkAnte.top, succ.checkSucc.top), 0)
  }

  @Derivation
  val coHide2Info: TwoPositionTacticInfo = TwoPositionTacticInfo.create(
    name = "coHide2",
    displayName = Some("WLR"),
    displayNameLong = Some("Co-Weaken Both"),
    displayPremises = "P |- Q",
    displayConclusion = "Γ, P |- Q, Δ",
    constructor = TacticConstructor0.create()(() => cohide2),
  )

  /** Cohides in succedent, but leaves antecedent as is. */
  val cohideOnlyR: BuiltInRightTactic = "cohideOnlyR".by { (pr: ProvableSig, pos: SuccPosition) =>
    val hiddenUntil = (1 to pos.checkTop.getIndex).foldLeft(pr)({ case (p, _) => hideR(1).computeResult(p) })
    (2 to hiddenUntil.subgoals.head.succ.length).foldLeft(hiddenUntil)({ case (p, _) => hideR(2).computeResult(p) })
  }

  @Derivation
  val cohideOnlyRInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "cohideOnlyR",
    displayName = Some("WR"),
    displayNameLong = Some("Co-Weaken Only Right"),
    displayPremises = "Γ, P |- Q",
    displayConclusion = "Γ, P |- Q, Δ",
    constructor = TacticConstructor0.create()(() => cohideOnlyR),
  )

  /** Cohides in antecedent, but leaves succedent as is. */
  val cohideOnlyL: BuiltInLeftTactic = "cohideOnlyL".by { (pr: ProvableSig, pos: AntePosition) =>
    val hiddenUntil = (1 to pos.checkTop.getIndex).foldLeft(pr)({ case (p, _) => hideL(-1).computeResult(p) })
    (2 to hiddenUntil.subgoals.head.ante.length).foldLeft(hiddenUntil)({ case (p, _) => hideL(-2).computeResult(p) })
  }

  @Derivation
  val cohideOnlyLInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "cohideOnlyL",
    displayName = Some("WL"),
    displayNameLong = Some("Co-Weaken Only Left"),
    displayPremises = "|- Q, Δ",
    displayConclusion = "Γ, P |- Q, Δ",
    constructor = TacticConstructor0.create()(() => cohideOnlyL),
  )

  /** !L Not left: move an negation in the antecedent to the succedent ([[org.keymaerax.core.NotLeft NotLeft]]) */
  val notL: CoreLeftTactic = "notL".coreby { (pr: ProvableSig, pos: AntePosition) => pr(NotLeft(pos.checkTop), 0) }

  @Derivation
  val notLInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "notL",
    displayName = Some("¬L"),
    displayNameAscii = Some("!L"),
    displayPremises = "Γ |- P, Δ",
    displayConclusion = "¬P, Γ |- Δ",
    constructor = TacticConstructor0.create()(() => notL),
  )

  /** !R Not right: move an negation in the succedent to the antecedent ([[org.keymaerax.core.NotRight NotRight]]) */
  val notR: CoreRightTactic = "notR".coreby { (pr: ProvableSig, pos: SuccPosition) => pr(NotRight(pos.checkTop), 0) }

  @Derivation
  val notRInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "notR",
    displayName = Some("¬R"),
    displayNameAscii = Some("!R"),
    displayPremises = "Γ, P |- Δ",
    displayConclusion = "Γ |- ¬P, Δ",
    constructor = TacticConstructor0.create()(() => notR),
  )

  /**
   * &L And left: split a conjunction in the antecedent into separate assumptions ([[org.keymaerax.core.AndLeft
   * AndLeft]])
   */
  val andL: CoreLeftTactic = "andL".coreby { (pr: ProvableSig, pos: AntePosition) => pr(AndLeft(pos.checkTop), 0) }

  @Derivation
  val andLInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "andL",
    displayName = Some("∧L"),
    displayNameAscii = Some("&L"),
    displayPremises = "Γ, P, Q |- Δ",
    displayConclusion = "P∧Q, Γ |- Δ",
    constructor = TacticConstructor0.create()(() => andL),
  )

  /**
   * Inverse of [[andL]].
   * {{{
   *   G, G', G'', a&b  |- D
   * -------------------------
   *   G, a, G', b, G'' |- D
   * }}}
   */
  def andLi(keepLeft: Boolean): BuiltInTwoPositionTactic = PropositionalTactics.andLi(keepLeft)
  val andLi: AppliedBuiltinTwoPositionTactic = andLi(keepLeft = false)(AntePos(0), AntePos(1))

  /**
   * &R And right: prove a conjunction in the succedent on two separate branches ([[org.keymaerax.core.AndRight
   * AndRight]])
   */
  val andR: DependentPositionTactic = "andR".by { (pos: Position, seq: Sequent) =>
    corelabelledby("andR", Right(andRRule), And.unapply, pos, seq)
  }

  @Derivation
  val andRInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "andR",
    displayName = Some("∧R"),
    displayNameAscii = Some("&R"),
    displayPremises = "Γ |- P, Δ ;; Γ |- Q, Δ",
    displayConclusion = "Γ |- P∧Q, Δ",
    constructor = TacticConstructor0.create()(() => andR),
  )

  val andRRule: CoreRightTactic = "andRRule".coreby { (pr: ProvableSig, pos: SuccPosition) =>
    pr(AndRight(pos.checkTop), 0)
  }

  @Derivation
  val andRRuleInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "andRRule",
    displayName = Some("∧R"),
    displayNameAscii = Some("&R"),
    displayPremises = "Γ |- P, Δ ;; Γ |- Q, Δ",
    displayConclusion = "Γ |- P∧Q, Δ",
    constructor = TacticConstructor0.create()(() => andRRule),
  )

  /**
   * \|L Or left: use a disjunction in the antecedent by assuming each option on separate branches
   * ([[org.keymaerax.core.OrLeft OrLeft]])
   */
  val orL: DependentPositionTactic = "orL".by { (pos: Position, seq: Sequent) =>
    corelabelledby("orL", Left(orLRule), Or.unapply, pos, seq)
  }

  @Derivation
  val orLInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "orL",
    displayName = Some("∨L"),
    displayNameAscii = Some("|L"),
    displayPremises = "P, Γ |- Δ ;; Q, Γ |- Δ",
    displayConclusion = "P∨Q, Γ |- Δ",
    constructor = TacticConstructor0.create()(() => orL),
  )

  val orLRule: CoreLeftTactic = "orLRule".coreby { (pr: ProvableSig, pos: AntePosition) => pr(OrLeft(pos.checkTop), 0) }

  @Derivation
  val orLRuleInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "orLRule",
    displayName = Some("∨L"),
    displayNameAscii = Some("|L"),
    displayPremises = "P, Γ |- Δ ;; Q, Γ |- Δ",
    displayConclusion = "P∨Q, Γ |- Δ",
    constructor = TacticConstructor0.create()(() => orLRule),
  )

  /**
   * Inverse of [[orR]].
   * {{{
   *   G |- D, D', D'', a | b
   * -------------------------
   *   G |- D, a, D', b, D''
   * }}}
   */
  def orRi(keepLeft: Boolean): BuiltInTwoPositionTactic = PropositionalTactics.orRi(keepLeft)
  val orRi: AppliedBuiltinTwoPositionTactic = orRi(keepLeft = false)(SuccPosition.base0(0), SuccPosition.base0(1))

  /**
   * \|R Or right: split a disjunction in the succedent into separate formulas to show alternatively
   * ([[org.keymaerax.core.OrRight OrRight]])
   */
  val orR: CoreRightTactic = "orR".coreby { (pr: ProvableSig, pos: SuccPosition) => pr(OrRight(pos.checkTop), 0) }

  @Derivation
  val orRInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "orR",
    displayName = Some("∨R"),
    displayNameAscii = Some("|R"),
    displayPremises = "Γ |- Δ, P, Q",
    displayConclusion = "Γ |- P∨Q, Δ",
    constructor = TacticConstructor0.create()(() => orR),
  )

  /**
   * ->L Imply left: use an implication in the antecedent by proving its left-hand side on one branch and using its
   * right-hand side on the other branch ([[org.keymaerax.core.ImplyLeft ImplyLeft]])
   */
  val implyL: DependentPositionTactic = "implyL".by { (pos: Position, seq: Sequent) =>
    corelabelledby("implyL", Left(implyLRule), Imply.unapply, pos, seq)
  }

  @Derivation
  val implyLInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "implyL",
    displayName = Some("→L"),
    displayNameAscii = Some("->L"),
    displayPremises = "Γ |- Δ, P ;; Q, Γ |- Δ",
    displayConclusion = "P→Q, Γ |- Δ",
    constructor = TacticConstructor0.create()(() => implyL),
  )

  val implyLRule: CoreLeftTactic = "implyLRule".coreby { (pr: ProvableSig, pos: AntePosition) =>
    pr(ImplyLeft(pos.checkTop), 0)
  }

  @Derivation
  val implyLRuleInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "implyLRule",
    displayName = Some("→L"),
    displayNameAscii = Some("->L"),
    displayPremises = "Γ |- Δ, P ;; Q, Γ |- Δ",
    displayConclusion = "P→Q, Γ |- Δ",
    constructor = TacticConstructor0.create()(() => implyLRule),
  )

  /**
   * ->R Imply right: prove an implication in the succedent by assuming its left-hand side and proving its right-hand
   * side ([[org.keymaerax.core.ImplyRight ImplyRight]])
   */
  val implyR: CoreRightTactic = "implyR".coreby { (pr: ProvableSig, pos: SuccPosition) =>
    pr(ImplyRight(pos.checkTop), 0)
  }

  @Derivation
  val implyRInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "implyR",
    displayName = Some("→R"),
    displayNameAscii = Some("->R"),
    displayPremises = "Γ, P |- Q, Δ",
    displayConclusion = "Γ |- P→Q, Δ",
    constructor = TacticConstructor0.create()(() => implyR),
  )

  /**
   * Inverse of [[implyR]].
   * {{{
   *   G, G' |- D, D', a -> b
   * -------------------------
   *   G, a, G' |- D, b, D'
   * }}}
   */
  def implyRi(keep: Boolean = false): BuiltInTwoPositionTactic = PropositionalTactics.implyRi(keep)
  val implyRi: AppliedBuiltinTwoPositionTactic = implyRi()(AntePos(0), SuccPos(0))

  /** eXternal wrapper for implyRi */
  val implyRiX: BuiltInTwoPositionTactic = "implyRi".forward(PropositionalTactics.implyRi(keep = false))

  @Derivation
  val implyRiInfo: TwoPositionTacticInfo = TwoPositionTacticInfo
    .create(name = "implyRi", constructor = TacticConstructor0.create()(() => implyRiX))

  /**
   * <->L Equiv left: use an equivalence by considering both true or both false cases ([[org.keymaerax.core.EquivLeft
   * EquivLeft]])
   */
  val equivL: DependentPositionTactic = "equivL".by { (pos: Position, seq: Sequent) =>
    corelabelledby(
      "equivL",
      Left(equivLRule),
      Equiv.unapply,
      pos,
      seq,
      (l: Formula, r: Formula) => (And(l, r).prettyString, And(Not(l), Not(r)).prettyString),
    )
  }

  @Derivation
  val equivLInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "equivL",
    displayName = Some("↔L"),
    displayNameAscii = Some("<->L"),
    displayPremises = "P∧Q, Γ |- Δ ;; ¬P∧¬Q, Γ |- Δ",
    displayConclusion = "P↔Q, Γ |- Δ",
    constructor = TacticConstructor0.create()(() => equivL),
  )

  val equivLRule: CoreLeftTactic = "equivLRule".coreby { (pr: ProvableSig, pos: AntePosition) =>
    pr(EquivLeft(pos.checkTop), 0)
  }

  @Derivation
  val equivLRuleInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "equivLRule",
    displayName = Some("↔L"),
    displayNameAscii = Some("<->L"),
    displayPremises = "P∧Q, Γ |- Δ ;; ¬P∧¬Q, Γ |- Δ",
    displayConclusion = "P↔Q, Γ |- Δ",
    constructor = TacticConstructor0.create()(() => equivLRule),
  )

  /**
   * <->R Equiv right: prove an equivalence by proving both implications ([[org.keymaerax.core.EquivRight EquivRight]])
   */
  val equivR: DependentPositionTactic = "equivR".by { (pos: Position, seq: Sequent) =>
    corelabelledby(
      "equivR",
      Right(equivRRule),
      Equiv.unapply,
      pos,
      seq,
      (l: Formula, r: Formula) => (And(l, r).prettyString, And(Not(l), Not(r)).prettyString),
    )
  }

  @Derivation
  val equivRInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "equivR",
    displayName = Some("↔R"),
    displayNameAscii = Some("<->R"),
    displayPremises = "Γ, P |- Δ, Q ;; Γ, Q |- Δ, P",
    displayConclusion = "Γ |- P↔Q, Δ",
    constructor = TacticConstructor0.create()(() => equivR),
  )

  val equivRRule: CoreRightTactic = "equivRRule".coreby { (pr: ProvableSig, pos: SuccPosition) =>
    pr(EquivRight(pos.checkTop), 0)
  }

  @Derivation
  val equivRRuleInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "equivRRule",
    displayName = Some("↔R"),
    displayNameAscii = Some("<->R"),
    displayPremises = "Γ, P |- Δ, Q ;; Γ, Q |- Δ, P",
    displayConclusion = "Γ |- P↔Q, Δ",
    constructor = TacticConstructor0.create()(() => equivRRule),
  )

  /**
   * cut a formula in to prove it on one branch and then assume it on the other. Or to perform a case distinction on
   * whether it holds ([[org.keymaerax.core.Cut Cut]]).
   * {{{
   * Use:          Show:
   * G, c |- D     G |- D, c
   * ----------------------- (cut)
   *         G |- D
   * }}}
   */
  def cut(f: Formula): InputTactic = "cut"
    .byWithInputs(List(f), cutX(f) & Idioms.<(label(BelleLabels.cutUse), label(BelleLabels.cutShow)))

  @Derivation
  val cutInfo: InputTacticInfo = InputTacticInfo.create(
    name = "cut",
    displayPremises = "Γ, C |- Δ ;; Γ |- Δ, C",
    displayConclusion = "Γ |- Δ",
    constructor = TacticConstructor1.create(FormulaArg("C"))((f: Formula) => cut(f)),
  )

  private def cutX(f: Formula): BuiltInTactic = anon { (provable: ProvableSig) => provable(core.Cut(f), 0) }

  /**
   * cut a formula in in place of pos on the right to prove its implication on the second branch and assume it on the
   * first. ([[org.keymaerax.core.CutRight CutRight]]).
   * {{{
   * G |- c, D    G |- c->p, D
   * ------------------------- (Cut right)
   *        G |- p, D
   * }}}
   */
  def cutR(f: Formula): DependentPositionWithAppliedInputTactic = "cutR".corebyWithInputsR(
    List(f),
    { (provable: ProvableSig, pos: SuccPosition) =>
      requireOneSubgoal(provable, "cutR(" + f + ")")
      provable(core.CutRight(f, pos.top), 0)
    },
  )

  @Derivation
  val cutRInfo: InputPositionTacticInfo = InputPositionTacticInfo.create(
    name = "cutR",
    displayPremises = "Γ |- C, Δ ;; Γ |- C→P, Δ",
    displayConclusion = "Γ |- P, Δ",
    constructor = TacticConstructor1.create(FormulaArg("C"))((f: Formula) => cutR(f)),
  )

  /**
   * cut a formula in in place of pos on the left to prove its implication on the second branch and assume it on the
   * first. ([[org.keymaerax.core.CutLeft CutLeft]]).
   * {{{
   * c, G |- D    G |- D, p->c
   * ------------------------- (Cut Left)
   *        p, G |- D
   * }}}
   */
  def cutL(f: Formula): DependentPositionWithAppliedInputTactic = "cutL".corebyWithInputsL(
    List(f),
    { (provable: ProvableSig, pos: AntePosition) =>
      requireOneSubgoal(provable, "cutL(" + f + ")")
      provable(core.CutLeft(f, pos.top), 0)
      // @todo label BelleLabels.cutUse/cutShow
    },
  )

  @Derivation
  val cutLInfo: InputPositionTacticInfo = InputPositionTacticInfo.create(
    name = "cutL",
    displayPremises = "Γ, C |- Δ ;; Γ |- Δ, P→C",
    displayConclusion = "Γ, P |- Δ",
    constructor = TacticConstructor1.create(FormulaArg("C"))((f: Formula) => cutL(f)),
  )

  /**
   * cut a formula in in place of pos to prove its implication on the second branch and assume it on the first (whether
   * pos is left or right). ([[org.keymaerax.core.CutLeft CutLeft]] or [[org.keymaerax.core.CutRight CutRight]]).
   * {{{
   * c, G |- D    G |- D, p->c
   * ------------------------- (Cut Left at antecedent<0)
   *        p, G |- D
   * }}}
   * {{{
   * G |- c, D    G |- c->p, D
   * ------------------------- (Cut right at succedent>0)
   *        G |- p, D
   * }}}
   */
  def cutLR(f: Formula): DependentPositionWithAppliedInputTactic = "cutLR"
    .byWithInputs(List(f), { cutLRFw(f)(_: Position) })

  @Derivation
  val cutLRInfo: InputPositionTacticInfo = InputPositionTacticInfo
    .create(name = "cutLR", constructor = TacticConstructor1.create(FormulaArg("f"))((f: Formula) => cutLR(f)))

  /** Builtin forward implementation of cutLR. */
  private[btactics] def cutLRFw(f: Formula): BuiltInPositionTactic = anon { (provable: ProvableSig, pos: Position) =>
    requireOneSubgoal(provable, "cutLR(" + f + ")")
    if (pos.isAnte) provable(core.CutLeft(f, pos.checkAnte.top), 0)
    else provable(core.CutRight(f, pos.checkSucc.top), 0)
  }

  /**
   * Exchange left rule reorders antecedent.
   * {{{
   * q, p, G |- D
   * ------------- (Exchange left)
   * p, q, G |- D
   * }}}
   */
  val exchangeL: BuiltInTwoPositionTactic = "exchangeL".by { (pr: ProvableSig, posOne: Position, posTwo: Position) =>
    pr(core.ExchangeLeftRule(posOne.checkAnte.top, posTwo.checkAnte.top), 0)
  }

  @Derivation
  val exchangeLInfo: TwoPositionTacticInfo = TwoPositionTacticInfo.create(
    name = "exchangeL",
    displayName = Some("XL"),
    displayNameLong = Some("Exchange Assumptions"),
    displayPremises = "Q, P, Γ |- Δ",
    displayConclusion = "P, Q, Γ |- Δ",
    constructor = TacticConstructor0.create()(() => exchangeL),
  )

  /**
   * Exchange right rule reorders succedent.
   * {{{
   * G |- q, p, D
   * ------------- (Exchange right)
   * G |- p, q, D
   * }}}
   */
  val exchangeR: BuiltInTwoPositionTactic = "exchangeR".by { (pr: ProvableSig, posOne: Position, posTwo: Position) =>
    pr(core.ExchangeRightRule(posOne.checkSucc.top, posTwo.checkSucc.top), 0)
  }

  @Derivation
  val exchangeRInfo: TwoPositionTacticInfo = TwoPositionTacticInfo.create(
    name = "exchangeR",
    displayName = Some("XR"),
    displayNameLong = Some("Exchange Obligations"),
    displayPremises = "Γ |- Q, P, Δ",
    displayConclusion = "Γ |- P, Q, Δ",
    constructor = TacticConstructor0.create()(() => exchangeR),
  )

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // First-order tactics

  // quantifiers
  /**
   * all right: Skolemize a universal quantifier in the succedent ([[org.keymaerax.core.Skolemize Skolemize]])
   * Skolemization with bound renaming on demand.
   * {{{
   * G |- p(x), D
   * ----------------------- (Skolemize) provided x not in G,D
   * G |- \forall x p(x), D
   * }}}
   * @see
   *   [[org.keymaerax.core.Skolemize]]
   * @example
   *   {{{
   *   y>5   |- x^2>=0
   *   --------------------------allSkolemize(1)
   *   y>5   |- \forall x x^2>=0
   *   }}}
   * @example
   *   Uniformly renames other occurrences of the quantified variable in the context on demand to avoid
   *   [[SkolemClashException]].
   *   {{{
   *   x_0>0 |- x^2>=0
   *   --------------------------allSkolemize(1)
   *   x>0   |- \forall x x^2>=0
   *   }}}
   */
  val allR: BuiltInPositionTactic = "allR".forward(FOQuantifierTactics.allSkolemize)

  @Derivation
  val allRInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "allR",
    displayName = Some("∀R"),
    displayNameAscii = Some("allR"),
    displayPremises = "Γ |- p(x), Δ",
    displayConclusion = "Γ |- ∀x p(x), Δ",
    constructor = TacticConstructor0.create()(() => allR),
  )

  def allRi(t: Term, x: scala.Option[Variable]): DependentPositionWithAppliedInputTactic = "allRi"
    .byWithInputs(List(t, x), { FOQuantifierTactics.universalGen(x, t)(_: Position) })

  @Derivation
  val allRiInfo: InputPositionTacticInfo = InputPositionTacticInfo.create(
    name = "allRi",
    displayName = Some("∀Ri"),
    displayNameAscii = Some("allRi"),
    displayLevel = DisplayLevel.Browse,
    displayPremises = "Γ |- ∀x p(f(x)), Δ",
    displayConclusion = "Γ |- p(f(y)), Δ",
    constructor = TacticConstructor2
      .create(TermArg("f"), OptionArg(VariableArg("x", List("x"))))((t: Term, x: scala.Option[Variable]) => allRi(t, x)),
  )

  /**
   * all left: instantiate a universal quantifier for variable `x` in the antecedent by the concrete instance `inst`.
   * {{{
   * p(inst), G |- D
   * ------------------------ ∀L
   * \forall x p(x), G |- D
   * }}}
   */
  def allL(x: Variable, inst: Term): BuiltInPositionTactic = FOQuantifierTactics.allInstantiate(Some(x), Some(inst))

  /** all left: instantiate a universal quantifier in the antecedent by the concrete instance `e` (itself if None). */
  def allL(e: scala.Option[Term]): DependentPositionWithAppliedInputTactic = "allL"
    .byWithInputs(List(e), { FOQuantifierTactics.allInstantiate(None, e)(_: Position) })

  @Derivation
  val allLInfo: InputPositionTacticInfo = InputPositionTacticInfo.create(
    name = "allL",
    displayName = Some("∀L"),
    displayNameAscii = Some("allL"),
    displayPremises = "p(θ), Γ |- Δ",
    displayConclusion = "∀x p(x), Γ |- Δ",
    constructor = TacticConstructor1.create(OptionArg(TermArg("θ", List("θ"))))((e: scala.Option[Term]) => allL(e)),
  )

  def allL(e: Term): DependentPositionWithAppliedInputTactic = allL(Some(e))

  /** all left: instantiate a universal quantifier in the antecedent by itself. */
  val allL: DependentPositionTactic = allL(None)

  /** all left: instantiate a universal quantifier in the antecedent by the term obtained from position `instPos`. */
  // @todo turn this into a more general function that obtains data from the sequent.
  // was  "all instantiate pos"
  def allLPos(instPos: Position): DependentPositionTactic = anon((pos: Position, sequent: Sequent) =>
    sequent.sub(instPos) match {
      case Some(t: Term) => allL(t)(pos)
      case Some(e) =>
        throw new TacticInapplicableFailure("all instantiate pos only applicable to terms, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException(
          "Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString
        )
    }
  )

  /**
   * Universal monotonicity in antecedent: replace `p(x)` with a characteristic property `q(x)`.
   * {{{
   * Use:                      Show:
   * G, \forall x q(x) |- D    G, p(x) |- D, q(x)
   * -------------------------------------------- M∀L
   * G, \forall x p(x) |- D
   * }}}
   */
  def allLmon(q: Formula): DependentPositionWithAppliedInputTactic = "allLmon".byWithInputs(
    List(q),
    { (pos: Position, seq: Sequent) =>
      seq.sub(pos) match {
        // @todo faster implementation uses derived axiom Ax.existsDistElim
        case Some(Forall(x, _)) => cutL(Forall(x, q))(pos) <
            (
              label(BelleLabels.cutUse),
              useAt(Ax.allDistElim)(Symbol("Rlast")) & allR(Symbol("Rlast")) & implyR(Symbol("Rlast")) &
                label(BelleLabels.cutShow),
            )
        case Some(e) => throw new TacticInapplicableFailure(
            "allLmon only applicable to universal quantifiers on the right, but got " + e.prettyString
          )
        case None => throw new IllFormedTacticApplicationException(
            "Position " + pos + " does not point to a valid position in sequent " + seq.prettyString
          )
      }
    },
  )

  @Derivation
  val allLmonInfo: InputPositionTacticInfo = InputPositionTacticInfo.create(
    name = "allLmon",
    displayName = Some("M∀L"),
    displayNameAscii = Some("MallL"),
    displayPremises = "Γ, ∀x q(x) |- Δ ;; Γ, p(x) |- Δ, q(x)",
    displayConclusion = "Γ, ∀x p(x) |- Δ",
    constructor = TacticConstructor1.create(FormulaArg("q(x)"))((q: Formula) => allLmon(q)),
  )

  /**
   * all left keep: keeping around the quantifier, instantiate a universal quantifier in the antecedent by the concrete
   * instance `e`.
   * {{{
   * \forll x p(x), G, p(e) |- D
   * --------------------------- ∀L
   * \forall x p(x), G |- D
   * }}}
   */
  def allLkeep(e: Term): DependentPositionWithAppliedInputTactic = "allLkeep".byWithInputs(
    List(e),
    { (pos: Position, seq: Sequent) =>
      seq.sub(pos) match {
        case Some(Forall(x, p)) => cut(Forall(x, p)) <
            (allL(e)(Symbol("Llast")), closeId(pos, SuccPosition(seq.succ.length + 1)))
        case Some(e) => throw new TacticInapplicableFailure(
            "allLkeep only applicable to universal quantifiers on the right, but got " + e.prettyString
          )
        case None => throw new IllFormedTacticApplicationException(
            "Position " + pos + " does not point to a valid position in sequent " + seq.prettyString
          )
      }
    },
  )

  @Derivation
  val allLkeepInfo: InputPositionTacticInfo = InputPositionTacticInfo.create(
    name = "allLkeep",
    displayName = Some("∀Lk"),
    displayNameAscii = Some("allLk"),
    displayPremises = "∀x p(x), Γ, p(θ) |- Δ",
    displayConclusion = "∀x p(x), Γ |- Δ",
    constructor = TacticConstructor1.create(TermArg("θ", List("θ")))((e: Term) => allLkeep(e)),
  )

  /**
   * exists left: Skolemize an existential quantifier in the antecedent by introducing a new name for the witness.
   * {{{
   *           p(x), G |- D
   * ------------------------ (Skolemize) provided x not in G,D
   * \exists x p(x), G |- D
   * }}}
   */
  val existsL: BuiltInPositionTactic = "existsL".by { (provable: ProvableSig, pos: Position) =>
    FOQuantifierTactics.existsSkolemize(pos).computeResult(provable)
  }

  @Derivation
  val existsLInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "existsL",
    displayName = Some("∃L"),
    displayNameAscii = Some("existsL"),
    displayPremises = "p(x), Γ |- Δ",
    displayConclusion = "∃x p(x), Γ |- Δ",
    constructor = TacticConstructor0.create()(() => existsL),
  )

  def existsLi(t: Term, x: scala.Option[Variable]): DependentPositionWithAppliedInputTactic = "existsLi"
    .byWithInputs(List(t, x), { FOQuantifierTactics.existsGen(x, t)(_: Position) })

  @Derivation
  val existsLiInfo: InputPositionTacticInfo = InputPositionTacticInfo.create(
    name = "existsLi",
    displayName = Some("∃Li"),
    displayNameAscii = Some("existsLi"),
    displayLevel = DisplayLevel.Browse,
    displayPremises = "Γ, ∃x p(f(x)) |- Δ",
    displayConclusion = "Γ, p(f(y)) |- Δ",
    constructor = TacticConstructor2
      .create(TermArg("f"), OptionArg(VariableArg("x", List("x"))))((t: Term, x: scala.Option[Variable]) =>
        existsLi(t, x)
      ),
  )

  /**
   * exists right: instantiate an existential quantifier for x in the succedent by a concrete instance `inst` as a
   * witness.
   * {{{
   * G |- p(inst), D
   * ----------------------- ∃R
   * G |- \exists x p(x), D
   * }}}
   */
  def existsR(x: Variable, inst: Term): BuiltInPositionTactic = FOQuantifierTactics
    .existsInstantiate(Some(x), Some(inst))

  /** exists right: instantiate an existential quantifier in the succedent by a concrete instance `inst` as a witness */

  def existsR(e: scala.Option[Term]): DependentPositionWithAppliedInputTactic = "existsR"
    .byWithInputs(List(e), { (pos: Position) => FOQuantifierTactics.existsInstantiate(None, e)(pos) })

  @Derivation
  val existsRInfo: InputPositionTacticInfo = InputPositionTacticInfo.create(
    name = "existsR",
    displayName = Some("∃R"),
    displayNameAscii = Some("existsR"),
    displayPremises = "Γ |- p(θ), Δ",
    displayConclusion = "Γ |- ∃x p(x), Δ",
    constructor = TacticConstructor1.create(OptionArg(TermArg("θ", List("θ"))))((e: scala.Option[Term]) => existsR(e)),
  )

  def existsR(e: Term): BuiltInPositionTactic = FOQuantifierTactics.existsInstantiate(None, Some(e))

  /** exists right: instantiate an existential quantifier for x in the succedent by itself as a witness */
  val existsR: DependentPositionTactic = existsR(None)

  /**
   * exists right: instantiate an existential quantifier in the succedent by a concrete term obtained from position
   * `instPos`.
   */
  // was "exists instantiate pos"
  def existsRPos(instPos: Position): DependentPositionTactic = anon((pos: Position, sequent: Sequent) =>
    sequent.sub(instPos) match {
      case Some(t: Term) => existsR(t)(pos)
      case Some(e) => throw new TacticInapplicableFailure(
          "exists instantiate pos only applicable to terms, but got " + e.prettyString
        )
      case None => throw new IllFormedTacticApplicationException(
          "Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString
        )
    }
  )

  /**
   * Existential monotonicity in succedent: replace `p(x)` with a characteristic property `q(x)`.
   * {{{
   * Use:                      Show:
   * G |- \exists x q(x), D    G, q(x) |- p(x), D
   * -------------------------------------------- M∃R
   * G |- \exists x p(x), D
   * }}}
   */
  def existsRmon(q: Formula): DependentPositionWithAppliedInputTactic = "existsRmon".byWithInputs(
    List(q),
    { (pos: Position, seq: Sequent) =>
      seq.sub(pos) match {
        case Some(Exists(x, _)) => cutR(Exists(x, q))(pos) <
            (
              label(BelleLabels.cutUse),
              // Implementation 1: implyR(pos) & existsL('Llast) & existsR(pos)
              // Implementation 2:
              useAt(Ax.existsDistElim)(pos) & allR(pos) & implyR(pos) & label(BelleLabels.cutShow),
            )
        case Some(e) => throw new TacticInapplicableFailure(
            "existsRmon only applicable to existential quantifiers on the right, but got " + e.prettyString
          )
        case None => throw new IllFormedTacticApplicationException(
            "Position " + pos + " does not point to a valid position in sequent " + seq.prettyString
          )
      }
    },
  )

  @Derivation
  val existsRmonInfo: InputPositionTacticInfo = InputPositionTacticInfo.create(
    name = "existsRmon",
    displayName = Some("M∃R"),
    displayNameAscii = Some("MexistsR"),
    displayPremises = "Γ |- ∃x q(x), Δ ;; Γ, q(x) |- p(x), Δ",
    displayConclusion = "Γ |- ∃x p(x), Δ",
    constructor = TacticConstructor1.create(FormulaArg("q(x)"))((q: Formula) => existsRmon(q)),
  )

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // closing tactics

  /**
   * close: closes the branch when the same formula is in the antecedent and succedent or true right or false left.
   * {{{
   *        *
   * ------------------ (Id)
   *   p, G |- p, D
   * }}}
   * {{{
   *       *
   * ------------------ (close true)
   *   G |- true, D
   * }}}
   * {{{
   *        *
   * ------------------ (close false)
   *   false, G |- D
   * }}}
   */
  val close: BuiltInTactic = "close".by { (pr: ProvableSig) => findClose.result(pr) }

  @Derivation
  val closeInfo: PlainTacticInfo = PlainTacticInfo.create(
    name = "close",
    displayName = Some("⊥/⊤"),
    displayNameAscii = Some("false/true"),
    displayNameLong = Some("Close by id/⊥/⊤"),
    displayPremises = "*",
    displayConclusion = "Γ, P |- P, Δ",
    constructor = TacticConstructor0.create()(() => close),
  )

  // alternative implementation
  // @todo optimizable seems like complicated and possibly slow code???
  /*anon {(seq: Sequent) => {
    seq.succ.zipWithIndex.find({
      case (True, _) => true
      case (fml, _) =>
       val x = seq.ante.contains(fml)
        x
    })
    match {
      case Some((True, i)) =>
        ProofRuleTactics.closeTrue(SuccPos(i))
      case Some((fml, i)) =>
        close(AntePos(seq.ante.indexOf(fml)), SuccPos(i))
      case None => seq.ante.zipWithIndex.find({ case (False, _) => true case _ => false }) match {
        case Some((False, i)) => ProofRuleTactics.closeFalse(AntePos(i))
        case _ => DebuggingTactics.error("Inapplicable close")
      }
    }
  }}*/

  /**
   * Find a succedent True or an antecedent False or the same formula left and right and give back its closing tactic.
   */
  private def findClose: BuiltInTactic = anon { (provable: ProvableSig) =>
    @inline
    def findCloseImp(pr: ProvableSig): ProvableSig = {
      // The control structure is complicated but ensures False/True are only searched for exactly once en passent.
      ProofRuleTactics.requireOneSubgoal(pr, "findClose")
      val seq = pr.subgoals.head
      val ante = seq.ante
      val succ = seq.succ
      if (succ.isEmpty) {
        for (j <- ante.indices) {
          if (ante(j) == False) return ProofRuleTactics.closeFalse(AntePos(j)).computeResult(pr)
        }
      } else {
        val fml0 = succ.head
        if (fml0 == True) return ProofRuleTactics.closeTrue(SuccPos(0)).computeResult(pr)
        // @todo optimizable: measure whether antecedent converted to HashMap for lookup is faster if succ.length>1 and ante.length large
        for (j <- ante.indices) {
          ante(j) match {
            case False => return ProofRuleTactics.closeFalse(AntePos(j)).computeResult(pr)
            case other => if (fml0 == other) return closeId(AntePos(j), SuccPos(0)).computeResult(pr)
          }
        }
        for (i <- succ.indices.tail) {
          succ(i) match {
            case True => return ProofRuleTactics.closeTrue(SuccPos(i)).computeResult(pr)
            case fml =>
              for (j <- ante.indices) { if (fml == ante(j)) return closeId(AntePos(j), SuccPos(i)).computeResult(pr) }
          }
        }
      }
      DebuggingTactics.error("Inapplicable close").result(pr)
    }
    findCloseImp(provable)
  }

  /**
   * close: closes the branch when the same formula is in the antecedent and succedent at the indicated positions
   * ([[org.keymaerax.core.Close Close]]).
   * {{{
   *        *
   * ------------------ (Id)
   *   p, G |- p, D
   * }}}
   */
  // @note same name (closeId) as SequentCalculus.closeId for serialization
  val closeId: BuiltInTwoPositionTactic = "closeId".by { (provable: ProvableSig, a: Position, s: Position) =>
    ProofRuleTactics.requireOneSubgoal(provable, "closeId(" + a + "," + s + ")")
    try { provable(Close(a.checkAnte.checkTop, s.checkSucc.checkTop), 0) }
    catch {
      case ex: NoncriticalCoreException => throw new TacticInapplicableFailure(
          "Tactic " + "closeId" + " applied at " + a + " and " + s + " is inapplicable in " + provable.prettyString,
          ex,
        )
    }
  }

  @Derivation
  val closeIdInfo: TwoPositionTacticInfo = TwoPositionTacticInfo.create(
    name = "closeId",
    displayNameLong = Some("Close by Identity"),
    constructor = TacticConstructor0.create()(() => closeId),
  )

  def close(a: Int, s: Int): BelleExpr = closeId(Position(a).checkAnte.top, Position(s).checkSucc.top)

  /**
   * closeIdWith: closes the branch with the formula at the given position when the same formula is in the antecedent
   * and succedent ([[org.keymaerax.core.Close Close]])
   */
  val closeIdWith: BuiltInPositionTactic = "idWith".by { (provable: ProvableSig, pos: Position) =>
    val s = provable.subgoals.head
    pos.top match {
      case p: AntePos => provable(Close(p, SuccPos(closeIdFound(pos, s.succ.indexOf(s(p))))), 0)
      case p: SuccPos => provable(Close(AntePos(closeIdFound(pos, s.ante.indexOf(s(p)))), p), 0)
    }
  }

  @Derivation
  val idWithInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "idWith",
    displayNameLong = Some("Close by Identity"),
    displayPremises = "*",
    displayConclusion = "Γ, P |- P, Δ",
    constructor = TacticConstructor0.create()(() => closeIdWith),
  )

  @inline
  private def closeIdFound(pos: Position, i: Int): Int =
    if (i >= 0) i
    else throw new TacticInapplicableFailure(
      "Inapplicable: closeIdWith at " + pos + " cannot close due to missing counterpart"
    )

  /**
   * id: closes the branch when the same formula is in the antecedent and succedent ([[org.keymaerax.core.Close
   * Close]]).
   * {{{
   *        *
   * ------------------ (id)
   *   p, G |- p, D
   * }}}
   */
  // @note do not forward to closeIdWith (performance)
  // @TODO: Currently needs to be new DependentTactic() for some crazy reason: SpoonFeedingInterpreter serializes as "closeId()"
  // if we use  anons {...}, even though the implementation is literally new DependentTactic(...). Mysterious.
  // Maybe the interpreter is checking type equality of anonymous classes somewhere...
  val id: BuiltInTactic = "id".by { (provable: ProvableSig) =>
    require(provable.subgoals.size == 1, "Expects exactly 1 subgoal, but got " + provable.subgoals.size + " subgoals")
    val s = provable.subgoals.head
    s.ante.intersect(s.succ).headOption match {
      case Some(fml) => provable(Close(AntePos(s.ante.indexOf(fml)), SuccPos(s.succ.indexOf(fml))), 0)
      case None => throw new TacticInapplicableFailure(
          "Expects same formula in antecedent and succedent. Found:\n" + s.prettyString
        )
    }
  }

  @Derivation
  val idInfo: PlainTacticInfo = PlainTacticInfo.create(
    name = "id",
    displayPremises = "*",
    displayConclusion = "Γ, P |- P, Δ",
    constructor = TacticConstructor0.create()(() => id),
  )

  val idx: DependentTactic = "idx".by { (sequent: Sequent) =>
    sequent.ante.intersect(sequent.succ).headOption match {
      case Some(fml) => closeId(AntePos(sequent.ante.indexOf(fml)), SuccPos(sequent.succ.indexOf(fml)))
      case None =>
        if (
          sequent
            .ante
            .exists({
              case _: Equal => true
              case _ => false
            })
        ) SaturateTactic(exhaustiveEqL2R(hide = true)(Symbol("L"))) & id
        else throw new TacticInapplicableFailure(
          "Expects same formula in antecedent and succedent. Found:\n" + sequent.prettyString
        )
    }
  }

  @Derivation
  val idxInfo: PlainTacticInfo = PlainTacticInfo.create(
    name = "idx",
    displayPremises = "*",
    displayConclusion = "Γ, x=y, P(x) |- P(y), Δ",
    constructor = TacticConstructor0.create()(() => idx),
  )

  /**
   * Alpha bound renaming of `what` to `to` at a specific position (for quantifier/assignment/ode). Variable `to` must
   * not occur free at the applied position.
   * @example
   *   {{{
   *   x=y |- [{y'=y}]y>=0      x=y |- [{x'=x}]x>=0, x=y
   *   ------------------------------------------------- alphaRen("x","y",1)
   *   x=y |- [{x'=x}]x>=0
   *   }}}
   */
  def alphaRen(what: Variable, to: Variable): DependentPositionWithAppliedInputTactic = "alphaRen".byWithInputs(
    List(what, to),
    { (pos: Position, seq: Sequent) =>
      if (!pos.isTopLevel) throw new TacticInapplicableFailure("Alpha renaming only applicable at top-level")
      seq.sub(pos) match {
        case Some(where: Formula) =>
          if (pos.isAnte) {
            cutL(And(Equal(what, to), Box(Assign(what, what), where)))(pos) <
              (
                existsLi(what, Some(what))(pos) & useAt(Ax.assignbequalityexists, PosInExpr(1 :: Nil))(pos) &
                  ProofRuleTactics.boundRenameAt(to)(pos ++ PosInExpr(1 :: Nil)) & HilbertCalculus.assignb(pos) * 2,
                implyR(Symbol("Rlast")) &
                  andR(Symbol("Rlast")) < (Idioms.nil, HilbertCalculus.assignb(Symbol("Rlast")) & id),
              )
          } else {
            cutR(Imply(Equal(what, to), Box(Assign(what, what), where)))(pos) <
              (
                allRi(what, Some(what))(pos) & useAt(Ax.assignbeq, PosInExpr(1 :: Nil))(pos) &
                  ProofRuleTactics.boundRenameAt(to)(pos ++ PosInExpr(1 :: Nil)) & HilbertCalculus.assignb(pos) * 2,
                implyR(pos) & implyL(Symbol("Llast")) < (Idioms.nil, HilbertCalculus.assignb(Symbol("Llast")) & id),
              )
          }
        case e => throw new TacticInapplicableFailure(
            "Alpha renaming only applicable at formulas, but got " + e.map(_.prettyString)
          )
      }
    },
  )

  @Derivation
  val alphaRenInfo: InputPositionTacticInfo = InputPositionTacticInfo.create(
    name = "alphaRen",
    displayName = Some("BR"),
    displayNameLong = Some("Alpha Bound Rename"),
    displayPremises = "Γ |- P(y), Δ ;; Γ |- P(x), Δ, x=y",
    displayConclusion = "Γ |- P(x), Δ",
    constructor = TacticConstructor2
      .create(VariableArg("x"), VariableArg("y", List("y")))((what: Variable, to: Variable) => alphaRen(what, to)),
  )

  /**
   * Alpha renaming of `what` to `to` everywhere in the sequent. Formulas that have variable `to` occur free are
   * excluded from the renaming.
   * @example
   *   {{{
   *   [y:=0;]y>=0 |- [{y'=y}]y>=0, [x:=y;]x=y      [x:=0;]x>=0 |- [{x'=x}]x>=0, x:=y;]x=y, x=y
   *   ---------------------------------------------------------------------------------------- alphaRenAll("x","y",1)
   *   [x:=0;]x>=0 |- [{x'=x}]x>=0, [x:=y;]x=y
   *   }}}
   */
  def alphaRenAll(what: Variable, to: Variable): InputTactic = "alphaRenAll".byWithInputs(
    List(what, to),
    { (seq: Sequent) =>
      val anteIdxs = seq
        .ante
        .indices
        .filter(i =>
          !StaticSemantics.boundVars(seq.ante(i)).intersect(Set(what, DifferentialSymbol(what))).isEmpty &&
            !StaticSemantics.freeVars(seq.ante(i)).contains(to)
        )
      val succIdxs = seq
        .succ
        .indices
        .filter(i =>
          !StaticSemantics.boundVars(seq.succ(i)).intersect(Set(what, DifferentialSymbol(what))).isEmpty &&
            !StaticSemantics.freeVars(seq.succ(i)).contains(to)
        )
      val anteRewrite = anteIdxs
        .map(i => alphaRen(what, to)(AntePos(i)) < (Idioms.nil, id))
        .reduceRightOption[BelleExpr](_ & _)
        .getOrElse(Idioms.nil)
      val succRewrite = succIdxs
        .map(i => alphaRen(what, to)(SuccPos(i)) < (Idioms.nil, id))
        .reduceRightOption[BelleExpr](_ & _)
        .getOrElse(Idioms.nil)

      if (seq.ante.contains(Equal(what, to))) {
        anteRewrite & succRewrite & exhaustiveEqL2R(hide = false)(AntePos(seq.ante.indexOf(Equal(what, to))))
      } else if (
        seq
          .ante
          .zipWithIndex
          .filter({ case (_, i) => anteIdxs.contains(i) })
          .forall({ case (f, _) => !StaticSemantics.freeVars(f).contains(what) }) &&
        seq
          .succ
          .zipWithIndex
          .filter({ case (_, i) => succIdxs.contains(i) })
          .forall({ case (f, _) => !StaticSemantics.freeVars(f).contains(to) })
      ) {
        cut(Exists(List(what), Equal(what, to))) <
          (
            existsL(Symbol("Llast")) & anteRewrite & succRewrite & exhaustiveEqL2R(hide = true)(Symbol("Llast")) &
              uniformRename(Variable(what.name, Some(what.index.map(_ + 1).getOrElse(0))), what),
            cohide(Symbol("Rlast")) & existsR(to)(1) & UnifyUSCalculus.byUS(Ax.equalReflexive),
          )
      } else {
        cut(Equal(what, to)) < (anteRewrite & succRewrite & exhaustiveEqL2R(hide = true)(Symbol("Llast")), Idioms.nil)
      }
    },
  )

  @Derivation
  val alphaRenAllInfo: InputTacticInfo = InputTacticInfo.create(
    name = "alphaRenAll",
    displayName = Some("α-renall"),
    displayNameAscii = Some("alpha-renall"),
    displayNameLong = Some("Alpha Rename All"),
    displayPremises = "Γ(y) |- Δ(y) ;; Γ(x) |- Δ(x), x=y",
    displayConclusion = "Γ(x) |- Δ(x)",
    constructor = TacticConstructor2
      .create(VariableArg("x"), VariableArg("y", List("y")))((what: Variable, to: Variable) => alphaRenAll(what, to)),
  )

  /** Alpha renaming everywhere in the sequent using an equality at a specific position in the antecedent. */
  val alphaRenAllBy: DependentPositionTactic = "alphaRenAllBy".by { (pos: Position, seq: Sequent) =>
    if (!pos.isAnte) throw new TacticInapplicableFailure(
      "Alpha renaming all by position must point to an equality of variabes in the antecedent"
    )
    seq(pos.top) match {
      case Equal(l: Variable, r: Variable) => alphaRenAll(l, r)
      case e => throw new TacticInapplicableFailure(
          "Alpha renaming all by position only applicable to an equality of variables, but got " + e.prettyString
        )
    }
  }

  @Derivation
  val alphaRenAllByInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "alphaRenAllBy",
    displayName = Some("α-renallby"),
    displayNameAscii = Some("alpha-renallby"),
    displayNameLong = Some("Alpha Rename All By Equality"),
    displayPremises = "Γ(y), x=y |- Δ(y)",
    displayConclusion = "Γ(x), x=y |- Δ(x)",
    constructor = TacticConstructor0.create()(() => alphaRenAllBy),
  )

  // alternative implementation
  /*anon {(seq: Sequent) =>
    //@todo optimizable performance avoiding the repeated search
    val fmls = seq.ante.intersect(seq.succ)
    val fml = fmls.headOption.getOrElse(throw new TacticInapplicableFailure("Expects same formula in antecedent and succedent. Found:\n" + seq.prettyString))
    close(AntePos(seq.ante.indexOf(fml)), SuccPos(seq.succ.indexOf(fml)))
  }*/
  /**
   * closeT: closes the branch when true is in the succedent ([[org.keymaerax.core.CloseTrue CloseTrue]]).
   * {{{
   *       *
   * ------------------ (close true)
   *   G |- true, D
   * }}}
   */
  val closeT: BuiltInTactic = "closeT".by { (pr: ProvableSig) =>
    ProofRuleTactics.closeTrue(Symbol("R"), True).computeResult(pr)
  }
  //  val closeT: BelleExpr = "closeTrue" by { ProofRuleTactics.closeTrue('R, True) }

  @Derivation
  val closeTInfo: PlainTacticInfo = PlainTacticInfo.create(
    name = "closeT",
    displayName = Some("⊤R"),
    displayNameAscii = Some("trueR"),
    displayNameLong = Some("Close ⊤"),
    displayPremises = "*",
    displayConclusion = "Γ |- ⊤, Δ",
    constructor = TacticConstructor0.create()(() => closeT),
  )

  /**
   * closeF: closes the branch when false is in the antecedent ([[org.keymaerax.core.CloseFalse CloseFalse]]).
   * {{{
   *        *
   * ------------------ (close false)
   *   false, G |- D
   * }}}
   */
  val closeF: BuiltInTactic = "closeF".by { (pr: ProvableSig) =>
    ProofRuleTactics.closeFalse(Symbol("L"), False).computeResult(pr)
  }

  //  val closeF: BelleExpr = "closeFalse" by { ProofRuleTactics.closeFalse('L, False) }

  @Derivation
  val closeFInfo: PlainTacticInfo = PlainTacticInfo.create(
    name = "closeF",
    displayName = Some("⊥L"),
    displayNameAscii = Some("falseL"),
    displayNameLong = Some("Close ⊥"),
    displayPremises = "*",
    displayConclusion = "Γ, ⊥ |- Δ",
    constructor = TacticConstructor0.create()(() => closeF),
  )

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // derived propositional

  /**
   * Turn implication `a->b` on the right into an equivalence `a<->b`, which is useful to prove by CE etc.
   * ([[org.keymaerax.core.EquivifyRight EquivifyRight]]).
   * {{{
   * G |- a<->b, D
   * -------------
   * G |- a->b,  D
   * }}}
   */
  val equivifyR: CoreRightTactic = "equivifyR".coreby { (pr: ProvableSig, pos: SuccPosition) =>
    pr(EquivifyRight(pos.checkTop), 0)
  }

  @Derivation
  val equivifyRInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "equivifyR",
    displayName = Some("→2↔"),
    displayNameAscii = Some("->2<->R"),
    displayNameLong = Some("Strengthen to Equivalence"),
    displayPremises = "Γ |- P↔Q, Δ",
    displayConclusion = "Γ |- P→Q, Δ",
    constructor = TacticConstructor0.create()(() => equivifyR),
  )

  /**
   * Modus Ponens: p&(p->q) -> q.
   * @example
   *   {{{
   *      p, q, G |- D
   *   ---------------- modusPonens
   *   p, p->q, G |- D
   *   }}}
   * @param assumption
   *   Position pointing to p
   * @param implication
   *   Position pointing to p->q
   */
  def modusPonens(assumption: AntePos, implication: AntePos): BelleExpr = PropositionalTactics
    .modusPonens(assumption, implication)

  /**
   * Commute equivalence on the left [[org.keymaerax.core.CommuteEquivLeft CommuteEquivLeft]].
   * {{{
   * q<->p, G |-  D
   * -------------- (<->cL)
   * p<->q, G |-  D
   * }}}
   */
  val commuteEquivL: CoreLeftTactic = "commuteEquivL".coreby { (pr: ProvableSig, pos: AntePosition) =>
    pr(CommuteEquivLeft(pos.checkTop), 0)
  }

  @Derivation
  val commuteEquivLInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "commuteEquivL",
    displayName = Some("↔cL"),
    displayNameAscii = Some("<->cLR"),
    displayNameLong = Some("Commute Equivalence Left"),
    displayPremises = "Q↔P, Γ |- Δ",
    displayConclusion = "P↔Q, Γ |- Δ",
    constructor = TacticConstructor0.create()(() => commuteEquivL),
  )

  /**
   * Commute equivalence on the right [[org.keymaerax.core.CommuteEquivRight CommuteEquivRight]].
   * {{{
   * G |- q<->p, D
   * ------------- (<->cR)
   * G |- p<->q, D
   * }}}
   */
  val commuteEquivR: CoreRightTactic = "commuteEquivR".coreby { (pr: ProvableSig, pos: SuccPosition) =>
    pr(CommuteEquivRight(pos.checkTop), 0)
  }

  @Derivation
  val commuteEquivRInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "commuteEquivR",
    displayName = Some("↔cR"),
    displayNameAscii = Some("<->cR"),
    displayNameLong = Some("Commute Equivalence Right"),
    displayPremises = "Γ |- Q↔P, Δ",
    displayConclusion = "Γ |- P↔Q, Δ",
    constructor = TacticConstructor0.create()(() => commuteEquivR),
  )

  /** Commute equality `a=b` to `b=a` */
  lazy val commuteEqual: BuiltInPositionTactic = "commuteEqual".forward(UnifyUSCalculus.useAt(Ax.equalCommute))

  @Derivation
  val commuteEqualInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "commuteEqual",
    displayName = Some("=c"),
    displayNameLong = Some("Commute Equal"),
    displayConclusion = "__p=q__ ↔ q=p",
    constructor = TacticConstructor0.create()(() => commuteEqual),
  )

  // Equality rewriting tactics

  /** Expands all special functions (abs/min/max). */
  val expandAll: BuiltInTactic = EqualityTactics.expandAll

  /** Rewrites all atom equalities in the assumptions. */
  val applyEqualities: BuiltInTactic = EqualityTactics.applyEqualities

  //  meta-tactics for proof structuring information but no effect

  /**
   * Call/label the current proof branch by the given label `s`.
   * @see
   *   [[Idioms.<()]]
   * @see
   *   [[sublabel()]]
   * @see
   *   [[BelleLabels]]
   */
  def label(s: BelleLabel): BelleExpr = LabelBranch(s)

  /**
   * Call/label the current proof branch by the top-level label `s`.
   * @see
   *   [[Idioms.<()]]
   * @see
   *   [[sublabel()]]
   * @see
   *   [[BelleLabels]]
   */
  def label(s: String): InputTactic = "label".byWithInputs(List(s), label(BelleTopLevelLabel(s)))

  @Derivation
  val labelInfo: InputTacticInfo = InputTacticInfo
    .create(name = "label", constructor = TacticConstructor1.create(StringArg("s"))(((s: String) => label(s))))

  /**
   * Mark the current proof branch and all subbranches `s``.
   *
   * @see
   *   [[label()]]
   */
  def sublabel(s: String): BelleExpr = UnifyUSCalculus.skip // LabelBranch(BelleSubLabel(???, s))

}
