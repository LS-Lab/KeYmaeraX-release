/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon._
import org.keymaerax.btactics.ProofRuleTactics.requireOneSubgoal
import org.keymaerax.btactics.TacticFactory._
import org.keymaerax.btactics.TactixLibrary.{exhaustiveEqL2R, uniformRename, useAt}
import org.keymaerax.btactics.macros.{DisplayLevel, Tactic, TacticInfo}
import org.keymaerax.core
import org.keymaerax.core._
import org.keymaerax.infrastruct.Augmentors._
import org.keymaerax.infrastruct.{AntePosition, PosInExpr, Position, SuccPosition}
import org.keymaerax.pt.ProvableSig

import scala.annotation.nowarn
import scala.reflect.runtime.universe

/**
 * Sequent Calculus for propositional and first-order logic.
 * @author
 *   Andre Platzer
 * @author
 *   Stefan Mitsch
 * @see
 *   [[SequentCalculus]]
 */
object SequentCalculus extends TacticProvider with SequentCalculus {

  /** @inheritdoc */
  override def getInfo: (Class[_], universe.Type) = (SequentCalculus.getClass, universe.typeOf[SequentCalculus.type])
}

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
trait SequentCalculus {

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Propositional tactics

  /** Hide/weaken whether left or right */
  @Tactic(
    name = "hide",
    displayName = Some("W"),
    displayNameLong = Some("Weaken"),
    displayPremises = "Γ |- Δ",
    displayConclusion = "Γ |- P, Δ",
  )
  val hide: BuiltInPositionTactic = anon { (pr: ProvableSig, pos: Position) =>
    pos match {
      case p: AntePosition => SequentCalculus.hideL(p).computeResult(pr)
      case p: SuccPosition => SequentCalculus.hideR(p).computeResult(pr)
    }
  }

  /** Hide/weaken left: weaken a formula to drop it from the antecedent ([[org.keymaerax.core.HideLeft HideLeft]]) */
  @Tactic(
    name = "hideL",
    displayName = Some("WL"),
    displayNameLong = Some("Weaken Left"),
    displayPremises = "Γ |- Δ",
    displayConclusion = "Γ, P |- Δ",
  )
  val hideL: CoreLeftTactic = coreanon { (pr: ProvableSig, pos: AntePosition) => pr(HideLeft(pos.checkTop), 0) }

  /** Hide/weaken right: weaken a formula to drop it from the succcedent ([[org.keymaerax.core.HideRight HideRight]]) */
  @Tactic(
    name = "hideR",
    displayName = Some("WR"),
    displayNameLong = Some("Weaken Right"),
    displayPremises = "Γ |- Δ",
    displayConclusion = "Γ |- P, Δ",
  )
  val hideR: CoreRightTactic = coreanon { (pr: ProvableSig, pos: SuccPosition) => pr(HideRight(pos.checkTop), 0) }

  /** CoHide/weaken left: drop all other formulas from the sequent ([[org.keymaerax.core.CoHideLeft CoHideLeft]]) */
  @Tactic(
    name = "cohideL",
    displayName = Some("WL"),
    displayNameLong = Some("Co-Weaken Left"),
    displayPremises = "P |- ",
    displayConclusion = "Γ, P |- Δ",
  )
  val cohideL: CoreLeftTactic = coreanon { (pr: ProvableSig, pos: AntePosition) => pr(CoHideLeft(pos.checkTop), 0) }

  /** CoHide/weaken right: drop all other formulas from the sequent ([[org.keymaerax.core.CoHideRight CoHideRight]]) */
  @Tactic(
    name = "cohideR",
    displayName = Some("WR"),
    displayNameLong = Some("Co-Weaken Right"),
    displayPremises = "|- P",
    displayConclusion = "Γ |- P, Δ",
  )
  val cohideR: CoreRightTactic = coreanon { (pr: ProvableSig, pos: SuccPosition) => pr(CoHideRight(pos.checkTop), 0) }

  /**
   * CoHide/coweaken whether left or right: drop all other formulas from the sequent ([[org.keymaerax.core.CoHideLeft
   * CoHideLeft]])
   */
  @Tactic(
    name = "cohide",
    displayName = Some("W"),
    displayNameLong = Some("Co-Weaken"),
    displayPremises = "|- P",
    displayConclusion = "Γ |- P, Δ",
  )
  val cohide: BuiltInPositionTactic = anon { (pr: ProvableSig, pos: Position) =>
    pos match {
      case p: AntePosition => SequentCalculus.cohideL(p).computeResult(pr)
      case p: SuccPosition => SequentCalculus.cohideR(p).computeResult(pr)
    }
  }

  /**
   * CoHide2/coweaken2 both left and right: drop all other formulas from the sequent ([[org.keymaerax.core.CoHide2
   * CoHide2]])
   */
  @Tactic(
    name = "coHide2",
    displayName = Some("WLR"),
    displayNameLong = Some("Co-Weaken Both"),
    displayPremises = "P |- Q",
    displayConclusion = "Γ, P |- Q, Δ",
  )
  val cohide2: BuiltInTwoPositionTactic = anon { (pr: ProvableSig, ante: Position, succ: Position) =>
    {
      require(ante.isAnte && succ.isSucc, "Expects an antecedent and a succedent position.")
      pr(CoHide2(ante.checkAnte.top, succ.checkSucc.top), 0)
    }
  }

  /** Cohides in succedent, but leaves antecedent as is. */
  @Tactic(
    name = "cohideOnlyR",
    displayName = Some("WR"),
    displayNameLong = Some("Co-Weaken Only Right"),
    displayPremises = "Γ, P |- Q",
    displayConclusion = "Γ, P |- Q, Δ",
  )
  val cohideOnlyR: BuiltInRightTactic = anon { (pr: ProvableSig, pos: SuccPosition) =>
    val hiddenUntil = (1 to pos.checkTop.getIndex).foldLeft(pr)({ case (p, _) => hideR(1).computeResult(p) })
    (2 to hiddenUntil.subgoals.head.succ.length).foldLeft(hiddenUntil)({ case (p, _) => hideR(2).computeResult(p) })
  }

  /** Cohides in antecedent, but leaves succedent as is. */
  @Tactic(
    name = "cohideOnlyL",
    displayName = Some("WL"),
    displayNameLong = Some("Co-Weaken Only Left"),
    displayPremises = "|- Q, Δ",
    displayConclusion = "Γ, P |- Q, Δ",
  )
  val cohideOnlyL: BuiltInLeftTactic = anon { (pr: ProvableSig, pos: AntePosition) =>
    val hiddenUntil = (1 to pos.checkTop.getIndex).foldLeft(pr)({ case (p, _) => hideL(-1).computeResult(p) })
    (2 to hiddenUntil.subgoals.head.ante.length).foldLeft(hiddenUntil)({ case (p, _) => hideL(-2).computeResult(p) })
  }

  /** !L Not left: move an negation in the antecedent to the succedent ([[org.keymaerax.core.NotLeft NotLeft]]) */
  @Tactic(
    name = "notL",
    displayName = Some("¬L"),
    displayNameAscii = Some("!L"),
    displayPremises = "Γ |- P, Δ",
    displayConclusion = "¬P, Γ |- Δ",
  )
  val notL: CoreLeftTactic = coreanon { (pr: ProvableSig, pos: AntePosition) => pr(NotLeft(pos.checkTop), 0) }
  private[btactics] val notLInfo: TacticInfo = TacticInfo("notL")

  /** !R Not right: move an negation in the succedent to the antecedent ([[org.keymaerax.core.NotRight NotRight]]) */
  @Tactic(
    name = "notR",
    displayName = Some("¬R"),
    displayNameAscii = Some("!R"),
    displayPremises = "Γ, P |- Δ",
    displayConclusion = "Γ |- ¬P, Δ",
  )
  val notR: CoreRightTactic = coreanon { (pr: ProvableSig, pos: SuccPosition) => pr(NotRight(pos.checkTop), 0) }
  private[btactics] val notRInfo: TacticInfo = TacticInfo("notR")

  /**
   * &L And left: split a conjunction in the antecedent into separate assumptions ([[org.keymaerax.core.AndLeft
   * AndLeft]])
   */
  @Tactic(
    name = "andL",
    displayName = Some("∧L"),
    displayNameAscii = Some("&L"),
    displayPremises = "Γ, P, Q |- Δ",
    displayConclusion = "P∧Q, Γ |- Δ",
  )
  val andL: CoreLeftTactic = coreanon { (pr: ProvableSig, pos: AntePosition) => pr(AndLeft(pos.checkTop), 0) }
  private[btactics] val andLInfo: TacticInfo = TacticInfo("andL")

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
  @Tactic(
    name = "andR",
    displayName = Some("∧R"),
    displayNameAscii = Some("&R"),
    displayPremises = "Γ |- P, Δ ;; Γ |- Q, Δ",
    displayConclusion = "Γ |- P∧Q, Δ",
  )
  val andR: DependentPositionTactic = anon { (pos: Position, seq: Sequent) =>
    corelabelledby("andR", Right(andRRule), And.unapply, pos, seq)
  }
  private[btactics] val andRInfo: TacticInfo = TacticInfo("andR")
  @Tactic(
    name = "andRRule",
    displayName = Some("∧R"),
    displayNameAscii = Some("&R"),
    displayPremises = "Γ |- P, Δ ;; Γ |- Q, Δ",
    displayConclusion = "Γ |- P∧Q, Δ",
  )
  val andRRule: CoreRightTactic = coreanon { (pr: ProvableSig, pos: SuccPosition) => pr(AndRight(pos.checkTop), 0) }

  /**
   * \|L Or left: use a disjunction in the antecedent by assuming each option on separate branches
   * ([[org.keymaerax.core.OrLeft OrLeft]])
   */
  @Tactic(
    name = "orL",
    displayName = Some("∨L"),
    displayNameAscii = Some("|L"),
    displayPremises = "P, Γ |- Δ ;; Q, Γ |- Δ",
    displayConclusion = "P∨Q, Γ |- Δ",
  )
  val orL: DependentPositionTactic = anon { (pos: Position, seq: Sequent) =>
    corelabelledby("orL", Left(orLRule), Or.unapply, pos, seq)
  }
  private[btactics] val orLInfo: TacticInfo = TacticInfo("orL")
  @Tactic(
    name = "orLRule",
    displayName = Some("∨L"),
    displayNameAscii = Some("|L"),
    displayPremises = "P, Γ |- Δ ;; Q, Γ |- Δ",
    displayConclusion = "P∨Q, Γ |- Δ",
  )
  val orLRule: CoreLeftTactic = coreanon { (pr: ProvableSig, pos: AntePosition) => pr(OrLeft(pos.checkTop), 0) }

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
  @Tactic(
    name = "orR",
    displayName = Some("∨R"),
    displayNameAscii = Some("|R"),
    displayPremises = "Γ |- Δ, P, Q",
    displayConclusion = "Γ |- P∨Q, Δ",
  )
  val orR: CoreRightTactic = coreanon { (pr: ProvableSig, pos: SuccPosition) => pr(OrRight(pos.checkTop), 0) }
  private[btactics] val orRInfo: TacticInfo = TacticInfo("orR")

  /**
   * ->L Imply left: use an implication in the antecedent by proving its left-hand side on one branch and using its
   * right-hand side on the other branch ([[org.keymaerax.core.ImplyLeft ImplyLeft]])
   */
  @Tactic(
    name = "implyL",
    displayName = Some("→L"),
    displayNameAscii = Some("->L"),
    displayPremises = "Γ |- Δ, P ;; Q, Γ |- Δ",
    displayConclusion = "P→Q, Γ |- Δ",
  )
  val implyL: DependentPositionTactic = anon { (pos: Position, seq: Sequent) =>
    corelabelledby("implyL", Left(implyLRule), Imply.unapply, pos, seq)
  }
  private[btactics] val implyLInfo: TacticInfo = TacticInfo("implyL")
  @Tactic(
    name = "implyLRule",
    displayName = Some("→L"),
    displayNameAscii = Some("->L"),
    displayPremises = "Γ |- Δ, P ;; Q, Γ |- Δ",
    displayConclusion = "P→Q, Γ |- Δ",
  )
  val implyLRule: CoreLeftTactic = coreanon { (pr: ProvableSig, pos: AntePosition) => pr(ImplyLeft(pos.checkTop), 0) }

  /**
   * ->R Imply right: prove an implication in the succedent by assuming its left-hand side and proving its right-hand
   * side ([[org.keymaerax.core.ImplyRight ImplyRight]])
   */
  @Tactic(
    name = "implyR",
    displayName = Some("→R"),
    displayNameAscii = Some("->R"),
    displayPremises = "Γ, P |- Q, Δ",
    displayConclusion = "Γ |- P→Q, Δ",
  )
  val implyR: CoreRightTactic = coreanon { (pr: ProvableSig, pos: SuccPosition) => pr(ImplyRight(pos.checkTop), 0) }
  private[btactics] val implyRInfo: TacticInfo = TacticInfo("implyR")

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
  @Tactic(name = "implyRi")
  val implyRiX: BuiltInTwoPositionTactic = PropositionalTactics.implyRi(keep = false)

  /**
   * <->L Equiv left: use an equivalence by considering both true or both false cases ([[org.keymaerax.core.EquivLeft
   * EquivLeft]])
   */
  @Tactic(
    name = "equivL",
    displayName = Some("↔L"),
    displayNameAscii = Some("<->L"),
    displayPremises = "P∧Q, Γ |- Δ ;; ¬P∧¬Q, Γ |- Δ",
    displayConclusion = "P↔Q, Γ |- Δ",
  )
  val equivL: DependentPositionTactic = anon { (pos: Position, seq: Sequent) =>
    corelabelledby(
      "equivL",
      Left(equivLRule),
      Equiv.unapply,
      pos,
      seq,
      (l: Formula, r: Formula) => (And(l, r).prettyString, And(Not(l), Not(r)).prettyString),
    )
  }
  private[btactics] val equivLInfo: TacticInfo = TacticInfo("equivL")
  @Tactic(
    name = "equivLRule",
    displayName = Some("↔L"),
    displayNameAscii = Some("<->L"),
    displayPremises = "P∧Q, Γ |- Δ ;; ¬P∧¬Q, Γ |- Δ",
    displayConclusion = "P↔Q, Γ |- Δ",
  )
  val equivLRule: CoreLeftTactic = coreanon { (pr: ProvableSig, pos: AntePosition) => pr(EquivLeft(pos.checkTop), 0) }

  /**
   * <->R Equiv right: prove an equivalence by proving both implications ([[org.keymaerax.core.EquivRight EquivRight]])
   */
  @Tactic(
    name = "equivR",
    displayName = Some("↔R"),
    displayNameAscii = Some("<->R"),
    displayPremises = "Γ, P |- Δ, Q ;; Γ, Q |- Δ, P",
    displayConclusion = "Γ |- P↔Q, Δ",
  )
  val equivR: DependentPositionTactic = anon { (pos: Position, seq: Sequent) =>
    corelabelledby(
      "equivR",
      Right(equivRRule),
      Equiv.unapply,
      pos,
      seq,
      (l: Formula, r: Formula) => (And(l, r).prettyString, And(Not(l), Not(r)).prettyString),
    )
  }
  private[btactics] val equivRInfo: TacticInfo = TacticInfo("equivR")
  @Tactic(
    name = "equivRRule",
    displayName = Some("↔R"),
    displayNameAscii = Some("<->R"),
    displayPremises = "Γ, P |- Δ, Q ;; Γ, Q |- Δ, P",
    displayConclusion = "Γ |- P↔Q, Δ",
  )
  val equivRRule: CoreRightTactic = coreanon { (pr: ProvableSig, pos: SuccPosition) => pr(EquivRight(pos.checkTop), 0) }

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
  @Tactic(name = "cut", displayPremises = "Γ, C |- Δ ;; Γ |- Δ, C", displayConclusion = "Γ |- Δ", inputs = "C:formula")
  def cut(f: Formula): InputTactic =
    inputanon { cutX(f) & Idioms.<(label(BelleLabels.cutUse), label(BelleLabels.cutShow)) }
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
  @Tactic(
    name = "cutR",
    displayPremises = "Γ |- C, Δ ;; Γ |- C→P, Δ",
    displayConclusion = "Γ |- P, Δ",
    inputs = "C:formula",
  )
  def cutR(f: Formula): DependentPositionWithAppliedInputTactic =
    inputanonR { (provable: ProvableSig, pos: SuccPosition) =>
      requireOneSubgoal(provable, "cutR(" + f + ")")
      provable(core.CutRight(f, pos.top), 0)
    }

  /**
   * cut a formula in in place of pos on the left to prove its implication on the second branch and assume it on the
   * first. ([[org.keymaerax.core.CutLeft CutLeft]]).
   * {{{
   * c, G |- D    G |- D, p->c
   * ------------------------- (Cut Left)
   *        p, G |- D
   * }}}
   */
  @Tactic(
    name = "cutL",
    displayPremises = "Γ, C |- Δ ;; Γ |- Δ, P→C",
    displayConclusion = "Γ, P |- Δ",
    inputs = "C:formula",
  )
  def cutL(f: Formula): DependentPositionWithAppliedInputTactic =
    inputanonL { (provable: ProvableSig, pos: AntePosition) =>
      requireOneSubgoal(provable, "cutL(" + f + ")")
      provable(core.CutLeft(f, pos.top), 0)
      // @todo label BelleLabels.cutUse/cutShow
    }

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
  @Tactic(name = "cutLR")
  def cutLR(f: Formula): DependentPositionWithAppliedInputTactic = inputanon { cutLRFw(f)(_: Position) }

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
  @Tactic(
    name = "exchangeL",
    displayName = Some("XL"),
    displayNameLong = Some("Exchange Assumptions"),
    displayPremises = "Q, P, Γ |- Δ",
    displayConclusion = "P, Q, Γ |- Δ",
  )
  val exchangeL: BuiltInTwoPositionTactic = anon { (pr: ProvableSig, posOne: Position, posTwo: Position) =>
    pr(core.ExchangeLeftRule(posOne.checkAnte.top, posTwo.checkAnte.top), 0)
  }

  /**
   * Exchange right rule reorders succedent.
   * {{{
   * G |- q, p, D
   * ------------- (Exchange right)
   * G |- p, q, D
   * }}}
   */
  @Tactic(
    name = "exchangeR",
    displayName = Some("XR"),
    displayNameLong = Some("Exchange Obligations"),
    displayPremises = "Γ |- Q, P, Δ",
    displayConclusion = "Γ |- P, Q, Δ",
  )
  val exchangeR: BuiltInTwoPositionTactic = anon { (pr: ProvableSig, posOne: Position, posTwo: Position) =>
    pr(core.ExchangeRightRule(posOne.checkSucc.top, posTwo.checkSucc.top), 0)
  }

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
  @Tactic(
    name = "allR",
    displayName = Some("∀R"),
    displayNameAscii = Some("allR"),
    displayPremises = "Γ |- p(x), Δ",
    displayConclusion = "Γ |- ∀x p(x), Δ",
  )
  val allR: BuiltInPositionTactic = FOQuantifierTactics.allSkolemize
  private[btactics] val allRInfo: TacticInfo = TacticInfo("allR")
  @Tactic(
    name = "allRi",
    displayName = Some("∀Ri"),
    displayNameAscii = Some("allRi"),
    displayLevel = DisplayLevel.Browse,
    inputs = "f:term;;x[x]:option[variable]",
    displayPremises = "Γ |- ∀x p(f(x)), Δ",
    displayConclusion = "Γ |- p(f(y)), Δ",
  )
  def allRi(t: Term, x: Option[Variable]): DependentPositionWithAppliedInputTactic =
    inputanon { FOQuantifierTactics.universalGen(x, t)(_: Position) }

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
  @Tactic(
    name = "allL",
    displayName = Some("∀L"),
    displayNameAscii = Some("allL"),
    inputs = "θ[θ]:option[term]",
    displayPremises = "p(θ), Γ |- Δ",
    displayConclusion = "∀x p(x), Γ |- Δ",
  )
  def allL(e: Option[Term]): DependentPositionWithAppliedInputTactic =
    inputanon { FOQuantifierTactics.allInstantiate(None, e)(_: Position) }
  def allL(e: Term): DependentPositionWithAppliedInputTactic = allL(Some(e))

  /** all left: instantiate a universal quantifier in the antecedent by itself. */
  val allL: DependentPositionTactic = allL(None)
  private[btactics] val allLInfo: TacticInfo = TacticInfo("allL")

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
  @Tactic(
    name = "allLmon",
    displayName = Some("M∀L"),
    displayNameAscii = Some("MallL"),
    inputs = "q(x):formula",
    displayPremises = "Γ, ∀x q(x) |- Δ ;; Γ, p(x) |- Δ, q(x)",
    displayConclusion = "Γ, ∀x p(x) |- Δ",
  )
  def allLmon(q: Formula): DependentPositionWithAppliedInputTactic = inputanon { (pos: Position, seq: Sequent) =>
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
  }

  /**
   * all left keep: keeping around the quantifier, instantiate a universal quantifier in the antecedent by the concrete
   * instance `e`.
   * {{{
   * \forll x p(x), G, p(e) |- D
   * --------------------------- ∀L
   * \forall x p(x), G |- D
   * }}}
   */
  @Tactic(
    name = "allLkeep",
    displayName = Some("∀Lk"),
    displayNameAscii = Some("allLk"),
    inputs = "θ[θ]:term",
    displayPremises = "∀x p(x), Γ, p(θ) |- Δ",
    displayConclusion = "∀x p(x), Γ |- Δ",
  )
  def allLkeep(e: Term): DependentPositionWithAppliedInputTactic = inputanon { (pos: Position, seq: Sequent) =>
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
  }

  /**
   * exists left: Skolemize an existential quantifier in the antecedent by introducing a new name for the witness.
   * {{{
   *           p(x), G |- D
   * ------------------------ (Skolemize) provided x not in G,D
   * \exists x p(x), G |- D
   * }}}
   */
  @Tactic(
    name = "existsL",
    displayName = Some("∃L"),
    displayNameAscii = Some("existsL"),
    displayPremises = "p(x), Γ |- Δ",
    displayConclusion = "∃x p(x), Γ |- Δ",
  )
  val existsL: BuiltInPositionTactic = anon { (provable: ProvableSig, pos: Position) =>
    FOQuantifierTactics.existsSkolemize(pos).computeResult(provable)
  }
  private[btactics] val existsLInfo: TacticInfo = TacticInfo("existsL")
  @Tactic(
    name = "existsLi",
    displayName = Some("∃Li"),
    displayNameAscii = Some("existsLi"),
    displayLevel = DisplayLevel.Browse,
    inputs = "f:term;;x[x]:option[variable]",
    displayPremises = "Γ, ∃x p(f(x)) |- Δ",
    displayConclusion = "Γ, p(f(y)) |- Δ",
  )
  def existsLi(t: Term, x: Option[Variable]): DependentPositionWithAppliedInputTactic =
    inputanon { FOQuantifierTactics.existsGen(x, t)(_: Position) }

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
  @Tactic(
    name = "existsR",
    displayName = Some("∃R"),
    displayNameAscii = Some("existsR"),
    inputs = "θ[θ]:option[term]",
    displayPremises = "Γ |- p(θ), Δ",
    displayConclusion = "Γ |- ∃x p(x), Δ",
  )
  def existsR(e: Option[Term]): DependentPositionWithAppliedInputTactic = inputanon { pos: Position =>
    FOQuantifierTactics.existsInstantiate(None, e)(pos)
  }
  def existsR(e: Term): BuiltInPositionTactic = FOQuantifierTactics.existsInstantiate(None, Some(e))

  /** exists right: instantiate an existential quantifier for x in the succedent by itself as a witness */
  val existsR: DependentPositionTactic = existsR(None)
  private[btactics] val existsRInfo: TacticInfo = TacticInfo("existsR")

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
  @Tactic(
    name = "existsRmon",
    displayName = Some("M∃R"),
    displayNameAscii = Some("MexistsR"),
    inputs = "q(x):formula",
    displayPremises = "Γ |- ∃x q(x), Δ ;; Γ, q(x) |- p(x), Δ",
    displayConclusion = "Γ |- ∃x p(x), Δ",
  )
  def existsRmon(q: Formula): DependentPositionWithAppliedInputTactic = inputanon { (pos: Position, seq: Sequent) =>
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
  }

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
  @Tactic(
    name = "close",
    displayName = Some("⊥/⊤"),
    displayNameAscii = Some("false/true"),
    displayNameLong = Some("Close by id/⊥/⊤"),
    displayPremises = "*",
    displayConclusion = "Γ, P |- P, Δ",
  )
  val close: BuiltInTactic = anon { (pr: ProvableSig) => findClose.result(pr) }

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
  private def findClose: BuiltInTactic = anon { provable: ProvableSig =>
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
  @Tactic(name = "closeId", displayNameLong = Some("Close by Identity"))
  val closeId: BuiltInTwoPositionTactic = anon((provable: ProvableSig, a: Position, s: Position) => {
    ProofRuleTactics.requireOneSubgoal(provable, "closeId(" + a + "," + s + ")")
    try { provable(Close(a.checkAnte.checkTop, s.checkSucc.checkTop), 0) }
    catch {
      case ex: NoncriticalCoreException => throw new TacticInapplicableFailure(
          "Tactic " + "closeId" + " applied at " + a + " and " + s + " is inapplicable in " + provable.prettyString,
          ex,
        )
    }
  })

  def close(a: Int, s: Int): BelleExpr = closeId(Position(a).checkAnte.top, Position(s).checkSucc.top)

  /**
   * closeIdWith: closes the branch with the formula at the given position when the same formula is in the antecedent
   * and succedent ([[org.keymaerax.core.Close Close]])
   */
  @Tactic(
    name = "idWith",
    displayNameLong = Some("Close by Identity"),
    displayPremises = "*",
    displayConclusion = "Γ, P |- P, Δ",
  )
  val closeIdWith: BuiltInPositionTactic = anon { (provable: ProvableSig, pos: Position) =>
    val s = provable.subgoals.head
    pos.top match {
      case p: AntePos => provable(Close(p, SuccPos(closeIdFound(pos, s.succ.indexOf(s(p))))), 0)
      case p: SuccPos => provable(Close(AntePos(closeIdFound(pos, s.ante.indexOf(s(p)))), p), 0)
    }
  }
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
  @Tactic(name = "id", displayPremises = "*", displayConclusion = "Γ, P |- P, Δ")
  val id: BuiltInTactic = anon { provable: ProvableSig =>
    require(provable.subgoals.size == 1, "Expects exactly 1 subgoal, but got " + provable.subgoals.size + " subgoals")
    val s = provable.subgoals.head
    s.ante.intersect(s.succ).headOption match {
      case Some(fml) => provable(Close(AntePos(s.ante.indexOf(fml)), SuccPos(s.succ.indexOf(fml))), 0)
      case None => throw new TacticInapplicableFailure(
          "Expects same formula in antecedent and succedent. Found:\n" + s.prettyString
        )
    }
  }

  @Tactic(name = "idx", displayPremises = "*", displayConclusion = "Γ, x=y, P(x) |- P(y), Δ")
  val idx: DependentTactic = new SingleGoalDependentTactic("idx") {
    override def computeExpr(sequent: Sequent): BelleExpr = {
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
  }

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
  @Tactic(
    name = "alphaRen",
    displayName = Some("BR"),
    displayNameLong = Some("Alpha Bound Rename"),
    displayPremises = "Γ |- P(y), Δ ;; Γ |- P(x), Δ, x=y",
    displayConclusion = "Γ |- P(x), Δ",
    inputs = "x:Variable;;y[y]:Variable",
  )
  def alphaRen(what: Variable, to: Variable): DependentPositionWithAppliedInputTactic =
    inputanon { (pos: Position, seq: Sequent) =>
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
    }

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
  @Tactic(
    name = "alphaRenAll",
    displayName = Some("α-renall"),
    displayNameAscii = Some("alpha-renall"),
    displayNameLong = Some("Alpha Rename All"),
    displayPremises = "Γ(y) |- Δ(y) ;; Γ(x) |- Δ(x), x=y",
    displayConclusion = "Γ(x) |- Δ(x)",
    inputs = "x:Variable;;y[y]:Variable",
  )
  def alphaRenAll(what: Variable, to: Variable): InputTactic = inputanon { (seq: Sequent) =>
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
          cohide(Symbol("Rlast")) & existsR(to)(1) & TactixLibrary.byUS(Ax.equalReflexive),
        )
    } else {
      cut(Equal(what, to)) < (anteRewrite & succRewrite & exhaustiveEqL2R(hide = true)(Symbol("Llast")), Idioms.nil)
    }
  }

  /** Alpha renaming everywhere in the sequent using an equality at a specific position in the antecedent. */
  @Tactic(
    name = "alphaRenAllBy",
    displayName = Some("α-renallby"),
    displayNameAscii = Some("alpha-renallby"),
    displayNameLong = Some("Alpha Rename All By Equality"),
    displayPremises = "Γ(y), x=y |- Δ(y)",
    displayConclusion = "Γ(x), x=y |- Δ(x)",
  )
  val alphaRenAllBy: DependentPositionTactic = anon { (pos: Position, seq: Sequent) =>
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
  @Tactic(
    name = "closeT",
    displayName = Some("⊤R"),
    displayNameAscii = Some("trueR"),
    displayNameLong = Some("Close ⊤"),
    displayPremises = "*",
    displayConclusion = "Γ |- ⊤, Δ",
  )
  val closeT: BuiltInTactic = anon { (pr: ProvableSig) =>
    ProofRuleTactics.closeTrue(Symbol("R"), True).computeResult(pr)
  }
//  val closeT: BelleExpr = "closeTrue" by { ProofRuleTactics.closeTrue('R, True) }
  /**
   * closeF: closes the branch when false is in the antecedent ([[org.keymaerax.core.CloseFalse CloseFalse]]).
   * {{{
   *        *
   * ------------------ (close false)
   *   false, G |- D
   * }}}
   */
  @Tactic(
    name = "closeF",
    displayName = Some("⊥L"),
    displayNameAscii = Some("falseL"),
    displayNameLong = Some("Close ⊥"),
    displayPremises = "*",
    displayConclusion = "Γ, ⊥ |- Δ",
  )
  val closeF: BuiltInTactic = anon { (pr: ProvableSig) =>
    ProofRuleTactics.closeFalse(Symbol("L"), False).computeResult(pr)
  }
//  val closeF: BelleExpr = "closeFalse" by { ProofRuleTactics.closeFalse('L, False) }

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
  @Tactic(
    name = "equivifyR",
    displayName = Some("→2↔"),
    displayNameAscii = Some("->2<->R"),
    displayNameLong = Some("Strengthen to Equivalence"),
    displayPremises = "Γ |- P↔Q, Δ",
    displayConclusion = "Γ |- P→Q, Δ",
  )
  val equivifyR: CoreRightTactic = coreanon { (pr: ProvableSig, pos: SuccPosition) =>
    pr(EquivifyRight(pos.checkTop), 0)
  }

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
  @Tactic(
    name = "commuteEquivL",
    displayName = Some("↔cL"),
    displayNameAscii = Some("<->cLR"),
    displayNameLong = Some("Commute Equivalence Left"),
    displayPremises = "Q↔P, Γ |- Δ",
    displayConclusion = "P↔Q, Γ |- Δ",
  )
  val commuteEquivL: CoreLeftTactic = coreanon { (pr: ProvableSig, pos: AntePosition) =>
    pr(CommuteEquivLeft(pos.checkTop), 0)
  }

  /**
   * Commute equivalence on the right [[org.keymaerax.core.CommuteEquivRight CommuteEquivRight]].
   * {{{
   * G |- q<->p, D
   * ------------- (<->cR)
   * G |- p<->q, D
   * }}}
   */
  @Tactic(
    name = "commuteEquivR",
    displayName = Some("↔cR"),
    displayNameAscii = Some("<->cR"),
    displayNameLong = Some("Commute Equivalence Right"),
    displayPremises = "Γ |- Q↔P, Δ",
    displayConclusion = "Γ |- P↔Q, Δ",
  )
  val commuteEquivR: CoreRightTactic = coreanon { (pr: ProvableSig, pos: SuccPosition) =>
    pr(CommuteEquivRight(pos.checkTop), 0)
  }

  /** Commute equality `a=b` to `b=a` */
  @Tactic(
    name = "commuteEqual",
    displayName = Some("=c"),
    displayNameLong = Some("Commute Equal"),
    displayConclusion = "__p=q__ ↔ q=p",
  )
  lazy val commuteEqual: BuiltInPositionTactic = UnifyUSCalculus.useAt(Ax.equalCommute)

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
  @Tactic(name = "label")
  def label(s: String): InputTactic = inputanon { label(BelleTopLevelLabel(s)) }

  /**
   * Mark the current proof branch and all subbranches `s``.
   *
   * @see
   *   [[label()]]
   */
  def sublabel(s: String): BelleExpr = UnifyUSCalculus.skip // LabelBranch(BelleSubLabel(???, s))

}
