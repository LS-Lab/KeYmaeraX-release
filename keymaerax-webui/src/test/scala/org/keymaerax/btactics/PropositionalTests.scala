/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon.BelleExpr
import org.keymaerax.btactics.PropositionalTactics._
import org.keymaerax.btactics.TactixLibrary.{alphaRule, betaRule, master, normalize, prop}
import org.keymaerax.btactics.macros.DerivationInfoAugmentors.ProvableInfoAugmentor
import org.keymaerax.core._
import org.keymaerax.infrastruct.{AntePosition, PosInExpr, SuccPosition}
import org.keymaerax.parser.StringConverter._
import org.keymaerax.pt.ProvableSig
import org.keymaerax.tags.{SummaryTest, UsualTest}

import scala.collection.immutable._
import org.scalatest.LoneElement._

/**
 * Tests Propositional Calculus.
 * @see
 *   [[org.keymaerax.btactics.PropositionalTactics]]
 */
@SummaryTest @UsualTest
class PropositionalTests extends TacticTestBase {

  "Modus ponens" should "should work in a simple example" in withTactics {
    val result = proveBy(
      Sequent(IndexedSeq("x>0".asFormula, "x>0 -> y>0".asFormula), IndexedSeq()),
      modusPonens(AntePos(0), AntePos(1)),
    )
    result.subgoals.loneElement shouldBe "x>0, y>0 ==> ".asSequent
  }

  it should "should work when assumption is behind conjunction in antecedent" in withTactics {
    val result = proveBy(
      Sequent(IndexedSeq("x>0 -> y>0".asFormula, "x>0".asFormula), IndexedSeq()),
      modusPonens(AntePos(1), AntePos(0)),
    )
    result.subgoals.loneElement shouldBe "y>0, x>0 ==> ".asSequent
  }

  it should "automatically simplify assumptions" in withQE { _ =>
    val s = "x>0->y>0, z=1, x>0 ==> y>0".asSequent
    proveBy(s, autoMP(-1)).subgoals.loneElement shouldBe "y>0, z=1, x>0 ==> y>0".asSequent
  }

  it should "automatically cut and use hidden assumptions" in withQE { _ =>
    val s = "Y>y, X>y, y<x&x<=Y->P(x) ==>  y<x&x<=min(X,Y)->P(x)".asSequent
    proveBy(s, autoMP(-3)).subgoals.loneElement shouldBe "Y>y, X>y, P(x) ==> y<x&x<=min(X,Y)->P(x)".asSequent
  }

  "equivRewriting" should "rewrite simple equivalence" in withTactics {
    proveBy("p(x) <-> q(x) ==> p(x)".asSequent, equivRewriting(-1, 1)).subgoals.loneElement shouldBe
      "p(x) <-> q(x) ==> q(x)".asSequent
    proveBy("p(x) <-> q(x), p(x) ==> ".asSequent, equivRewriting(-1, -2)).subgoals.loneElement shouldBe
      "p(x) <-> q(x), q(x) ==> ".asSequent
  }

  it should "rewrite with renaming" in withTactics {
    proveBy("\\forall x (p(x) <-> q(x)) ==> p(y)".asSequent, equivRewriting(-1, 1)).subgoals.loneElement shouldBe
      "\\forall x (p(x) <-> q(x)) ==> q(y)".asSequent
    proveBy("\\forall x (p(x) <-> q(x)), p(y) ==> ".asSequent, equivRewriting(-1, -2)).subgoals.loneElement shouldBe
      "\\forall x (p(x) <-> q(x)), q(y) ==> ".asSequent
  }

  it should "rewrite in context" in withTactics {
    proveBy("Q()<->R() ==> !Q()".asSequent, equivRewriting(AntePosition(1), SuccPosition(1, List(0))))
      .subgoals
      .loneElement shouldBe "Q()<->R() ==> !R()".asSequent
  }

  it should "rewrite in equivalence" in withTactics {
    proveBy("Q()<->R() ==> Q()<->R()".asSequent, equivRewriting(AntePosition(1), SuccPosition(1, List(0))))
      .subgoals
      .loneElement shouldBe "Q()<->R() ==> R()<->R()".asSequent
  }

  "toSingleFormula" should "collapse a sequent into a single formula" in withTactics {
    proveBy("a=1, b=2, c=3 ==> x=1, y=2".asSequent, toSingleFormula).subgoals.loneElement shouldBe
      "==> a=1&b=2&c=3 -> x=1|y=2".asSequent
    proveBy(" ==> x=1, y=2".asSequent, toSingleFormula).subgoals.loneElement shouldBe "==> true -> x=1|y=2".asSequent
    proveBy("a=1, b=2, c=3 ==> ".asSequent, toSingleFormula).subgoals.loneElement shouldBe
      "==> a=1&b=2&c=3 -> false".asSequent
  }

  "implyRi" should "introduce implication from antecedent and succedent" in withTactics {
    val result = proveBy(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("y>0".asFormula)), implyRi)
    result.subgoals.loneElement shouldBe " ==> x>0 -> y>0".asSequent
  }

  it should "work as two-position tactic" in withTactics {
    val result = proveBy(
      Sequent(IndexedSeq("a=2".asFormula, "x>0".asFormula), IndexedSeq("y>0".asFormula, "b=3".asFormula)),
      implyRi()(AntePos(1), SuccPos(0)),
    )
    result.subgoals.loneElement shouldBe "a=2 ==> x>0 -> y>0, b=3".asSequent
  }

  "orRi" should "introduce disjunction from succedent" in withTactics {
    val result = proveBy(Sequent(IndexedSeq(), IndexedSeq("x>0".asFormula, "y>0".asFormula)), orRi)
    result.subgoals.loneElement shouldBe " ==> x>0 | y>0".asSequent
  }

  it should "work as two-position tactic" in withTactics {
    val result = proveBy(
      Sequent(IndexedSeq("a=2".asFormula), IndexedSeq("y>0".asFormula, "b=3".asFormula, "x>0".asFormula)),
      orRi(keepLeft = false)(SuccPos(1), SuccPos(0)),
    )
    result.subgoals.loneElement shouldBe "a=2 ==> x>0, b=3 | y>0".asSequent
  }

  "andLi" should "introduce conjunction from antecedent" in withTactics {
    val result = proveBy(Sequent(IndexedSeq("x>0".asFormula, "y>0".asFormula), IndexedSeq()), andLi)
    result.subgoals.loneElement shouldBe "x>0 & y>0 ==> ".asSequent
  }

  it should "work as two-position tactic" in withTactics {
    val result = proveBy(
      Sequent(IndexedSeq("y>0".asFormula, "b=3".asFormula, "x>0".asFormula), IndexedSeq("a=2".asFormula)),
      andLi(keepLeft = false)(AntePosition.base0(1), AntePosition.base0(0)),
    )
    result.subgoals.loneElement shouldBe "x>0, b=3 & y>0 ==> a=2".asSequent
  }

  it should "keep left conjunct if asked" in withTactics {
    val result =
      proveBy("y>0, b=3, x>0 ==> a=2".asSequent, andLi(keepLeft = true)(AntePosition.base0(1), AntePosition.base0(0)))
    result.subgoals.loneElement shouldBe "b=3, x>0, b=3 & y>0 ==> a=2".asSequent
  }

  private def succImplication(t: BelleExpr, check: Option[ProvableSig => Any] = None): Unit = {
    val result = proveBy("x>1 -> y>1".asFormula, t)
    check match {
      case Some(c) => c(result)
      case None => result.subgoals.loneElement shouldBe "x>1 ==> y>1".asSequent
    }
  }

  private def succDisjunction(t: BelleExpr, check: Option[ProvableSig => Any] = None): Unit = {
    val result = proveBy("x>1 | y>1".asFormula, t)
    check match {
      case Some(c) => c(result)
      case None => result.subgoals.loneElement shouldBe "==> x>1, y>1".asSequent
    }
  }

  private def succConjunction(t: BelleExpr, check: Option[ProvableSig => Any] = None): Unit = {
    val result = proveBy("x>1 & y>1".asFormula, t)
    check match {
      case Some(c) => c(result)
      case None =>
        result.subgoals should have size 2
        result.subgoals(0) shouldBe " ==> x>1".asSequent
        result.subgoals(1) shouldBe " ==> y>1".asSequent
    }
  }

  private def succNegation(t: BelleExpr, check: Option[ProvableSig => Any] = None): Unit = {
    val result = proveBy("!y>1".asFormula, t)
    check match {
      case Some(c) => c(result)
      case None => result.subgoals.loneElement shouldBe "y>1 ==> ".asSequent
    }
  }

  private def succEquivalence(t: BelleExpr, check: Option[ProvableSig => Any] = None): Unit = {
    val result = proveBy("x>1 <-> y>1".asFormula, t)
    check match {
      case Some(c) => c(result)
      case None =>
        result.subgoals should have size 2
        result.subgoals(0) shouldBe "x>1 ==> y>1".asSequent
        result.subgoals(1) shouldBe "y>1 ==> x>1".asSequent
    }
  }

  private def anteImplication(t: BelleExpr, check: Option[ProvableSig => Any] = None): Unit = {
    val result = proveBy(Sequent(IndexedSeq("x>1 -> y>1".asFormula), IndexedSeq()), t)
    check match {
      case Some(c) => c(result)
      case None =>
        result.subgoals should have size 2
        result.subgoals(0) shouldBe "==> x>1".asSequent
        result.subgoals(1) shouldBe "y>1 ==> ".asSequent
    }
  }

  private def anteConjunction(t: BelleExpr, check: Option[ProvableSig => Any] = None): Unit = {
    val result = proveBy(Sequent(IndexedSeq("x>1 & y>1".asFormula), IndexedSeq()), t)
    check match {
      case Some(c) => c(result)
      case None => result.subgoals.loneElement shouldBe "x>1, y>1 ==> ".asSequent
    }
  }

  private def anteDisjunction(t: BelleExpr, check: Option[ProvableSig => Any] = None): Unit = {
    val result = proveBy(Sequent(IndexedSeq("x>1 | y>1".asFormula), IndexedSeq()), t)
    check match {
      case Some(c) => c(result)
      case None =>
        result.subgoals should have size 2
        result.subgoals(0) shouldBe "x>1 ==> ".asSequent
        result.subgoals(1) shouldBe "y>1 ==> ".asSequent
    }
  }

  private def anteNegation(t: BelleExpr, check: Option[ProvableSig => Any] = None): Unit = {
    val result = proveBy(Sequent(IndexedSeq("!x>1".asFormula), IndexedSeq()), t)
    check match {
      case Some(c) => c(result)
      case None => result.subgoals.loneElement shouldBe "==> x>1".asSequent
    }
  }

  "Alpha rule" should "handle implication in succedent" in withTactics { succImplication(alphaRule) }
  it should "handle disjunction in succedent" in withTactics { succDisjunction(alphaRule) }
  it should "handle negation in succedent" in withTactics { succNegation(alphaRule) }
  it should "handle conjunction in antecedent" in withTactics { anteConjunction(alphaRule) }
  it should "handle negation in antecedent" in withTactics { anteNegation(alphaRule) }

  "Beta rule" should "handle implication in antecedent" in withTactics { anteImplication(betaRule) }
  it should "handle disjunction in antecedent" in withTactics { anteDisjunction(betaRule) }
  it should "handle conjunction in succedent" in withTactics { succConjunction(betaRule) }
  it should "handle equivalence in antecedent" in withTactics {
    val result = proveBy(Sequent(IndexedSeq("x>1 <-> y>1".asFormula), IndexedSeq()), betaRule)
    result.subgoals should have size 2
    result.subgoals(0) shouldBe "x>1 & y>1 ==> ".asSequent
    result.subgoals(1) shouldBe "!x>1 & !y>1 ==> ".asSequent
  }
  it should "handle equivalence in succedent" in withTactics { succEquivalence(betaRule) }

  "Prop" should "handle implication in succedent" in withTactics { succImplication(prop) }
  it should "handle disjunction in succedent" in withTactics { succDisjunction(prop) }
  it should "handle negation in succedent" in withTactics { succNegation(prop) }
  it should "handle conjunction in antecedent" in withTactics { anteConjunction(prop) }
  it should "handle negation in antecedent" in withTactics { anteNegation(prop) }
  it should "handle implication in antecedent" in withTactics { anteImplication(prop) }
  it should "handle disjunction in antecedent" in withTactics { anteDisjunction(prop) }
  it should "handle conjunction in succedent" in withTactics { succConjunction(prop) }
  it should "handle equivalence in antecedent" in withTactics {
    val result = proveBy(Sequent(IndexedSeq("x>1 <-> y>1".asFormula), IndexedSeq()), prop)
    result.subgoals should have size 2
    result.subgoals(0) shouldBe "x>1, y>1 ==> ".asSequent
    result.subgoals(1) shouldBe "==> x>1, y>1".asSequent
  }
  it should "handle equivalence in succedent" in withTactics { succEquivalence(prop) }
  it should "handle nested branching" in withTactics {
    proveBy("(p_()<->q_())&q_()->p_()<->true".asFormula, prop) shouldBe Symbol("proved")
  }
  it should "handle more nested branching" in withTactics {
    val result = proveBy("(A_() -> (L_() = LL_())) -> (A_() -> L_()+R_() = LL_()+R_())".asFormula, prop)
    result.subgoals.loneElement shouldBe "L_()=LL_(), A_() ==> L_()+R_()=LL_()+R_()".asSequent
  }

  "Builtin prop" should "handle implication in succedent" in withTactics { succImplication(PropositionalTactics.prop) }
  it should "handle disjunction in succedent" in withTactics { succDisjunction(PropositionalTactics.prop) }
  it should "handle negation in succedent" in withTactics { succNegation(PropositionalTactics.prop) }
  it should "handle conjunction in antecedent" in withTactics { anteConjunction(PropositionalTactics.prop) }
  it should "handle negation in antecedent" in withTactics { anteNegation(PropositionalTactics.prop) }
  it should "handle implication in antecedent" in withTactics { anteImplication(PropositionalTactics.prop) }
  it should "handle disjunction in antecedent" in withTactics { anteDisjunction(PropositionalTactics.prop) }
  it should "handle conjunction in succedent" in withTactics { succConjunction(PropositionalTactics.prop) }
  it should "handle equivalence in antecedent" in withTactics {
    val result = proveBy(Sequent(IndexedSeq("x>1 <-> y>1".asFormula), IndexedSeq()), PropositionalTactics.prop)
    result.subgoals should have size 2
    result.subgoals(0) shouldBe "x>1, y>1 ==> ".asSequent
    result.subgoals(1) shouldBe "==> y>1, x>1".asSequent
  }
  it should "handle equivalence in succedent" in withTactics { succEquivalence(PropositionalTactics.prop) }
  it should "handle nested branching" in withTactics {
    proveBy("(p_()<->q_())&q_()->p_()<->true".asFormula, PropositionalTactics.prop) shouldBe Symbol("proved")
  }
  it should "handle more nested branching" in withTactics {
    val result =
      proveBy("(A_() -> (L_() = LL_())) -> (A_() -> L_()+R_() = LL_()+R_())".asFormula, PropositionalTactics.prop)
    result.subgoals.loneElement shouldBe "L_()=LL_(), A_() ==> L_()+R_()=LL_()+R_()".asSequent
  }

  "Normalize" should "handle implication in succedent" in withTactics { succImplication(normalize) }
  it should "handle disjunction in succedent" in withTactics { succDisjunction(normalize) }
  it should "not FOL negate in succedent" in withTactics {
    succNegation(normalize, Some(_.subgoals.loneElement shouldBe "==> !y>1".asSequent))
  }
  it should "handle conjunction in antecedent" in withTactics { anteConjunction(normalize) }
  it should "not FOL negate in antecedent" in withTactics {
    anteNegation(normalize, Some(_.subgoals.loneElement shouldBe "!x>1 ==> ".asSequent))
  }
  it should "not split FOL implication in antecedent" in withQE { _ =>
    anteImplication(normalize, Some(_.subgoals.loneElement shouldBe "x>1 -> y>1 ==> ".asSequent))
  }
  it should "not split FOL disjunction in antecedent" in withTactics {
    anteDisjunction(normalize, Some(_.subgoals.loneElement shouldBe "x>1 | y>1 ==> ".asSequent))
  }
  it should "not split FOL conjunction in succedent" in withTactics {
    succConjunction(normalize, Some(_.subgoals.loneElement shouldBe "==> x>1 & y>1".asSequent))
  }
  it should "not split FOL equivalence in antecedent" in withTactics {
    val result = proveBy(Sequent(IndexedSeq("x>1 <-> y>1".asFormula), IndexedSeq()), normalize)
    result.subgoals.loneElement shouldBe "x>1 <-> y>1 ==> ".asSequent
  }
  it should "not split FOL equivalence in succedent" in withTactics {
    succEquivalence(normalize, Some(_.subgoals.loneElement shouldBe "==> x>1 <-> y>1".asSequent))
  }

  private def checkFalse(subgoals: Int)(p: ProvableSig): Unit = {
    p.subgoals should have size subgoals
    p.subgoals.foreach(_ shouldBe " ==> false".asSequent)
  }

  "Auto" should "handle implication in succedent" in withMathematica { _ =>
    succImplication(master(), Some(checkFalse(1)))
  }
  it should "handle disjunction in succedent" in withMathematica { _ => succDisjunction(master(), Some(checkFalse(1))) }
  it should "handle negation in succedent" in withMathematica { _ => succNegation(master(), Some(checkFalse(1))) }
  it should "handle conjunction in antecedent" in withMathematica { _ =>
    anteConjunction(master(), Some(checkFalse(1)))
  }
  it should "handle negation in antecedent" in withMathematica { _ => anteNegation(master(), Some(checkFalse(1))) }
  it should "not split FOL implication in antecedent" in withMathematica { _ =>
    anteImplication(master(), Some(checkFalse(1)))
  }
  it should "not split FOL disjunction in antecedent" in withMathematica { _ =>
    anteDisjunction(master(), Some(checkFalse(1)))
  }
  it should "not split FOL conjunction in succedent" in withMathematica { _ =>
    succConjunction(master(), Some(checkFalse(1)))
  }
  it should "not split FOL equivalence in antecedent" in withMathematica { _ =>
    val result = proveBy(Sequent(IndexedSeq("x>1 <-> y>1".asFormula), IndexedSeq()), master())
    checkFalse(1)(result)
  }
  it should "not split FOL equivalence in succedent" in withMathematica { _ =>
    succEquivalence(master(), Some(checkFalse(1)))
  }

  "Propositional CMon" should "unpeel single negation" in withTactics {
    val result =
      proveBy(Sequent(IndexedSeq("!x>0".asFormula), IndexedSeq("!y>0".asFormula)), propCMon(PosInExpr(0 :: Nil)))
    result.subgoals.loneElement shouldBe "y>0 ==> x>0".asSequent
  }

  it should "unpeel single conjunction" in withTactics {
    {
      val result = proveBy(
        Sequent(IndexedSeq("y>0 & x>0".asFormula), IndexedSeq("z>0 & x>0".asFormula)),
        propCMon(PosInExpr(0 :: Nil)),
      )
      result.subgoals.loneElement shouldBe "y>0 ==> z>0".asSequent
    }
    {
      val result = proveBy(
        Sequent(IndexedSeq("x>0 & y>0".asFormula), IndexedSeq("x>0 & z>0".asFormula)),
        propCMon(PosInExpr(1 :: Nil)),
      )
      result.subgoals.loneElement shouldBe "y>0 ==> z>0".asSequent
    }
  }

  it should "unpeel single disjunction" in withTactics {
    {
      val result = proveBy(
        Sequent(IndexedSeq("y>0 | x>0".asFormula), IndexedSeq("z>0 | x>0".asFormula)),
        propCMon(PosInExpr(0 :: Nil)),
      )
      result.subgoals.loneElement shouldBe "y>0 ==> z>0".asSequent
    }
    {
      val result = proveBy(
        Sequent(IndexedSeq("x>0 | y>0".asFormula), IndexedSeq("x>0 | z>0".asFormula)),
        propCMon(PosInExpr(1 :: Nil)),
      )
      result.subgoals.loneElement shouldBe "y>0 ==> z>0".asSequent
    }
  }

  it should "unpeel single implication" in withTactics {
    {
      val result = proveBy(
        Sequent(IndexedSeq("y>0 -> x>0".asFormula), IndexedSeq("z>0 -> x>0".asFormula)),
        propCMon(PosInExpr(0 :: Nil)),
      )
      result.subgoals.loneElement shouldBe "z>0 ==> y>0".asSequent
    }
    {
      val result = proveBy(
        Sequent(IndexedSeq("x>0 -> y>0".asFormula), IndexedSeq("x>0 -> z>0".asFormula)),
        propCMon(PosInExpr(1 :: Nil)),
      )
      result.subgoals.loneElement shouldBe "y>0 ==> z>0".asSequent
    }
  }

  it should "unpeel single box" in withTactics {
    val result = proveBy(
      Sequent(IndexedSeq("[x:=2;]x>1".asFormula), IndexedSeq("[x:=2;]x>0".asFormula)),
      propCMon(PosInExpr(1 :: Nil)),
    )
    result.subgoals.loneElement shouldBe "x>1 ==> x>0".asSequent
  }

  it should "unpeel single universal quantifier" in withTactics {
    val result = proveBy(
      Sequent(IndexedSeq("\\forall x x>1".asFormula), IndexedSeq("\\forall x x>0".asFormula)),
      propCMon(PosInExpr(0 :: Nil)),
    )
    result.subgoals.loneElement shouldBe "x>1 ==> x>0".asSequent
  }

  it should "unpeel single existential quantifier" in withTactics {
    val result = proveBy(
      Sequent(IndexedSeq("\\exists x x>1".asFormula), IndexedSeq("\\exists x x>0".asFormula)),
      propCMon(PosInExpr(0 :: Nil)),
    )
    result.subgoals.loneElement shouldBe "x>1 ==> x>0".asSequent
  }

  it should "unpeel complicated context" in withTactics {
    val result = proveBy(
      Sequent(
        IndexedSeq("\\exists x (a=2 -> b>1&!\\forall x x>0)".asFormula),
        IndexedSeq("\\exists x (a=2 -> b>1&!\\forall x x>1)".asFormula),
      ),
      propCMon(PosInExpr(0 :: 1 :: 1 :: 0 :: 0 :: Nil)),
    )
    result.subgoals.loneElement shouldBe "x>1 ==> x>0".asSequent
  }

  it should "report when trying to unpeel too far" in withTactics {
    the[IllegalArgumentException] thrownBy proveBy(
      Sequent(
        IndexedSeq("\\exists x (a=2 -> b>1&!\\forall x x>0)".asFormula),
        IndexedSeq("\\exists x (a=2 -> b>1&!\\forall x x>1)".asFormula),
      ),
      propCMon(PosInExpr(0 :: 1 :: 1 :: 0 :: 0 :: 1 :: 1 :: Nil)),
    ) should have message
      "requirement failed: Propositional CMon requires single antecedent and single succedent formula with matching context to .0.1.1.0.0.1.1, but got \\exists x (a=2->b>1&!\\forall x x>0)\n  ==>  \\exists x (a=2->b>1&!\\forall x x>1)\n(.0.1.1.0.0.1.1 points to non-existing position in sequent)"
  }

  it should "report when contexts don't match" in withTactics {
    the[IllegalArgumentException] thrownBy proveBy(
      Sequent(IndexedSeq("\\exists x (a=3 -> z>=3)".asFormula), IndexedSeq("\\exists x (a=2 -> z>=1)".asFormula)),
      propCMon(PosInExpr(0 :: 1 :: Nil)),
    ) should have message
      "requirement failed: Propositional CMon requires single antecedent and single succedent formula with matching context to .0.1, but got \\exists x (a=3->z>=3)\n  ==>  \\exists x (a=2->z>=1)\n\\exists x (a=3->⎵) != \\exists x (a=2->⎵)"
  }

  "Negation normal" should "produce a proof" in withTactics {
    val fml = "!!p() & !q() | !(r() -> s())".asFormula
    val (dnf, proof) = PropositionalTactics.negationNormalForm(fml)
    dnf shouldBe "p()&!q()|r()&!s()".asFormula
    proof shouldBe Symbol("proved")
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(Equiv(fml, dnf)))
  }

  it should "produce a proof (2)" in withTactics {
    val fml = "!!p() & !x=1 | !(r() -> y>=2)".asFormula
    val (dnf, proof) = PropositionalTactics.negationNormalForm(fml)
    dnf shouldBe "p()&x!=1 | r()&y<2".asFormula
    proof shouldBe Symbol("proved")
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(Equiv(fml, dnf)))
  }

  "Right-associate" should "produce a proof" in withTactics {
    val fml = "(p() & q()) & r()".asFormula
    val (r, proof) = PropositionalTactics.rightAssociate(fml)
    r shouldBe "p() & q() & r()".asFormula
    proof shouldBe Symbol("proved")
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(Equiv(fml, r)))
  }

  "Distribute or over and" should "produce a proof (1)" in withTactics {
    val fml = "p() & (q() | r())".asFormula
    val (dist, proof) = PropositionalTactics.orDistAnd(fml)
    dist shouldBe "q()&p() | r()&p()".asFormula
    proof shouldBe Symbol("proved")
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(Equiv(fml, dist)))
  }

  it should "produce a proof (2)" in withTactics {
    val fml = "p_1()&(q()|r()) | p_2()&(q()|r())".asFormula
    val (dist, proof) = PropositionalTactics.orDistAnd(fml)
    dist shouldBe "(q()&p_1() | r()&p_1()) | (q()&p_2()|r()&p_2())".asFormula
    proof shouldBe Symbol("proved")
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(Equiv(fml, dist)))
  }

  it should "produce a proof (3)" in withTactics {
    val fml = "p_1()&(q()|r()) | p_2()&(q()|r()) | p_3()&(q()|r()) | p_4()".asFormula
    val (dist, proof) = PropositionalTactics.orDistAnd(fml)
    dist shouldBe "(q()&p_1() | r()&p_1()) | (q()&p_2()|r()&p_2()) | (q()&p_3()|r()&p_3()) | p_4()".asFormula
    proof shouldBe Symbol("proved")
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(Equiv(fml, dist)))
  }

//  "Distribute or over and reverse" should "produce a proof (1)" in withTactics {
//    val fml = "p() & (q() | r())".asFormula
//    val reversed = ProvableSig.startProof(Equiv(fml, "q()&p() | r()&p()".asFormula))(PropositionalTactics.orDistAndReverse(fml)(SuccPosition.base0(0, PosInExpr(List(1)))).computeResult _, 0)
//    //@todo rearrange disjunctions, close by equivReflexive
//    reversed shouldBe 'proved
//  }
//
//  it should "produce a proof (2)" in withTactics {
//    val fml = "p_1()&(q()|r()) | p_2()&(q()|r()) | p_3()&(q()|r()) | p_4()".asFormula
//    val reversed = ProvableSig.startProof(Equiv(fml, "(q()&p_1() | r()&p_1()) | (q()&p_2()|r()&p_2()) | (q()&p_3()|r()&p_3()) | p_4()".asFormula))(PropositionalTactics.orDistAndReverse(fml)(SuccPosition.base0(0, PosInExpr(List(1)))).computeResult _, 0)
//    reversed shouldBe 'proved
//  }
//
//  it should "work on a water tank example" in withTactics {
//    val src = "(cpost<=ep()&ep()>=0)&(lpost>=0&(fd=0|ep()*fd+l>0&fd>=0)|(fd < 0&cpost*fd+l>=0)&ep()*fd+l=0)|(cpost < ep()&ep()>0)&((fd < 0&cpost*fd+l>=0)&ep()*fd+l<=0|fd>0&lpost>=0)".asFormula
//
//    //val (q, _) = orDistAnd(src)
//
//    val fml =
//      """((ep()*fd+l>0&fd>=0)&lpost>=0)&cpost<=ep()&ep()>=0 |
//        |(fd=0&lpost>=0)&cpost<=ep()&ep()>=0 |
//        |((fd < 0&cpost*fd+l>=0)&ep()*fd+l=0)&cpost<=ep()&ep()>=0 |
//        |((fd < 0&cpost*fd+l>=0)&ep()*fd+l<=0)&cpost < ep()&ep()>0 |
//        |(fd>0&lpost>=0)&cpost < ep()&ep()>0
//        |""".stripMargin.asFormula
//    val reversed = ProvableSig.startProof(Equiv(src, fml))(PropositionalTactics.orDistAndReverse(src)(SuccPosition.base0(0, PosInExpr(List(1)))).computeResult _, 0)
//    reversed(UnifyUSCalculus.byUS(Ax.equivReflexive.provable).result _, 0) shouldBe 'proved
//  }

  "Disjunctive normal form" should "produce a proof (1)" in withTactics {
    val fml = "p() | q()".asFormula
    val (dnf, proof) = PropositionalTactics.disjunctiveNormalForm(fml)
    dnf shouldBe "p() | q()".asFormula
    proof shouldBe Symbol("proved")
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(Equiv(fml, dnf)))
  }

  it should "produce a proof (2)" in withTactics {
    val fml = "(p() | q()) & r()".asFormula
    val (dnf, proof) = PropositionalTactics.disjunctiveNormalForm(fml)
    dnf shouldBe "(p() & r()) | (q() & r())".asFormula
    proof shouldBe Symbol("proved")
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(Equiv(fml, dnf)))
  }

  it should "produce a proof (3)" in withTactics {
    val fml = "p() & (q_1() | q_2()) & (r_1() | r_2())".asFormula
    val (dnf, proof) = PropositionalTactics.disjunctiveNormalForm(fml)
    dnf shouldBe "q_1()&r_1()&p() | q_1()&r_2()&p() | q_2()&r_1()&p() | q_2()&r_2()&p()".asFormula
    proof shouldBe Symbol("proved")
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(Equiv(fml, dnf)))
  }

  it should "produce a proof (4)" in withTactics {
    val fml = "p_1() & (q_1() | q_2()) & (r_1() | r_2()) & p_2() & (s_1() | s_2() | s_3())".asFormula
    val (dnf, proof) = PropositionalTactics.disjunctiveNormalForm(fml)
    dnf shouldBe
      """q_1()&r_1()&s_1()&p_1()&p_2() | q_1()&r_1()&s_2()&p_1()&p_2() | q_1()&r_1()&s_3()&p_1()&p_2() | q_1()&r_2()&s_1()&p_1()&p_2() | q_1()&r_2()&s_2()&p_1()&p_2() | q_1()&r_2()&s_3()&p_1()&p_2() |
        |q_2()&r_1()&s_1()&p_1()&p_2() | q_2()&r_1()&s_2()&p_1()&p_2() | q_2()&r_1()&s_3()&p_1()&p_2() | q_2()&r_2()&s_1()&p_1()&p_2() | q_2()&r_2()&s_2()&p_1()&p_2() | q_2()&r_2()&s_3()&p_1()&p_2()
        |""".stripMargin.asFormula
    proof shouldBe Symbol("proved")
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(Equiv(fml, dnf)))
  }

  it should "produce a proof (5)" in withTactics {
    val fml = "(x=0 & y=1 | x=1 & !y=3) <-> (!z<4 & a+b!=5)".asFormula
    val (dnf, proof) = PropositionalTactics.disjunctiveNormalForm(fml)
    dnf shouldBe
      "x=0&y=1&z>=4&a+b!=5|x=1&y!=3&z>=4&a+b!=5|x!=0&x!=1&z < 4|x!=0&x!=1&a+b=5|x!=0&y=3&z < 4|x!=0&y=3&a+b=5|y!=1&x!=1&z < 4|y!=1&x!=1&a+b=5|y!=1&y=3&z < 4|y!=1&y=3&a+b=5"
        .asFormula
    proof shouldBe Symbol("proved")
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(Equiv(fml, dnf)))
  }
}
