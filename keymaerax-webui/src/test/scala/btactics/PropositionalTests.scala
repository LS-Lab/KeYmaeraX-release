package edu.cmu.cs.ls.keymaerax.btactics

/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/


import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, IllFormedTacticApplicationException}
import edu.cmu.cs.ls.keymaerax.btactics.PropositionalTactics._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.{alphaRule, betaRule, master, normalize, prop}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{AntePosition, PosInExpr}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, UsualTest}

import scala.collection.immutable._
import org.scalatest.LoneElement._

/**
 * Tests Propositional Calculus.
 * @see [[edu.cmu.cs.ls.keymaerax.btactics.PropositionalTactics]]
 */
@SummaryTest
@UsualTest
class PropositionalTests extends TacticTestBase {

  "Modus ponens" should "should work in a simple example" in withTactics {
    val result = proveBy(Sequent(IndexedSeq("x>0".asFormula, "x>0 -> y>0".asFormula), IndexedSeq()),
      modusPonens(AntePos(0), AntePos(1)))
    result.subgoals.loneElement shouldBe "x>0, y>0 ==> ".asSequent
  }

  it should "should work when assumption is behind conjunction in antecedent" in withTactics {
    val result = proveBy(Sequent(IndexedSeq("x>0 -> y>0".asFormula, "x>0".asFormula), IndexedSeq()),
      modusPonens(AntePos(1), AntePos(0)))
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

  "toSingleFormula" should "collapse a sequent into a single formula" in withTactics {
    proveBy("a=1, b=2, c=3 ==> x=1, y=2".asSequent, toSingleFormula).subgoals.loneElement shouldBe "==> a=1&b=2&c=3 -> x=1|y=2".asSequent
    proveBy(" ==> x=1, y=2".asSequent, toSingleFormula).subgoals.loneElement shouldBe "==> true -> x=1|y=2".asSequent
    proveBy("a=1, b=2, c=3 ==> ".asSequent, toSingleFormula).subgoals.loneElement shouldBe "==> a=1&b=2&c=3 -> false".asSequent
  }

  "implyRi" should "introduce implication from antecedent and succedent" in withTactics {
    val result = proveBy(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("y>0".asFormula)), implyRi)
    result.subgoals.loneElement shouldBe " ==> x>0 -> y>0".asSequent
  }

  it should "work as two-position tactic" in withTactics {
    val result = proveBy(Sequent(IndexedSeq("a=2".asFormula, "x>0".asFormula), IndexedSeq("y>0".asFormula, "b=3".asFormula)),
      implyRi()(AntePos(1), SuccPos(0)))
    result.subgoals.loneElement shouldBe "a=2 ==> x>0 -> y>0, b=3".asSequent
  }

  "orRi" should "introduce disjunction from succedent" in withTactics {
    val result = proveBy(Sequent(IndexedSeq(), IndexedSeq("x>0".asFormula, "y>0".asFormula)), orRi)
    result.subgoals.loneElement shouldBe " ==> x>0 | y>0".asSequent
  }

  it should "work as two-position tactic" in withTactics {
    val result = proveBy(Sequent(IndexedSeq("a=2".asFormula), IndexedSeq("y>0".asFormula, "b=3".asFormula, "x>0".asFormula)),
      orRi(keepLeft=false)(SuccPos(1), SuccPos(0)))
    result.subgoals.loneElement shouldBe "a=2 ==> x>0, b=3 | y>0".asSequent
  }

  "andLi" should "introduce conjunction from antecedent" in withTactics {
    val result = proveBy(Sequent(IndexedSeq("x>0".asFormula, "y>0".asFormula), IndexedSeq()), andLi)
    result.subgoals.loneElement shouldBe "x>0 & y>0 ==> ".asSequent
  }

  it should "work as two-position tactic" in withTactics {
    val result = proveBy(Sequent(IndexedSeq("y>0".asFormula, "b=3".asFormula, "x>0".asFormula), IndexedSeq("a=2".asFormula)),
      andLi(keepLeft=false)(AntePosition.base0(1), AntePosition.base0(0)))
    result.subgoals.loneElement shouldBe "x>0, b=3 & y>0 ==> a=2".asSequent
  }

  it should "keep left conjunct if asked" in withTactics {
    val result = proveBy("y>0, b=3, x>0 ==> a=2".asSequent, andLi(keepLeft=true)(AntePosition.base0(1), AntePosition.base0(0)))
    result.subgoals.loneElement shouldBe "b=3, x>0, b=3 & y>0 ==> a=2".asSequent
  }

  private def succImplication(t: BelleExpr, check: Option[ProvableSig => Any] = None) {
    val result = proveBy("x>1 -> y>1".asFormula, t)
    check match {
      case Some(c) => c(result)
      case None => result.subgoals.loneElement shouldBe "x>1 ==> y>1".asSequent
    }
  }

  private def succDisjunction(t: BelleExpr, check: Option[ProvableSig => Any] = None) {
    val result = proveBy("x>1 | y>1".asFormula, t)
    check match {
      case Some(c) => c(result)
      case None => result.subgoals.loneElement shouldBe "==> x>1, y>1".asSequent
    }
  }

  private def succConjunction(t: BelleExpr, check: Option[ProvableSig => Any] = None) {
    val result = proveBy("x>1 & y>1".asFormula, t)
    check match {
      case Some(c) => c(result)
      case None =>
        result.subgoals should have size 2
        result.subgoals(0) shouldBe " ==> x>1".asSequent
        result.subgoals(1) shouldBe " ==> y>1".asSequent
    }
  }

  private def succNegation(t: BelleExpr, check: Option[ProvableSig => Any] = None) {
    val result = proveBy("!y>1".asFormula, t)
    check match {
      case Some(c) => c(result)
      case None => result.subgoals.loneElement shouldBe "y>1 ==> ".asSequent
    }
  }

  private def succEquivalence(t: BelleExpr, check: Option[ProvableSig => Any] = None) {
    val result = proveBy("x>1 <-> y>1".asFormula, t)
    check match {
      case Some(c) => c(result)
      case None =>
        result.subgoals should have size 2
        result.subgoals(0) shouldBe "x>1 ==> y>1".asSequent
        result.subgoals(1) shouldBe "y>1 ==> x>1".asSequent
    }
  }

  private def anteImplication(t: BelleExpr, check: Option[ProvableSig => Any] = None) {
    val result = proveBy(Sequent(IndexedSeq("x>1 -> y>1".asFormula), IndexedSeq()), t)
    check match {
      case Some(c) => c(result)
      case None =>
        result.subgoals should have size 2
        result.subgoals(0) shouldBe "==> x>1".asSequent
        result.subgoals(1) shouldBe "y>1 ==> ".asSequent
    }
  }

  private def anteConjunction(t: BelleExpr, check: Option[ProvableSig => Any] = None) {
    val result = proveBy(Sequent(IndexedSeq("x>1 & y>1".asFormula), IndexedSeq()), t)
    check match {
      case Some(c) => c(result)
      case None => result.subgoals.loneElement shouldBe "x>1, y>1 ==> ".asSequent
    }
  }

  private def anteDisjunction(t: BelleExpr, check: Option[ProvableSig => Any] = None) {
    val result = proveBy(Sequent(IndexedSeq("x>1 | y>1".asFormula), IndexedSeq()), t)
    check match {
      case Some(c) => c(result)
      case None =>
        result.subgoals should have size 2
        result.subgoals(0) shouldBe "x>1 ==> ".asSequent
        result.subgoals(1) shouldBe "y>1 ==> ".asSequent
    }
  }

  private def anteNegation(t: BelleExpr, check: Option[ProvableSig => Any] = None) {
    val result = proveBy(Sequent(IndexedSeq("!x>1".asFormula), IndexedSeq()), t)
    check match {
      case Some(c) => c(result)
      case None =>
        result.subgoals.loneElement shouldBe "==> x>1".asSequent
    }
  }

  "Alpha rule" should "handle implication in succedent" in withTactics { succImplication(alphaRule) }
  it should "handle disjunction in succedent" in withTactics {succDisjunction(alphaRule) }
  it should "handle negation in succedent" in withTactics {succNegation(alphaRule) }
  it should "handle conjunction in antecedent" in withTactics {anteConjunction(alphaRule) }
  it should "handle negation in antecedent" in withTactics {anteNegation(alphaRule) }

  "Beta rule" should "handle implication in antecedent" in withTactics {anteImplication(betaRule) }
  it should "handle disjunction in antecedent" in withTactics {anteDisjunction(betaRule) }
  it should "handle conjunction in succedent" in withTactics {succConjunction(betaRule) }
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
  it should "handle nested branching" in withTactics { proveBy("(p_()<->q_())&q_()->p_()<->true".asFormula, prop) shouldBe 'proved }
  it should "handle more nested branching" in withTactics {
    val result = proveBy("(A_() -> (L_() = LL_())) -> (A_() -> L_()+R_() = LL_()+R_())".asFormula, prop)
    result.subgoals.loneElement shouldBe "L_()=LL_(), A_() ==> L_()+R_()=LL_()+R_()".asSequent
  }

  "Normalize" should "handle implication in succedent" in withTactics { succImplication(normalize) }
  it should "handle disjunction in succedent" in withTactics { succDisjunction(normalize) }
  it should "not FOL negate in succedent" in withTactics { succNegation(normalize, Some(_.subgoals.loneElement shouldBe "==> !y>1".asSequent)) }
  it should "handle conjunction in antecedent" in withTactics { anteConjunction(normalize) }
  it should "not FOL negate in antecedent" in withTactics { anteNegation(normalize, Some(_.subgoals.loneElement shouldBe "!x>1 ==> ".asSequent)) }
  it should "not split FOL implication in antecedent" in withQE { _ => anteImplication(normalize, Some(_.subgoals.loneElement shouldBe "x>1 -> y>1 ==> ".asSequent)) }
  it should "not split FOL disjunction in antecedent" in withTactics { anteDisjunction(normalize, Some(_.subgoals.loneElement shouldBe "x>1 | y>1 ==> ".asSequent)) }
  it should "not split FOL conjunction in succedent" in withTactics { succConjunction(normalize, Some(_.subgoals.loneElement shouldBe "==> x>1 & y>1".asSequent)) }
  it should "not split FOL equivalence in antecedent" in withTactics {
    val result = proveBy(Sequent(IndexedSeq("x>1 <-> y>1".asFormula), IndexedSeq()), normalize)
    result.subgoals.loneElement shouldBe "x>1 <-> y>1 ==> ".asSequent
  }
  it should "not split FOL equivalence in succedent" in withTactics { succEquivalence(normalize, Some(_.subgoals.loneElement shouldBe "==> x>1 <-> y>1".asSequent)) }

  private def checkFalse(subgoals: Int)(p: ProvableSig): Unit = {
    p.subgoals should have size subgoals
    p.subgoals.foreach(_ shouldBe " ==> false".asSequent)
  }

  "Auto" should "handle implication in succedent" in withMathematica { _ => succImplication(master(), Some(checkFalse(1))) }
  it should "handle disjunction in succedent" in withMathematica { _ => succDisjunction(master(), Some(checkFalse(1))) }
  it should "handle negation in succedent" in withMathematica { _ => succNegation(master(), Some(checkFalse(1))) }
  it should "handle conjunction in antecedent" in withMathematica { _ => anteConjunction(master(), Some(checkFalse(1))) }
  it should "handle negation in antecedent" in withMathematica { _ => anteNegation(master(), Some(checkFalse(1))) }
  it should "not split FOL implication in antecedent" in withMathematica { _ => anteImplication(master(), Some(checkFalse(1))) }
  it should "not split FOL disjunction in antecedent" in withMathematica { _ => anteDisjunction(master(), Some(checkFalse(1))) }
  it should "not split FOL conjunction in succedent" in withMathematica { _ => succConjunction(master(), Some(checkFalse(1))) }
  it should "not split FOL equivalence in antecedent" in withMathematica { _ =>
    val result = proveBy(Sequent(IndexedSeq("x>1 <-> y>1".asFormula), IndexedSeq()), master())
    checkFalse(1)(result)
  }
  it should "not split FOL equivalence in succedent" in withMathematica { _ => succEquivalence(master(), Some(checkFalse(1))) }

  "Propositional CMon" should "unpeel single negation" in withTactics {
    val result = proveBy(Sequent(IndexedSeq("!x>0".asFormula), IndexedSeq("!y>0".asFormula)),
      propCMon(PosInExpr(0::Nil)))
    result.subgoals.loneElement shouldBe "y>0 ==> x>0".asSequent
  }

  it should "unpeel single conjunction" in withTactics {
    {
      val result = proveBy(Sequent(IndexedSeq("y>0 & x>0".asFormula), IndexedSeq("z>0 & x>0".asFormula)),
        propCMon(PosInExpr(0 :: Nil)))
      result.subgoals.loneElement shouldBe "y>0 ==> z>0".asSequent
    }
    {
      val result = proveBy(Sequent(IndexedSeq("x>0 & y>0".asFormula), IndexedSeq("x>0 & z>0".asFormula)),
        propCMon(PosInExpr(1 :: Nil)))
      result.subgoals.loneElement shouldBe "y>0 ==> z>0".asSequent
    }
  }

  it should "unpeel single disjunction" in withTactics {
    {
      val result = proveBy(Sequent(IndexedSeq("y>0 | x>0".asFormula), IndexedSeq("z>0 | x>0".asFormula)),
        propCMon(PosInExpr(0 :: Nil)))
      result.subgoals.loneElement shouldBe "y>0 ==> z>0".asSequent
    }
    {
      val result = proveBy(Sequent(IndexedSeq("x>0 | y>0".asFormula), IndexedSeq("x>0 | z>0".asFormula)),
        propCMon(PosInExpr(1 :: Nil)))
      result.subgoals.loneElement shouldBe "y>0 ==> z>0".asSequent
    }
  }

  it should "unpeel single implication" in withTactics {
    {
      val result = proveBy(Sequent(IndexedSeq("y>0 -> x>0".asFormula), IndexedSeq("z>0 -> x>0".asFormula)),
        propCMon(PosInExpr(0 :: Nil)))
      result.subgoals.loneElement shouldBe "z>0 ==> y>0".asSequent
    }
    {
      val result = proveBy(Sequent(IndexedSeq("x>0 -> y>0".asFormula), IndexedSeq("x>0 -> z>0".asFormula)),
        propCMon(PosInExpr(1 :: Nil)))
      result.subgoals.loneElement shouldBe "y>0 ==> z>0".asSequent
    }
  }

  it should "unpeel single box" in withTactics {
    val result = proveBy(Sequent(IndexedSeq("[x:=2;]x>1".asFormula), IndexedSeq("[x:=2;]x>0".asFormula)),
      propCMon(PosInExpr(1 :: Nil)))
    result.subgoals.loneElement shouldBe "x>1 ==> x>0".asSequent
  }

  it should "unpeel single universal quantifier" in withTactics {
    val result = proveBy(Sequent(IndexedSeq("\\forall x x>1".asFormula), IndexedSeq("\\forall x x>0".asFormula)),
      propCMon(PosInExpr(0 :: Nil)))
    result.subgoals.loneElement shouldBe "x>1 ==> x>0".asSequent
  }

  it should "unpeel single existential quantifier" in withTactics {
    val result = proveBy(Sequent(IndexedSeq("\\exists x x>1".asFormula), IndexedSeq("\\exists x x>0".asFormula)),
      propCMon(PosInExpr(0 :: Nil)))
    result.subgoals.loneElement shouldBe "x>1 ==> x>0".asSequent
  }

  it should "unpeel complicated context" in withTactics {
    val result = proveBy(Sequent(IndexedSeq("\\exists x (a=2 -> b>1&!\\forall x x>0)".asFormula), IndexedSeq("\\exists x (a=2 -> b>1&!\\forall x x>1)".asFormula)),
      propCMon(PosInExpr(0::1::1::0::0::Nil)))
    result.subgoals.loneElement shouldBe "x>1 ==> x>0".asSequent
  }

  it should "report when trying to unpeel too far" in withTactics {
    the [IllFormedTacticApplicationException] thrownBy proveBy(Sequent(IndexedSeq("\\exists x (a=2 -> b>1&!\\forall x x>0)".asFormula), IndexedSeq("\\exists x (a=2 -> b>1&!\\forall x x>1)".asFormula)),
      propCMon(PosInExpr(0::1::1::0::0::1::1::Nil))) should have message "Unable to execute tactic 'Prop. CMon', cause: part position .1 of term 0 may not be defined"

  }
}
