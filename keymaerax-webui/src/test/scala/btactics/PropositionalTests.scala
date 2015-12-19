package btactics

/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/


import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.btactics.PropositionalTactics._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.{alphaRule, betaRule, normalize, prop}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.PosInExpr
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, UsualTest}

import scala.collection.immutable._

/**
 * Tests Propositional Calculus.
 * @see [[edu.cmu.cs.ls.keymaerax.btactics.PropositionalTactics]]
 */
@SummaryTest
@UsualTest
class PropositionalTests extends TacticTestBase {

  "Modus ponens" should "should work in a simple example" in {
    val result = proveBy(Sequent(Nil, IndexedSeq("x>0".asFormula, "x>0 -> y>0".asFormula), IndexedSeq()),
      modusPonens(AntePos(0), AntePos(1)))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x>0".asFormula, "y>0".asFormula)
    result.subgoals.head.succ shouldBe empty
  }

  it should "should work when assumption is behind conjunction in antecedent" in {
    val result = proveBy(Sequent(Nil, IndexedSeq("x>0 -> y>0".asFormula, "x>0".asFormula), IndexedSeq()),
      modusPonens(AntePos(1), AntePos(0)))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x>0".asFormula, "y>0".asFormula)
    result.subgoals.head.succ shouldBe empty
  }

  "implyRi" should "introduce implication from antecedent and succedent" in {
    val result = proveBy(Sequent(Nil, IndexedSeq("x>0".asFormula), IndexedSeq("y>0".asFormula)),
      implyRi())
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "x>0 -> y>0".asFormula
  }

  it should "work as two-position tactic" in {
    val result = proveBy(Sequent(Nil, IndexedSeq("a=2".asFormula, "x>0".asFormula), IndexedSeq("y>0".asFormula, "b=3".asFormula)),
      implyRi(AntePos(1), SuccPos(0)))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "a=2".asFormula
    result.subgoals.head.succ should contain only ("x>0 -> y>0".asFormula, "b=3".asFormula)
  }

  private def succImplication(t: BelleExpr) {
    val result = proveBy("x>1 -> y>1".asFormula, t)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x>1".asFormula
    result.subgoals.head.succ should contain only "y>1".asFormula
  }

  private def succDisjunction(t: BelleExpr) {
    val result = proveBy("x>1 | y>1".asFormula, t)
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only ("x>1".asFormula, "y>1".asFormula)
  }

  private def succConjunction(t: BelleExpr) {
    val result = proveBy("x>1 & y>1".asFormula, t)
    result.subgoals should have size 2
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "x>1".asFormula
    result.subgoals.last.ante shouldBe empty
    result.subgoals.last.succ should contain only "y>1".asFormula
  }

  private def succNegation(t: BelleExpr) {
    val result = proveBy("!y>1".asFormula, t)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "y>1".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  private def succEquivalence(t: BelleExpr) {
    val result = proveBy("x>1 <-> y>1".asFormula, t)
    result.subgoals should have size 2
    result.subgoals.head.ante should contain only "x>1".asFormula
    result.subgoals.head.succ should contain only "y>1".asFormula
    result.subgoals.last.ante should contain only "y>1".asFormula
    result.subgoals.last.succ should contain only "x>1".asFormula
  }

  private def anteImplication(t: BelleExpr) {
    val result = proveBy(Sequent(Nil, IndexedSeq("x>1 -> y>1".asFormula), IndexedSeq()), t)
    result.subgoals should have size 2
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "x>1".asFormula
    result.subgoals.last.ante should contain only "y>1".asFormula
    result.subgoals.last.succ shouldBe empty
  }

  private def anteConjunction(t: BelleExpr) {
    val result = proveBy(Sequent(Nil, IndexedSeq("x>1 & y>1".asFormula), IndexedSeq()), t)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x>1".asFormula, "y>1".asFormula)
    result.subgoals.head.succ shouldBe empty
  }

  private def anteDisjunction(t: BelleExpr) {
    val result = proveBy(Sequent(Nil, IndexedSeq("x>1 | y>1".asFormula), IndexedSeq()), t)
    result.subgoals should have size 2
    result.subgoals.head.ante should contain only "x>1".asFormula
    result.subgoals.head.succ shouldBe empty
    result.subgoals.last.ante should contain only "y>1".asFormula
    result.subgoals.last.succ shouldBe empty
  }

  private def anteNegation(t: BelleExpr) {
    val result = proveBy(Sequent(Nil, IndexedSeq("!x>1".asFormula), IndexedSeq()), t)
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "x>1".asFormula
  }

  "Alpha rule" should "handle implication in succedent" in succImplication(alphaRule)
  it should "handle disjunction in succedent" in succDisjunction(alphaRule)
  it should "handle negation in succedent" in succNegation(alphaRule)
  it should "handle conjunction in antecedent" in anteConjunction(alphaRule)
  it should "handle negation in antecedent" in anteNegation(alphaRule)

  "Beta rule" should "handle implication in antecedent" in anteImplication(betaRule)
  it should "handle disjunction in antecedent" in anteDisjunction(betaRule)
  it should "handle conjunction in succedent" in succConjunction(betaRule)
  it should "handle equivalence in antecedent" in {
    val result = proveBy(Sequent(Nil, IndexedSeq("x>1 <-> y>1".asFormula), IndexedSeq()), betaRule)
    result.subgoals should have size 2
    result.subgoals.head.ante should contain only "x>1 & y>1".asFormula
    result.subgoals.head.succ shouldBe empty
    result.subgoals.last.ante should contain only "!x>1 & !y>1".asFormula
    result.subgoals.last.succ shouldBe empty
  }
  it should "handle equivalence in succedent" in succEquivalence(betaRule)

  "Prop" should "handle implication in succedent" in succImplication(prop)
  it should "handle disjunction in succedent" in succDisjunction(prop)
  it should "handle negation in succedent" in succNegation(prop)
  it should "handle conjunction in antecedent" in anteConjunction(prop)
  it should "handle negation in antecedent" in anteNegation(prop)
  it should "handle implication in antecedent" in anteImplication(prop)
  it should "handle disjunction in antecedent" in anteDisjunction(prop)
  it should "handle conjunction in succedent" in succConjunction(prop)
  it should "handle equivalence in antecedent" in {
    val result = proveBy(Sequent(Nil, IndexedSeq("x>1 <-> y>1".asFormula), IndexedSeq()), prop)
    result.subgoals should have size 2
    result.subgoals.head.ante should contain only ("x>1".asFormula, "y>1".asFormula)
    result.subgoals.head.succ shouldBe empty
    result.subgoals.last.ante shouldBe empty
    result.subgoals.last.succ should contain only ("x>1".asFormula, "y>1".asFormula)
  }
  it should "handle equivalence in succedent" in succEquivalence(prop)

  "Normalize" should "handle implication in succedent" in succImplication(normalize)
  it should "handle disjunction in succedent" in succDisjunction(normalize)
  it should "handle negation in succedent" in succNegation(normalize)
  it should "handle conjunction in antecedent" in anteConjunction(normalize)
  it should "handle negation in antecedent" in anteNegation(normalize)
  it should "handle implication in antecedent" in anteImplication(normalize)
  it should "handle disjunction in antecedent" in anteDisjunction(normalize)
  it should "handle conjunction in succedent" in succConjunction(normalize)
  it should "handle equivalence in antecedent" in {
    val result = proveBy(Sequent(Nil, IndexedSeq("x>1 <-> y>1".asFormula), IndexedSeq()), prop)
    result.subgoals should have size 2
    result.subgoals.head.ante should contain only ("x>1".asFormula, "y>1".asFormula)
    result.subgoals.head.succ shouldBe empty
    result.subgoals.last.ante shouldBe empty
    result.subgoals.last.succ should contain only ("x>1".asFormula, "y>1".asFormula)
  }
  it should "handle equivalence in succedent" in succEquivalence(normalize)

  "Propositional CMon" should "unpeel single negation" in {
    val result = proveBy(Sequent(Nil, IndexedSeq("!x>0".asFormula), IndexedSeq("!y>0".asFormula)),
      propCMon(PosInExpr(0::Nil)))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "y>0".asFormula
    result.subgoals.head.succ should contain only "x>0".asFormula
  }

  it should "unpeel single conjunction" in {
    {
      val result = proveBy(Sequent(Nil, IndexedSeq("y>0 & x>0".asFormula), IndexedSeq("z>0 & x>0".asFormula)),
        propCMon(PosInExpr(0 :: Nil)))
      result.subgoals should have size 1
      result.subgoals.head.ante should contain only "y>0".asFormula
      result.subgoals.head.succ should contain only "z>0".asFormula
    }
    {
      val result = proveBy(Sequent(Nil, IndexedSeq("x>0 & y>0".asFormula), IndexedSeq("x>0 & z>0".asFormula)),
        propCMon(PosInExpr(1 :: Nil)))
      result.subgoals should have size 1
      result.subgoals.head.ante should contain only "y>0".asFormula
      result.subgoals.head.succ should contain only "z>0".asFormula
    }
  }

  it should "unpeel single disjunction" in {
    {
      val result = proveBy(Sequent(Nil, IndexedSeq("y>0 | x>0".asFormula), IndexedSeq("z>0 | x>0".asFormula)),
        propCMon(PosInExpr(0 :: Nil)))
      result.subgoals should have size 1
      result.subgoals.head.ante should contain only "y>0".asFormula
      result.subgoals.head.succ should contain only "z>0".asFormula
    }
    {
      val result = proveBy(Sequent(Nil, IndexedSeq("x>0 | y>0".asFormula), IndexedSeq("x>0 | z>0".asFormula)),
        propCMon(PosInExpr(1 :: Nil)))
      result.subgoals should have size 1
      result.subgoals.head.ante should contain only "y>0".asFormula
      result.subgoals.head.succ should contain only "z>0".asFormula
    }
  }

  it should "unpeel single implication" in {
    {
      val result = proveBy(Sequent(Nil, IndexedSeq("y>0 -> x>0".asFormula), IndexedSeq("z>0 -> x>0".asFormula)),
        propCMon(PosInExpr(0 :: Nil)))
      result.subgoals should have size 1
      result.subgoals.head.ante should contain only "z>0".asFormula
      result.subgoals.head.succ should contain only "y>0".asFormula
    }
    {
      val result = proveBy(Sequent(Nil, IndexedSeq("x>0 -> y>0".asFormula), IndexedSeq("x>0 -> z>0".asFormula)),
        propCMon(PosInExpr(1 :: Nil)))
      result.subgoals should have size 1
      result.subgoals.head.ante should contain only "y>0".asFormula
      result.subgoals.head.succ should contain only "z>0".asFormula
    }
  }

  it should "unpeel single box" in {
    val result = proveBy(Sequent(Nil, IndexedSeq("[x:=2;]x>1".asFormula), IndexedSeq("[x:=2;]x>0".asFormula)),
      propCMon(PosInExpr(1 :: Nil)))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x>1".asFormula
    result.subgoals.head.succ should contain only "x>0".asFormula
  }

  it should "unpeel single universal quantifier" in {
    val result = proveBy(Sequent(Nil, IndexedSeq("\\forall x x>1".asFormula), IndexedSeq("\\forall x x>0".asFormula)),
      propCMon(PosInExpr(0 :: Nil)))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x>1".asFormula
    result.subgoals.head.succ should contain only "x>0".asFormula
  }

  it should "unpeel single existential quantifier" in {
    val result = proveBy(Sequent(Nil, IndexedSeq("\\exists x x>1".asFormula), IndexedSeq("\\exists x x>0".asFormula)),
      propCMon(PosInExpr(0 :: Nil)))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x>1".asFormula
    result.subgoals.head.succ should contain only "x>0".asFormula
  }

  it should "unpeel complicated context" in {
    val result = proveBy(Sequent(Nil,
      IndexedSeq("\\exists x (a=2 -> b>1&!\\forall x x>0)".asFormula),
      IndexedSeq("\\exists x (a=2 -> b>1&!\\forall x x>1)".asFormula)),
      propCMon(PosInExpr(0::1::1::0::0::Nil)))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x>1".asFormula
    result.subgoals.head.succ should contain only "x>0".asFormula
  }
}
