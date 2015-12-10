package btactics

/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/


import edu.cmu.cs.ls.keymaerax.btactics.PropositionalTactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
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
}
