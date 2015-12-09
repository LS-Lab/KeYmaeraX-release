package btactics

/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/


import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.PropositionalTactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, UsualTest}
import org.scalatest.{BeforeAndAfterEach, FlatSpec, Matchers}
import test.RandomFormula
import testHelper.KeYmaeraXTestTags

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
}
