package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{AntePosition, Find, BelleError}
import edu.cmu.cs.ls.keymaerax.btactics.{TactixLibrary}
import edu.cmu.cs.ls.keymaerax.core.Sequent
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable

/**
 * Tests [[edu.cmu.cs.ls.keymaerax.bellerophon.PositionLocator]]
 */
class LocateTests extends TacticTestBase {

  "'L" should "locate the sole applicable formula in antecedent" in {
    val result = proveBy(
      Sequent(immutable.IndexedSeq("x>0 & y>0".asFormula), immutable.IndexedSeq()),
      TactixLibrary.andL('L)
    )
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x>0".asFormula, "y>0".asFormula)
    result.subgoals.head.succ shouldBe empty
  }

  it should "locate the first applicable formula in antecedent" in {
    val result = proveBy(
      Sequent(immutable.IndexedSeq("a=2".asFormula, "x>0 & y>0".asFormula, "b=3 & c=4".asFormula), immutable.IndexedSeq()),
      TactixLibrary.andL('L)
    )
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("a=2".asFormula, "x>0".asFormula, "y>0".asFormula, "b=3 & c=4".asFormula)
    result.subgoals.head.succ shouldBe empty
  }

  it should "locate the first applicable formula after start in antecedent" in {
    val result = proveBy(
      Sequent(immutable.IndexedSeq("a=2".asFormula, "x>0 & y>0".asFormula, "b=3 & c=4".asFormula), immutable.IndexedSeq()),
      TactixLibrary.andL(Find(0, None, AntePosition(3)))
    )
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("a=2".asFormula, "x>0 & y>0".asFormula, "b=3".asFormula, "c=4".asFormula)
    result.subgoals.head.succ shouldBe empty
  }

  it should "locate the first applicable formula of a specific shape" in {
    val result = proveBy(
      Sequent(immutable.IndexedSeq("a=2".asFormula, "x>0 & y>0".asFormula, "b=3 & c=4".asFormula), immutable.IndexedSeq()),
      TactixLibrary.andL(Find(0, Some("b=3 & c=4".asFormula), AntePosition(1)))
    )
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("a=2".asFormula, "x>0 & y>0".asFormula, "b=3".asFormula, "c=4".asFormula)
    result.subgoals.head.succ shouldBe empty
  }

  it should "throw an exception if no applicable position can be found" in {
    val e = intercept[BelleError] { proveBy(
      Sequent(immutable.IndexedSeq("a=2".asFormula, "x>0 | y>0".asFormula), immutable.IndexedSeq()),
      TactixLibrary.andL('L)
    )}
    e.getMessage should include ("Position tactic andL is not applicable at -1")
    e.getMessage should include ("Position tactic andL is not applicable at -2")
  }

  it should "work with dependent position tactics" in {
    val result = proveBy(
      Sequent(immutable.IndexedSeq("x>0 & y>0".asFormula), immutable.IndexedSeq()),
      TactixLibrary.step('L)
    )
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x>0".asFormula, "y>0".asFormula)
    result.subgoals.head.succ shouldBe empty
  }

  "'R" should "locate the sole applicable formula in succedent" in {
    val result = proveBy(
      Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("x>0 | y>0".asFormula)),
      TactixLibrary.orR('R)
    )
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only ("x>0".asFormula, "y>0".asFormula)
  }

  it should "locate the first applicable formula in antecedent" in {
    val result = proveBy(
      Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("a=2".asFormula, "x>0 | y>0".asFormula, "b=3 | c=4".asFormula)),
      TactixLibrary.orR('R)
    )
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only ("a=2".asFormula, "x>0".asFormula, "y>0".asFormula, "b=3 | c=4".asFormula)
  }

  it should "throw an exception if no applicable position can be found" in {
    val e = intercept[BelleError] { proveBy(
      Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("a=2".asFormula, "x>0 & y>0".asFormula)),
      TactixLibrary.orR('R)
    )}
    e.getMessage should include ("Position tactic orR is not applicable at 1")
    e.getMessage should include ("Position tactic orR is not applicable at 2")
  }

  it should "work with dependent position tactics" in {
    val result = proveBy(
      Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("[?x>0;]x>0".asFormula)),
      TactixLibrary.step('R)
    )
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "x>0 -> x>0".asFormula
  }

  "'_" should "locate the sole applicable formula in sequent" in {
    val result = proveBy(
      Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("x>0 | y>0".asFormula)),
      TactixLibrary.orR('_)
    )
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only ("x>0".asFormula, "y>0".asFormula)
  }

  it should "locate the first applicable formula" in {
    val result = proveBy(
      Sequent(immutable.IndexedSeq("a=2".asFormula, "x>0 & y>0".asFormula, "b=3 & c=4".asFormula), immutable.IndexedSeq()),
      TactixLibrary.andL('_)
    )
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("a=2".asFormula, "x>0".asFormula, "y>0".asFormula, "b=3 & c=4".asFormula)
    result.subgoals.head.succ shouldBe empty
  }

  it should "throw an exception if no applicable position can be found" in {
    val e = intercept[BelleError] { proveBy(
      Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("a=2".asFormula, "x>0 & y>0".asFormula)),
      TactixLibrary.orR('_)
    )}
    e.getMessage should include ("Position tactic orR is not applicable at 1")
    e.getMessage should include ("Position tactic orR is not applicable at 2")
  }

  "'Llast" should "apply on last formula in antecedent" in {
    val result = proveBy(
      Sequent(immutable.IndexedSeq("a=2".asFormula, "x>0 & y>0".asFormula, "b=3 & c=4".asFormula), immutable.IndexedSeq()),
      TactixLibrary.andL('Llast)
    )
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("a=2".asFormula, "x>0 & y>0".asFormula, "b=3".asFormula, "c=4".asFormula)
    result.subgoals.head.succ shouldBe empty
  }

}
