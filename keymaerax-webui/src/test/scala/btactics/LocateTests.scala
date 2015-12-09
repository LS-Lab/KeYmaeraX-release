package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleError
import edu.cmu.cs.ls.keymaerax.btactics.{FindAnte, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.core.Sequent
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.{AntePosition}

import scala.collection.immutable

/**
 * Tests
 * [[edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.la]]
 */
class LocateTests extends TacticTestBase {

  "la" should "locate the sole applicable formula in antecedent" in {
    val result = proveBy(
      Sequent(Nil, immutable.IndexedSeq("x>0 & y>0".asFormula), immutable.IndexedSeq()),
      TactixLibrary.andL('L)
    )
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x>0".asFormula, "y>0".asFormula)
    result.subgoals.head.succ shouldBe empty
  }

  it should "locate the first applicable formula in antecedent" in {
    val result = proveBy(
      Sequent(Nil, immutable.IndexedSeq("a=2".asFormula, "x>0 & y>0".asFormula, "b=3 & c=4".asFormula), immutable.IndexedSeq()),
      TactixLibrary.andL('L)
    )
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("a=2".asFormula, "x>0".asFormula, "y>0".asFormula, "b=3 & c=4".asFormula)
    result.subgoals.head.succ shouldBe empty
  }

  it should "locate the first applicable formula after start in antecedent" in {
    val result = proveBy(
      Sequent(Nil, immutable.IndexedSeq("a=2".asFormula, "x>0 & y>0".asFormula, "b=3 & c=4".asFormula), immutable.IndexedSeq()),
      TactixLibrary.andL(FindAnte(0, None, new AntePosition(2)))
    )
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("a=2".asFormula, "x>0 & y>0".asFormula, "b=3".asFormula, "c=4".asFormula)
    result.subgoals.head.succ shouldBe empty
  }

  it should "locate the first applicable formula of a specific shape" in {
    val result = proveBy(
      Sequent(Nil, immutable.IndexedSeq("a=2".asFormula, "x>0 & y>0".asFormula, "b=3 & c=4".asFormula), immutable.IndexedSeq()),
      TactixLibrary.andL(FindAnte(0, Some("b_=3 & c_=4".asFormula), new AntePosition(0)))
    )
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("a=2".asFormula, "x>0 & y>0".asFormula, "b=3".asFormula, "c=4".asFormula)
    result.subgoals.head.succ shouldBe empty
  }

  it should "throw an exception if no applicable position can be found" in {
    val e = intercept[BelleError] { proveBy(
      Sequent(Nil, immutable.IndexedSeq("a=2".asFormula, "x>0 | y>0".asFormula), immutable.IndexedSeq()),
      TactixLibrary.andL('L)
    )}
    e.getMessage should include ("Position tactic AndL is not applicable at -1")
    e.getMessage should include ("Position tactic AndL is not applicable at -2")
  }

  "ls" should "locate the sole applicable formula in succedent" in {
    val result = proveBy(
      Sequent(Nil, immutable.IndexedSeq(), immutable.IndexedSeq("x>0 | y>0".asFormula)),
      TactixLibrary.orR('R)
    )
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only ("x>0".asFormula, "y>0".asFormula)
  }

  it should "locate the first applicable formula in antecedent" in {
    val result = proveBy(
      Sequent(Nil, immutable.IndexedSeq(), immutable.IndexedSeq("a=2".asFormula, "x>0 | y>0".asFormula, "b=3 | c=4".asFormula)),
      TactixLibrary.orR('R)
    )
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only ("a=2".asFormula, "x>0".asFormula, "y>0".asFormula, "b=3 | c=4".asFormula)
  }

  it should "throw an exception if no applicable position can be found" in {
    val e = intercept[BelleError] { proveBy(
      Sequent(Nil, immutable.IndexedSeq(), immutable.IndexedSeq("a=2".asFormula, "x>0 & y>0".asFormula)),
      TactixLibrary.orR('R)
    )}
    e.getMessage should include ("Position tactic OrR is not applicable at 1")
    e.getMessage should include ("Position tactic OrR is not applicable at 2")
  }

}
