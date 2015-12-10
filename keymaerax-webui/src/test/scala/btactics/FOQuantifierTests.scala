package btactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, UsualTest}

import edu.cmu.cs.ls.keymaerax.btactics.FOQuantifierTactics.{allL, existsR}

import scala.collection.immutable

/**
 * Tests [[edu.cmu.cs.ls.keymaerax.btactics.FOQuantifierTactics]].
 */
@SummaryTest
@UsualTest
class FOQuantifierTests extends TacticTestBase {
  "allL" should "instantiate simple predicate" in {
    val tactic = allL(Some("x".asVariable), "z".asTerm)(-1)
    val result = proveBy(Sequent(Nil, immutable.IndexedSeq("\\forall x x>0".asFormula), immutable.IndexedSeq()), tactic)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "z>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "instantiate the first variable if none is specified" in {
    val result = proveBy(
      Sequent(Nil, immutable.IndexedSeq("\\forall x x>0".asFormula), immutable.IndexedSeq()),
      allL(None, "z".asTerm)(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "z>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "rename when instantiating simple predicate" in {
    val result = proveBy(
      Sequent(Nil, immutable.IndexedSeq("\\forall y y>0".asFormula), immutable.IndexedSeq()),
      allL(Some("y".asVariable), "z".asTerm)(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "z>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "instantiate assignment modality" in {
    val result = proveBy(
      Sequent(Nil, immutable.IndexedSeq("\\forall x [y:=x;][y:=2;]y>0".asFormula), immutable.IndexedSeq()),
      allL(Some("x".asVariable), "z".asTerm)(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "[y:=z;][y:=2;]y>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  //@todo not supported yet (but was supported in non-sequential version)
  ignore should "instantiate assignment modality 2" in {
    val result = proveBy(
      Sequent(Nil, immutable.IndexedSeq("\\forall y [y:=y+1;]y>0".asFormula), immutable.IndexedSeq()),
      allL(Some("y".asVariable), "z".asTerm)(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "[y:=z+1+1;]y>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "instantiate ODE modality" in {
    val result = proveBy(
      Sequent(Nil, immutable.IndexedSeq("\\forall x [{y'=x}]y>0".asFormula), immutable.IndexedSeq()),
      allL(Some("x".asVariable), "z".asTerm)(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "[{y'=z}]y>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  //@todo not supported yet (but was supported in non-sequential version)
  ignore should "instantiate more complicated ODE modality" in {
    val result = proveBy(
      Sequent(Nil, immutable.IndexedSeq("\\forall y [{y'=x & y>2}]y>0".asFormula), immutable.IndexedSeq()),
      allL(Some("y".asVariable), "z".asTerm)(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "[{z'=x & z>2}]z>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  //@todo not supported yet (but was supported in non-sequential version)
  ignore should "instantiate even if ODE modality follows in some subformula" in {
    val result = proveBy(
      Sequent(Nil, immutable.IndexedSeq("\\forall y (y=0 -> [{y'=x & y>2}]y>0)".asFormula), immutable.IndexedSeq()),
      allL(Some("y".asVariable), "z".asTerm)(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "z=0 -> [{z'=x & z>2}]z>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "instantiate assignment irrespective of what follows" in {
    val result = proveBy(
      Sequent(Nil, immutable.IndexedSeq("\\forall x [y:=x;][{y'=1}]y>0".asFormula), immutable.IndexedSeq()),
      allL(Some("x".asVariable), "z".asTerm)(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "[y:=z;][{y'=1}]y>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  "existsR" should "instantiate simple formula" in {
    val result = proveBy(
      Sequent(Nil, immutable.IndexedSeq(), immutable.IndexedSeq("\\exists x x>0".asFormula)),
      existsR(Some("x".asVariable), "z".asTerm)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "z>0".asFormula
  }
}
