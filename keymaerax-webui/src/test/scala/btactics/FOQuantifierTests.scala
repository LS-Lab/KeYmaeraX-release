package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleError
import edu.cmu.cs.ls.keymaerax.btactics.FOQuantifierTactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, UsualTest}
import edu.cmu.cs.ls.keymaerax.tactics.PosInExpr

import scala.collection.immutable.IndexedSeq

/**
 * Tests [[edu.cmu.cs.ls.keymaerax.btactics.FOQuantifierTactics]].
 */
@SummaryTest
@UsualTest
class FOQuantifierTests extends TacticTestBase {
  "allL" should "instantiate simple predicate" in {
    val tactic = allInstantiate(Some("x".asVariable), Some("z".asTerm))(-1)
    val result = proveBy(Sequent(Nil, IndexedSeq("\\forall x x>0".asFormula), IndexedSeq()), tactic)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "z>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "instantiate simple predicate with the quantified variable itself" in {
    val tactic = allInstantiate(Some("x".asVariable), None)(-1)
    val result = proveBy(Sequent(Nil, IndexedSeq("\\forall x x>0".asFormula), IndexedSeq()), tactic)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "instantiate the first variable if none is specified" in {
    val result = proveBy(
      Sequent(Nil, IndexedSeq("\\forall x x>0".asFormula), IndexedSeq()),
      allInstantiate(None, Some("z".asTerm))(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "z>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "instantiate the first variable with itself if none is specified" in {
    val result = proveBy(
      Sequent(Nil, IndexedSeq("\\forall x x>0".asFormula), IndexedSeq()),
      allInstantiate(None, None)(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "rename when instantiating simple predicate" in {
    val result = proveBy(
      Sequent(Nil, IndexedSeq("\\forall y y>0".asFormula), IndexedSeq()),
      allInstantiate(Some("y".asVariable), Some("z".asTerm))(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "z>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "instantiate assignment modality" in {
    val result = proveBy(
      Sequent(Nil, IndexedSeq("\\forall x [y:=x;][y:=2;]y>0".asFormula), IndexedSeq()),
      allInstantiate(Some("x".asVariable), Some("z".asTerm))(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "[y:=z;][y:=2;]y>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  //@todo not supported yet (but was supported in non-sequential version)
  ignore should "instantiate assignment modality 2" in {
    val result = proveBy(
      Sequent(Nil, IndexedSeq("\\forall y [y:=y+1;]y>0".asFormula), IndexedSeq()),
      allInstantiate(Some("y".asVariable), Some("z".asTerm))(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "[y:=z+1+1;]y>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "instantiate ODE modality" in {
    val result = proveBy(
      Sequent(Nil, IndexedSeq("\\forall x [{y'=x}]y>0".asFormula), IndexedSeq()),
      allInstantiate(Some("x".asVariable), Some("z".asTerm))(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "[{y'=z}]y>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  //@todo not supported yet (but was supported in non-sequential version)
  ignore should "instantiate more complicated ODE modality" in {
    val result = proveBy(
      Sequent(Nil, IndexedSeq("\\forall y [{y'=x & y>2}]y>0".asFormula), IndexedSeq()),
      allInstantiate(Some("y".asVariable), Some("z".asTerm))(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "[{z'=x & z>2}]z>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  //@todo not supported yet (but was supported in non-sequential version)
  ignore should "instantiate even if ODE modality follows in some subformula" in {
    val result = proveBy(
      Sequent(Nil, IndexedSeq("\\forall y (y=0 -> [{y'=x & y>2}]y>0)".asFormula), IndexedSeq()),
      allInstantiate(Some("y".asVariable), Some("z".asTerm))(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "z=0 -> [{z'=x & z>2}]z>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "instantiate assignment irrespective of what follows" in {
    val result = proveBy(
      Sequent(Nil, IndexedSeq("\\forall x [y:=x;][{y'=1}]y>0".asFormula), IndexedSeq()),
      allInstantiate(Some("x".asVariable), Some("z".asTerm))(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "[y:=z;][{y'=1}]y>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "instantiate in context" in {
    val result = proveBy(
      Sequent(Nil, IndexedSeq("b>2 & [a:=2;]!!\\forall x [y:=x;][{y'=1}]y>0".asFormula), IndexedSeq()),
      allInstantiate(Some("x".asVariable), Some("z".asTerm))(-1, 1::1::0::0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "b>2 & [a:=2;]!![y:=z;][{y'=1}]y>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "instantiate in succedent when in negative polarity" in {
    val result = proveBy(
      Sequent(Nil, IndexedSeq(), IndexedSeq("a=2 -> !(\\forall x [y:=x;][{y'=1}]y>0)".asFormula)),
      allInstantiate(Some("x".asVariable), Some("z".asTerm))(1, 1::0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "a=2 -> ![y:=z;][{y'=1}]y>0".asFormula
  }

  "existsR" should "instantiate simple formula" in {
    val result = proveBy(
      Sequent(Nil, IndexedSeq(), IndexedSeq("\\exists x x>0".asFormula)),
      existsInstantiate(Some("x".asVariable), Some("z".asTerm))(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "z>0".asFormula
  }

  it should "instantiate in context" in {
    val result = proveBy(
      Sequent(Nil, IndexedSeq(), IndexedSeq("a=2 & \\exists x x>0".asFormula)),
      existsInstantiate(Some("x".asVariable), Some("z".asTerm))(1, 1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "a=2 & z>0".asFormula
  }

  it should "instantiate in antecedent when in negative polarity" in {
    val result = proveBy(
      Sequent(Nil, IndexedSeq("a=2 -> !\\exists x x>0".asFormula), IndexedSeq()),
      existsInstantiate(Some("x".asVariable), Some("z".asTerm))(-1, 1::0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "a=2 -> !z>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  "exists generalize" should "only generalize the specified occurrences of t" in {
    val result = proveBy(Sequent(Nil, IndexedSeq("a+b=a+b".asFormula), IndexedSeq()),
      existsGeneralize(Variable("z"), PosInExpr(0 :: Nil) :: Nil)(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "\\exists z z=a+b".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "generalize all the specified occurrences of t" in {
    val result = proveBy(Sequent(Nil, IndexedSeq("a+b=a+b".asFormula), IndexedSeq()),
      existsGeneralize(Variable("z"), PosInExpr(0 :: Nil) :: PosInExpr(1:: Nil) :: Nil)(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "\\exists z z=z".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "reject positions that refer to different terms" in {
    a [BelleError] should be thrownBy proveBy(Sequent(Nil, IndexedSeq("a+b=a+c".asFormula), IndexedSeq()),
      existsGeneralize(Variable("z"), PosInExpr(0 :: Nil) :: PosInExpr(1:: Nil) :: Nil)(-1))
  }
}
