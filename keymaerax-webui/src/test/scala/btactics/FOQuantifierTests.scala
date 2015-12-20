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

  it should "instantiate with a universal quantifier following" in {
    {
      val result = proveBy(
        Sequent(Nil, IndexedSeq("\\forall z \\forall y y>z".asFormula), IndexedSeq()),
        allInstantiate()(-1))
      result.subgoals should have size 1
      result.subgoals.head.ante should contain only "\\forall y y>z".asFormula
      result.subgoals.head.succ shouldBe empty
    }
    {
      val result = proveBy(
        Sequent(Nil, IndexedSeq("\\forall x \\forall y y>x".asFormula), IndexedSeq()),
        allInstantiate(Some("x".asVariable), Some("z".asTerm))(-1))
      result.subgoals should have size 1
      result.subgoals.head.ante should contain only "\\forall y y>z".asFormula
      result.subgoals.head.succ shouldBe empty
    }
  }

  it should "instantiate assignment modality" in {
    val result = proveBy(
      Sequent(Nil, IndexedSeq("\\forall x [y:=x;][y:=2;]y>0".asFormula), IndexedSeq()),
      allInstantiate(Some("x".asVariable), Some("z".asTerm))(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "[y:=z;][y:=2;]y>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "instantiate assignment modality 2" in {
    val result = proveBy(
      Sequent(Nil, IndexedSeq("\\forall y [y:=y+1;]y>0".asFormula), IndexedSeq()),
      allInstantiate(Some("y".asVariable), Some("z+1".asTerm))(-1))
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

  "all generalize" should "introduce a new universal quantifier" in {
    val result = proveBy("\\forall x x^2 >= -f()^2".asFormula,
      universalGen(Some(Variable("z")), FuncOf(Function("f", None, Unit, Real), Nothing))(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\forall z \\forall x x^2 >= -z^2".asFormula
  }

  it should "generalize terms" in {
    val result = proveBy("\\forall x x^2 >= -(y+5)^2".asFormula, universalGen(Some(Variable("z")), "y+5".asTerm)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\forall z \\forall x x^2 >= -z^2".asFormula
  }

  it should "generalize only free occurrences" in {
    val result = proveBy("(\\forall x x>5) & x<2".asFormula, universalGen(Some(Variable("z")), "x".asTerm)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\forall z ((\\forall x x>5) & z<2)".asFormula
  }

  it should "pick a name when generalizing only free occurrences" in {
    val result = proveBy("(\\forall x x>5) & x<2".asFormula, universalGen(None, "x".asTerm)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\forall x_0 ((\\forall x x>5) & x_0<2)".asFormula
  }

  "Universal closure" should "work for simple formula" in {
    val result = proveBy("x>5".asFormula, universalClosure(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\forall x_0 x_0>5".asFormula
  }

  it should "work when indexed names are already there" in {
    val result = proveBy("x_0>0 & x_1>1 & x_2>2".asFormula, universalClosure(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\forall x_5 \\forall x_4 \\forall x_3 (x_3>0 & x_4>1 & x_5>2)".asFormula
  }

  it should "compute closure for formulas with variables and parameterless function symbols" in {
    val result = proveBy("x>5 & f()<2 & y+3>z".asFormula, universalClosure(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\forall z_0 \\forall y_0 \\forall x_0 \\forall f_0 (x_0>5 & f_0<2 & y_0+3>z_0)".asFormula
  }

  it should "ignore bound variables in closure" in {
    val result = proveBy("\\forall x \\forall y (x>5 & f()<2 & y+3>z)".asFormula, universalClosure(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\forall z_0 \\forall f_0 (\\forall x \\forall y (x>5 & f_0<2 & y+3>z_0))".asFormula
  }

  it should "not ignore variables that are not bound everywhere" in {
    val result = proveBy("(\\forall x x>5) & x<2".asFormula, universalClosure(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\forall x_0 ((\\forall x x>5) & x_0<2)".asFormula
  }

  it should "not do anything if all variables are bound" in {
    val result = proveBy("\\forall x x>5".asFormula, universalClosure(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\forall x x>5".asFormula
  }

  it should "use the provided order of symbols" in {
    val result = proveBy("a>0 & x>5 & y<2".asFormula, universalClosure(Variable("x")::Variable("a")::Variable("y")::Nil)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\forall x_0 \\forall a_0 \\forall y_0 (a_0>0 & x_0>5 & y_0<2)".asFormula
  }

  it should "append non-mentioned symbols in reverse alphabetical order" in {
    val result = proveBy("a>0 & x>5 & y<2".asFormula, universalClosure(Variable("x")::Nil)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\forall x_0 \\forall y_0 \\forall a_0 (a_0>0 & x_0>5 & y_0<2)".asFormula
  }

  it should "not be applicable when the order is not a subset of the free variables plus signature" in {
    a [BelleError] should be thrownBy proveBy("a>0 & x>5 & y<2".asFormula, universalClosure(Variable("b")::Nil)(1))
  }
}
