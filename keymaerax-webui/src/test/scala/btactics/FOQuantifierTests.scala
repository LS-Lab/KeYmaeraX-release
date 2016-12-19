package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{Position, BelleThrowable, PosInExpr}
import edu.cmu.cs.ls.keymaerax.btactics.FOQuantifierTactics._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, UsualTest}

import scala.collection.immutable.IndexedSeq

/**
 * Tests [[edu.cmu.cs.ls.keymaerax.btactics.FOQuantifierTactics]].
 */
@SummaryTest
@UsualTest
class FOQuantifierTests extends TacticTestBase {
  "allL" should "instantiate simple predicate" in {
    val tactic = allInstantiate(Some("x".asVariable), Some("z".asTerm))(-1)
    val result = proveBy(Sequent(IndexedSeq("\\forall x x>0".asFormula), IndexedSeq()), tactic)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "z>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "instantiate simple predicate with the quantified variable itself" in {
    val tactic = allInstantiate(Some("x".asVariable), None)(-1)
    val result = proveBy(Sequent(IndexedSeq("\\forall x x>0".asFormula), IndexedSeq()), tactic)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "instantiate the first variable if none is specified" in {
    val result = proveBy(
      Sequent(IndexedSeq("\\forall x x>0".asFormula), IndexedSeq()),
      allInstantiate(None, Some("z".asTerm))(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "z>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "instantiate the first variable with itself if none is specified" in {
    val result = proveBy(
      Sequent(IndexedSeq("\\forall x x>0".asFormula), IndexedSeq()),
      allInstantiate(None, None)(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "rename when instantiating simple predicate" in {
    val result = proveBy(
      Sequent(IndexedSeq("\\forall y y>0".asFormula), IndexedSeq()),
      allInstantiate(Some("y".asVariable), Some("z".asTerm))(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "z>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "instantiate with a universal quantifier following" in {
    {
      val result = proveBy(
        Sequent(IndexedSeq("\\forall z \\forall y y>z".asFormula), IndexedSeq()),
        allInstantiate()(-1))
      result.subgoals should have size 1
      result.subgoals.head.ante should contain only "\\forall y y>z".asFormula
      result.subgoals.head.succ shouldBe empty
    }
    {
      val result = proveBy(
        Sequent(IndexedSeq("\\forall x \\forall y y>x".asFormula), IndexedSeq()),
        allInstantiate(Some("x".asVariable), Some("z".asTerm))(-1))
      result.subgoals should have size 1
      result.subgoals.head.ante should contain only "\\forall y y>z".asFormula
      result.subgoals.head.succ shouldBe empty
    }
  }

  it should "instantiate assignment modality" in {
    val result = proveBy(
      Sequent(IndexedSeq("\\forall x [y:=x;][y:=2;]y>0".asFormula), IndexedSeq()),
      allInstantiate(Some("x".asVariable), Some("z".asTerm))(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "[y:=z;][y:=2;]y>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "instantiate assignment modality 2" in {
    val result = proveBy(
      Sequent(IndexedSeq("\\forall y [y:=y+1;]y>0".asFormula), IndexedSeq()),
      allInstantiate(Some("y".asVariable), Some("z+1".asTerm))(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "[y:=z+1+1;]y>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "instantiate free ODE modality" in {
    val result = proveBy(
      Sequent(IndexedSeq("\\forall x [{y'=x}]y>0".asFormula), IndexedSeq()),
      allInstantiate(Some("x".asVariable), Some("z".asTerm))(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "[{y'=z}]y>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "diffWeaken simple" in {
    val result = proveBy("[{x'=5&x<7}]x<7".asFormula,
      diffWeaken(1) & prop)
    println(result)
    result shouldBe 'proved
  }

  it should "diffWeaken ouch" in withMathematica { qeTool =>
    val result = proveBy("[{x'=1}][{x'=2&x>0}]x>0".asFormula,
      diffWeaken(1) & implyR(1) & diffWeaken(1) & prop)
    println(result)
    result shouldBe 'proved
  }

  it should "diffWeaken before loopy" in withMathematica { qeTool =>
    val result = proveBy("[{x'=1&x>0}][{x:=2;}*]x>0".asFormula,
      diffWeaken(1) & implyR(1) & loop("x>0".asFormula)(1) & master())
    println(result)
    result shouldBe 'proved
  }

  it should "diffWeaken before semibound" in withMathematica { qeTool =>
    val result = proveBy("[{x'=1&x>0}][{x:=2;++y:=2;}]x>0".asFormula,
      diffWeaken(1) & master())
    println(result)
    result shouldBe 'proved
  }

  it should "instantiate free ODE modality whatever the names" in {
    val result = proveBy(
      Sequent(IndexedSeq("\\forall u [{v'=u}]v>0".asFormula), IndexedSeq()),
      allInstantiate(Some("u".asVariable), Some("z".asTerm))(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "[{v'=z}]v>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "instantiate bound ODE modality" in {
    val result = proveBy(
      Sequent(IndexedSeq("\\forall x [{x'=5}]x>=0".asFormula), IndexedSeq()),
      allInstantiate(Some("x".asVariable), Some("z".asTerm))(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "\\forall x (x=z -> [{x'=5}]x>=0)".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "instantiate bound ODE modality whatever the names" in {
    val result = proveBy(
      Sequent(IndexedSeq("\\forall y [{y'=5}]y>=0".asFormula), IndexedSeq()),
      allInstantiate(Some("y".asVariable), Some("z".asTerm))(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "\\forall y (y=z -> [{y'=5}]y>=0)".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "instantiate more complicated ODE modality" in {
    val result = proveBy(
      Sequent(IndexedSeq("\\forall y [{y'=x & y>2}]y>0".asFormula), IndexedSeq()),
      allInstantiate(Some("y".asVariable), Some("z".asTerm))(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "\\forall y (y=z -> [{y'=x & y>2}]y>0)".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "instantiate even if ODE modality follows in some subformula" in {
    val result = proveBy(
      Sequent(IndexedSeq("\\forall y (y=0 -> [{y'=x & y>2}]y>0)".asFormula), IndexedSeq()),
      allInstantiate(Some("y".asVariable), Some("z".asTerm))(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "\\forall y (y=z -> y=0 -> [{y'=x & y>2}]y>0)".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "instantiate assignment irrespective of what follows" in {
    val result = proveBy(
      Sequent(IndexedSeq("\\forall x [y:=x;][{y'=1}]y>0".asFormula), IndexedSeq()),
      allInstantiate(Some("x".asVariable), Some("z".asTerm))(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "[y:=z;][{y'=1}]y>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "instantiate in context" in {
    val result = proveBy(
      Sequent(IndexedSeq("b>2 & [a:=2;]!!\\forall x [y:=x;][{y'=1}]y>0".asFormula), IndexedSeq()),
      allInstantiate(Some("x".asVariable), Some("z".asTerm))(-1, 1::1::0::0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "b>2 & [a:=2;]!![y:=z;][{y'=1}]y>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "instantiate in succedent when in simple negative polarity" in {
    val result = proveBy(
      Sequent(IndexedSeq(), IndexedSeq("!(\\forall x [y:=x;][{y'=1}]y>0)".asFormula)),
      allInstantiate(Some("x".asVariable), Some("z".asTerm))(1, 0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "![y:=z;][{y'=1}]y>0".asFormula
  }

  it should "instantiate in succedent when in negative polarity" in {
    val result = proveBy(
      Sequent(IndexedSeq(), IndexedSeq("a=2 -> !(\\forall x [y:=x;][{y'=1}]y>0)".asFormula)),
      allInstantiate(Some("x".asVariable), Some("z".asTerm))(1, 1::0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "a=2 -> ![y:=z;][{y'=1}]y>0".asFormula
  }

  it should "instantiate by position" in {
    val result = proveBy(Sequent(IndexedSeq("\\forall x x>0".asFormula, "y>0".asFormula), IndexedSeq()),
      allLPos(Position(-2, 0::Nil))(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "y>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "instantiate ODE" ignore {
    val result = proveBy(Sequent(IndexedSeq("\\forall t_ [{x'=2,t_'=1&true}]x>b".asFormula), IndexedSeq()),
      allInstantiate(None, Some("0".asTerm))(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "t_=0->[{x'=2,t_'=1&true}]x>b".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  "existsR" should "instantiate simple formula" in {
    val result = proveBy(
      Sequent(IndexedSeq(), IndexedSeq("\\exists x x>0".asFormula)),
      existsInstantiate(Some("x".asVariable), Some("z".asTerm))(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "z>0".asFormula
  }

  it should "instantiate in context" in {
    val result = proveBy(
      Sequent(IndexedSeq(), IndexedSeq("a=2 & \\exists x x>0".asFormula)),
      existsInstantiate(Some("x".asVariable), Some("z".asTerm))(1, 1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "a=2 & z>0".asFormula
  }

  it should "instantiate in antecedent when in negative polarity" in {
    val result = proveBy(
      Sequent(IndexedSeq("a=2 -> !\\exists x x>0".asFormula), IndexedSeq()),
      existsInstantiate(Some("x".asVariable), Some("z".asTerm))(-1, 1::0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "a=2 -> !z>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "instantiate variables bound in an ODE" in {
    val result = proveBy(
      Sequent(IndexedSeq(), IndexedSeq("\\exists y [{x'=2,y'=0*y+1&true}]x>0".asFormula)),
      existsInstantiate()(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{x'=2,y'=0*y+1&true}]x>0".asFormula
  }

  it should "instantiate ODE" in {
    val result = proveBy("\\exists t_ (t_=0&![{x'=2,t_'=1&true}]x>b)".asFormula,
      existsInstantiate(None, Some("0".asTerm))(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "t_=0".asFormula
    result.subgoals.head.succ should contain only "t_=0&![{x'=2,t_'=1&true}]x>b".asFormula
  }

  "exists generalize" should "only generalize the specified occurrences of t" in {
    val result = proveBy(Sequent(IndexedSeq("a+b=a+b".asFormula), IndexedSeq()),
      existsGeneralize(Variable("z"), PosInExpr(0 :: Nil) :: Nil)(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "\\exists z z=a+b".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "generalize all the specified occurrences of t" in {
    val result = proveBy(Sequent(IndexedSeq("a+b=a+b".asFormula), IndexedSeq()),
      existsGeneralize(Variable("z"), PosInExpr(0 :: Nil) :: PosInExpr(1:: Nil) :: Nil)(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "\\exists z z=z".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "reject positions that refer to different terms" in {
    a [BelleThrowable] should be thrownBy proveBy(Sequent(IndexedSeq("a+b=a+c".asFormula), IndexedSeq()),
      existsGeneralize(Variable("z"), PosInExpr(0 :: Nil) :: PosInExpr(1:: Nil) :: Nil)(-1))
  }

  "all generalize" should "introduce a new universal quantifier" in {
    val result = proveBy("\\forall x x^2 >= -f()^2".asFormula,
      universalGen(Some(Variable("z")), FuncOf(Function("f", None, Unit, Real), Nothing))(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\forall z \\forall x x^2 >= -z^2".asFormula
  }

  it should "introduce a new universal quantifier in context" in {
    val result = proveBy("a=2 -> [x:=3;]\\forall x x^2 >= -f()^2".asFormula,
      universalGen(Some(Variable("z")), FuncOf(Function("f", None, Unit, Real), Nothing))(1, 1::1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "a=2 -> [x:=3;]\\forall z \\forall x x^2 >= -z^2".asFormula
  }

  it should "introduce a new universal quantifier in context before an ODE" in {
    val result = proveBy("a=2 -> [x:=3;][{x'=5}]x>0".asFormula,
      universalGen(Some(Variable("x")), Variable("x"))(1, 1::1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "a=2 -> [x:=3;]\\forall x [{x'=5}]x>0".asFormula
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
    a [BelleThrowable] should be thrownBy proveBy("a>0 & x>5 & y<2".asFormula, universalClosure(Variable("b")::Nil)(1))
  }

//  "Exists eliminate" should "instantiate example from axiomatic ODE solver" in {
//    val tactic = HilbertCalculus.useAt("exists eliminate", (us:Subst) => {RenUSubst(scala.collection.immutable.Seq(("x_".asVariable, "t".asVariable)))})(1)
//    val result = proveBy("\\exists t [{x'=v,v'=a, t'=1}]x>0".asFormula, tactic)
//  }

  "all skolemize" should "skolemize simple" in {
    val result = proveBy("\\forall x x>0".asFormula, allSkolemize(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "x>0".asFormula
  }

  it should "skolemize simple at any succedent position" in {
    val s = Sequent(IndexedSeq(), IndexedSeq("y>0".asFormula, "\\forall x x>0".asFormula))
    val result = proveBy(s, allSkolemize(2))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only ("y>0".asFormula, "x>0".asFormula)
  }

  it should "skolemize simple at any succedent position with position locator" in {
    val s = Sequent(IndexedSeq(), IndexedSeq("y>0".asFormula, "\\forall x x>0".asFormula))
    val result = proveBy(s, allSkolemize('R))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only ("y>0".asFormula, "x>0".asFormula)
  }

  it should "skolemize with boundrenaming when variable to skolemize is there already" in {
    val result = proveBy(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("\\forall x x>0".asFormula)), allSkolemize(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x_0>0".asFormula
    result.subgoals.head.succ should contain only "x>0".asFormula
  }

  it should "not rename variables bound somewhere else" in {
    val result = proveBy(Sequent(IndexedSeq("\\forall x x>0".asFormula, "\\exists x x=1".asFormula), IndexedSeq("\\forall x x>0".asFormula, "<x:=2;>x=2".asFormula)), allSkolemize(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("\\forall x x>0".asFormula, "\\exists x x=1".asFormula)
    result.subgoals.head.succ should contain only ("x>0".asFormula, "<x:=2;>x=2".asFormula)
  }

  it should "not rename variables bound somewhere else if not top-level" in {
    val result = proveBy(Sequent(IndexedSeq("x>0 & \\forall x x>0".asFormula), IndexedSeq("\\forall x x>0".asFormula)), allSkolemize(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x_0>0 & \\forall x x>0".asFormula
    result.subgoals.head.succ should contain only "x>0".asFormula
  }

  it should "not rename variables bound somewhere else if not top-level 2" in {
    val result = proveBy(Sequent(IndexedSeq("x>0 & (\\forall x x>0 | \\forall x x<0)".asFormula), IndexedSeq("\\forall x x>0".asFormula)), allSkolemize(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x_0>0 & (\\forall x x>0 | \\forall x x<0)".asFormula
    result.subgoals.head.succ should contain only "x>0".asFormula
  }

  it should "not rename variables bound somewhere else if not top-level 3" in {
    val result = proveBy(Sequent(IndexedSeq("x>0 & (\\forall y \\forall x x>0 | \\forall y \\forall x x<0)".asFormula), IndexedSeq("\\forall x x>0".asFormula)), allSkolemize(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x_0>0 & (\\forall y \\forall x x>0 | \\forall y \\forall x x<0)".asFormula
    result.subgoals.head.succ should contain only "x>0".asFormula
  }

  it should "not rename variables bound somewhere else if not top-level 4" in {
    val result = proveBy(Sequent(IndexedSeq("x>0 & (\\forall x \\forall x x>0 | \\forall x \\forall x x<0)".asFormula), IndexedSeq("\\forall x x>0".asFormula)), allSkolemize(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x_0>0 & (\\forall x \\forall x x>0 | \\forall x \\forall x x<0)".asFormula
    result.subgoals.head.succ should contain only "x>0".asFormula
  }

  it should "not rename bound inside formula" in {
    val result = proveBy("\\forall a (a>0 | \\forall a a<0)".asFormula, allSkolemize(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "a>0 | \\forall a a<0".asFormula
  }

  it should "not rename bound inside formula 2" in {
    val result = proveBy("\\forall a (a>0 -> [a:=a+1;]a>0)".asFormula, allSkolemize(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "a>0 -> [a:=a+1;]a>0".asFormula
  }

  "exists skolemize" should "skolemize simple" in {
    val result = proveBy(Sequent(IndexedSeq("\\exists x x>0".asFormula), IndexedSeq()), existsSkolemize(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "skolemize with boundrenaming when variable to skolemize is there already" in {
    val result = proveBy(Sequent(IndexedSeq("x>0".asFormula, "\\exists x x>0".asFormula), IndexedSeq()), existsSkolemize(-2))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x_0>0".asFormula, "x>0".asFormula)
    result.subgoals.head.succ shouldBe empty
  }

  "quantifier rules" should "not prove false \\forall x \\exists y p(x,y) -> \\exists y \\forall x p(x,y)" in {
    val result = proveBy("\\forall x \\exists y p(x,y) -> \\exists y \\forall x p(x,y)".asFormula,
      implyR(1) & existsR(1) & allL(-1) & allR(1) & existsL(-1) & (close | skip)
    )
    result should not be 'proved
    result.isProved shouldBe false
  }

  it should "not prove false \\forall x \\exists y p(x,y) -> \\exists y \\forall x p(x,y) with insts" in {
    val result = proveBy("\\forall x \\exists y p(x,y) -> \\exists y \\forall x p(x,y)".asFormula,
      implyR(1) & existsR(Variable("y"),Variable("y"))(1) & allL(Variable("x"),Variable("x"))(-1) & allR(1) & existsL(-1) & (close | skip)
    )
    result should not be 'proved
    result.isProved shouldBe false
  }

  it should "not prove false \\forall x \\exists y p(x,y) -> \\exists y \\forall x p(x,y) with vars" in {
    val result = proveBy("\\forall x \\exists y p(x,y) -> \\exists y \\forall x p(x,y)".asFormula,
      implyR(1) & existsR(Variable("y"))(1) & allL(Variable("x"))(-1) & allR(1) & existsL(-1) & (close | skip)
    )
    result should not be 'proved
    result.isProved shouldBe false
  }

  it should "fail to instantiate non-existent quantified variables" in {
    val result = proveBy(" (\\forall x q(x)) -> \\exists y q(y) ".asFormula,
      implyR(1) & (allL(Variable("z"),Variable("y"))(-1) | nil)
        & (existsR(Variable("z"),Variable("x"))(1) | nil)
        & (close | skip))

    result should not be 'proved
    result.isProved shouldBe false
  }
}
