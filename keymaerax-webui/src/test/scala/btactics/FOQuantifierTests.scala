package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleThrowable
import edu.cmu.cs.ls.keymaerax.btactics.FOQuantifierTactics._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{PosInExpr, Position}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, UsualTest}

import scala.collection.immutable.IndexedSeq
import org.scalatest.LoneElement._
import testHelper.KeYmaeraXTestTags.TodoTest

/**
 * Tests [[edu.cmu.cs.ls.keymaerax.btactics.FOQuantifierTactics]].
 */
@SummaryTest
@UsualTest
class FOQuantifierTests extends TacticTestBase {
  "allL" should "instantiate simple predicate" in {
    val tactic = allInstantiate(Some("x".asVariable), Some("z".asTerm))(-1)
    val result = proveBy(Sequent(IndexedSeq("\\forall x x>0".asFormula), IndexedSeq()), tactic)
    result.subgoals.loneElement shouldBe "z>0 ==> ".asSequent
  }

  it should "instantiate simple predicate with the quantified variable itself" in {
    val tactic = allInstantiate(Some("x".asVariable), None)(-1)
    val result = proveBy(Sequent(IndexedSeq("\\forall x x>0".asFormula), IndexedSeq()), tactic)
    result.subgoals.loneElement shouldBe "x>0 ==> ".asSequent
  }

  it should "instantiate the first variable if none is specified" in {
    val result = proveBy(
      Sequent(IndexedSeq("\\forall x x>0".asFormula), IndexedSeq()),
      allInstantiate(None, Some("z".asTerm))(-1))
    result.subgoals.loneElement shouldBe "z>0 ==> ".asSequent
  }

  it should "instantiate the first variable with itself if none is specified" in {
    val result = proveBy(
      Sequent(IndexedSeq("\\forall x x>0".asFormula), IndexedSeq()),
      allInstantiate(None, None)(-1))
    result.subgoals.loneElement shouldBe "x>0 ==> ".asSequent
  }

  it should "rename when instantiating simple predicate" in {
    val result = proveBy(
      Sequent(IndexedSeq("\\forall y y>0".asFormula), IndexedSeq()),
      allInstantiate(Some("y".asVariable), Some("z".asTerm))(-1))
    result.subgoals.loneElement shouldBe "z>0 ==> ".asSequent
  }

  it should "instantiate with a universal quantifier following" in {
    {
      val result = proveBy(
        Sequent(IndexedSeq("\\forall z \\forall y y>z".asFormula), IndexedSeq()),
        allInstantiate(None, None)(-1))
      result.subgoals.loneElement shouldBe "\\forall y y>z ==> ".asSequent
    }
    {
      val result = proveBy(
        Sequent(IndexedSeq("\\forall x \\forall y y>x".asFormula), IndexedSeq()),
        allInstantiate(Some("x".asVariable), Some("z".asTerm))(-1))
      result.subgoals.loneElement shouldBe "\\forall y y>z ==> ".asSequent
    }
  }

  it should "instantiate assignment modality" in {
    val result = proveBy(
      Sequent(IndexedSeq("\\forall x [y:=x;][y:=2;]y>0".asFormula), IndexedSeq()),
      allInstantiate(Some("x".asVariable), Some("z".asTerm))(-1))
    result.subgoals.loneElement shouldBe "[y:=z;][y:=2;]y>0 ==> ".asSequent
  }

  it should "instantiate assignment modality 2" in {
    val result = proveBy(
      Sequent(IndexedSeq("\\forall y [y:=y+1;]y>0".asFormula), IndexedSeq()),
      allInstantiate(Some("y".asVariable), Some("z+1".asTerm))(-1))
    result.subgoals.loneElement shouldBe "[y:=z+1+1;]y>0 ==> ".asSequent
  }

  it should "instantiate free ODE modality" in {
    val result = proveBy(
      Sequent(IndexedSeq("\\forall x [{y'=x}]y>0".asFormula), IndexedSeq()),
      allInstantiate(Some("x".asVariable), Some("z".asTerm))(-1))
    result.subgoals.loneElement shouldBe "[{y'=z}]y>0 ==> ".asSequent
  }

  it should "diffWeaken simple" in {
    val result = proveBy("[{x'=5&x<7}]x<7".asFormula,
      dW(1) & prop)
    println(result)
    result shouldBe 'proved
  }

  it should "diffWeaken ouch" in withMathematica { _ =>
    val result = proveBy("[{x'=1}][{x'=2&x>0}]x>0".asFormula,
      dW(1) & implyR(1) & dW(1) & prop)
    println(result)
    result shouldBe 'proved
  }

  it should "diffWeaken before loopy" in withMathematica { _ =>
    val result = proveBy("[{x'=1&x>0}][{x:=2;}*]x>0".asFormula,
      dW(1) & implyR(1) & loop("x>0".asFormula)(1) & master())
    println(result)
    result shouldBe 'proved
  }

  it should "diffWeaken before semibound" in withMathematica { _ =>
    val result = proveBy("[{x'=1&x>0}][{x:=2;++y:=2;}]x>0".asFormula,
      dW(1) & master())
    println(result)
    result shouldBe 'proved
  }

  it should "instantiate free ODE modality whatever the names" in {
    val result = proveBy(
      Sequent(IndexedSeq("\\forall u [{v'=u}]v>0".asFormula), IndexedSeq()),
      allInstantiate(Some("u".asVariable), Some("z".asTerm))(-1))
    result.subgoals.loneElement shouldBe "[{v'=z}]v>0 ==> ".asSequent
  }

  it should "instantiate bound ODE modality" in {
    proveBy(
      Sequent(IndexedSeq("\\forall x [{x'=5}]x>=0".asFormula), IndexedSeq()),
      allInstantiate(Some("x".asVariable), Some("z".asTerm))(-1)).
      subgoals.loneElement shouldBe "[{z'=5}]z>=0 ==> ".asSequent

    proveBy(
      Sequent(IndexedSeq("\\forall x [{x'=z}]x>=0".asFormula), IndexedSeq()),
      allInstantiate(Some("x".asVariable), Some("z".asTerm))(-1)).
      subgoals.loneElement shouldBe "x=z, [{x'=z}]x>=0 ==> ".asSequent

    proveBy(
      Sequent(IndexedSeq("\\forall x [{x'=5}]x>=0".asFormula), IndexedSeq()),
      allInstantiate(Some("x".asVariable), Some("z+7".asTerm))(-1)).
      subgoals.loneElement shouldBe "x=z+7, [{x'=5}]x>=0 ==> ".asSequent
  }

  it should "instantiate bound ODE modality whatever the names" in {
    val result = proveBy(
      Sequent(IndexedSeq("\\forall y [{y'=5}]y>=0".asFormula), IndexedSeq()),
      allInstantiate(Some("y".asVariable), Some("z".asTerm))(-1))
    result.subgoals.loneElement shouldBe "[{z'=5}]z>=0 ==> ".asSequent
  }

  it should "instantiate more complicated ODE modality" in {
    proveBy(
      Sequent(IndexedSeq("\\forall y [{y'=x & y>2}]y>0".asFormula), IndexedSeq()),
      allInstantiate(Some("y".asVariable), Some("z".asTerm))(-1)).
      subgoals.loneElement shouldBe "[{z'=x & z>2}]z>0 ==> ".asSequent

    proveBy(
      Sequent(IndexedSeq("\\forall y [{y'=x & y>2}]y>0".asFormula), IndexedSeq()),
      allInstantiate(Some("y".asVariable), Some("z+7".asTerm))(-1)).
      subgoals.loneElement shouldBe "y=z+7, [{y'=x & y>2}]y>0 ==> ".asSequent
  }

  it should "instantiate even if ODE modality follows in some subformula" in {
    proveBy(
      Sequent(IndexedSeq("\\forall y (y=0 -> [{y'=x & y>2}]y>0)".asFormula), IndexedSeq()),
      allInstantiate(Some("y".asVariable), Some("z".asTerm))(-1)).
      subgoals.loneElement shouldBe "z=0 -> [{z'=x & z>2}]z>0 ==> ".asSequent

    proveBy(
      Sequent(IndexedSeq("\\forall y (y=0 -> [{y'=x & y>2}]y>0)".asFormula), IndexedSeq()),
      allInstantiate(Some("y".asVariable), Some("z+7".asTerm))(-1)).
      subgoals.loneElement shouldBe "y=z+7, y=0 -> [{y'=x & y>2}]y>0 ==> ".asSequent
  }

  it should "instantiate assignment irrespective of what follows" in {
    val result = proveBy(
      Sequent(IndexedSeq("\\forall x [y:=x;][{y'=1}]y>0".asFormula), IndexedSeq()),
      allInstantiate(Some("x".asVariable), Some("z".asTerm))(-1))
    result.subgoals.loneElement shouldBe "[y:=z;][{y'=1}]y>0 ==> ".asSequent
  }

  it should "instantiate in context" in {
    val result = proveBy(
      Sequent(IndexedSeq("b>2 & [a:=2;]!!\\forall x [y:=x;][{y'=1}]y>0".asFormula), IndexedSeq()),
      allInstantiate(Some("x".asVariable), Some("z".asTerm))(-1, 1::1::0::0::Nil))
    result.subgoals.loneElement shouldBe "b>2 & [a:=2;]!![y:=z;][{y'=1}]y>0 ==> ".asSequent
  }

  it should "instantiate in succedent when in simple negative polarity" in {
    val result = proveBy(
      Sequent(IndexedSeq(), IndexedSeq("!(\\forall x [y:=x;][{y'=1}]y>0)".asFormula)),
      allInstantiate(Some("x".asVariable), Some("z".asTerm))(1, 0::Nil))
    result.subgoals.loneElement shouldBe "==> ![y:=z;][{y'=1}]y>0".asSequent
  }

  it should "instantiate in succedent when in negative polarity" in {
    val result = proveBy(
      Sequent(IndexedSeq(), IndexedSeq("a=2 -> !(\\forall x [y:=x;][{y'=1}]y>0)".asFormula)),
      allInstantiate(Some("x".asVariable), Some("z".asTerm))(1, 1::0::Nil))
    result.subgoals.loneElement shouldBe "==> a=2 -> ![y:=z;][{y'=1}]y>0".asSequent
  }

  it should "instantiate by position" in {
    val result = proveBy(Sequent(IndexedSeq("\\forall x x>0".asFormula, "y>0".asFormula), IndexedSeq()),
      allLPos(Position(-2, 0::Nil))(-1))
    result.subgoals.loneElement shouldBe "y>0, y>0 ==> ".asSequent
  }

  it should "instantiate ODE" ignore {
    val result = proveBy(Sequent(IndexedSeq("\\forall t_ [{x'=2,t_'=1&true}]x>b".asFormula), IndexedSeq()),
      allInstantiate(None, Some("0".asTerm))(-1))
    result.subgoals.loneElement shouldBe "t_=0->[{x'=2,t_'=1&true}]x>b ==> ".asSequent
  }

  "existsR" should "instantiate simple formula" in {
    val result = proveBy(
      Sequent(IndexedSeq(), IndexedSeq("\\exists x x>0".asFormula)),
      existsInstantiate(Some("x".asVariable), Some("z".asTerm))(1))
    result.subgoals.loneElement shouldBe "==> z>0".asSequent
  }

  it should "instantiate in context" in {
    val result = proveBy(
      Sequent(IndexedSeq(), IndexedSeq("a=2 & \\exists x x>0".asFormula)),
      existsInstantiate(Some("x".asVariable), Some("z".asTerm))(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> a=2 & z>0".asSequent
  }

  it should "instantiate in antecedent when in negative polarity" in {
    val result = proveBy(
      Sequent(IndexedSeq("a=2 -> !\\exists x x>0".asFormula), IndexedSeq()),
      existsInstantiate(Some("x".asVariable), Some("z".asTerm))(-1, 1::0::Nil))
    result.subgoals.loneElement shouldBe "a=2 -> !z>0 ==> ".asSequent
  }

  it should "instantiate variables bound in an ODE" in {
    proveBy(
      Sequent(IndexedSeq(), IndexedSeq("\\exists y [{x'=2,y'=0*y+1&true}]x>0".asFormula)),
      existsInstantiate(None, None)(1)).subgoals.loneElement shouldBe "==> [{x'=2,y'=0*y+1&true}]x>0".asSequent

    proveBy(
      Sequent(IndexedSeq(), IndexedSeq("\\exists y [{x'=2,y'=0*y+1&true}]x>0".asFormula)),
      existsInstantiate(None, Some("z".asTerm))(1)).subgoals.loneElement shouldBe "==> [{x'=2,z'=0*z+1&true}]x>0".asSequent

    proveBy(
      Sequent(IndexedSeq(), IndexedSeq("\\exists y [{x'=2,y'=0*y+1&true}]x>0".asFormula)),
      existsInstantiate(None, Some("z+7".asTerm))(1)).
      subgoals.loneElement shouldBe "y=z+7 ==> [{x'=2,y'=0*y+1&true}]x>0".asSequent
  }

  it should "instantiate ODE" in {
    val result = proveBy("\\exists t_ (t_=0&![{x'=2,t_'=1&true}]x>b)".asFormula,
      existsInstantiate(None, Some("0".asTerm))(1))
    result.subgoals.loneElement shouldBe "t_=0 ==> t_=0&![{x'=2,t_'=1&true}]x>b".asSequent
  }

  it should "instantiate ODE correctly when there are multiple succedents" in {
    val result = proveBy("x = y ==> z != 1, \\exists z [{z'=1}]x=z , y!=1".asSequent,
      existsR(Number(1))(2)
    )
    //note: there is a reordering of the succedents after existsR!
    result.subgoals.loneElement shouldBe "x=y, z=1  ==>  z_0!=1, y!=1, [{z'=1&true}]x=z".asSequent
  }

  it should "instantiate in the presence of space exceptions" in {
    val result = proveBy("z=1 ==> \\exists y [{y'=f(|y|)^2, z' = g(|y|), a'=h(||)}]y>=0".asSequent,
      existsR("z+1".asTerm)(1)
    )
    println(result)
    result.subgoals.loneElement shouldBe "z=1, y=z+1  ==>  [{y'=f(|y|)^2,z'=g(|y|),a'=h(||)&true}]y>=0".asSequent
  }

  it should "FEATURE_REQUEST: instantiate in the presence of space exceptions with self reference" taggedAs TodoTest in {
    val result = proveBy("z=1, ==> \\exists y [{y'=f(|y|)^2, z' = g(|y|), a'=h(||)}]y>=0".asSequent,
      existsR("z+y".asTerm)(1)
    )
    // todo: this is hard and/or impossible since cannot "invent" an old name for y
  }

  "exists generalize" should "only generalize the specified occurrences of t" in {
    val result = proveBy(Sequent(IndexedSeq("a+b=a+b".asFormula), IndexedSeq()),
      existsGeneralize(Variable("z"), PosInExpr(0 :: Nil) :: Nil)(-1))
    result.subgoals.loneElement shouldBe "\\exists z z=a+b ==> ".asSequent
  }

  it should "generalize all the specified occurrences of t" in {
    val result = proveBy(Sequent(IndexedSeq("a+b=a+b".asFormula), IndexedSeq()),
      existsGeneralize(Variable("z"), PosInExpr(0 :: Nil) :: PosInExpr(1:: Nil) :: Nil)(-1))
    result.subgoals.loneElement shouldBe "\\exists z z=z ==> ".asSequent
  }

  it should "reject positions that refer to different terms" in {
    a [BelleThrowable] should be thrownBy proveBy(Sequent(IndexedSeq("a+b=a+c".asFormula), IndexedSeq()),
      existsGeneralize(Variable("z"), PosInExpr(0 :: Nil) :: PosInExpr(1:: Nil) :: Nil)(-1))
  }

  "all generalize" should "introduce a new universal quantifier" in {
    val result = proveBy("\\forall x x^2 >= -f()^2".asFormula,
      universalGen(Some(Variable("z")), FuncOf(Function("f", None, Unit, Real), Nothing))(1))
    result.subgoals.loneElement shouldBe "==> \\forall z \\forall x x^2 >= -z^2".asSequent
  }

  it should "introduce a new universal quantifier in context" in {
    val result = proveBy("a=2 -> [x:=3;]\\forall x x^2 >= -f()^2".asFormula,
      universalGen(Some(Variable("z")), FuncOf(Function("f", None, Unit, Real), Nothing))(1, 1::1::Nil))
    result.subgoals.loneElement shouldBe "==> a=2 -> [x:=3;]\\forall z \\forall x x^2 >= -z^2".asSequent
  }

  it should "introduce a new universal quantifier in context before an ODE" in {
    val result = proveBy("a=2 -> [x:=3;][{x'=5}]x>0".asFormula,
      universalGen(Some(Variable("x")), Variable("x"))(1, 1::1::Nil))
    result.subgoals.loneElement shouldBe "==> a=2 -> [x:=3;]\\forall x [{x'=5}]x>0".asSequent
  }

  it should "generalize terms" in {
    val result = proveBy("\\forall x x^2 >= -(y+5)^2".asFormula, universalGen(Some(Variable("z")), "y+5".asTerm)(1))
    result.subgoals.loneElement shouldBe "==> \\forall z \\forall x x^2 >= -z^2".asSequent
  }

  it should "generalize only free occurrences" in {
    val result = proveBy("(\\forall x x>5) & x<2".asFormula, universalGen(Some(Variable("z")), "x".asTerm)(1))
    result.subgoals.loneElement shouldBe "==> \\forall z ((\\forall x x>5) & z<2)".asSequent
  }

  it should "pick a name when generalizing only free occurrences" in {
    val result = proveBy("(\\forall x x>5) & x<2".asFormula, universalGen(None, "x".asTerm)(1))
    result.subgoals.loneElement shouldBe "==> \\forall x_0 ((\\forall x x>5) & x_0<2)".asSequent
  }

  it should "not auto-generate names that overlap with bound variables and cause clashes" in {
    proveBy("B()<=2 -> \\exists B B()<=2".asFormula, universalGen(None, "B()".asTerm)(1)).
      subgoals.loneElement shouldBe "==> \\forall B_0 (B_0<=2 -> \\exists B B_0<=2)".asSequent
  }

  "Universal closure" should "work for simple formula" in {
    val result = proveBy("x>5".asFormula, universalClosure(1))
    result.subgoals.loneElement shouldBe "==> \\forall x x>5".asSequent
  }

  it should "work when indexed names are already there" in {
    val result = proveBy("x_0>0 & x_1>1 & x_2>2".asFormula, universalClosure(1))
    result.subgoals.loneElement shouldBe "==> \\forall x_2 \\forall x_1 \\forall x_0 (x_0>0 & x_1>1 & x_2>2)".asSequent
  }

  it should "compute closure for formulas with variables and parameterless function symbols" in {
    val result = proveBy("x>5 & f()<2 & y+3>z".asFormula, universalClosure(1))
    result.subgoals.loneElement shouldBe "==> \\forall z \\forall y \\forall x \\forall f (x>5 & f<2 & y+3>z)".asSequent
  }

  it should "ignore bound variables in closure" in {
    val result = proveBy("\\forall x \\forall y (x>5 & f()<2 & y+3>z)".asFormula, universalClosure(1))
    result.subgoals.loneElement shouldBe "==> \\forall z \\forall f (\\forall x \\forall y (x>5 & f<2 & y+3>z))".asSequent
  }

  it should "not ignore variables that are not bound everywhere" in {
    val result = proveBy("(\\forall x x>5) & x<2".asFormula, universalClosure(1))
    result.subgoals.loneElement shouldBe "==> \\forall x_0 ((\\forall x x>5) & x_0<2)".asSequent
  }

  it should "not do anything if all variables are bound" in {
    val result = proveBy("\\forall x x>5".asFormula, universalClosure(1))
    result.subgoals.loneElement shouldBe "==> \\forall x x>5".asSequent
  }

  it should "use the provided order of symbols" in {
    val result = proveBy("a>0 & x>5 & y<2".asFormula, universalClosure(Variable("x")::Variable("a")::Variable("y")::Nil)(1))
    result.subgoals.loneElement shouldBe "==> \\forall x \\forall a \\forall y (a>0 & x>5 & y<2)".asSequent
  }

  it should "append non-mentioned symbols in reverse alphabetical order" in {
    val result = proveBy("a>0 & x>5 & y<2".asFormula, universalClosure(Variable("x")::Nil)(1))
    result.subgoals.loneElement shouldBe "==> \\forall x \\forall y \\forall a (a>0 & x>5 & y<2)".asSequent
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
    result.subgoals.loneElement shouldBe "==> x>0".asSequent
  }

  it should "skolemize simple at any succedent position" in {
    val s = Sequent(IndexedSeq(), IndexedSeq("y>0".asFormula, "\\forall x x>0".asFormula))
    val result = proveBy(s, allSkolemize(2))
    result.subgoals.loneElement shouldBe "==> y>0, x>0".asSequent
  }

  it should "skolemize simple at any succedent position with position locator" in {
    val s = Sequent(IndexedSeq(), IndexedSeq("y>0".asFormula, "\\forall x x>0".asFormula))
    val result = proveBy(s, allSkolemize('R))
    result.subgoals.loneElement shouldBe "==> y>0, x>0".asSequent
  }

  it should "skolemize with boundrenaming when variable to skolemize is there already" in {
    val result = proveBy(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("\\forall x x>0".asFormula)), allSkolemize(1))
    result.subgoals.loneElement shouldBe "x_0>0 ==> x>0".asSequent
  }

  it should "not rename variables bound somewhere else" in {
    val result = proveBy(Sequent(IndexedSeq("\\forall x x>0".asFormula, "\\exists x x=1".asFormula), IndexedSeq("\\forall x x>0".asFormula, "<x:=2;>x=2".asFormula)), allSkolemize(1))
    result.subgoals.loneElement shouldBe "\\forall x x>0, \\exists x x=1 ==> x>0, <x:=2;>x=2".asSequent
  }

  it should "not rename variables bound somewhere else if not top-level" in {
    val result = proveBy(Sequent(IndexedSeq("x>0 & \\forall x x>0".asFormula), IndexedSeq("\\forall x x>0".asFormula)), allSkolemize(1))
    result.subgoals.loneElement shouldBe "x_0>0 & \\forall x x>0 ==> x>0".asSequent
  }

  it should "not rename variables bound somewhere else if not top-level 2" in {
    val result = proveBy(Sequent(IndexedSeq("x>0 & (\\forall x x>0 | \\forall x x<0)".asFormula), IndexedSeq("\\forall x x>0".asFormula)), allSkolemize(1))
    result.subgoals.loneElement shouldBe "x_0>0 & (\\forall x x>0 | \\forall x x<0) ==> x>0".asSequent
  }

  it should "not rename variables bound somewhere else if not top-level 3" in {
    val result = proveBy(Sequent(IndexedSeq("x>0 & (\\forall y \\forall x x>0 | \\forall y \\forall x x<0)".asFormula), IndexedSeq("\\forall x x>0".asFormula)), allSkolemize(1))
    result.subgoals.loneElement shouldBe "x_0>0 & (\\forall y \\forall x x>0 | \\forall y \\forall x x<0) ==> x>0".asSequent
  }

  it should "not rename variables bound somewhere else if not top-level 4" in {
    val result = proveBy(Sequent(IndexedSeq("x>0 & (\\forall x \\forall x x>0 | \\forall x \\forall x x<0)".asFormula), IndexedSeq("\\forall x x>0".asFormula)), allSkolemize(1))
    result.subgoals.loneElement shouldBe "x_0>0 & (\\forall x \\forall x x>0 | \\forall x \\forall x x<0) ==> x>0".asSequent
  }

  it should "not rename bound inside formula" in {
    val result = proveBy("\\forall a (a>0 | \\forall a a<0)".asFormula, allSkolemize(1))
    result.subgoals.loneElement shouldBe "==> a>0 | \\forall a a<0".asSequent
  }

  it should "not rename bound inside formula 2" in {
    val result = proveBy("\\forall a (a>0 -> [a:=a+1;]a>0)".asFormula, allSkolemize(1))
    result.subgoals.loneElement shouldBe "==> a>0 -> [a:=a+1;]a>0".asSequent
  }

  it should "rename nondeterministic assignments" in {
    val result = proveBy("[a:=*;][b:=*;]a>0 ==> \\forall b [a:=*;]a>0".asSequent, allSkolemize(1))
    result.subgoals.loneElement shouldBe "[a:=*;][b:=*;]a>0 ==> [a:=*;]a>0".asSequent
  }

  "exists skolemize" should "skolemize simple" in {
    val result = proveBy(Sequent(IndexedSeq("\\exists x x>0".asFormula), IndexedSeq()), existsSkolemize(-1))
    result.subgoals.loneElement shouldBe "x>0 ==> ".asSequent
  }

  it should "skolemize with boundrenaming when variable to skolemize is there already" in {
    val result = proveBy(Sequent(IndexedSeq("x>0".asFormula, "\\exists x x>0".asFormula), IndexedSeq()), existsSkolemize(-2))
    result.subgoals.loneElement shouldBe "x_0>0, x>0 ==> ".asSequent
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
