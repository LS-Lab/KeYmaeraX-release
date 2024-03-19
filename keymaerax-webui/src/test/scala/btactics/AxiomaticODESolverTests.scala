/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.AxiomaticODESolver._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{PosInExpr, Position, SuccPosition}
import edu.cmu.cs.ls.keymaerax.parser.ArchiveParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tagobjects.{DeploymentTest, SummaryTest}
import org.scalatest.LoneElement._
import org.scalatest.PrivateMethodTester
import testHelper.KeYmaeraXTestTags.{AdvocatusTest, IgnoreInBuildTest, TodoTest}

import scala.collection.immutable._

/**
 * Tests the axiomatic ODE solver.
 * @author
 *   Nathan Fulton
 * @author
 *   Stefan Mitsch
 */
class AxiomaticODESolverTests extends TacticTestBase with PrivateMethodTester {
  private val dgc = PrivateMethod[BuiltInPositionTactic](Symbol("DGC"))

  "Selection sort" should "not have a match error" in withMathematica { _ =>
    val ode = "[{posLead'=velLead,velLead'=A,posCtrl'=velCtrl,velCtrl'=a,t'=1}] true".asFormula
    proveBy(ode, TactixLibrary.solve(1) & TactixLibrary.unfoldProgramNormalize) shouldBe Symbol("proved")
  }

  "Selection sort" should "achieve intended permutation" in withMathematica { _ =>
    val ode = "{w' = 2,  x' = 0, y' = 3, z' = 1}".asDifferentialProgram
    val goal = List(Variable("x"), Variable("z"), Variable("w"), Variable("y"))
    val e = selectionSort(True, True, ode, goal, Position(1, 0 :: Nil)) & HilbertCalculus.byUS(Ax.equivReflexive)
    val fml = "[{w' = 2,  x' = 0, y' = 3, z' = 1}]true <-> [{x' = 0, z' = 1, w' = 2, y' = 3}]true".asFormula
    proveBy(fml, e) shouldBe Symbol("proved")
  }

  "dfs" should "order dependencies nicely" in {
    val ode = "{x' = y + z, y' = 2, z' = y + w, w' = y}".asDifferentialProgram
    val res = dfs(ode)
    // res shouldBe Some(List(Variable("y"), Variable("w"), Variable("z"), Variable("x")))
    res shouldBe Some(List(Variable("x"), Variable("z"), Variable("w"), Variable("y")))
  }

  it should "favor reverse original order" in {
    // @note not a hard requirement, just so that the result of solve has right-most ODEs outermost in its nested quantifier
    //      which in the usual input order favors simpler solutions outermost, e.g., t=t_0+t_, v=v_0+a*t_, x=....
    dfs("{a'=2, x'=a, b'=3}".asDifferentialProgram) shouldBe
      Some("b".asVariable :: "x".asVariable :: "a".asVariable :: Nil)
    dfs("{b'=2, x'=a, a'=3}".asDifferentialProgram) shouldBe
      Some("x".asVariable :: "a".asVariable :: "b".asVariable :: Nil)
    dfs("{b'=2, a'=3, x'=a}".asDifferentialProgram) shouldBe
      Some("x".asVariable :: "a".asVariable :: "b".asVariable :: Nil)
  }

  it should "detect cycles" in {
    val ode = "{x' = -y, y' = x}".asDifferentialProgram
    val res = dfs(ode)
    res shouldBe None
  }

  it should "not duplicate variables in sorted result" in {
    dfs("{v'=a, x'=v}".asDifferentialProgram) shouldBe Some("x".asVariable :: "v".asVariable :: Nil)
    dfs("{y'=v+c, v'=a, x'=v}".asDifferentialProgram) shouldBe
      Some("x".asVariable :: "y".asVariable :: "v".asVariable :: Nil)
  }

  it should "sort dependencies stable" in {
    // @note try triggering sort instabilities with many runs
    for (i <- 1 to 10000) withClue(s"Sort run $i") {
      AxiomaticODESolver.dfs("{vo'=ao,vr'=ar,xr'=vr,xo'=vo,t'=1,T'=1}".asDifferentialProgram) shouldBe Some(
        "T".asVariable :: "t".asVariable :: "xo".asVariable :: "xr".asVariable :: "vr".asVariable :: "vo".asVariable ::
          Nil
      )
    }
  }

  // region integration tests
  "Axiomatic ODE solver" should "work on the single integrator x'=v" taggedAs (DeploymentTest, SummaryTest) in
    withMathematica { _ =>
      val f = "x=1&v=2 -> [{x'=v}]x^3>=1".asFormula
      val t = implyR(1) & AxiomaticODESolver()(1)
      val result = proveBy(f, t)
      result.subgoals.loneElement shouldBe "x=1&v=2 ==> \\forall t_ (t_>=0->(v*t_+x)^3>=1)".asSequent
    }

  it should "retain initial evolution domain" in withMathematica { _ =>
    val result = proveBy(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("[{x'=1&x<0}]x>=0".asFormula)), solve(1))
    result.subgoals.loneElement shouldBe
      "x>0 ==> \\forall t_ (t_>=0 -> \\forall s_ (0<=s_ & s_<=t_ -> s_+x<0) -> t_+x>=0)".asSequent
  }

  it should "work on the single integrator x'=v in context" taggedAs (DeploymentTest, SummaryTest) in withMathematica {
    _ =>
      val result = proveBy("x=1&v=2 -> [{x'=v}]x^3>=1".asFormula, AxiomaticODESolver()(1, 1 :: Nil))
      result.subgoals.loneElement shouldBe "==> x=1&v=2 -> \\forall t_ (t_>=0->(v*t_+x)^3>=1)".asSequent
  }

  it should "work on the single integrator x'=v with evolution domain" taggedAs (DeploymentTest, SummaryTest) in
    withMathematica { _ =>
      val result = proveBy("x=1&v=2 -> [{x'=v&x>=0}]x^3>=1".asFormula, implyR(1) & AxiomaticODESolver()(1))
      result.subgoals.loneElement shouldBe
        "x=1&v=2 ==> \\forall t_ (t_>=0->\\forall s_ (0<=s_&s_<=t_ -> v*s_+x>=0)->(v*t_+x)^3>=1)".asSequent
    }

  it should "work on the single integrator x'=v in the antecedent" taggedAs (DeploymentTest, SummaryTest) in
    withMathematica { _ =>
      val result = proveBy(Sequent(IndexedSeq("[{x'=v}]x^3>=1".asFormula), IndexedSeq()), AxiomaticODESolver()(-1))
      result.subgoals.loneElement shouldBe "\\forall t_ (t_>=0->(v*t_+x)^3>=1) ==> ".asSequent
    }

  it should "work on the single integrator x'=v in the antecedent when not sole formula" taggedAs
    (DeploymentTest, SummaryTest) in withMathematica { _ =>
      val result = proveBy(
        Sequent(IndexedSeq("a=2".asFormula, "[{x'=v}]x^3>=1".asFormula, "b=3".asFormula), IndexedSeq()),
        AxiomaticODESolver()(-2),
      )
      result.subgoals.loneElement shouldBe "a=2, \\forall t_ (t_>=0->(v*t_+x)^3>=1), b=3 ==> ".asSequent
    }

  it should "introduce initial ghosts" taggedAs (DeploymentTest, SummaryTest) in withMathematica { _ =>
    val f = "x>=1&v>=2 -> [{x'=v}]x^3>=1".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    result.subgoals.loneElement shouldBe "x>=1&v>=2 ==> \\forall t_ (t_>=0->(v*t_+x)^3>=1)".asSequent
  }

  it should "work on the double integrator x''=a" taggedAs (DeploymentTest, SummaryTest) in withMathematica { _ =>
    val f = "x=1&v=2&a=0 -> [{x'=v,v'=a}]x^3>=1".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    result.subgoals.loneElement shouldBe "x=1&v=2&a=0 ==> \\forall t_ (t_>=0->(a*(t_^2/2)+v*t_+x)^3>=1)".asSequent
  }

  it should "work on the double integrator x''=a in the antecedent" taggedAs (DeploymentTest, SummaryTest) in
    withMathematica { _ =>
      val result = proveBy(Sequent(IndexedSeq("[{x'=v,v'=a}]x^3>=1".asFormula), IndexedSeq()), AxiomaticODESolver()(-1))
      result.subgoals.loneElement shouldBe "\\forall t_ (t_>=0->(a*(t_^2/2)+v*t_+x)^3>=1) ==> ".asSequent
    }

  it should "work on the double integrator x''=a in context" taggedAs (DeploymentTest, SummaryTest) in withMathematica {
    _ =>
      val f = "x=1&v=2&a=0 -> [{x'=v,v'=a}]x^3>=1".asFormula
      val t = AxiomaticODESolver()(1, 1 :: Nil)
      val result = proveBy(f, t)
      result.subgoals.loneElement shouldBe "==> x=1&v=2&a=0 -> \\forall t_ (t_>=0->(a*(t_^2/2)+v*t_+x)^3>=1)".asSequent
  }

  it should "solve inside another solution" taggedAs (DeploymentTest, SummaryTest) in withMathematica { _ =>
    proveBy(
      "x>=0, y>=0 ==> [{x'=1}][{y'=x}]y>=0".asSequent,
      AxiomaticODESolver()(1) & AxiomaticODESolver()(1, 0 :: 1 :: Nil),
    ).subgoals.loneElement shouldBe
      "x>=0, y>=0 ==> \\forall t__0 (t__0>=0->\\forall t_ (t_>=0->(t__0+x)*t_+y>=0))".asSequent
  }

  it should "solve in the context of an assignment to t_" taggedAs (DeploymentTest, SummaryTest) in withMathematica {
    _ =>
      proveBy("x>=0, y>=0 ==> [t_:=4;][{x'=y*t_}]x>=0".asSequent, AxiomaticODESolver()(1, 1 :: Nil))
        .subgoals
        .loneElement shouldBe "x>=0, y>=0 ==> [t__0:=4;]\\forall t_ (t_>=0->y*t__0*t_+x>=0)".asSequent
  }

  it should "solve in the context of a system constant" taggedAs (DeploymentTest, SummaryTest) in withMathematica { _ =>
    proveBy("==> [a;][{x'=1}]x>=0".asSequent, AxiomaticODESolver()(1, 1 :: Nil)).subgoals.loneElement shouldBe
      " ==> [a;]\\forall t_ (t_>=0->t_+x>=0)".asSequent
  }

  it should "still introduce internal time even if own time is present" in withMathematica { _ =>
    val f = "x=1&v=2&a=0&t=0 -> [{x'=v,v'=a,t'=1}]x^3>=1".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    result.subgoals.loneElement shouldBe "x=1&v=2&a=0&t=0 ==> \\forall t_ (t_>=0->(a*(t_^2/2)+v*t_+x)^3>=1)".asSequent
  }

  it should "solve double integrator" in withMathematica { _ =>
    val f = "x=1&v=2&a=3&t=0 -> [{x'=v,v'=a, t'=1}]x>=0".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    result.subgoals.loneElement shouldBe "x=1&v=2&a=3&t=0 ==> \\forall t_ (t_>=0->a*(t_^2/2)+v*t_+x>=0)".asSequent
  }

  it should "solve double integrator out of order" taggedAs (DeploymentTest, SummaryTest) in withMathematica { _ =>
    val f = "x=1&v=2&a=3&t=0 -> [{v'=a, t'=1, x'=v}]x>=0".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    result.subgoals.loneElement shouldBe "x=1&v=2&a=3&t=0 ==> \\forall t_ (t_>=0->a*(t_^2/2)+v*t_+x>=0)".asSequent
  }

  it should "not fail reordering a single ODE" taggedAs (DeploymentTest, SummaryTest) in withMathematica { _ =>
    val f = "t=0 -> [{t'=1}]t>=0".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    result.subgoals.loneElement shouldBe "t=0 ==> \\forall t_ (t_>=0->t_+t>=0)".asSequent
  }

  it should "prove empty evolution domain" in withMathematica { _ =>
    val f = "x=1&v=2&a=3&t=0 -> [{x'=v,v'=a, t'=1}]x>=0".asFormula
    val t = implyR(1) & AxiomaticODESolver.axiomaticSolve()(1)
    val result = proveBy(f, t)
    result.subgoals.loneElement shouldBe "x=1&v=2&a=3&t=0 ==> \\forall t_ (t_>=0 -> a*(t_^2/2)+v*t_+x>=0)".asSequent
  }

  it should "instantiate with duration when asked" in withMathematica { _ =>
    val f = "x=1&v=2&a=3&t=0 -> [{x'=v,v'=a, t'=1 & v>=0}]x>=0".asFormula
    val t = implyR(1) & AxiomaticODESolver.axiomaticSolve(instEnd = true)(1)
    val result = proveBy(f, t)
    result.subgoals.loneElement shouldBe
      "x=1&v=2&a=3&t=0 ==> \\forall t_ (t_>=0 -> (a*t_+v>=0 -> a*(t_^2/2)+v*t_+x>=0))".asSequent
  }

  it should "work with a non-arithmetic post-condition" in withMathematica { _ =>
    val f = "x=1&v=2&a=3&t=0 -> [{x'=v,v'=a, t'=1}][{j'=k,k'=l, z'=1}]x>=0".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    result.subgoals.loneElement shouldBe
      "x=1&v=2&a=3&t=0 ==> \\forall t_ (t_>=0->[{j'=k,k'=l, z'=1}]a*(t_^2/2)+v*t_+x>=0)".asSequent
  }

  it should "work on the triple integrator x'''=j" in withMathematica { _ =>
    val f = "x=1&v=2&a=3&j=4 -> [{x'=v,v'=a,a'=j}]x^3>=1".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    result.subgoals.loneElement shouldBe
      "x=1&v=2&a=3&j=4 ==> \\forall t_ (t_>=0->(j*(t_^3/6)+a*(t_^2/2)+v*t_+x)^3>=1)".asSequent
  }

  it should "work on the triple integrator x'''=j in the antecedent" in withMathematica { _ =>
    val result =
      proveBy(Sequent(IndexedSeq("[{x'=v,v'=a,a'=j}]x^3>=1".asFormula), IndexedSeq()), AxiomaticODESolver()(-1))
    result.subgoals.loneElement shouldBe "\\forall t_ (t_>=0->(j*(t_^3/6)+a*(t_^2/2)+v*t_+x)^3>=1) ==> ".asSequent
  }

  it should "work on the triple integrator x'''=1" taggedAs (DeploymentTest, SummaryTest) in withMathematica { _ =>
    val f = "x=1&v=2&a=0 -> [{a'=1,x'=v,v'=a}]x^3>=1".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    result.subgoals.loneElement shouldBe
      "x=1&v=2&a=0 ==> \\forall t_ (t_>=0->(t_^3/6+a*(t_^2/2)+v*t_+x)^3>=1)".asSequent
  }

  it should "solve simple nested ODEs" in withMathematica { _ =>
    val sequent = Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("[{x'=2}][{x'=3}]x>0".asFormula))
    proveBy(sequent, solve(1)).subgoals.loneElement shouldBe
      "x_1>0 ==> \\forall t_ (t_>=0 -> \\forall x (x=2*t_+x_1 -> [{x'=3}]x>0))".asSequent
    proveBy(sequent, solve(1, 1 :: Nil)).subgoals.loneElement shouldBe
      "x>0 ==> [{x'=2}]\\forall t_ (t_>=0 -> 3*t_+x > 0)".asSequent
  }

  it should "fail fast on unsolvable ODEs" in withMathematica { _ =>
    the[BelleTacticFailure] thrownBy proveBy("x>0 ==> [{x'=x}]x>0".asSequent, solve(1)) should have message
      "ODE not known to have polynomial solutions. Differential equations with cyclic dependencies need invariants instead of solve()."
    the[BelleTacticFailure] thrownBy
      proveBy("x>0 ==> [{x'=2}][{x'=x}]x>0".asSequent, solve(1, PosInExpr(1 :: Nil))) should have message
      "ODE not known to have polynomial solutions. Differential equations with cyclic dependencies need invariants instead of solve()."
        .stripMargin
  }

  it should "solve in universal context in ante" in withMathematica { _ =>
    val result =
      proveBy(Sequent(IndexedSeq("\\forall z [{x'=2}]x>0".asFormula), IndexedSeq()), solve(-1, PosInExpr(0 :: Nil)))
    result.subgoals.loneElement shouldBe "\\forall z \\forall t_ (t_>=0 -> 2*t_+x>0) ==> ".asSequent
  }

  it should "solve in nasty assignment context in ante" in withMathematica { _ =>
    val result =
      proveBy(Sequent(IndexedSeq("[x:=*;][{x'=2}]x>0".asFormula), IndexedSeq()), solve(-1, PosInExpr(1 :: Nil)))
    result.subgoals.loneElement shouldBe "[x:=*;]\\forall t_ (t_>=0 -> 2*t_+x>0) ==> ".asSequent
  }

  it should "solve in nasty universal context in ante" in withMathematica { _ =>
    val result =
      proveBy(Sequent(IndexedSeq("\\forall x [{x'=2}]x>0".asFormula), IndexedSeq()), solve(-1, PosInExpr(0 :: Nil)))
    result.subgoals.loneElement shouldBe "\\forall x \\forall t_ (t_>=0 -> 2*t_+x>0) ==> ".asSequent
  }

  it should "solve in unprovable context" in withMathematica { _ =>
    val result = proveBy("false & [{x'=2}]x>0".asFormula, solve(1, PosInExpr(1 :: Nil)))
    result.subgoals.loneElement shouldBe "==> false & \\forall t_ (t_>=0 -> 2*t_+x>0)".asSequent
  }

  it should "work on the single integrator x'=v in positive context in the antecedent" taggedAs
    (DeploymentTest, SummaryTest) in withMathematica { _ =>
      val result = proveBy(
        Sequent(IndexedSeq("a=2 -> [{x'=v}]x^3>=1".asFormula), IndexedSeq()),
        AxiomaticODESolver()(-1, 1 :: Nil),
      )
      result.subgoals.loneElement shouldBe "a=2 -> (\\forall t_ (t_>=0->(v*t_+x)^3>=1)) ==> ".asSequent
    }

  it should "work on the single integrator x'=v in negative context in the antecedent" taggedAs
    (DeploymentTest, SummaryTest) in withMathematica { _ =>
      val result = proveBy(
        Sequent(IndexedSeq("[{x'=v}]x^3>=1 -> a=2".asFormula), IndexedSeq()),
        AxiomaticODESolver()(-1, 0 :: Nil),
      )
      result.subgoals.loneElement shouldBe "(\\forall t_ (t_>=0->(v*t_+x)^3>=1)) -> a=2 ==> ".asSequent
    }

  it should "work on the single integrator x'=v in negative context in the succedent" taggedAs
    (DeploymentTest, SummaryTest) in withMathematica { _ =>
      val result = proveBy("[{x'=v}]x^3>=1 -> x=1&v=2".asFormula, AxiomaticODESolver()(1, 0 :: Nil))
      result.subgoals.loneElement shouldBe "==> (\\forall t_ (t_>=0->(v*t_+x)^3>=1)) -> x=1&v=2".asSequent
    }

  it should "work on single integrators with constant factors" taggedAs (DeploymentTest, SummaryTest) in
    withMathematica { _ =>
      // val f = "x=1&v=2&a=3 -> [{x'=v,v'=a}]x^3>=1".asFormula
      val s = Sequent(IndexedSeq("x=0".asFormula, "t=0".asFormula), IndexedSeq("[{x'=2*t,t'=1}]x=t^2".asFormula))
      val t = AxiomaticODESolver()(1)
      val result = proveBy(s, t)
      result.subgoals.loneElement shouldBe "x=0, t=0 ==> \\forall t_ (t_>=0->2*(t_^2/2+t*t_)+x=(t_+t)^2)".asSequent
    }

  it should "work on double integrators with constant factors" taggedAs (DeploymentTest, SummaryTest) in
    withMathematica { _ =>
      val s = Sequent(
        IndexedSeq("a=0".asFormula, "x=0".asFormula, "t=0".asFormula),
        IndexedSeq("[{x'=2*v,v'=a,t'=1}]x=a*t^2".asFormula),
      )
      val t = AxiomaticODESolver()(1)
      val result = proveBy(s, t)
      result.subgoals.loneElement shouldBe
        "a=0, x=0, t=0 ==> \\forall t_ (t_>=0->2*(a*(t_^2/2)+v*t_)+x=a*(t_+t)^2)".asSequent
    }

  it should "solve when reserved time is present" in withMathematica { _ =>
    val result = proveBy("[{v'=a}]v>=0, kyxtime=0 ==> [{x'=y}]x>=0".asSequent, solve(1) & solve(-1))
    result.subgoals.loneElement shouldBe
      "\\forall t_ (t_>=0->a*t_+v>=0), kyxtime=0 ==> \\forall t_ (t_>=0->y*t_+x>=0)".asSequent
  }

  it should "not fail on potential division by zero" in withMathematica { _ =>
    val result = proveBy("x > 0 & v > 0 ==> [{x' = v / r}]x > 0".asSequent, solve(1))
    result.subgoals.loneElement shouldBe "x>0&v>0 ==> \\forall t_ (t_>=0->v/r*t_+x>0)".asSequent
    // but QE should not be able to prove it
    proveBy(result, QE).subgoals.loneElement shouldBe "==> false".asSequent
  }

  it should "rename duration variable correctly when solving nested ODEs" in withMathematica { _ =>
    val result = proveBy(
      "x=3 & y=8 ==> [{x'=1 & x<=5}][{y'=-1 & y>7}](x<=5 & y>7)".asSequent,
      solve(1) & solve(1, 0 :: 1 :: 1 :: Nil),
    )
    result.subgoals.loneElement shouldBe
      "x=3 & y=8 ==> \\forall t__0 (t__0>=0->\\forall s_ (0<=s_&s_<=t__0->s_+x<=5)->\\forall t_ (t_>=0->\\forall s_ (0<=s_&s_<=t_->y-s_>7)->t__0+x<=5&y-t_>7))"
        .asSequent
  }

  "Diamond axiomatic ODE solver" should "work on the single integrator x'=v" taggedAs (DeploymentTest, SummaryTest) in
    withMathematica { _ =>
      val f = "x=1&v=2 -> <{x'=v}>x^3>=1".asFormula
      val t = implyR(1) & AxiomaticODESolver()(1)
      val result = proveBy(f, t)
      result.subgoals.loneElement shouldBe "x=1&v=2 ==> \\exists t_ (t_>=0 & (v*t_+x)^3>=1)".asSequent
    }

  it should "work on the single integrator x'=v with evolution domain constraint" taggedAs
    (DeploymentTest, SummaryTest) in withMathematica { _ =>
      val f = "x=1&v=2 -> <{x'=v & x>=0}>x^3>=1".asFormula
      val t = implyR(1) & AxiomaticODESolver()(1)
      val result = proveBy(f, t)
      result.subgoals.loneElement shouldBe
        "x=1&v=2 ==> \\exists t_ (t_>=0 & \\forall s_ (0<=s_&s_<=t_ -> v*s_+x>=0) & (v*t_+x)^3>=1)".asSequent
    }

  it should "work on the single integrator x'=v in context" taggedAs (DeploymentTest, SummaryTest) in withMathematica {
    _ =>
      val f = "x=1&v=2 -> <{x'=v}>x^3>=1".asFormula
      val t = AxiomaticODESolver()(1, 1 :: Nil)
      val result = proveBy(f, t)
      result.subgoals.loneElement shouldBe "==> x=1&v=2 -> \\exists t_ (t_>=0 & (v*t_+x)^3>=1)".asSequent
  }

  it should "work on the single integrator x'=v in the antecedent" taggedAs (DeploymentTest, SummaryTest) in
    withMathematica { _ =>
      val result = proveBy("<{x'=v}>x^3>=1 ==> x>=1 | v>0".asSequent, AxiomaticODESolver()(-1))
      result.subgoals.loneElement shouldBe "\\exists t_ (t_>=0 & (v*t_+x)^3>=1) ==> x>=1 | v>0".asSequent
    }

  it should "work on the single integrator x'=v in negative polarity" taggedAs (DeploymentTest, SummaryTest) in
    withMathematica { _ =>
      val f = "x=-1, v=-2 ==> !<{x'=v}>x^3>=1".asSequent
      val t = AxiomaticODESolver()(1, 0 :: Nil)
      val result = proveBy(f, t)
      result.subgoals.loneElement shouldBe "x=-1, v=-2 ==> !\\exists t_ (t_>=0 & (v*t_+x)^3>=1)".asSequent
    }

  it should "introduce initial ghosts" taggedAs (DeploymentTest, SummaryTest) in withMathematica { _ =>
    val f = "x>=1&v>=2 -> <{x'=v}>x^3>=1".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    result.subgoals.loneElement shouldBe "x>=1&v>=2 ==> \\exists t_ (t_>=0&(v*t_+x)^3>=1)".asSequent
  }

  it should "work on the double integrator x''=a" taggedAs (DeploymentTest, SummaryTest) in withMathematica { _ =>
    val f = "x=1&v=2&a=0 -> <{x'=v,v'=a}>x^3>=1".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    result.subgoals.loneElement shouldBe "x=1&v=2&a=0 ==> \\exists t_ (t_>=0&(a*(t_^2/2)+v*t_+x)^3>=1)".asSequent
  }

  it should "still introduce internal time even if own time is present" in withMathematica { _ =>
    val f = "x=1&v=2&a=0&t=0 -> <{x'=v,v'=a,t'=1}>x^3>=1".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    result.subgoals.loneElement shouldBe "x=1&v=2&a=0&t=0 ==> \\exists t_ (t_>=0&(a*(t_^2/2)+v*t_+x)^3>=1)".asSequent
  }

  it should "solve double integrator" in withMathematica { _ =>
    val f = "x=1&v=2&a=3&t=0 -> <{x'=v,v'=a, t'=1}>x>=0".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    result.subgoals.loneElement shouldBe "x=1&v=2&a=3&t=0 ==> \\exists t_ (t_>=0&a*(t_^2/2)+v*t_+x>=0)".asSequent
  }

  it should "work with a non-arithmetic post-condition" in withMathematica { _ =>
    val f = "x=1&v=2&a=3&t=0 -> <{x'=v,v'=a, t'=1}>[{j'=k,k'=l, z'=1}]x>=0".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    result.subgoals.loneElement shouldBe
      "x=1&v=2&a=3&t=0 ==> \\exists t_ (t_>=0&[{j'=k,k'=l, z'=1}]a*(t_^2/2)+v*t_+x>=0)".asSequent
  }

  it should "work on the triple integrator x'''=j" in withMathematica { _ =>
    val f = "x=1&v=2&a=3&j=4 -> <{x'=v,v'=a,a'=j}>x^3>=1".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    result.subgoals.loneElement shouldBe
      "x=1&v=2&a=3&j=4 ==> \\exists t_ (t_>=0&(j*(t_^3/6)+a*(t_^2/2)+v*t_+x)^3>=1)".asSequent
  }

  it should "solve simple nested ODEs" in withMathematica { _ =>
    val result = proveBy(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("<{x'=2}>[{x'=3}]x>0".asFormula)), solve(1))
    result.subgoals.loneElement shouldBe
      "x_1>0 ==> \\exists t_ (t_>=0 & \\forall x (x=2*t_+x_1 -> [{x'=3}]x>0))".asSequent
  }

  it should "support diamond with postcond that binds variables we bind" in withMathematica { _ =>
    val result = proveBy(Sequent(IndexedSeq(), IndexedSeq("<{x'=1}>\\forall x x^2 >= 0".asFormula)), solve(1))
    result.subgoals.loneElement shouldBe "==> \\exists t_ (t_>=0 & \\forall x x^2 >= 0)".asSequent
  }

  it should "support box with postcond that binds variables we bind" in withMathematica { _ =>
    val result = proveBy(Sequent(IndexedSeq(), IndexedSeq("[{x'=1}]\\forall x x^2 >= 0".asFormula)), solve(1))
    result.subgoals.loneElement shouldBe "==> \\forall t_ (t_>=0 -> \\forall x x^2 >= 0)".asSequent
  }

  it should "support diamond with postcond that binds variables we bind via assignment" in withMathematica { _ =>
    val result = proveBy(Sequent(IndexedSeq(), IndexedSeq("<{x'=1}>[x:= x + 1;] x^2 >= 0".asFormula)), solve(1))
    result.subgoals.loneElement shouldBe "==> \\exists t_ (t_>=0 & [x:=1*(0+1*t_-0)+x+1;]x^2 >= 0)".asSequent
  }

  it should "support box with postcond that binds variables we bind via assignment" in withMathematica { _ =>
    val result = proveBy(Sequent(IndexedSeq(), IndexedSeq("[{x'=1}][x:= x + 1;] x^2 >= 0".asFormula)), solve(1))
    result.subgoals.loneElement shouldBe "==> \\forall t_ (t_>=0->[x:=1*(0+1*t_-0)+x+1;]x^2>=0)".asSequent
  }

  it should "solve a ModelPlex question" in withMathematica { _ =>
    val result = proveBy(
      "(-1<=fpost_0()&fpost_0()<=(m-l)/ep)&\\forall c (c=cpost_0()->c=0&<{l'=fpost_0(),c'=1&0<=l&c<=ep}>((fpost()=fpost_0()&lpost()=l)&cpost()=c))"
        .asFormula,
      solve(1, 1 :: 0 :: 1 :: 1 :: Nil),
    )
    result.subgoals.loneElement shouldBe
      "==> (-1<=fpost_0()&fpost_0()<=(m-l)/ep)&\\forall c (c=cpost_0()->c=0&\\exists t_ (t_>=0 & \\forall s_ (0<=s_&s_<=t_ -> 0<=fpost_0()*s_+l&s_+c<=ep) & (fpost()=fpost_0()&lpost()=fpost_0()*t_+l)&cpost()=t_+c))"
        .asSequent
  }

  it should "rename duration variable correctly when solving nested ODEs" in withMathematica { _ =>
    val result = proveBy(
      "x=3 & y=8 ==> <{x'=1 & x<=5}><{y'=-1 & y>7}>(x<=5 & y>7)".asSequent,
      solve(1) & solve(1, 0 :: 1 :: 1 :: Nil),
    )
    result.subgoals.loneElement shouldBe
      "x=3 & y=8 ==> \\exists t__0 (t__0>=0 & \\forall s_ (0<=s_&s_<=t__0->s_+x<=5) & \\exists t_ (t_>=0 & \\forall s_ (0<=s_&s_<=t_->y-s_>7) & t__0+x<=5&y-t_>7))"
        .asSequent
  }

  "Axiomatic ODE solver for proofs" should "prove the single integrator x'=v" taggedAs (DeploymentTest, SummaryTest) in
    withMathematica { _ =>
      val f = "x=1&v=2 -> [{x'=v}]x^3>=1".asFormula
      val t = implyR(1) & AxiomaticODESolver()(1) & DebuggingTactics.print("About to QE on") & QE
      proveBy(f, t) shouldBe Symbol("proved")
    }

  it should "prove the double integrator x''=a" taggedAs (DeploymentTest, SummaryTest) in withMathematica { _ =>
    val f = "x=1&v=2&a=3 -> [{x'=v,v'=a}]x^3>=1".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1) & DebuggingTactics.print("About to QE on") & QE
    proveBy(f, t) shouldBe Symbol("proved")
  }

  it should "prove the triple integrator x'''=j" in withMathematica { _ =>
    val f = "x=1&v=2&a=3&j=4 -> [{x'=v,v'=a,a'=j}]x^3>=1".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1) & DebuggingTactics.print("About to QE on") & QE
    proveBy(f, t) shouldBe Symbol("proved")
  }

  it should "prove with constant v'=0" in withMathematica { _ =>
    val f = "A>0 & B>0 & x+v^2/(2*B)<=S & v=0 -> [{x'=v,v'=0&v>=0&x+v^2/(2*B)>=S}](v>=0&x+v^2/(2*B)<=S)".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1) & DebuggingTactics.print("About to QE on") & QE
    proveBy(f, t) shouldBe Symbol("proved")
  }

  it should "prove STTT tutorial example 5 acceleration" in withMathematica { _ =>
    val f =
      "A>0 & B>0 & ep>0 & v>=0 & x+v^2/(2*B)<=S & x+v^2/(2*B)+(A/B+1)*(A/2*ep^2+ep*v)<=S & c=0 -> [{x'=v,v'=A,c'=1&v>=0&c<=ep}](v>=0&x+v^2/(2*B)<=S)"
        .asFormula
    val t = implyR(1) & AxiomaticODESolver()(1) & DebuggingTactics.print("About to QE on") & QE
    proveBy(f, t) shouldBe Symbol("proved")
  }

  // endregion

  // region unit tests

  // @todo exists monotone
  "SetupTimeVar" should "work when time exists" in {
    val system = "[{x'=v}]1=1".asFormula
    val result = proveBy(system, addTimeVar(1))
    result.subgoals.loneElement shouldBe "==> [kyxtime_0:=0;][{x'=v,kyxtime_0'=1&true}]1=1".asSequent
  }

  "CutInSolns" should "solve x'=y,t'=1" ignore withMathematica { _ =>
    // @todo setup correctly
    val f = "[kyxtime:=0;][kyxtime_0:=kyxtime;][x_0:=x;][t_0:=t;][{x'=y,t'=1}]x>=0".asFormula
    val t = AxiomaticODESolver.cutInSoln(2)(1, 1 :: 1 :: 1 :: 1 :: Nil)
    val result = proveBy(f, t)
    result.subgoals.loneElement shouldBe
      "==> [kyxtime:=0;][kyxtime_0:=kyxtime;][x_0:=x;][t_0:=t;][{x'=y,t'=1&true&x=y*(kyxtime-kyxtime_0)+x_0}]x>=0"
        .asSequent
  }

  // @todo fix.
  it should "solve single time dependent eqn" taggedAs TodoTest ignore withMathematica { _ =>
    val f = "x=0&t=0 -> [kyxtime:=0;][kyxtime_0:=kyxtime;][x_0:=x;][t_0:=t;][{x'=t, t'=1}]x>=0".asFormula
    val t = implyR(1) & SaturateTactic(AxiomaticODESolver.cutInSoln(2)(1, 1 :: 1 :: 1 :: 1 :: Nil))
    val result = proveBy(f, t)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=0&t=0".asFormula
    result.subgoals.head.succ should contain only ???
  }

  "SimplifyPostCondition" should "work" in withMathematica { _ =>
    val f = "[{x'=1}](true&x=22 -> x>0)".asFormula
    val t = simplifyPostCondition(1)(1, 1 :: Nil)
    proveBy(f, t).subgoals.loneElement shouldBe "==> [{x'=1&true}]22>0".asSequent
  }

  "DS& differential equation solution" should "be careful in postcondition" taggedAs AdvocatusTest in withMathematica {
    _ =>
      // @note t_ introduced with assumption t_>=0 by axiom DS& differential equation solution
      a[InapplicableUnificationKeyFailure] should be thrownBy proveBy("[{x'=1}]t_>=0".asFormula, useAt(Ax.DS)(1))
  }

  // @todo this proof is broken by the second DS quantifying over the same t_
  "ODE solver" should "not shadow time" ignore withMathematica { _ =>
    val fml = "[t := 0; {pos' = vel, t' = 1 & t <= T};  {pos' = vel}] (t <= T)".asFormula
    val result = proveBy(fml, normalize & solve(1) & normalize & solve(1) & normalize)
    result shouldBe Symbol("proved")
  }

  // endregion

  // region stand-alone integrator

  "Integrator.apply" should "world on x'=v, v'=a" in {
    val initialConds = conditionsToValues(extractInitialConditions(None)("x=1&v=2&a=3&t=0".asFormula))
    val system = "{x'=v,v'=a, t'=1}".asProgram.asInstanceOf[ODESystem]
    val result = Integrator.apply(initialConds, "t_".asVariable, system)
    result shouldBe "x=a*(t_^2/2)+2*t_+1".asFormula :: "t=1*t_+0".asFormula :: "v=a*t_+2".asFormula :: Nil
  }

  "IntegratorDiffSolution_" should "work as a _" in withMathematica { _ =>
    val initialConds = conditionsToValues(extractInitialConditions(None)("x=x_0&v=v_0&a=a_0&t=t_0".asFormula))
      .view
      .mapValues[Variable](x => x.asInstanceOf[Variable])
      .toMap
    val system = "{x'=v,v'=a, t'=1}".asProgram.asInstanceOf[ODESystem]
    val result = new IntegratorODESolverTool().odeSolve(system.ode, "t".asVariable, initialConds)
    println(result.get.asInstanceOf[And])
  }
  // endregion

  "ODE Solver" should "not exploit soundness bugs" in withMathematica { _ =>
    try {
      val model = """Functions.
                    |  R b.
                    |  R m.
                    |End.
                    |
                    |ProgramVariables.
                    |  R x.
                    |  R v.
                    |  R a.
                    |End.
                    |
                    |Problem.
                    |  x<=m & b>0 -> [a:=-b; {x'=v,v'=a & v>=0}]x<=m
                    |End.
                    |""".stripMargin
      val problem: Formula = ArchiveParser.parseAsFormula(model)

      val t: BelleExpr = implyR(1) & composeb(1) & assignb(1) & AxiomaticODESolver.axiomaticSolve()(1) & allR(1) &
        implyR(1) & implyR(1) & assignb(1) & QE

      val result: ProvableSig = proveBy(problem, t)
      result.isProved shouldBe false
    } catch {
      case _: Throwable => // ok.
    }
  }

  // region Additional unit tests for new core
  // Tests DifferentialTactics that the ODE solver relies on using sample inputs that the ODE solver will probably see.
  // @note these tests are largely redundant with the integration tests and are mostly just for bug localization.

  "Tactic Library Dependencies" should "DGC" taggedAs IgnoreInBuildTest in {
    val f = "[{x' = v}]1=1".asFormula
    val t = (HilbertCalculus invokePrivate dgc(Variable("timeVar", None), Number(1)))(1)
    proveBy(f, t).subgoals.loneElement shouldBe "==> \\exists timeVar [{x'=v,timeVar'=1&true}]1=1".asSequent
  }

  /** @note there's a more robust version of this test in [[DifferentialTests]] */
  it should "DG" taggedAs IgnoreInBuildTest in {
    val f = "[{x'=v}]1=1".asFormula
    val t = DifferentialTactics.dG("zz' = 22*zz + 99".asDifferentialProgram, None)(1)
    proveBy(f, t).subgoals.loneElement shouldBe "==> \\exists zz [{x'=v,zz'=22*zz+99&true}]1=1".asSequent
  }

  it should "assignbExists" in {
    val f = "\\exists kyxtime [{x'=v,kyxtime'=1&true}]1=1".asFormula
    val t = DLBySubst.assignbExists(Number(1))(1)
    proveBy(f, t).subgoals.loneElement shouldBe "==> [kyxtime:=1;][{x'=v,kyxtime'=1&true}]1=1".asSequent
  }

  "Assignb in context" should "work" in {
    val f =
      "\\forall t_ (t_>=0->\\forall s_ (0<=s_&s_<=t_->true)->[kyxtime:=kyxtime+1*t_;](v*kyxtime+1)^3>=1)".asFormula
    val pos =
      SuccPosition(
        SuccPos(0),
        PosInExpr(0 :: 1 :: 1 :: Nil),
      ) // Also tests this as the appropriate position. See [[AxiomaticODESolver.apply]]'s definition of "timeAssignmentPos"
    val t = DebuggingTactics.debugAt("At that position is: ", doPrint = true)(pos) & HilbertCalculus.assignb(pos)

    proveBy(f, t).subgoals.loneElement shouldBe
      "==> \\forall t_ (t_>=0->\\forall s_ (0<=s_&s_<=t_->true)->(v*(kyxtime+1*t_)+1)^3>=1)".asSequent
  }

  // endregion

  // region The precondition check.

  "IsCanonicallyLinear" should "work" in {
    val program = "{a'=a*b, b'=c, c'=d, d'=e}".asProgram.asInstanceOf[ODESystem].ode
    DifferentialHelper.isCanonicallyLinear(program) shouldBe true
  }

  it should "work when false" in {
    val program = "{a'=a*b, b'=c, c'=d, d'=c}".asProgram.asInstanceOf[ODESystem].ode
    DifferentialHelper.isCanonicallyLinear(program) shouldBe false
  }

  "Precondition check" should "fail early when the ODE doesn't have the correct shape" in withMathematica { _ =>
    val f = "x=1&v=2&a=0&t=0 -> [{x'=v,v'=x,t'=1}]x^3>=1".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    the[BelleThrowable] thrownBy proveBy(f, t) should have message
      "ODE not known to have polynomial solutions. Differential equations with cyclic dependencies need invariants instead of solve()."
  }
  // endregion

}
