/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.AxiomaticODESolver._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.{byUS, _}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser
import edu.cmu.cs.ls.keymaerax.pt.{NoProofTermProvable, ProvableSig}
import org.scalatest.PrivateMethodTester
import testHelper.KeYmaeraXTestTags.{DeploymentTest, IgnoreInBuildTest, SummaryTest, TodoTest}

import scala.collection.immutable._

/**
  * Tests the axioamtic ODE solver.
  * @author Nathan Fulton
  * @author Stefan Mitsch
  */
class AxiomaticODESolverTests extends TacticTestBase with PrivateMethodTester {
  private val dgc = PrivateMethod[DependentPositionTactic]('DGC)

  "Selection sort" should "not have a match error" in withMathematica { qeTool =>
    val ode = "[{posLead'=velLead,velLead'=A,posCtrl'=velCtrl,velCtrl'=a,t'=1}] true".asFormula
    proveBy(ode,TactixLibrary.solve(1) & TactixLibrary.unfoldProgramNormalize) shouldBe 'proved
  }

  "Selection sort" should "achieve intended permutation" in withMathematica { qeTool =>
    val ode = "{w' = 2,  x' = 0, y' = 3, z' = 1}".asDifferentialProgram
    val goal = List(Variable("x"), Variable("z"), Variable("w"), Variable("y"))
    val e = selectionSort(True, True, ode, goal, Position(1, 0::Nil)) & HilbertCalculus.byUS("<-> reflexive")
    val fml = "[{w' = 2,  x' = 0, y' = 3, z' = 1}]true <-> [{x' = 0, z' = 1, w' = 2, y' = 3}]true".asFormula
    proveBy(fml, e) shouldBe 'proved
  }


  "dfs" should "order dependencies nicely" in withMathematica { qeTool =>
    val ode  = "{x' = y + z, y' = 2, z' = y + w, w' = y}".asDifferentialProgram
    val res = dfs(ode)
    //res shouldBe Some(List(Variable("y"), Variable("w"), Variable("z"), Variable("x")))
    res shouldBe Some(List(Variable("x"), Variable("z"), Variable("w"), Variable("y")))
  }

  it should "detect cycles" in withMathematica { qeTool =>
    val ode = "{x' = -y, y' = x}".asDifferentialProgram
    val res = dfs(ode)
    res shouldBe None
  }

  //region integration tests
  "Axiomatic ODE solver" should "work on the single integrator x'=v" taggedAs(DeploymentTest, SummaryTest) in withMathematica { qeTool =>
    val f = "x=1&v=2 -> [{x'=v}]x^3>=1".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=1&v=2".asFormula
    result.subgoals.head.succ should contain only "\\forall t_ (t_>=0->(v*t_+x)^3>=1)".asFormula
  }

  it should "retain initial evolution domain" in withMathematica { tool =>
    val result = proveBy(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("[{x'=1&x<0}]x>=0".asFormula)), solve(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain theSameElementsAs List("x>0".asFormula)
    result.subgoals.head.succ should contain theSameElementsAs List("\\forall t_ (t_>=0 -> \\forall s_ (0<=s_ & s_<=t_ -> s_+x<0) -> t_+x>=0)".asFormula)
  }

  it should "work on the single integrator x'=v in context" taggedAs(DeploymentTest, SummaryTest) in withMathematica { qeTool =>
    val result = proveBy("x=1&v=2 -> [{x'=v}]x^3>=1".asFormula, AxiomaticODESolver()(1, 1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "x=1&v=2 -> \\forall t_ (t_>=0->(v*t_+x)^3>=1)".asFormula
  }

  it should "work on the single integrator x'=v with evolution domain" taggedAs(DeploymentTest, SummaryTest) in withMathematica { qeTool =>
    val result = proveBy("x=1&v=2 -> [{x'=v&x>=0}]x^3>=1".asFormula, implyR(1) & AxiomaticODESolver()(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain theSameElementsAs "x=1&v=2".asFormula::Nil
    result.subgoals.head.succ should contain only "\\forall t_ (t_>=0->\\forall s_ (0<=s_&s_<=t_ -> v*s_+x>=0)->(v*t_+x)^3>=1)".asFormula
  }

  it should "work on the single integrator x'=v in the antecedent" taggedAs(DeploymentTest, SummaryTest) in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("[{x'=v}]x^3>=1".asFormula), IndexedSeq()), AxiomaticODESolver()(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "\\forall t_ (t_>=0->(v*t_+x)^3>=1)".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "work on the single integrator x'=v in the antecedent when not sole formula" taggedAs(DeploymentTest, SummaryTest) in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("a=2".asFormula, "[{x'=v}]x^3>=1".asFormula, "b=3".asFormula), IndexedSeq()), AxiomaticODESolver()(-2))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain theSameElementsAs List("a=2".asFormula, "\\forall t_ (t_>=0->(v*t_+x)^3>=1)".asFormula, "b=3".asFormula)
    result.subgoals.head.succ shouldBe empty
  }

  it should "introduce initial ghosts" taggedAs(DeploymentTest, SummaryTest) in withMathematica { qeTool =>
    val f = "x>=1&v>=2 -> [{x'=v}]x^3>=1".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x>=1&v>=2".asFormula
    result.subgoals.head.succ should contain only "\\forall t_ (t_>=0->(v*t_+x)^3>=1)".asFormula
  }

  it should "work on the double integrator x''=a" taggedAs(DeploymentTest, SummaryTest) in withMathematica { qeTool =>
    val f = "x=1&v=2&a=0 -> [{x'=v,v'=a}]x^3>=1".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=1&v=2&a=0".asFormula
    result.subgoals.head.succ should contain only "\\forall t_ (t_>=0->(a/2*t_^2+v*t_+x)^3>=1)".asFormula
  }

  it should "work on the double integrator x''=a in the antecedent" taggedAs(DeploymentTest, SummaryTest) in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("[{x'=v,v'=a}]x^3>=1".asFormula), IndexedSeq()), AxiomaticODESolver()(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "\\forall t_ (t_>=0->(a/2*t_^2+v*t_+x)^3>=1)".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "work on the double integrator x''=a in context" taggedAs(DeploymentTest, SummaryTest) in withMathematica { qeTool =>
    val f = "x=1&v=2&a=0 -> [{x'=v,v'=a}]x^3>=1".asFormula
    val t = AxiomaticODESolver()(1, 1::Nil)
    val result = proveBy(f, t)
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "x=1&v=2&a=0 -> \\forall t_ (t_>=0->(a/2*t_^2+v*t_+x)^3>=1)".asFormula
  }

  it should "still introduce internal time even if own time is present" in withMathematica { qeTool =>
    val f = "x=1&v=2&a=0&t=0 -> [{x'=v,v'=a,t'=1}]x^3>=1".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=1&v=2&a=0&t=0".asFormula
    result.subgoals.head.succ should contain only "\\forall t_ (t_>=0->(a/2*t_^2+v*t_+x)^3>=1)".asFormula
  }

  it should "solve double integrator" in  withMathematica { qeTool =>
    val f = "x=1&v=2&a=3&t=0 -> [{x'=v,v'=a, t'=1}]x>=0".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f,t)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=1&v=2&a=3&t=0".asFormula
    result.subgoals.head.succ should contain only "\\forall t_ (t_>=0->a/2*t_^2+v*t_+x>=0)".asFormula
  }

  it should "solve double integrator out of order" taggedAs(DeploymentTest, SummaryTest) in withMathematica { qeTool =>
    val f = "x=1&v=2&a=3&t=0 -> [{v'=a, t'=1, x'=v}]x>=0".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f,t)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=1&v=2&a=3&t=0".asFormula
    result.subgoals.head.succ should contain only "\\forall t_ (t_>=0->a/2*t_^2+v*t_+x>=0)".asFormula
  }

  it should "not fail reordering a single ODE" taggedAs TodoTest ignore withMathematica { qeTool =>
    val f = "t=0 -> [{t'=1}]t>=0".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f,t)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "t=0".asFormula
    result.subgoals.head.succ should contain only "\\forall t_ (t_>=0->t_+t>=0)".asFormula
  }

  it should "prove empty evolution domain" in  withMathematica { qeTool =>
    val f = "x=1&v=2&a=3&t=0 -> [{x'=v,v'=a, t'=1}]x>=0".asFormula
    val t = implyR(1) & AxiomaticODESolver.axiomaticSolve()(1)
    val result = proveBy(f,t)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=1&v=2&a=3&t=0".asFormula
    result.subgoals.head.succ should contain only "\\forall t_ (t_>=0 -> a/2*t_^2+v*t_+x>=0)".asFormula
  }

  it should "instantiate with duration when asked" in  withMathematica { qeTool =>
    val f = "x=1&v=2&a=3&t=0 -> [{x'=v,v'=a, t'=1 & v>=0}]x>=0".asFormula
    val t = implyR(1) & AxiomaticODESolver.axiomaticSolve(instEnd = true)(1)
    val result = proveBy(f,t)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=1&v=2&a=3&t=0".asFormula
    result.subgoals.head.succ should contain only "\\forall t_ (t_>=0 -> (a*t_+v>=0 -> a/2*t_^2+v*t_+x>=0))".asFormula
  }

  it should "work with a non-arithmetic post-condition" in withMathematica { qeTool =>
    val f = "x=1&v=2&a=3&t=0 -> [{x'=v,v'=a, t'=1}][{j'=k,k'=l, z'=1}]x>=0".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f,t)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=1&v=2&a=3&t=0".asFormula
    result.subgoals.head.succ should contain only "\\forall t_ (t_>=0->[{j'=k,k'=l, z'=1}]a/2*t_^2+v*t_+x>=0)".asFormula
  }

  it should "work on the triple integrator x'''=j" in withMathematica { qeTool =>
    val f = "x=1&v=2&a=3&j=4 -> [{x'=v,v'=a,a'=j}]x^3>=1".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    //@todo solution 1/6 (jt^3 + 3at^2 + 6vt + 6x)
    //@todo solution 1 + 2 t + 3/2 t^2 + 4/6 t^3
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=1&v=2&a=3&j=4".asFormula
    result.subgoals.head.succ should contain only "\\forall t_ (t_>=0->(j/2/3*t_^3+(a/2)*t_^2+v*t_+x)^3>=1)".asFormula
  }

  it should "work on the triple integrator x'''=j in the antecedent" in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("[{x'=v,v'=a,a'=j}]x^3>=1".asFormula), IndexedSeq()), AxiomaticODESolver()(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "\\forall t_ (t_>=0->(j/2/3*t_^3+(a/2)*t_^2+v*t_+x)^3>=1)".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "solve simple nested ODEs" in withMathematica { tool =>
    val result = proveBy(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("[{x'=2}][{x'=3}]x>0".asFormula)), solve(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain theSameElementsAs List("x_1>0".asFormula)
    result.subgoals.head.succ should contain theSameElementsAs List("\\forall t_ (t_>=0 -> \\forall x (x=2*t_+x_1 -> [{x'=3}]x>0))".asFormula)
  }

  it should "solve in universal context in ante" in withMathematica { tool =>
    val result = proveBy(Sequent(IndexedSeq("\\forall z [{x'=2}]x>0".asFormula), IndexedSeq()), solve(-1, PosInExpr(0::Nil)))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "\\forall z \\forall t_ (t_>=0 -> 2*t_+x>0)".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "solve in nasty assignment context in ante" in withMathematica { tool =>
    val result = proveBy(Sequent(IndexedSeq("[x:=*;][{x'=2}]x>0".asFormula), IndexedSeq()), solve(-1, PosInExpr(1::Nil)))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "[x:=*;]\\forall t_ (t_>=0 -> 2*t_+x>0)".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "solve in nasty universal context in ante" in withMathematica { tool =>
    val result = proveBy(Sequent(IndexedSeq("\\forall x [{x'=2}]x>0".asFormula), IndexedSeq()), solve(-1, PosInExpr(0::Nil)))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "\\forall x \\forall t_ (t_>=0 -> 2*t_+x>0)".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "solve in unprovable context" in withMathematica { tool =>
    val result = proveBy("false & [{x'=2}]x>0".asFormula, solve(1, PosInExpr(1::Nil)))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "false & \\forall t_ (t_>=0 -> 2*t_+x>0)".asFormula
  }

  it should "work on the single integrator x'=v in positive context in the antecedent" taggedAs(DeploymentTest, SummaryTest) in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("a=2 -> [{x'=v}]x^3>=1".asFormula), IndexedSeq()), AxiomaticODESolver()(-1, 1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "a=2 -> (\\forall t_ (t_>=0->(v*t_+x)^3>=1))".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "work on the single integrator x'=v in negative context in the antecedent" taggedAs(DeploymentTest, SummaryTest) in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("[{x'=v}]x^3>=1 -> a=2".asFormula), IndexedSeq()), AxiomaticODESolver()(-1, 0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "(\\forall t_ (t_>=0->(v*t_+x)^3>=1)) -> a=2".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "work on the single integrator x'=v in negative context in the succedent" taggedAs(DeploymentTest, SummaryTest) in withMathematica { qeTool =>
    val result = proveBy("[{x'=v}]x^3>=1 -> x=1&v=2".asFormula, AxiomaticODESolver()(1, 0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "(\\forall t_ (t_>=0->(v*t_+x)^3>=1)) -> x=1&v=2".asFormula
  }

  it should "work on single integrators with constant factors" taggedAs(DeploymentTest, SummaryTest) in withMathematica { qeTool =>
    //val f = "x=1&v=2&a=3 -> [{x'=v,v'=a}]x^3>=1".asFormula
    val s = Sequent(IndexedSeq("x=0".asFormula, "t=0".asFormula), IndexedSeq("[{x'=2*t,t'=1}]x=t^2".asFormula))
    val t = AxiomaticODESolver()(1)
    val result = proveBy(s, t)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain ("x=0".asFormula)
    result.subgoals.head.ante should contain ("t=0".asFormula)
    result.subgoals.head.succ should contain only "\\forall t_ (t_>=0->2*(t_^2/2+t*t_)+x=(t_+t)^2)".asFormula
  }

  it should "work on double integrators with constant factors" taggedAs(DeploymentTest, SummaryTest) in withMathematica { qeTool =>
    val s = Sequent(IndexedSeq("a=0".asFormula, "x=0".asFormula, "t=0".asFormula), IndexedSeq("[{x'=2*v,v'=a,t'=1}]x=a*t^2".asFormula))
    val t = AxiomaticODESolver()(1)
    val result = proveBy(s, t)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain ("a=0".asFormula)
    result.subgoals.head.ante should contain ("x=0".asFormula)
    result.subgoals.head.ante should contain ("t=0".asFormula)
    result.subgoals.head.succ should contain only "\\forall t_ (t_>=0->2*(a/2*t_^2+v*t_)+x=a*(t_+t)^2)".asFormula
  }

  "Diamond axiomatic ODE solver" should "work on the single integrator x'=v" taggedAs(DeploymentTest, SummaryTest) in withMathematica { qeTool =>
    val f = "x=1&v=2 -> <{x'=0*x+v}>x^3>=1".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=1&v=2".asFormula
    result.subgoals.head.succ should contain only "\\exists t_ (t_>=0 & (v*t_+x)^3>=1)".asFormula
  }

  it should "work on the single integrator x'=v with evolution domain constraint" taggedAs(DeploymentTest, SummaryTest) in withMathematica { qeTool =>
    val f = "x=1&v=2 -> <{x'=v & x>=0}>x^3>=1".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=1&v=2".asFormula
    result.subgoals.head.succ should contain only "\\exists t_ (t_>=0 & \\forall s_ (0<=s_&s_<=t_ -> v*s_+x>=0) & (v*t_+x)^3>=1)".asFormula
  }

  it should "work on the single integrator x'=v in context" taggedAs(DeploymentTest, SummaryTest) in withMathematica { qeTool =>
    val f = "x=1&v=2 -> <{x'=0*x+v}>x^3>=1".asFormula
    val t = AxiomaticODESolver()(1, 1::Nil)
    val result = proveBy(f, t)
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "x=1&v=2 -> \\exists t_ (t_>=0 & (v*t_+x)^3>=1)".asFormula
  }

  it should "introduce initial ghosts" taggedAs(DeploymentTest, SummaryTest) in withMathematica { qeTool =>
    val f = "x>=1&v>=2 -> <{x'=0*x+v}>x^3>=1".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x>=1&v>=2".asFormula
    result.subgoals.head.succ should contain only "\\exists t_ (t_>=0&(v*t_+x)^3>=1)".asFormula
  }

  it should "work on the double integrator x''=a" taggedAs(DeploymentTest, SummaryTest) in withMathematica { qeTool =>
    val f = "x=1&v=2&a=0 -> <{x'=0*x+v,v'=0*v+a}>x^3>=1".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=1&v=2&a=0".asFormula
    result.subgoals.head.succ should contain only "\\exists t_ (t_>=0&(a/2*t_^2+v*t_+x)^3>=1)".asFormula
  }

  it should "still introduce internal time even if own time is present" in withMathematica { qeTool =>
    val f = "x=1&v=2&a=0&t=0 -> <{x'=0*x+v,v'=0*v+a,t'=0*t+1}>x^3>=1".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=1&v=2&a=0&t=0".asFormula
    result.subgoals.head.succ should contain only "\\exists t_ (t_>=0&(a/2*t_^2+v*t_+x)^3>=1)".asFormula
  }

  it should "solve double integrator" in  withMathematica { qeTool =>
    val f = "x=1&v=2&a=3&t=0 -> <{x'=0*x+v,v'=0*v+a, t'=0*t+1}>x>=0".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f,t)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=1&v=2&a=3&t=0".asFormula
    result.subgoals.head.succ should contain only "\\exists t_ (t_>=0&a/2*t_^2+v*t_+x>=0)".asFormula
  }

  it should "work with a non-arithmetic post-condition" in withMathematica { qeTool =>
    val f = "x=1&v=2&a=3&t=0 -> <{x'=0*x+v,v'=0*v+a, t'=0*t+1}>[{j'=k,k'=l, z'=1}]x>=0".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f,t)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=1&v=2&a=3&t=0".asFormula
    result.subgoals.head.succ should contain only "\\exists t_ (t_>=0&[{j'=k,k'=l, z'=1}]a/2*t_^2+v*t_+x>=0)".asFormula
  }

  it should "work on the triple integrator x'''=j" in withMathematica { qeTool =>
    val f = "x=1&v=2&a=3&j=4 -> <{x'=0*x+v,v'=0*v+a,a'=0*a+j}>x^3>=1".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    //@todo solution 1/6 (jt^3 + 3at^2 + 6vt + 6x)
    //@todo solution 1 + 2 t + 3/2 t^2 + 4/6 t^3
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=1&v=2&a=3&j=4".asFormula
    result.subgoals.head.succ should contain only "\\exists t_ (t_>=0&(j/2/3*t_^3+a/2*t_^2+v*t_+x)^3>=1)".asFormula
  }

  it should "solve simple nested ODEs" ignore withMathematica { tool =>
    val result = proveBy(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("<{x'=2}>[{x'=3}]x>0".asFormula)), solve(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain theSameElementsAs List("x_1>0".asFormula)
    result.subgoals.head.succ should contain theSameElementsAs List("\\exists t_ (t_>=0 -> \\forall x (x=2*t_+x_1 -> [{x'=3}]x>0))".asFormula)
  }

  it should "solve a ModelPlex question" in withMathematica { tool =>
    val result = proveBy("(-1<=fpost_0()&fpost_0()<=(m-l)/ep)&\\forall c (c=cpost_0()->c=0&<{l'=0*l+fpost_0(),c'=0*c+1&0<=l&c<=ep}>((fpost()=fpost_0()&lpost()=l)&cpost()=c))".asFormula,
      solve(1, 1::0::1::1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain theSameElementsAs List("(-1<=fpost_0()&fpost_0()<=(m-l)/ep)&\\forall c (c=cpost_0()->c=0&\\exists t_ (t_>=0 & \\forall s_ (0<=s_&s_<=t_ -> 0<=fpost_0()*s_+l&s_+c<=ep) & (fpost()=fpost_0()&lpost()=fpost_0()*t_+l)&cpost()=t_+c))".asFormula)
  }

  "Axiomatic ODE solver for proofs" should "prove the single integrator x'=v" taggedAs(DeploymentTest, SummaryTest) in withMathematica { qeTool =>
    val f = "x=1&v=2 -> [{x'=v}]x^3>=1".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1) & DebuggingTactics.print("About to QE on") & QE()
    proveBy(f, t) shouldBe 'proved
  }

  it should "prove the double integrator x''=a" taggedAs(DeploymentTest, SummaryTest) in withMathematica { qeTool =>
    val f = "x=1&v=2&a=3 -> [{x'=v,v'=a}]x^3>=1".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1) & DebuggingTactics.print("About to QE on") & QE()
    proveBy(f, t) shouldBe 'proved
  }

  it should "prove the triple integrator x'''=j" in withMathematica { qeTool =>
    val f = "x=1&v=2&a=3&j=4 -> [{x'=v,v'=a,a'=j}]x^3>=1".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1) & DebuggingTactics.print("About to QE on") & QE()
    proveBy(f, t) shouldBe 'proved
  }

  it should "prove with constant v'=0" in withMathematica { qeTool =>
    val f = "A>0 & B>0 & x+v^2/(2*B)<=S & v=0 -> [{x'=v,v'=0&v>=0&x+v^2/(2*B)>=S}](v>=0&x+v^2/(2*B)<=S)".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1) & DebuggingTactics.print("About to QE on") & QE()
    proveBy(f, t) shouldBe 'proved
  }

  it should "prove STTT tutorial example 5 acceleration" in withMathematica { qeTool =>
    val f = "A>0 & B>0 & ep>0 & v>=0 & x+v^2/(2*B)<=S & x+v^2/(2*B)+(A/B+1)*(A/2*ep^2+ep*v)<=S & c=0 -> [{x'=v,v'=A,c'=1&v>=0&c<=ep}](v>=0&x+v^2/(2*B)<=S)".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1) & DebuggingTactics.print("About to QE on") & QE()
    proveBy(f, t) shouldBe 'proved
  }

  //endregion


  //region unit tests

  //@todo exists monotone
  "SetupTimeVar" should "work when time exists" in {
    val system = "[{x'=v}]1=1".asFormula
    val result = proveBy(system, addTimeVar(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[kyxtime:=0;][{x'=v,kyxtime'=1&true}]1=1".asFormula
  }

  "CutInSolns" should "solve x'=y,t'=1" ignore withMathematica { qeTool =>
    //@todo setup correctly
    val f = "[kyxtime:=0;][kyxtime_0:=kyxtime;][x_0:=x;][t_0:=t;][{x'=y,t'=1}]x>=0".asFormula
    val t = AxiomaticODESolver.cutInSoln(2)(1, 1::1::1::1::Nil)
    val result = proveBy(f,t)
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[kyxtime:=0;][kyxtime_0:=kyxtime;][x_0:=x;][t_0:=t;][{x'=y,t'=1&true&x=y*(kyxtime-kyxtime_0)+x_0}]x>=0".asFormula
  }

  //@todo fix.
  it should "solve single time dependent eqn" taggedAs(TodoTest) ignore withMathematica { qeTool =>
    val f = "x=0&t=0 -> [kyxtime:=0;][kyxtime_0:=kyxtime;][x_0:=x;][t_0:=t;][{x'=t, t'=1}]x>=0".asFormula
    val t = implyR(1) & (AxiomaticODESolver.cutInSoln(2)(1, 1::1::1::1::Nil)*)
    val result = proveBy(f, t)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=0&t=0".asFormula
    result.subgoals.head.succ should contain only ???
  }

  "SimplifyPostCondition" should "work" in withMathematica { qeTool =>
    val f = "[{x'=1}](true&x=22 -> x>0)".asFormula
    val t = simplifyPostCondition(1)(1, 1::Nil)
    loneSucc(proveBy(f,t)) shouldBe "[{x'=1&true}]22>0".asFormula
  }

  //@todo unsound bananas in post condition
  "DS& differential equation solution" should "be careful in postcondition" in withMathematica { qeTool =>
    val fml = "[{x'=1}] t_>=0".asFormula
    val result = proveBy(fml, useAt("DS& differential equation solution")(1) & normalize)
    result shouldBe 'proved
  }

  //@todo this proof is broken by the second DS quantifying over the same t_
  "ODE solver" should "not shadow time" ignore withMathematica { qeTool =>
    val fml = "[t := 0; {pos' = vel, t' = 1 & t <= T};  {pos' = vel}] (t <= T)".asFormula
    val result = proveBy(fml, normalize & solve(1) & normalize & solve(1) & normalize)
    result shouldBe 'proved
  }


  //endregion

  //region stand-alone integrator

  "Integrator.apply" should "world on x'=v, v'=a" in {
    val initialConds = conditionsToValues(extractInitialConditions(None)("x=1&v=2&a=3&t=0".asFormula))
    val system = "{x'=v,v'=a, t'=1}".asProgram.asInstanceOf[ODESystem]
    val result = Integrator.apply(initialConds, "t_".asVariable, system)
    result shouldBe "x=a/2*t_^2+2*t_+1".asFormula :: "t=1*t_+0".asFormula :: "v=a*t_+2".asFormula :: Nil
  }

  "IntegratorDiffSolutionTool" should "work as a tool" in withMathematica { qe =>
    val initialConds = conditionsToValues(extractInitialConditions(None)("x=x_0&v=v_0&a=a_0&t=t_0".asFormula)).mapValues[Variable](x => x.asInstanceOf[Variable])
    val system = "{x'=v,v'=a, t'=1}".asProgram.asInstanceOf[ODESystem]
    val result = new IntegratorODESolverTool().odeSolve(system.ode, "t".asVariable, initialConds)
    println(result.get.asInstanceOf[And])
  }
  //endregion

  "ODE Solver" should "not exploit soundness bugs" in withMathematica { qet =>
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
      val problem: Formula = KeYmaeraXProblemParser(model)

      val t: BelleExpr = implyR(1) & composeb(1) & assignb(1) & AxiomaticODESolver.axiomaticSolve()(1) & allR(1) & implyR(1) & implyR(1) & assignb(1) & QE

      val result : ProvableSig = proveBy(problem, t)
      result.isProved shouldBe false
    } catch {
      case _ : Throwable => //ok.
    }
  }

  //region Additional unit tests for new core
  //Tests DifferentialTactics that the ODE solver relies on using sample inputs that the ODE solver will probably see.
  //@note these tests are largely redundant with the integration tests and are mostly just for bug localization.

  "Tactic Library Dependencies" should "DGC" taggedAs IgnoreInBuildTest in {
    val f = "[{x' = v}]1=1".asFormula
    val t = (HilbertCalculus invokePrivate dgc(Variable("timeVar", None), Number(1)))(1)
    loneSucc(proveBy(f,t)) shouldBe "\\exists timeVar [{x'=v,timeVar'=1&true}]1=1".asFormula
  }

  /** @note there's a more robust version of this test in [[DifferentialTests]] */
  it should "DG" taggedAs IgnoreInBuildTest in {
    val f = "[{x'=v}]1=1".asFormula
    val t = DifferentialTactics.dG("zz' = 22*zz + 99".asDifferentialProgram, None)(1)
    loneSucc(proveBy(f,t)) shouldBe "\\exists zz [{x'=v,zz'=22*zz+99&true}]1=1".asFormula
  }

  it should "assignbExists" in {
    val f = "\\exists kyxtime [{x'=v,kyxtime'=1&true}]1=1".asFormula
    val t = DLBySubst.assignbExists(Number(1))(1)
    loneSucc(proveBy(f,t)) shouldBe "[kyxtime:=1;][{x'=v,kyxtime'=1&true}]1=1".asFormula
  }

  "Assignb in context" should "work" in {
    val f = "\\forall t_ (t_>=0->\\forall s_ (0<=s_&s_<=t_->true)->[kyxtime:=kyxtime+1*t_;](v*kyxtime+1)^3>=1)".asFormula
    val pos = SuccPosition(SuccPos(0), PosInExpr(0::1::1::Nil)) //Also tests this as the appropriate position. See [[AxiomaticODESolver.apply]]'s definition of "timeAssignmentPos"
    val t = DebuggingTactics.debugAt("At that position is: ", doPrint=true)(pos) & HilbertCalculus.assignb(pos)

    loneSucc(proveBy(f,t)) shouldBe "\\forall t_ (t_>=0->\\forall s_ (0<=s_&s_<=t_->true)->(v*(kyxtime+1*t_)+1)^3>=1)".asFormula
  }

  //endregion

  //region The precondition check.

  "IsCanonicallyLinear" should "work" in {
    val program = "{a'=a*b, b'=c, c'=d, d'=e}".asProgram.asInstanceOf[ODESystem].ode
    DifferentialHelper.isCanonicallyLinear(program) shouldBe true
  }

  it should "work when false" in {
    val program = "{a'=a*b, b'=c, c'=d, d'=c}".asProgram.asInstanceOf[ODESystem].ode
    DifferentialHelper.isCanonicallyLinear(program) shouldBe false
  }

  "Precondition check" should "fail early when the ODE doesn't have the correct shape" in withMathematica { qeTool =>
    val f = "x=1&v=2&a=0&t=0 -> [{x'=v,v'=x,t'=1}]x^3>=1".asFormula
    val t = implyR(1) & AxiomaticODESolver()(1)
    the [BelleUserGeneratedError] thrownBy proveBy(f, t) should have message "[Bellerophon Runtime] [Bellerophon User-Generated Message] Expected ODE to be linear and in correct order."
  }
  //endregion

}
