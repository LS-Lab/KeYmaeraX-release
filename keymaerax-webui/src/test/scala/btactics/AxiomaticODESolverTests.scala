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
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser
import org.scalatest.PrivateMethodTester
import testHelper.KeYmaeraXTestTags.{DeploymentTest, IgnoreInBuildTest, SummaryTest, TodoTest}

/**
  * @author Nathan Fulton
  */
class AxiomaticODESolverTests extends TacticTestBase with PrivateMethodTester {
  private val dgc = PrivateMethod[DependentPositionTactic]('DGC)

  //region integration tests
  "Axiomatic ODE solver" should "work on the single integrator x'=v" taggedAs(DeploymentTest, SummaryTest) in withMathematica { qeTool =>
    val f = "x=1&v=2 -> [{x'=v}]x^3>=1".asFormula
    val t = TactixLibrary.implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    result.subgoals should have size 1
    //@todo shouldn't need kyxtime
    result.subgoals.head.ante should contain only ("x=1&v=2".asFormula, "kyxtime=0".asFormula, "x_0=x".asFormula, "kyxtime_0=kyxtime".asFormula)
    //@todo should be v*s_ instead of v*t_
    result.subgoals.head.succ should contain only "\\forall t_ (t_>=0->\\forall s_ (0<=s_&s_<=t_->true)->(v*(kyxtime+1*t_)+x_0)^3>=1)".asFormula
  }

  it should "introduce initial ghosts" taggedAs(DeploymentTest, SummaryTest) in withMathematica { qeTool =>
    val f = "x>=1&v>=2 -> [{x'=v}]x^3>=1".asFormula
    val t = TactixLibrary.implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x>=1&v>=2".asFormula, "kyxtime=0".asFormula, "x_0=x".asFormula, "kyxtime_0=kyxtime".asFormula)
    result.subgoals.head.succ should contain only "\\forall t_ (t_>=0->\\forall s_ (0<=s_&s_<=t_->true)->(v*(kyxtime+1*t_)+x_0)^3>=1)".asFormula
  }

  it should "work on the double integrator x''=a" taggedAs(DeploymentTest, SummaryTest) in withMathematica { qeTool =>
    val f = "x=1&v=2&a=0 -> [{x'=v,v'=a}]x^3>=1".asFormula
    val t = TactixLibrary.implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x=1&v=2&a=0".asFormula, "kyxtime=0".asFormula, "x_0=x".asFormula, "v_0=v".asFormula, "kyxtime_0=kyxtime".asFormula)
    result.subgoals.head.succ should contain only "\\forall t_ (t_>=0->\\forall s_ (0<=s_&s_<=t_->true)->(a/2*(kyxtime+1*t_)^2+v_0*(kyxtime+1*t_)+x_0)^3>=1)".asFormula
  }

  it should "still introduce internal time even if own time is present" in withMathematica { qeTool =>
    val f = "x=1&v=2&a=0&t=0 -> [{x'=v,v'=a,t'=1}]x^3>=1".asFormula
    val t = TactixLibrary.implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x=1&v=2&a=0&t=0".asFormula, "kyxtime=0".asFormula, "x_0=x".asFormula, "t_0=t".asFormula, "v_0=v".asFormula, "kyxtime_0=kyxtime".asFormula)
    result.subgoals.head.succ should contain only "\\forall t_ (t_>=0->\\forall s_ (0<=s_&s_<=t_->true)->(a/2*(kyxtime+1*t_)^2+v_0*(kyxtime+1*t_)+x_0)^3>=1)".asFormula
  }

  it should "solve double integrator" in  withMathematica { qeTool =>
    val f = "x=1&v=2&a=3&t=0 -> [{x'=v,v'=a, t'=1}]x>=0".asFormula
    val t = TactixLibrary.implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f,t)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x=1&v=2&a=3&t=0".asFormula, "kyxtime=0".asFormula, "x_0=x".asFormula, "v_0=v".asFormula, "t_0=t".asFormula, "kyxtime_0=kyxtime".asFormula)
    result.subgoals.head.succ should contain only "\\forall t_ (t_>=0->\\forall s_ (0<=s_&s_<=t_->true)->a/2*(kyxtime+1*t_)^2+v_0*(kyxtime+1*t_)+x_0>=0)".asFormula
  }

  //@todo support non-arithmetic post-condition.
  it should "not fail if the post-condition is non-arithmetic." taggedAs(TodoTest) ignore withMathematica { qeTool =>
    val f = "x=1&v=2&a=3&t=0 -> [{x'=v,v'=a, t'=1}][{j'=k,k'=l, z'=1}]x>=0".asFormula
    val t = TactixLibrary.implyR(1) & AxiomaticODESolver()(1)
    println(proveBy(f,t))
    //shouldBe "\\forall t_ (t_>=0->\\forall s_ (0<=s_&s_<=t_->true)->a/2*(t+1*t_)^2+2*(t+1*t_)+1>=0)".asFormula
  }

  it should "work on the triple integrator x'''=j" in withMathematica { qeTool =>
    val f = "x=1&v=2&a=3&j=4 -> [{x'=v,v'=a,a'=j}]x^3>=1".asFormula
    val t = TactixLibrary.implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    //@todo solution 1/6 (jt^3 + 3at^2 + 6vt + 6x)
    //@todo solution 1 + 2 t + 3/2 t^2 + 4/6 t^3
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x=1&v=2&a=3&j=4".asFormula, "kyxtime=0".asFormula, "x_0=x".asFormula, "v_0=v".asFormula, "a_0=a".asFormula, "kyxtime_0=kyxtime".asFormula)
    result.subgoals.head.succ should contain only "\\forall t_ (t_>=0->\\forall s_ (0<=s_&s_<=t_->true)->((j/2)/3*(kyxtime+1*t_)^3+(a_0/2)*(kyxtime+1*t_)^2+v_0*(kyxtime+1*t_)+x_0)^3>=1)".asFormula
  }

  "Axiomatic ODE solver for proofs" should "prove the single integrator x'=v" taggedAs(DeploymentTest, SummaryTest) in withMathematica { qeTool =>
    val f = "x=1&v=2 -> [{x'=v}]x^3>=1".asFormula
    val t = TactixLibrary.implyR(1) & AxiomaticODESolver()(1) & DebuggingTactics.debug("About to QE on", true) & TactixLibrary.QE()
    proveBy(f, t) shouldBe 'proved
  }

  it should "prove the double integrator x''=a" taggedAs(DeploymentTest, SummaryTest) in withMathematica { qeTool =>
    val f = "x=1&v=2&a=3 -> [{x'=v,v'=a}]x^3>=1".asFormula
    val t = TactixLibrary.implyR(1) & AxiomaticODESolver()(1) & DebuggingTactics.debug("About to QE on", true) & TactixLibrary.QE()
    proveBy(f, t) shouldBe 'proved
  }

  it should "prove the triple integrator x'''=j" in withMathematica { qeTool =>
    val f = "x=1&v=2&a=3&j=4 -> [{x'=v,v'=a,a'=j}]x^3>=1".asFormula
    val t = TactixLibrary.implyR(1) & AxiomaticODESolver()(1) & DebuggingTactics.debug("About to QE on", true) & TactixLibrary.QE()
    proveBy(f, t) shouldBe 'proved
  }

  //endregion


  //region unit tests

  //@todo exists monotone
  "SetupTimeVar" should "work when time exists" in {
    val system = "[{x'=v}]1=1".asFormula
    val tactic = addTimeVarIfNecessary
    val result = proveBy(system, tactic(SuccPosition(1, 0::Nil)))
    loneSucc(result) shouldBe "[{x'=v,kyxtime'=1&true}]1=1".asFormula
  }

  "CutInSolns" should "solve x'=y,t'=1" in withMathematica { qeTool =>
    val f = "x=0&y=0&t=0 -> [{x'=y, t'=1}]x>=0".asFormula
    val t = TactixLibrary.implyR(1) &  AxiomaticODESolver.cutInSoln(1)
    loneSucc(proveBy(f,t)) shouldBe "[{x'=y,t'=1&true&x=y*kyxtime+0}]x>=0".asFormula
  }

  //@todo fix.
  it should "solve single time dependent eqn" taggedAs(TodoTest) ignore withMathematica { qeTool =>
    val f = "x=0&y=0&t=0 -> [{x'=t, t'=1}]x>=0".asFormula
    val t = TactixLibrary.implyR(1) & (AxiomaticODESolver.cutInSoln(1)*)
    loneSucc(proveBy(f,t)) shouldBe ???
  }

  "SimplifyPostCondition" should "work" in withMathematica { qeTool =>
    val f = "[{x'=1}](x=22 -> x>0)".asFormula
    val t = simplifyPostCondition(1)
    loneSucc(proveBy(f,t)) shouldBe "[{x'=1&true}]22>0".asFormula
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

      import TactixLibrary.{implyR, composeb, assignb, allR, QE}
      val t: BelleExpr = implyR(1) & composeb(1) & assignb(1) & AxiomaticODESolver.axiomaticSolve()(1) & allR(1) & implyR(1) & implyR(1) & assignb(1) & QE

      val result : Provable = proveBy(problem, t)
      result.isProved shouldBe false
    } catch {
      case _ : Throwable => //ok.
    }
  }

  //region Additional unit tests for new core
  //Tests DifferentialTactics that the ODE solver relies on using sample inputs that the ODE solver will probably see.
  //@note these tests are largely redundant with the integration tests and are mostly just for bug localization.

  "Tactic Library Dependencies" should "DGC" taggedAs(IgnoreInBuildTest) in {
    val f = "[{x' = v}]1=1".asFormula
    val t = (HilbertCalculus invokePrivate dgc(Variable("timeVar", None), Number(1)))(1)
    loneSucc(proveBy(f,t)) shouldBe "\\exists timeVar [{x'=v,timeVar'=1&true}]1=1".asFormula
  }

  /** @note there's a more robust version of this test in [[DifferentialTests]] */
  it should "DG" taggedAs(IgnoreInBuildTest) in {
    val f = "[{x'=v}]1=1".asFormula
    val t = DifferentialTactics.DG("zz' = 22*zz + 99".asDifferentialProgram)(1)
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
    val t = DebuggingTactics.debugAt("At that position is: ", true)(pos) & HilbertCalculus.assignb(pos)

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
    val t = TactixLibrary.implyR(1) & AxiomaticODESolver()(1)
    the [BelleUserGeneratedError] thrownBy proveBy(f, t) should have message "[Bellerophon Runtime] [Bellerophon User-Generated Message] Expected ODE to be linear and in correct order."
  }

  it should "fail early when the ODE is in wrong order" in withMathematica { qeTool =>
    val f = "x=1&v=2&a=0&t=0 -> [{v'=a,x'=v,t'=1}]x^3>=1".asFormula
    val t = TactixLibrary.implyR(1) & AxiomaticODESolver()(1)
    the [BelleUserGeneratedError] thrownBy proveBy(f, t) should have message "[Bellerophon Runtime] [Bellerophon User-Generated Message] Expected ODE to be linear and in correct order."
  }

  //endregion

  //We're just looking for now errors during the diffGhost steps. This test is here to help isolate when both implementations are having troubles ghosting.
  "Original diff solve" should "work" in withMathematica { qet =>
    val model = "[{x'=v,v'=a}]1=1".asFormula
    val t: BelleExpr = DifferentialTactics.diffSolve(None)(qet)(1)
    proveBy(model, t) //just don't throw any exceptions.
  }
}
