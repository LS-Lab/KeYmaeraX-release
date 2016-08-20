/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.AxiomaticODESolver._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser
import org.scalatest.PrivateMethodTester
import testHelper.KeYmaeraXTestTags.{DeploymentTest, IgnoreInBuildTest, SummaryTest, TodoTest}

/**
  * @author Nathan Fulton
  */
class AxiomaticODESolverTests extends TacticTestBase with PrivateMethodTester {
  import DifferentialHelper._
  import Augmentors._
  import TacticFactory._

  val dgc = PrivateMethod[DependentPositionTactic]('DGC)

  //region integration tests
  "axiomatic ode solver" should "work on the single integrator x'=v" taggedAs(DeploymentTest, SummaryTest) in withMathematica(implicit qeTool => {
    val f = "x=1&v=2 -> [{x'=v}]x^3>=1".asFormula
    val t = TactixLibrary.implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    loneSucc(result) shouldBe "\\forall t_ (t_>=0->\\forall s_ (0<=s_&s_<=t_->true)->(v*(kyxtime+1*t_)+1)^3>=1)".asFormula
  })

  it should "work on the double integrator x''=a" taggedAs(DeploymentTest, SummaryTest) in withMathematica(implicit qeTool => {
    val f = "x=1&v=2&a=0 -> [{x'=v,v'=a}]x^3>=1".asFormula
    val t = TactixLibrary.implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    loneSucc(result) shouldBe "\\forall t_ (t_>=0->\\forall s_ (0<=s_&s_<=t_->true)->(a/2*(kyxtime+1*t_)^2+2*(kyxtime+1*t_)+1)^3>=1)".asFormula
  })

  it should "work using my own time" in withMathematica(implicit qeTool => {
    val f = "x=1&v=2&a=0&t=0 -> [{x'=v,v'=a,t'=1}]x^3>=1".asFormula
    val t = TactixLibrary.implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    loneSucc(result) shouldBe "\\forall t_ (t_>=0->\\forall s_ (0<=s_&s_<=t_->true)->(a/2*(t+1*t_)^2+2*(t+1*t_)+1)^3>=1)".asFormula
  })

  it should "solve double integrator" in {withMathematica(implicit qeTool => {
    val f = "x=1&v=2&a=3&t=0 -> [{x'=v,v'=a, t'=1}]x>=0".asFormula
    val t = TactixLibrary.implyR(1) & AxiomaticODESolver()(1)
    loneSucc(proveBy(f,t)) shouldBe "\\forall t_ (t_>=0->\\forall s_ (0<=s_&s_<=t_->true)->a/2*(t+1*t_)^2+2*(t+1*t_)+1>=0)".asFormula
  })}

  //@todo support non-arithmetic post-condition.
  ignore should "not fail if the post-condition is non-arithmetic." taggedAs(TodoTest) in {withMathematica(implicit qeTool => {
    val f = "x=1&v=2&a=3&t=0 -> [{x'=v,v'=a, t'=1}][{j'=k,k'=l, z'=1}]x>=0".asFormula
    val t = TactixLibrary.implyR(1) & AxiomaticODESolver()(1)
    println(proveBy(f,t))
    //shouldBe "\\forall t_ (t_>=0->\\forall s_ (0<=s_&s_<=t_->true)->a/2*(t+1*t_)^2+2*(t+1*t_)+1>=0)".asFormula
  })}

  it should "work on the triple integrator x'''=j" in {withMathematica(implicit qeTool => {
    val f = "x=1&v=2&a=3&j=4 -> [{x'=v,v'=a,a'=j}]x^3>=1".asFormula
    val t = TactixLibrary.implyR(1) & AxiomaticODESolver()(1)
    val result = proveBy(f, t)
    //@todo solution 1/6 (jt^3 + 3at^2 + 6vt + 6x)
    //@todo solution 1 + 2 t + 3/2 t^2 + 4/6 t^3
    loneSucc(result) shouldBe "\\forall t_ (t_>=0->\\forall s_ (0<=s_&s_<=t_->true)->((j/2)/3*(kyxtime+1*t_)^3+(3/2)*(kyxtime+1*t_)^2+2*(kyxtime+1*t_)+1)^3>=1)".asFormula
  })}

  "axiomatic ode solver for proofs" should "prove the single integrator x'=v" taggedAs(DeploymentTest, SummaryTest) in withMathematica(implicit qeTool => {
    val f = "x=1&v=2 -> [{x'=v}]x^3>=1".asFormula
    val t = TactixLibrary.implyR(1) & AxiomaticODESolver()(1) & DebuggingTactics.debug("About to QE on", true) & TactixLibrary.QE()
    proveBy(f, t) shouldBe 'proved
  })

  it should "prove the double integrator x''=a" taggedAs(DeploymentTest, SummaryTest) in withMathematica {implicit qeTool =>
    val f = "x=1&v=2&a=3 -> [{x'=v,v'=a}]x^3>=1".asFormula
    val t = TactixLibrary.implyR(1) & AxiomaticODESolver()(1) & DebuggingTactics.debug("About to QE on", true) & TactixLibrary.QE()
    proveBy(f, t) shouldBe 'proved
  }

  it should "prove the triple integrator x'''=j" in {withMathematica(implicit qeTool => {
    val f = "x=1&v=2&a=3&j=4 -> [{x'=v,v'=a,a'=j}]x^3>=1".asFormula
    val t = TactixLibrary.implyR(1) & AxiomaticODESolver()(1) & DebuggingTactics.debug("About to QE on", true) & TactixLibrary.QE()
    proveBy(f, t) shouldBe 'proved
  })}

  //endregion


  //region unit tests

  //@todo exists monotone
  "setupTimeVar" should "work when time exists" in {
    val system = "[{x'=v}]1=1".asFormula
    val tactic = addTimeVarIfNecessary
    val result = proveBy(system, tactic(SuccPosition(1, 0::Nil)))
    loneSucc(result) shouldBe "[{x'=v,kyxtime'=1&true}]1=1".asFormula
  }

  "cutInSolns" should "solve x'=y,t'=1" in {withMathematica(implicit qeTool => {
    val f = "x=0&y=0&t=0 -> [{x'=y, t'=1}]x>=0".asFormula
    val t = TactixLibrary.implyR(1) &  AxiomaticODESolver.cutInSoln(1)
    loneSucc(proveBy(f,t)) shouldBe "[{x'=y,t'=1&true&x=y*t+0}]x>=0".asFormula
  })}

  //@todo fix.
  ignore should "solve single time dependent eqn" taggedAs(TodoTest) in {withMathematica(implicit qeTool => {
    val f = "x=0&y=0&t=0 -> [{x'=t, t'=1}]x>=0".asFormula
    val t = TactixLibrary.implyR(1) & (AxiomaticODESolver.cutInSoln(1)*)
    loneSucc(proveBy(f,t)) shouldBe ???
  })}

  //endregion

  //region proveAs construct

  "proveAs" should "prove as" in {
    val f = "P() -> P()".asFormula
    val t = ProveAs("piffp", f, TactixLibrary.implyR(1) & TactixLibrary.close) & HilbertCalculus.lazyUseAt("piffp")(1)
    proveBy(f,t) shouldBe 'proved
  }

  it should "work in simplifyPostCondition" in {withMathematica(implicit qeTool => {
    val f = "[{x'=1}](x=22 -> x>0)".asFormula
    val t = simplifyPostCondition(1)
    loneSucc(proveBy(f,t)) shouldBe "[{x'=1&true}]22>0".asFormula
  })}

  //endregion

  //region stand-alone integrator

  "Integrator.apply" should "world on x'=v, v'=a" in {
    val initialConds = conditionsToValues(extractInitialConditions(None)("x=1&v=2&a=3&t=0".asFormula))
    val system = "{x'=v,v'=a, t'=1}".asProgram.asInstanceOf[ODESystem]
    val result = Integrator.apply(initialConds, system)
    result shouldBe "x=a/2*t^2+2*t+1".asFormula :: "v=a*t+2".asFormula :: Nil
  }
  //endregion

  "ODE Solver" should "not exploit soundness bugs" in {withMathematica(implicit qet => {
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
  })}

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
    proveBy(f,t) shouldBe "[kyxtime:=1;][{x'=v,kyxtime'=1&true}]1=1".asFormula
  }

  "assignb in context" should "work" in {
    val f = "\\forall t_ (t_>=0->\\forall s_ (0<=s_&s_<=t_->true)->[kyxtime:=kyxtime+1*t_;](v*kyxtime+1)^3>=1)".asFormula
    val pos = SuccPosition(SuccPos(0), PosInExpr(0::1::1::Nil)) //Also tests this as the appropriate position. See [[AxiomaticODESolver.apply]]'s definition of "timeAssignmentPos"
    val t = DebuggingTactics.debugAt("At that position is: ", true)(pos) & HilbertCalculus.assignb(pos)

    loneSucc(proveBy(f,t)) shouldBe "\\forall t_ (t_>=0->\\forall s_ (0<=s_&s_<=t_->true)->(v*(kyxtime+1*t_)+1)^3>=1)".asFormula
  }

  //endregion

  //We're just looking for now errors during the diffGhost steps. This test is here to help isolate when both implementations are having troubles ghosting.
  "Original diff solve" should "work" in {withMathematica(implicit qet => {
    val model = "[{x'=v,v'=a}]1=1".asFormula
    val t: BelleExpr = DifferentialTactics.diffSolve(None)(qet)(1)
    proveBy(model, t) //just don't throw any exceptions.
  })}
}