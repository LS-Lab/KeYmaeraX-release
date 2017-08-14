/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core.Number
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import testHelper.KeYmaeraXTestTags

/**
  * Tests the series expansion tactics.
  * @author Nathan Fulton
  */
class ApproximatorTests extends TacticTestBase {
  "taylorCircular approximator" should "approximate {s'=c, c'=s, t'=1} with some initial help." in withMathematica(_ => {
    val f = "c=1 & s=0 & t=0->[{s'=c,c'=-s,t'=1&s^2+c^2=1&s<=t&c<=1}]1=0".asFormula
    val t = TactixLibrary.implyR(1) & Approximator.taylorCircular("s".asVariable, "c".asVariable, Number(5))(1)


    val result = proveBy(f,t)
    result.subgoals.length shouldBe 1
    println(result.prettyString)
  })

  it should "approximate {s'=c, c'=s, t'=1} from c=1,s=0" in withMathematica(_ => {
    val f = "c=1 & s=0 & t=0->[{s'=c,c'=-s,t'=1}]1=0".asFormula
    val t = TactixLibrary.implyR(1) & Approximator.taylorCircular("s".asVariable, "c".asVariable, Number(5))(1)

    val result = proveBy(f,t)
    result.subgoals.length shouldBe 1
    println(result.prettyString)
  })

  it should "prove some of the high bounds on s and c" in withMathematica(_ => {
    val f = """c=1 & s=0 & t=0->[{s'=c,c'=-s,t'=1}](c>=1+-t^2/2+t^4/24+-t^6/720 &
              |s>=t+-t^3/6+t^5/120+-t^7/5040 &
              |c<=1+-t^2/2+t^4/24+-t^6/720+t^8/40320 &
              |s<=t+-t^3/6+t^5/120+-t^7/5040+t^9/362880)""".stripMargin.asFormula
    val t = TactixLibrary.implyR(1) & Approximator.taylorCircular("s".asVariable, "c".asVariable, Number(5))(1) & TactixLibrary.dW(1) & TactixLibrary.QE
    proveBy(f,t) shouldBe 'proved
  })

  ignore should "prove a bound in context" in withMathematica(_ => {
    val f = "c=1 & s=0 & t=0->[blah := something;][{s'=c,c'=-s,t'=1}](c>=1+-t^2/2+t^4/24+-t^6/720)".asFormula
    val t = TactixLibrary.implyR(1) & Approximator.taylorCircular("s".asVariable, "c".asVariable, Number(5))(1,1::Nil) & TactixLibrary.dW(1,1::Nil) & TactixLibrary.assignb(1) & TactixLibrary.QE //@todo the tactic that does this successively.
    proveBy(f,t) shouldBe 'proved
  })

  it should "prove initial bounds for cos" in withMathematica(_ => {
    val f = "c=1&s=0&t=0 -> [{s'=c,c'=-s,t'=1 & s^2 + c^2 = 1}]c <= 1".asFormula
    val t = TactixLibrary.implyR(1) & TactixLibrary.dW(1) & TactixLibrary.QE
    proveBy(f,t) shouldBe 'proved
  })

  it should "prove initial bounds for sin" in withMathematica(_ => {
    val f = "c=1&s=0&t=0 -> [{s'=c,c'=-s,t'=1&(true&s^2+c^2=1)&c<=1}]s<=t".asFormula
    val t = TactixLibrary.implyR(1) & TactixLibrary.dI()(1) & DebuggingTactics.debug("About to close", true)  & TactixLibrary.QE

    proveBy(f,t) shouldBe 'proved
  })

  "expApproximate" should "approximate e'=e" in withMathematica(_ => {
    val f = "t=0 & e=1 -> [{e'=e,t'=1 & e >= 1 & e >= 1 + t}]1=0".asFormula
    val t = TactixLibrary.implyR(1) & Approximator.expApproximate("e".asVariable, Number(10))(1)

    val result = proveBy(f,t)
    result.subgoals.length shouldBe 1
    println(result.prettyString)
  })

  it should "prove a bound on e'=e" in withMathematica(_ => {
    val f = "t=0 & e=1 -> [{e'=e,t'=1 & e >= 1}](e>=1+t+t^2/2+t^3/6+t^4/24+t^5/120+t^6/720+t^7/5040+t^8/40320+t^9/362880)".asFormula
    val t = TactixLibrary.implyR(1) & Approximator.expApproximate("e".asVariable, Number(10))(1) & DebuggingTactics.debug("here",true) & TactixLibrary.dW(1) & TactixLibrary.QE
    val result = proveBy(f,t)
    result shouldBe 'proved
  })

  it should "by able to prove first bound on e'=e by ODE" in withMathematica(_ => {
    val f = "t=0 & e=1 -> [{e'=e,t'=1}](e>=1)".asFormula
    val t = TactixLibrary.implyR(1) & TactixLibrary.ODE(1)
    proveBy(f,t) shouldBe 'proved
  })

  it should "prove a bound on e'=e without initial term" in withMathematica(_ => {
    val f = "t=0 & e=1 -> [{e'=e,t'=1}](e>=1+t+t^2/2+t^3/6+t^4/24+t^5/120+t^6/720+t^7/5040+t^8/40320+t^9/362880)".asFormula
    val t = TactixLibrary.implyR(1) & Approximator.expApproximate("e".asVariable, Number(10))(1) & TactixLibrary.dW(1) & TactixLibrary.QE
    proveBy(f,t) shouldBe 'proved
  })

  "Tactic pretty printer" should "properly print expApproximation tactics" taggedAs(KeYmaeraXTestTags.DeploymentTest) in {
    val t = Approximator.expApproximate("e".asVariable, Number(10))(1)
    val print = t.prettyString
    print shouldBe "expApproximation({`e`},{`10`},1)"
    //@todo check print of parse after patching DerivationInfo.
  }

  it should "properly print taylor approximation tactics" taggedAs(KeYmaeraXTestTags.DeploymentTest) in {
    val t = Approximator.taylorCircular("s".asVariable, "c".asVariable, Number(5))(1)
    val print = t.prettyString
    print shouldBe "taylorCircular({`s`},{`c`},{`5`},1)"
    //@todo check print of parse after patching DerivationInfo.
  }

  it should "properly print and parse top-level approximation tactic" taggedAs(KeYmaeraXTestTags.DeploymentTest) in {
    val t = Approximator.autoApproximate(Number(10))(1)
    val print = t.prettyString
    print shouldBe "autoApproximate({`10`},1)"
    print.asTactic shouldBe t
  }

  "autoApproximate" should "approximate exp" taggedAs(KeYmaeraXTestTags.DeploymentTest) in withMathematica(_ => {
    val f = "t=0 & e=1 -> [{e'=e,t'=1}](e>=1+t+t^2/2+t^3/6+t^4/24+t^5/120+t^6/720+t^7/5040+t^8/40320+t^9/362880)".asFormula
    val t = TactixLibrary.implyR(1) & Approximator.autoApproximate(Number(10))(1) & TactixLibrary.dW(1) & TactixLibrary.QE
    proveBy(f,t) shouldBe 'proved
  })

  it should "approximate sin/cos" taggedAs(KeYmaeraXTestTags.DeploymentTest) in withMathematica(_ => {
    val f = """c=1 & s=0 & t=0->[{s'=c,c'=-s,t'=1}](c>=1+-t^2/2+t^4/24+-t^6/720 &
              |s>=t+-t^3/6+t^5/120+-t^7/5040 &
              |c<=1+-t^2/2+t^4/24+-t^6/720+t^8/40320 &
              |s<=t+-t^3/6+t^5/120+-t^7/5040+t^9/362880)""".stripMargin.asFormula
    val t = TactixLibrary.implyR(1) & Approximator.autoApproximate(Number(5))(1) & TactixLibrary.dW(1) & TactixLibrary.QE
    proveBy(f,t) shouldBe 'proved

  })


  //@todo test some actual proofs.
}
