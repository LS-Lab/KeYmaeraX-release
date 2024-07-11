/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon.parser.BellePrettyPrinter
import org.keymaerax.core.Number
import org.keymaerax.infrastruct.Position
import org.keymaerax.parser.StringConverter._
import org.keymaerax.tagobjects.{DeploymentTest, TodoTest}
import org.scalatest.LoneElement._

/**
 * Tests the series expansion tactics.
 * @author
 *   Nathan Fulton
 */
class ApproximatorTests extends TacticTestBase {
  "circularApproximate approximator" should "approximate {s'=c, c'=s, t'=1} with some initial help." in
    withMathematica { _ =>
      val f = "c=1 & s=0 & t=0->[{s'=c,c'=-s,t'=1&s^2+c^2=1&s<=t&c<=1}]1=0".asFormula
      val t = TactixLibrary.implyR(1) & Approximator.circularApproximate("s".asVariable, "c".asVariable, Number(5))(1)

      val result = proveBy(f, t)
      result.subgoals.loneElement shouldBe
        "c=1&s=0&t=0, old=s^2+c^2 ==> [{s'=c,c'=-s,t'=1&(((((((((s^2+c^2=1&s<=t&c<=1)&s^2+c^2=old)&c>=1+-t^2/2)&s>=t+-t^3/6)&c<=1+-t^2/2+t^4/24)&s<=t+-t^3/6+t^5/120)&c>=1+-t^2/2+t^4/24+-t^6/720)&s>=t+-t^3/6+t^5/120+-t^7/5040)&c<=1+-t^2/2+t^4/24+-t^6/720+t^8/40320)&s<=t+-t^3/6+t^5/120+-t^7/5040+t^9/362880}]1=0"
          .asSequent
    }

  it should "FEATURE_REQUEST: approximate {s'=c, c'=s, t'=1} from c=1,s=0" taggedAs TodoTest in withMathematica(_ => {
    val f = "c=1 & s=0 & t=0->[{s'=c,c'=-s,t'=1}]1=0".asFormula
    val t = TactixLibrary.implyR(1) & Approximator.circularApproximate("s".asVariable, "c".asVariable, Number(5))(1)

    val result = proveBy(f, t)
    result.subgoals.length shouldBe 1
    println(result.prettyString)
  })

  it should "FEATURE_REQUEST: prove some of the high bounds on s and c" taggedAs TodoTest in withMathematica(_ => {
    val f = """c=1 & s=0 & t=0->[{s'=c,c'=-s,t'=1}](c>=1+-t^2/2+t^4/24+-t^6/720 &
              |s>=t+-t^3/6+t^5/120+-t^7/5040 &
              |c<=1+-t^2/2+t^4/24+-t^6/720+t^8/40320 &
              |s<=t+-t^3/6+t^5/120+-t^7/5040+t^9/362880)""".stripMargin.asFormula
    val t = TactixLibrary.implyR(1) & Approximator.circularApproximate("s".asVariable, "c".asVariable, Number(5))(1) &
      TactixLibrary.dW(1) & TactixLibrary.QE
    proveBy(f, t) shouldBe Symbol("proved")
  })

  ignore should "prove a bound in context" in withMathematica(_ => {
    val f = "c=1 & s=0 & t=0->[blah := something;][{s'=c,c'=-s,t'=1}](c>=1+-t^2/2+t^4/24+-t^6/720)".asFormula
    val t = TactixLibrary
      .implyR(1) & Approximator.circularApproximate("s".asVariable, "c".asVariable, Number(5))(1, 1 :: Nil) &
      TactixLibrary.dW(1, 1 :: Nil) & TactixLibrary.assignb(1) &
      TactixLibrary.QE // @todo the tactic that does this successively.
    proveBy(f, t) shouldBe Symbol("proved")
  })

  it should "prove initial bounds for cos" in withMathematica(_ => {
    val f = "c=1&s=0&t=0 -> [{s'=c,c'=-s,t'=1 & s^2 + c^2 = 1}]c <= 1".asFormula
    val t = TactixLibrary.implyR(1) & TactixLibrary.dW(1) & TactixLibrary.QE
    proveBy(f, t) shouldBe Symbol("proved")
  })

  it should "prove initial bounds for sin" in withMathematica(_ => {
    val f = "c=1&s=0&t=0 -> [{s'=c,c'=-s,t'=1&(true&s^2+c^2=1)&c<=1}]s<=t".asFormula
    val t = TactixLibrary.implyR(1) & TactixLibrary.dI()(1) & TactixLibrary.QE
    proveBy(f, t) shouldBe Symbol("proved")
  })

  "expApproximate" should "approximate e'=e restricted to e >= 1 & e >= 1 + t" in withMathematica(_ => {
    val f = "t=0 & e=1 -> [{e'=e,t'=1 & e >= 1 & e >= 1 + t}]1=0".asFormula
    val t = TactixLibrary.implyR(1) & Approximator.expApproximate("e".asVariable, Number(10))(1)

    val result = proveBy(f, t)
    result.subgoals.length shouldBe 1
  })

  it should "prove a bound on e'=e" in withMathematica(_ => {
    val f =
      "t=0 & e=1 -> [{e'=e,t'=1 & e >= 1}](e>=1+t+t^2/2+t^3/6+t^4/24+t^5/120+t^6/720+t^7/5040+t^8/40320+t^9/362880)"
        .asFormula
    val t = TactixLibrary.implyR(1) & Approximator.expApproximate("e".asVariable, Number(10))(1) & TactixLibrary.dW(1) &
      TactixLibrary.QE
    val result = proveBy(f, t)
    result shouldBe Symbol("proved")
  })

  it should "by able to prove first bound on e'=e by ODE" in withMathematica(_ => {
    val f = "t=0 & e=1 -> [{e'=e,t'=1}](e>=1)".asFormula
    val t = TactixLibrary.implyR(1) & TactixLibrary.ODE(1)
    proveBy(f, t) shouldBe Symbol("proved")
  })

  it should "prove a bound on e'=e without initial term" in withMathematica(_ => {
    val f =
      "t=0 & e=1 -> [{e'=e,t'=1}](e>=1+t+t^2/2+t^3/6+t^4/24+t^5/120+t^6/720+t^7/5040+t^8/40320+t^9/362880)".asFormula
    val t = TactixLibrary.implyR(1) & Approximator.expApproximate("e".asVariable, Number(10))(1) & TactixLibrary.dW(1) &
      TactixLibrary.QE
    proveBy(f, t) shouldBe Symbol("proved")
  })

  ignore should "prove in ctx a bound on e'=e without initial term" in withMathematica(_ => {
    val f = "t=0 & e=1 -> [z:=0;][{e'=e,t'=1}](e>=1+t+t^2/2+t^3/6+t^4/24+t^5/120+t^6/720+t^7/5040+t^8/40320+t^9/362880)"
      .asFormula
    val t = TactixLibrary.implyR(1) & Approximator.expApproximate("e".asVariable, Number(10))(1) &
      TactixLibrary.assignb(1) & TactixLibrary.dW(1) & TactixLibrary.QE
    proveBy(f, t) shouldBe Symbol("proved")
  })

  "Tactic pretty printer" should "properly print expApproximate tactics" taggedAs DeploymentTest in {
    val t = Approximator.expApproximate("e".asVariable, Number(10))(1)
    val print = t.prettyString
    print shouldBe """expApproximate("e", "10", 1)"""
    print.asTactic shouldBe t
  }

  it should "properly print taylor approximation tactics" taggedAs DeploymentTest in {
    val t = Approximator.circularApproximate("s".asVariable, "c".asVariable, Number(5))(1)
    val print = BellePrettyPrinter(t)
    print should equal("""circularApproximate("s","c","5",1)""")(after being whiteSpaceRemoved)
    print.asTactic shouldBe t
    // @todo check print of parse after patching DerivationInfo.
  }

  it should "properly print and parse top-level autoApproximate tactic" taggedAs DeploymentTest in {
    val t = Approximator.autoApproximate(Number(10))(1)
    val print = t.prettyString
    print shouldBe """autoApproximate("10", 1)"""
    print.asTactic shouldBe t
  }

  "autoApproximate" should "approximate exp" taggedAs DeploymentTest in withMathematica(_ => {
    val f =
      "t=0 & e=1 -> [{e'=e,t'=1}](e>=1+t+t^2/2+t^3/6+t^4/24+t^5/120+t^6/720+t^7/5040+t^8/40320+t^9/362880)".asFormula
    val t = TactixLibrary.implyR(1) & Approximator.autoApproximate(Number(10))(1) & TactixLibrary.dW(1) &
      TactixLibrary.QE
    proveBy(f, t) shouldBe Symbol("proved")
  })

  it should "FEATURE_REQUEST: approximate sin/cos" taggedAs TodoTest in withMathematica(_ => {
    val f = """c=1 & s=0 & t=0->[{s'=c,c'=-s,t'=1}](c>=1+-t^2/2+t^4/24+-t^6/720 &
              |s>=t+-t^3/6+t^5/120+-t^7/5040 &
              |c<=1+-t^2/2+t^4/24+-t^6/720+t^8/40320 &
              |s<=t+-t^3/6+t^5/120+-t^7/5040+t^9/362880)""".stripMargin.asFormula
    val t = TactixLibrary.implyR(1) & Approximator.autoApproximate(Number(5))(1) & TactixLibrary.dW(1) &
      TactixLibrary.QE
    proveBy(f, t) shouldBe Symbol("proved")

  })

  // region In-context unit tests

  "In-context proofs" should "prove cut in context using ceat" ignore withMathematica(_ => {
    val f = "[{x'=v,v'=a&1=1}](false)".asFormula

    val fact = Approximator.dcInCtx(f, "1+1=2".asFormula, TactixLibrary.dI()(1))

    println(fact.prettyString)

    val result = proveBy("[{x'=v,v'=a&1=1}](false)".asFormula, TactixLibrary.CEat(fact)(1))
    println(result)
    result.subgoals.length shouldBe 1
  })

  it should "prove cut in context using ceat with helper method" ignore withMathematica(_ => {
    val f = "[{x'=v,v'=a&1=1}](false)".asFormula
    val cut = "1+1=2".asFormula
    val cutProof = TactixLibrary.dI()(1)
    proveBy(f, Approximator.extendEvDomAndProve(f, cut, cutProof)(1)).subgoals.length shouldBe 1
  })

  "dC" should "work in context" ignore withMathematica(_ => {
    val f = "[z:=12;][{x'=v,v'=a&1=1}](false)".asFormula
    val cut = "1+1=2".asFormula
    println(proveBy(
      f,
      TactixLibrary.dC(cut)(Position(1, 1 :: Nil)) <
        (
          TactixLibrary.nil,
          TactixLibrary.dI()(Position(1, 1 :: Nil)) & (TactixLibrary.QE | (TactixLibrary.G(1) & TactixLibrary.QE)),
        ),
    ))
  })
  // endregion
  // @todo test some actual proofs.
}
