/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core.Number
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

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

  it should "prove one of the high bounds on s and c" in withMathematica(_ => {
    val f = """c=1 & s=0 & t=0->[{s'=c,c'=-s,t'=1}](c>=1+-t^2/2+t^4/24+-t^6/720 &
              |s>=t+-t^3/6+t^5/120+-t^7/5040 &
              |c<=1+-t^2/2+t^4/24+-t^6/720+t^8/40320 &
              |s<=t+-t^3/6+t^5/120+-t^7/5040+t^9/362880)""".asFormula
    val t = TactixLibrary.implyR(1) & Approximator.taylorCircular("s".asVariable, "c".asVariable, Number(5))(1) & TactixLibrary.dW(1) & TactixLibrary.QE //@todo the tactic that does this successively.
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

  "expApproximation" should "approximate e'=e" in withMathematica(_ => {
    val f = "t=0 & e=1 -> [{e'=e,t'=1 & e >= 1 + x}]1=0".asFormula
    val t = TactixLibrary.implyR(1) & Approximator.expApproximation("e".asVariable, Number(10))(1)

    val result = proveBy(f,t)
    result.subgoals.length shouldBe 1
    println(result.prettyString)
  })

  "Tactic pretty printer" should "properly print expApproximation tactics" in {
    val t = Approximator.expApproximation("e".asVariable, Number(10))(1)
    val print = t.prettyString
    print shouldBe "expApproximation({`e`},{`10`},1)"
    //@todo check preint of parse after patching DerivationInfo.
  }

  it should "properly print taylor approximation tactics" in {
    val t = Approximator.taylorCircular("s".asVariable, "c".asVariable, Number(5))(1)
    val print = t.prettyString
    print shouldBe "taylorCircular({`s`},{`c`},{`5`},1)"
    //@todo check preint of parse after patching DerivationInfo.
  }

  //@todo test some actual proofs.
}
