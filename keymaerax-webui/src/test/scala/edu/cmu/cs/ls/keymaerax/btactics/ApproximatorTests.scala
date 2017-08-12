/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core.Number
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
  * @author Nathan Fulton
  */
class ApproximatorTests extends TacticTestBase {
  "The approximator" should "approximation [{s'=c,c'=-s,t'=1}]1=1" in withMathematica(_ => {
    val f = "c=0 & s=1 & t=0->[{s'=c,c'=-s,t'=1&s^2+c^2=1&s<=t&c<=1}]1=1".asFormula
    val t = TactixLibrary.implyR(1) & Approximator.taylorCircular("s".asVariable, "c".asVariable, Number(5))(1)


    val result = proveBy(f,t)
    result.subgoals.length shouldBe 1
    println(result.prettyString)
  })

  it should "approximate e'=e" in withMathematica(_ => {
    val f = "t=0 & e=1 -> [{e'=e,t'=1 & e >= 1 + x}]1=1".asFormula
    val t = TactixLibrary.implyR(1) & Approximator.expApproximation("e".asVariable, Number(10))(1)

    val result = proveBy(f,t)
    result.subgoals.length shouldBe 1
    println(result.prettyString)
  })

}
