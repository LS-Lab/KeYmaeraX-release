/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.btactics.{DebuggingTactics, ModelPlex, SimplifierV2, TacticTestBase}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.language.postfixOps

/**
  * Tests the test synthesis tactics.
  * @author Stefan Mitsch
  */
class TestSynthesisTests extends TacticTestBase {

  "Test synthesis" should "generate test cases without safety margin" in withMathematica { tool =>
    val (modelplexInput, assumptions) = ModelPlex.createMonitorSpecificationConjecture(
      "true -> [x:=*; ?-3<=x&x<=5;]x>=-3".asFormula, Variable("x"))

    val monitor = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1) &
      DebuggingTactics.print("After chase") & ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1) &
      DebuggingTactics.print("After Opt. 1")
      & SimplifierV2.simpTac(1)).subgoals.head.succ.head

    val ts = new TestSynthesis(tool)
    val amount = 100
    // search for sunshine test case values (initial+expected)
    val testConfig = ts.synthesizeTestConfig(monitor, amount, Some(20))
    testConfig should have size amount
    testConfig.foreach(_.keys.map({case v: Variable => v case FuncOf(fn, _) => fn})
      should contain theSameElementsAs StaticSemantics.symbols(monitor))

    // compute safety margin of test case
    val safetyMargins = testConfig.map(ts.synthesizeSafetyMarginCheck(monitor, _))
    safetyMargins.foreach({case Number(i) => i.doubleValue should (be >= 0.0 and be <= 4.0)})
  }

  it should "generate test cases with safety margin in some range" in withMathematica { tool =>
    val (modelplexInput, assumptions) = ModelPlex.createMonitorSpecificationConjecture(
      "true -> [x:=*; ?-3<=x&x<=5;]x>=-3".asFormula, Variable("x"))

    val monitor = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1) &
      DebuggingTactics.print("After chase") & ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1) &
      DebuggingTactics.print("After Opt. 1")
      & SimplifierV2.simpTac(1)).subgoals.head.succ.head

    val ts = new TestSynthesis(tool)
    val amount = 100
    val range@(Number(lower), Number(upper)) = (Number(0), Number(1))
    // search for sunshine test case values (initial+expected)
    val testConfig = ts.synthesizeTestConfig(monitor, amount, Some(20), Some(range))
    testConfig should have size amount
    testConfig.foreach(_.keys.map({case v: Variable => v case FuncOf(fn, _) => fn})
      should contain theSameElementsAs StaticSemantics.symbols(monitor))

    // compute safety margin of test case
    val safetyMargins = testConfig.map(ts.synthesizeSafetyMarginCheck(monitor, _))
    safetyMargins.foreach({case Number(i) => i should (be >= lower and be <= upper)})
  }

  it should "generate no tests when safety margin range is invalid" in withMathematica { tool =>
    val (modelplexInput, assumptions) = ModelPlex.createMonitorSpecificationConjecture(
      "true -> [x:=2;]x>=2".asFormula, Variable("x"))

    val monitor = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1) &
      DebuggingTactics.print("After chase") & ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1) &
      DebuggingTactics.print("After Opt. 1")
      & SimplifierV2.simpTac(1)).subgoals.head.succ.head

    val ts = new TestSynthesis(tool)
    val amount = 5
    // invalid range, all compliant tests for x:=2 have margin 0
    val range = (Number(-2), Number(-1))
    // search for sunshine test case values (initial+expected)
    val testConfig = ts.synthesizeTestConfig(monitor, amount, Some(20), Some(range))
    testConfig should have size 0
  }

  it should "find the maximum safety margin range" in withMathematica { tool =>
    val (modelplexInput, assumptions) = ModelPlex.createMonitorSpecificationConjecture(
      "true -> [x:=*; ?-3<=x&x<=5;]x>=-3".asFormula, Variable("x"))

    val monitor = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1) &
      DebuggingTactics.print("After chase") & ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1) &
      DebuggingTactics.print("After Opt. 1")
      & SimplifierV2.simpTac(1)).subgoals.head.succ.head

    val ts = new TestSynthesis(tool)
    val (Number(lower), Number(upper)) = ts.getSafetyRange(monitor)
    // numeric evaluation doesn't get it exactly right
    lower.doubleValue should be (0.0 +- 0.1)
    upper.doubleValue should be (4.0 +- 0.1)
  }

  //@todo cannot reparse number 1.5E-14
  it should "find the maximum even when safety margin range is a point" ignore withMathematica { tool =>
    val (modelplexInput, assumptions) = ModelPlex.createMonitorSpecificationConjecture(
      "true -> [x:=2;]x>=2".asFormula, Variable("x"))

    val monitor = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1) &
      DebuggingTactics.print("After chase") & ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1) &
      DebuggingTactics.print("After Opt. 1")
      & SimplifierV2.simpTac(1)).subgoals.head.succ.head

    val ts = new TestSynthesis(tool)
    val (Number(lower), Number(upper)) = ts.getSafetyRange(monitor)
    // numeric evaluation doesn't get it exactly right
    lower.doubleValue should be (0.0 +- 0.1)
    upper.doubleValue should be (0.0 +- 0.1)
  }

}
