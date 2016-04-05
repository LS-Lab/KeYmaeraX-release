/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{OnAll, TheType}
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics.print
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import testHelper.ParserFactory._

import scala.language.postfixOps

/**
 * Tutorial test cases.
 *
 * @author Stefan Mitsch
 */
@SlowTest
class CpsWeekTutorial extends TacticTestBase {

  "Example 1" should "have 4 open goals for abstract invariant J(x,v)" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/01_robo1.kyx"))
    val tactic = implyR('R) & andL('R)*@TheType() & loop("J(x,v)".asFormula)('R) <(
      print("Base case") partial,
      print("Use case") partial,
      print("Step") & normalize & OnAll(diffSolve(None)('R) partial) partial
      )
    val result = proveBy(s, tactic)
    result.subgoals should have size 4
    result.subgoals.head.ante should contain only ("x!=m".asFormula, "b>0".asFormula)
    result.subgoals.head.succ should contain only "J(x,v)".asFormula
    result.subgoals(1).ante should contain only ("J(x,v)".asFormula, "b>0".asFormula)
    result.subgoals(1).succ should contain only "x!=m".asFormula
    result.subgoals(2).ante should contain only ("J(x_0,v_0)".asFormula, "b>0".asFormula, "t__0=0".asFormula, "true".asFormula)
    result.subgoals(2).succ should contain only "((true&t_>=0)&v=a*t_+v_0)&x=1/2*(a*t_^2+2*t_*v_0+2*x_0)->J(x,v)".asFormula
    //@todo where did SB(x,m) in succedent go?
    result.subgoals(3).ante should contain only ("J(x_0,v_0)".asFormula, "b>0".asFormula, "t__0=0".asFormula, "true".asFormula)
    result.subgoals(3).succ should contain only "((true&t_>=0)&v=-1*b*t_+v_0)&x=1/2*(-1*b*t_^2+2*t_*v_0+2*x_0)->J(x,v)".asFormula
  }

  it should "have 4 open goals for abstract invariant J(x,v) with master" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/01_robo1.kyx"))
    val result = proveBy(s, master())
    result.subgoals should have size 4
    result.subgoals.head.ante should contain only ("x!=m".asFormula, "b>0".asFormula)
    result.subgoals.head.succ should contain only "J(x,v)".asFormula
    result.subgoals(1).ante should contain only ("J(x,v)".asFormula, "b>0".asFormula)
    result.subgoals(1).succ should contain only "x!=m".asFormula
    result.subgoals(2).ante should contain only ("J(x_0,v_0)".asFormula, "b>0".asFormula, "t__0=0".asFormula,
      "true".asFormula, "x=1/2*(a*t_^2+2*t_*v_0+2*x_0)".asFormula, "v=a*t_+v_0".asFormula, "t_>=0".asFormula)
    result.subgoals(2).succ should contain only "J(x,v)".asFormula
    //@todo where did SB(x,m) in succedent go?
    result.subgoals(3).ante should contain only ("J(x_0,v_0)".asFormula, "b>0".asFormula, "t__0=0".asFormula,
      "true".asFormula, "x=1/2*(-1*b*t_^2+2*t_*v_0+2*x_0)".asFormula, "v=-1*b*t_+v_0".asFormula, "t_>=0".asFormula)
    result.subgoals(3).succ should contain only "J(x,v)".asFormula
  }

  "Example 2" should "have expected open goal and a counter example" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/02_robo2-justbrakenaive.kyx"))
    val result = proveBy(s, master())
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x_0<=m".asFormula, "b>0".asFormula, "t__0=0".asFormula,
      "v_0>=0".asFormula, "x=1/2*(-1*b*t_^2+2*t_*v_0+2*x_0)".asFormula, "v=-1*b*t_+v_0".asFormula, "v>=0".asFormula,
      "t_>=0".asFormula)
    result.subgoals.head.succ should contain only "x<=m".asFormula

    // counter example
    tool.findCounterExample(result.subgoals.head.toFormula).get.keySet should contain only ("b".asVariable,
      "x_0".asVariable, "t_".asVariable, "v_0".asVariable, "m".asVariable, "x".asVariable, "t__0".asVariable,
      "v".asVariable)
    // can't actually check cex values, may differ from run to run

    // cut in concrete values to get nicer CEX
    val cutFml = "x_0=1 & v_0=2 & m=x_0+3".asFormula
    val afterCut = proveBy(result.subgoals.head, cut(cutFml))
    afterCut.subgoals should have size 2
    afterCut.subgoals.head.ante should contain (cutFml)
    val cex = tool.findCounterExample(afterCut.subgoals.head.toFormula).get
    cex.keySet should contain only ("b".asVariable,
      "x_0".asVariable, "t_".asVariable, "v_0".asVariable, "m".asVariable, "x".asVariable, "t__0".asVariable,
      "v".asVariable)
    cex.get("x_0".asVariable) should contain ("1".asTerm)
    cex.get("v_0".asVariable) should contain ("2".asTerm)
    cex.get("m".asVariable) should contain ("4".asTerm)
  }

  "Motzkin" should "be provable with DI+DW" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/motzkin.kyx"))
    val tactic = implyR('R) & diffInvariant("x1^4*x2^2+x1^2*x2^4-3*x1^2*x2^2+1 <= c".asFormula)('R) & diffWeaken('R) & prop
    proveBy(s, tactic) shouldBe 'proved
  }

  "Self crossing" should "be provable with DI+DW" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/10-diffinv-self-crossing.kyx"))
    val tactic = implyR('R) & diffInvariant("x^2+x^3-y^2-c=0".asFormula)('R) & diffWeaken('R) & prop
    proveBy(s, tactic) shouldBe 'proved
  }



}
