/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{OnAll, TheType}
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics.{print,printIndexed}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.core.{DotTerm, Formula, SubstitutionPair, USubst}
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

  "Example 0" should "prove with abstract invariant J(x)" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/00_robosimple.kyx"))
    val tactic = implyR('R) & (andL('L)*) & loop("J(v)".asFormula)('R) <(
      skip,
      skip,
      print("Step") & normalize & OnAll(diffSolve(None)('R) partial) partial
      ) & US(USubst(SubstitutionPair(
            "J(v)".asFormula.replaceFree("v".asTerm, DotTerm), "v<=10".asFormula.replaceFree("v".asTerm, DotTerm))::Nil)) & OnAll(QE)

    proveBy(s, tactic) shouldBe 'proved
  }

  "Example 1" should "have 4 open goals for abstract invariant J(x,v)" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/01_robo1.kyx"))
    val tactic = implyR('R) & (andL('L)*) & loop("J(x,v)".asFormula)('R) <(
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

  it should "prove automatically with the correct conditions" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/01_robo1-full.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "prove with a manually written searchy tactic" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/01_robo1-full.kyx"))
    val tactic = implyR('R) & (andL('L)*) & loop("v^2<=2*b*(m-x)".asFormula)('R) <(
      print("Base case") & closeId,
      print("Use case") & QE,
      print("Step") & normalize & diffSolve(None)('R) & QE
      )
    proveBy(s, tactic) shouldBe 'proved
  }

  "Example 2" should "have expected open goal and a counter example" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/02_robo2-justbrakenaive.kyx"))
    val result = proveBy(s, master())
    result.isProved shouldBe false //@note This assertion is a soundness check!
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

  it should "find the braking condition" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/02_robo2-justbrakenaive.kyx"))
    val result = proveBy(s, master())
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x_0<=m".asFormula, "b>0".asFormula, "t__0=0".asFormula,
      "v_0>=0".asFormula, "x=1/2*(-1*b*t_^2+2*t_*v_0+2*x_0)".asFormula, "v=-1*b*t_+v_0".asFormula, "v>=0".asFormula,
      "t_>=0".asFormula)
    result.subgoals.head.succ should contain only "x<=m".asFormula

    val initCond = proveBy(result.subgoals.head, ToolTactics.partialQE)
    initCond.subgoals should have size 1
    initCond.subgoals.head.ante shouldBe empty
    initCond.subgoals.head.succ should contain only "v_0<=0|v_0>0&(t_<=0|t_>0&(((b<=0|(0 < b&b < t_^-1*v_0)&((m < x_0|(x_0<=m&m < 1/2*(-1*b*t_^2+2*t_*v_0+2*x_0))&((x < 1/2*(-1*b*t_^2+2*t_*v_0+2*x_0)|x=1/2*(-1*b*t_^2+2*t_*v_0+2*x_0)&((v < -1*b*t_+v_0|v=-1*b*t_+v_0&(t__0 < 0|t__0>0))|v>-1*b*t_+v_0))|x>1/2*(-1*b*t_^2+2*t_*v_0+2*x_0)))|m>=1/2*(-1*b*t_^2+2*t_*v_0+2*x_0)))|b=t_^-1*v_0&((m < x_0|(x_0<=m&m < 1/2*(-1*b*t_^2+2*t_*v_0+2*x_0))&((x < 1/2*(-1*b*t_^2+2*t_*v_0+2*x_0)|x=1/2*(-1*b*t_^2+2*t_*v_0+2*x_0)&((v < 0|v=0&(t__0 < 0|t__0>0))|v>0))|x>1/2*(-1*b*t_^2+2*t_*v_0+2*x_0)))|m>=1/2*(-1*b*t_^2+2*t_*v_0+2*x_0)))|b>t_^-1*v_0))".asFormula
    // explain in tutorial: mostly crap that violates our assumptions, but m>=... and b=t_^-1*v_0 look interesting -> transform

    val simpler = proveBy(initCond.subgoals.head, ToolTactics.transform("b=v_0/t_ & t_>0 & m>=1/2*(-1*b*t_^2+2*t_*v_0+2*x_0)".asFormula)(tool)(1))
    simpler.subgoals should have size 1
    simpler.subgoals.head.ante shouldBe empty
    simpler.subgoals.head.succ should contain only "b=v_0/t_ & t_>0 & m>=1/2*(-1*b*t_^2+2*t_*v_0+2*x_0)".asFormula

    // now let's transform once again and put in t_ = v_0/b
    val cond = proveBy(simpler.subgoals.head, ToolTactics.transform("b>0 & t_=v_0/b & v_0>0 & m>=x_0+v_0^2/(2*b)".asFormula)(tool)(1))
    cond.subgoals should have size 1
    cond.subgoals.head.ante shouldBe empty
    cond.subgoals.head.succ should contain only "b>0 & t_=v_0/b & v_0>0 & m>=x_0+v_0^2/(2*b)".asFormula
  }

  it should "prove braking automatically with the correct condition" in withMathematica { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/03_robo2-justbrake.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "find the acceleration condition" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/04_robo2-justaccnaive.kyx"))
    val result = proveBy(s, master())
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("A>=0".asFormula, "b>0".asFormula, "v_0^2<=2*b*(m-x_0)".asFormula,
      "ep>0".asFormula, "Q(x_0,v_0)".asFormula, "t_0=0".asFormula, "t__0=0".asFormula, "v_0>=0".asFormula, "0<=ep".asFormula,
      "x=1/2*(A*t_^2+2*t_*v_0+2*x_0)".asFormula, "v=A*t_+v_0".asFormula, "t=0+t_".asFormula, "t_>=0".asFormula,
      "v>=0".asFormula, "t<=ep".asFormula)
    result.subgoals.head.succ should contain only "v^2 <= 2*b*(m-x)".asFormula

    val initCond = proveBy(result.subgoals.head, hideL(-5, "Q(x_0,v_0)".asFormula) & ToolTactics.partialQE)
    initCond.subgoals should have size 1
    initCond.subgoals.head.ante shouldBe empty
    initCond.subgoals.head.succ should contain only "(t_ < 0|t_=0&(v_0<=0|v_0>0&((v < v_0|v=v_0&(ep<=0|ep>0&(b<=0|b>0&((x < 1/2*b^-1*(2*b*m+-1*v_0^2)|x=1/2*b^-1*(2*b*m+-1*v^2))|x>1/2*b^-1*(2*b*m+-1*v_0^2)))))|v>v_0)))|t_>0&((v_0 < 0|v_0=0&(v<=0|v>0&((t < t_|t=t_&((A < t_^-1*v|A=t_^-1*v&(ep < t|ep>=t&(b<=0|b>0&(((x<=1/2*b^-1*(2*b*m+-1*v^2)|(1/2*b^-1*(2*b*m+-1*v^2) < x&x < 1/2*b^-1*(2*b*m+A*b*t_^2))&((x_0 < 1/2*(-1*A*t_^2+2*x)|x_0=1/2*(-1*A*t_^2+2*x)&((t_0 < 0|t_0=0&(t__0 < 0|t__0>0))|t_0>0))|x_0>1/2*(-1*A*t_^2+2*x)))|x=1/2*b^-1*(2*b*m+A*b*t_^2)&((x_0 < m|x_0=m&((t_0 < 0|t_0=0&(t__0 < 0|t__0>0))|t_0>0))|x_0>m))|x>1/2*b^-1*(2*b*m+A*b*t_^2)))))|A>t_^-1*v))|t>t_)))|v_0>0&(v < v_0|v>=v_0&((t < t_|t=t_&((A < t_^-1*(v+-1*v_0)|A=t_^-1*(v+-1*v_0)&(ep < t|ep>=t&(b<=0|b>0&(((x<=1/2*b^-1*(2*b*m+-1*v^2)|(1/2*b^-1*(2*b*m+-1*v^2) < x&x < 1/2*b^-1*(2*b*m+A*b*t_^2+2*b*t_*v_0+-1*v_0^2))&((x_0 < 1/2*(-1*A*t_^2+-2*t_*v_0+2*x)|x_0=1/2*(-1*A*t_^2+-2*t_*v_0+2*x)&((t_0 < 0|t_0=0&(t__0 < 0|t__0>0))|t_0>0))|x_0>1/2*(-1*A*t_^2+-2*t_*v_0+2*x)))|x=1/2*b^-1*(2*b*m+A*b*t_^2+2*b*t_*v_0+-1*v_0^2)&((x_0 < 1/2*b^-1*(2*b*m+-1*v_0^2)|x_0=1/2*(-1*A*t_^2+-2*t_*v_0+2*x)&((t_0 < 0|t_0=0&(t__0 < 0|t__0>0))|t_0>0))|x_0>1/2*b^-1*(2*b*m+-1*v_0^2)))|x>1/2*b^-1*(2*b*m+A*b*t_^2+2*b*t_*v_0+-1*v_0^2)))))|A>t_^-1*(v+-1*v_0)))|t>t_)))".asFormula
    // wanted condition not immediately obvious, hence not tested
  }

  it should "prove acceleration automatically with the correct condition" in withMathematica { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/05_robo2-justacc.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "prove the full model" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/06_robo2-full.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  "A searchy tactic" should "prove both a simple and a complicated model" in withMathematica { implicit tool =>
    def tactic(j: Formula) = implyR('R) & (andL('L)*) & loop(j)('R) <(
      print("Base case") & closeId,
      print("Use case") & QE,
      print("Step") & normalize & OnAll(diffSolve(None)('R) & QE)
      )

    val simple = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/01_robo1-full.kyx"))
    proveBy(simple, tactic("v^2<=2*b*(m-x)".asFormula)) shouldBe 'proved

    val harder = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/06_robo2-full.kyx"))
    proveBy(harder, tactic("v^2<=2*b*(m-x)".asFormula)) shouldBe 'proved
  }

  "2D Car" should "be provable" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/07_robo3-full.kyx"))

    def di(a: String) = diffInvariant("dx^2+dy^2=1".asFormula, "t>=0".asFormula, s"v=old(v)+$a*t".asFormula,
      s"-t*(v-$a/2*t)<=x-old(x) & x-old(x)<=t*(v-$a/2*t)".asFormula,
      s"-t*(v-$a/2*t)<=y-old(y) & y-old(y)<=t*(v-$a/2*t)".asFormula)('R)

    val dw = exhaustiveEqR2L(hide=true)('Llast)*3 /* 3 old(...) in DI */ & (andL('L)*) &
      print("Before diffWeaken") & diffWeaken(1) & print("After diffWeaken")

    val tactic = implyR('R) & (andL('L)*) & loop("r!=0 & v>=0 & dx^2+dy^2=1 & (2*b*abs(mx-x)>v^2 | 2*b*abs(my-y)>v^2)".asFormula)('R) <(
      print("Base case") & QE,
      print("Use case") & QE,
      print("Step") & chase('R) & andR('R) <(
        allR('R) & implyR('R) & di("-b") & dw & QE,
        // in tutorial: only show braking branch, acceleration takes too long (needs abs and hiding and cuts etc.)
        allR('R)*2 & implyR('R) & allR('R)*2 & implyR('R) & allR('R) & implyR('R) & di("A") & dw & printIndexed("Bar") partial
        ) partial
      )
    val result = proveBy(s, tactic)
    result.subgoals should have size 1
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
