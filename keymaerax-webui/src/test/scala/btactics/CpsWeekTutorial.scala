/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.bellerophon.OnAll
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics.{print, printIndexed}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.core.{DotTerm, Formula, SubstitutionPair, USubst}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser
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

  "Example 0" should "prove with abstract invariant J(x)" in withMathematica { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/00_robosimple.kyx"))
    val tactic = implyR('R) & (andL('L)*) & loop("J(v)".asFormula)('R) <(
      skip,
      skip,
      print("Step") & normalize & OnAll(diffSolve('R) partial) partial
      ) & US(USubst(SubstitutionPair(
            "J(v)".asFormula.replaceFree("v".asTerm, DotTerm()), "v<=10".asFormula.replaceFree("v".asTerm, DotTerm()))::Nil)) & OnAll(QE)

    proveBy(s, tactic) shouldBe 'proved
  }

  "Example 1" should "have 4 open goals for abstract invariant J(x,v)" in withMathematica { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/01_robo1.kyx"))
    val tactic = implyR('R) & (andL('L)*) & loop("J(x,v)".asFormula)('R) <(
      print("Base case"),
      print("Use case"),
      print("Step") & normalize & print("Foo") & OnAll(diffSolve('R))
      )
    val result = proveBy(s, tactic)
    result.subgoals should have size 4
    result.subgoals.head.ante should contain only ("x!=m".asFormula, "b>0".asFormula)
    result.subgoals.head.succ should contain only "J(x,v)".asFormula
    result.subgoals(1).ante should contain only ("J(x,v)".asFormula, "b>0".asFormula)
    result.subgoals(1).succ should contain only "x!=m".asFormula
    result.subgoals(2).ante should contain only ("J(x,v)".asFormula, "b>0".asFormula)
    result.subgoals(2).succ should contain only ("\\forall t_ (t_>=0 -> J(a/2*t_^2+v*t_+x,a*t_+v))".asFormula, "SB(x,m)".asFormula)
    result.subgoals(3).ante should contain only ("J(x,v)".asFormula, "b>0".asFormula)
    result.subgoals(3).succ should contain only " \\forall t_ (t_>=0 -> J((-b)/2*t_^2+v*t_+x,(-b)*t_+v))".asFormula
  }

  it should "have 4 open goals for abstract invariant J(x,v) with master" in withMathematica { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/01_robo1.kyx"))
    val result = proveBy(s, master())
    result.subgoals should have size 4
    result.subgoals.head.ante should contain only ("x!=m".asFormula, "b>0".asFormula)
    result.subgoals.head.succ should contain only "J(x,v)".asFormula
    result.subgoals(1).ante should contain only ("J(x,v)".asFormula, "b>0".asFormula)
    result.subgoals(1).succ should contain only "x!=m".asFormula
    result.subgoals(2).ante should contain only ("J(x,v)".asFormula, "b>0".asFormula, "t_>=0".asFormula)
    result.subgoals(2).succ should contain only ("J(a/2*t_^2+v*t_+x,a*t_+v)".asFormula, "SB(x,m)".asFormula)
    result.subgoals(3).ante should contain only ("J(x,v)".asFormula, "b>0".asFormula, "t_>=0".asFormula)
    result.subgoals(3).succ should contain only "J((-b)/2*t_^2+v*t_+x,(-b)*t_+v)".asFormula
  }

  it should "prove automatically with the correct conditions" in withMathematica { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/01_robo1-full.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "prove with a manually written searchy tactic" in withMathematica { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/01_robo1-full.kyx"))
    val tactic = implyR('R) & (andL('L)*) & loop("v^2<=2*b*(m-x)".asFormula)('R) <(
      print("Base case") & closeId,
      print("Use case") & QE,
      print("Step") & normalize & diffSolve('R) & QE
      )
    proveBy(s, tactic) shouldBe 'proved
  }

  it should "stop after ODE to let users inspect a counterexample with false speed sb condition" in withMathematica { _ =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/cpsweek/01_robo1-falsespeedsb.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/cpsweek/01_robo1-falsespeedsb.kyt")).mkString)
    val result = proveBy(KeYmaeraXProblemParser(modelContent), tactic)
    result.subgoals should have size 2
  }

  "Example 2" should "have expected open goal and a counter example" in withMathematica { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/02_robo2-justbrakenaive.kyx"))
    val result = proveBy(s, master())
    result.isProved shouldBe false //@note This assertion is a soundness check!
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x<=m".asFormula, "b>0".asFormula, "t_>=0".asFormula,
      "\\forall s_ (0<=s_&s_<=t_ -> (-b)*s_+v>=0)".asFormula)
    result.subgoals.head.succ should contain only "(-b)/2*t_^2+v*t_+x <= m".asFormula

    // counter example
    tool.findCounterExample(result.subgoals.head.toFormula).get.keySet should contain only ("b".asVariable,
      "x".asVariable, "v".asVariable, "m".asVariable, "t_".asVariable, "s_".asVariable)
    // can't actually check cex values, may differ from run to run

    // cut in concrete values to get nicer CEX
    val cutFml = "x=1 & v=2 & m=x+3".asFormula
    val afterCut = proveBy(result.subgoals.head, cut(cutFml))
    afterCut.subgoals should have size 2
    afterCut.subgoals.head.ante should contain (cutFml)
    val cex = tool.findCounterExample(afterCut.subgoals.head.toFormula).get
    cex.keySet should contain only ("b".asVariable, "x".asVariable, "v".asVariable, "m".asVariable, "t_".asVariable, "s_".asVariable)
    cex.get("x".asVariable) should contain ("1".asTerm)
    cex.get("v".asVariable) should contain ("2".asTerm)
    cex.get("m".asVariable) should contain ("4".asTerm)
  }

  it should "find the braking condition" in withMathematica { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/02_robo2-justbrakenaive.kyx"))
    val result = proveBy(s, master())
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x<=m".asFormula, "b>0".asFormula, "t_>=0".asFormula,
      "\\forall s_ (0<=s_&s_<=t_ -> (-b)*s_+v>=0)".asFormula)
    result.subgoals.head.succ should contain only "(-b)/2*t_^2+v*t_+x <= m".asFormula

    val initCond = proveBy(result.subgoals.head, TactixLibrary.partialQE)
    initCond.subgoals should have size 1
    initCond.subgoals.head.ante shouldBe empty
    initCond.subgoals.head.succ should contain only "v<=0|v>0&(t_<=0|t_>0&((b<=0|(0 < b&b<=t_^-1*v)&(m < x|m>=1/2*(-1*b*t_^2+2*t_*v+2*x)))|b>t_^-1*v))".asFormula
    // explain in tutorial: mostly crap that violates our assumptions, but m>=... and b=t_^-1*v_0 look interesting -> transform

    val simpler = proveBy(initCond.subgoals.head, TactixLibrary.transform("b=v/t_ & t_>0 & m >= -b/2*t_^2+v*t_+x".asFormula)(1))
    simpler.subgoals should have size 1
    simpler.subgoals.head.ante shouldBe empty
    simpler.subgoals.head.succ should contain only "b=v/t_ & t_>0 & m >= -b/2*t_^2+v*t_+x".asFormula

    // now let's transform once again and put in t_ = v/b
    val cond = proveBy(simpler.subgoals.head, TactixLibrary.transform("b>0 & t_=v/b & v>0 & m-x >= v^2/(2*b)".asFormula)(1))
    cond.subgoals should have size 1
    cond.subgoals.head.ante shouldBe empty
    cond.subgoals.head.succ should contain only "b>0 & t_=v/b & v>0 & m-x >= v^2/(2*b)".asFormula
  }

  it should "prove braking automatically with the correct condition" in withMathematica { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/03_robo2-justbrake.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "find the acceleration condition" in withMathematica { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/04_robo2-justaccnaive.kyx"))
    val result = proveBy(s, master())
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("A>=0".asFormula, "b>0".asFormula, "v^2<=2*b*(m-x)".asFormula,
      "ep>0".asFormula, "Q(x,v)".asFormula, "t=0".asFormula, "t_>=0".asFormula, "\\forall s_ (0<=s_&s_<=t_ -> A*s_+v>=0 & s_+0<=ep)".asFormula)
    result.subgoals.head.succ should contain only "(A*t_+v)^2 <= 2*b*(m-(A/2*t_^2+v*t_+x))".asFormula

    val initCond = proveBy(result.subgoals.head, hideL(-5, "Q(x,v)".asFormula) & TactixLibrary.partialQE)
    initCond.subgoals should have size 1
    initCond.subgoals.head.ante shouldBe empty
    initCond.subgoals.head.succ should contain only "(A < 0|A=0&(b<=0|b>0&(v<=0|v>0&(t_<=0|t_>0&(ep < t_|ep>=t_&((t < 0|t=0&(m < 1/2*b^-1*(v^2+2*b*x)|m>=1/2*b^-1*(2*b*t_*v+v^2+2*b*x)))|t>0))))))|A>0&(b<=0|b>0&((v < 0|v=0&(t_<=0|t_>0&(ep < t_|ep>=t_&((t < 0|t=0&(m < x|m>=1/2*b^-1*(A^2*t_^2+A*b*t_^2+2*b*x)))|t>0))))|v>0&(t_<=0|t_>0&(ep < t_|ep>=t_&((t < 0|t=0&(m < 1/2*b^-1*(v^2+2*b*x)|m>=1/2*b^-1*(A^2*t_^2+A*b*t_^2+2*A*t_*v+2*b*t_*v+v^2+2*b*x)))|t>0)))))".asFormula

    // now get rid of stuff that violates our assumptions and transform into nicer shape
    val simpler = proveBy(initCond.subgoals.head, TactixLibrary.transform("b>0 & A>=0 & t_>=0 & m>=1/2*b^-1*(A^2*t_^2+A*b*t_^2+2*A*t_*v+2*b*t_*v+v^2+2*b*x)".asFormula)(1))
    simpler.subgoals should have size 1
    simpler.subgoals.head.ante shouldBe empty
    simpler.subgoals.head.succ should contain only "b>0 & A>=0 & t_>=0 & m>=1/2*b^-1*(A^2*t_^2+A*b*t_^2+2*A*t_*v+2*b*t_*v+v^2+2*b*x)".asFormula

    val cond = proveBy(simpler.subgoals.head, TactixLibrary.transform("b>0 & A>=0 & t_>=0 & m-x >= v^2/(2*b)+(A/b+1)*(A/2*t_^2 + v*t_)".asFormula)(1))
    cond.subgoals should have size 1
    cond.subgoals.head.ante shouldBe empty
    cond.subgoals.head.succ should contain only "b>0 & A>=0 & t_>=0 & m-x >= v^2/(2*b)+(A/b+1)*(A/2*t_^2 + v*t_)".asFormula
  }

  it should "prove acceleration automatically with the correct condition" in withMathematica { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/05_robo2-justacc.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "prove the full model" in withMathematica { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/06_robo2-full.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "be provable from parsed tactic" in withMathematica { _ => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/cpsweek/06_robo2-full.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/cpsweek/06_robo2-full.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable from parsed tactic with Z3" in withZ3 { _ => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/cpsweek/06_robo2-full.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/cpsweek/06_robo2-full.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "find a hint for SB from parsed tactic" in withMathematica { _ =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/cpsweek/06_robo2-fullnaive.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/cpsweek/06_robo2-fullnaive.kyt")).mkString)
    val result = proveBy(KeYmaeraXProblemParser(modelContent), tactic)
    result.subgoals should have size 2
    //unsimplified
    result.subgoals.last.succ should contain only "(x < 0&((t < 0&(ep<=0|ep>0&((v < 0|v=0&(A<=0|A>0&(b<=0|b>0&(m < x|m>=1/2*(A*ep^2+-2*A*ep*t+A*t^2+2*x)))))|v>0&(A < 0|A>=0&(b<=0|b>0&(m < x|m>=1/2*(A*ep^2+-2*A*ep*t+A*t^2+2*ep*v+-2*t*v+2*x))))))|t=0&(ep<=0|ep>0&((v < 0|v=0&(A<=0|A>0&(b<=0|b>0&(m < x|m>=1/2*(A*ep^2+2*x)))))|v>0&(A < 0|A>=0&(b<=0|b>0&(m < x|m>=1/2*(A*ep^2+2*ep*v+2*x)))))))|t>0&(ep<=t|ep>t&((v < 0|v=0&(A<=0|A>0&(b<=0|b>0&(m < x|m>=1/2*(A*ep^2+-2*A*ep*t+A*t^2+2*x)))))|v>0&(A < 0|A>=0&(b<=0|b>0&(m < x|m>=1/2*(A*ep^2+-2*A*ep*t+A*t^2+2*ep*v+-2*t*v+2*x)))))))|x=0&(t<=0&(ep<=0|ep>0&((v < 0|v=0&(A<=0|A>0&(b<=0|b>0&(m < 0|m>=1/2*(A*ep^2+-2*A*ep*t+A*t^2)))))|v>0&(A < 0|A>=0&(b<=0|b>0&(m < 0|m>=1/2*(A*ep^2+-2*A*ep*t+A*t^2+2*ep*v+-2*t*v))))))|t>0&(ep<=t|ep>t&((v < 0|v=0&(A<=0|A>0&(b<=0|b>0&(m < 0|m>=1/2*(A*ep^2+-2*A*ep*t+A*t^2)))))|v>0&(A < 0|A>=0&(b<=0|b>0&(m < 0|m>=1/2*(A*ep^2+-2*A*ep*t+A*t^2+2*ep*v+-2*t*v))))))))|x>0&(t<=0&(ep<=0|ep>0&((v < 0|v=0&(A<=0|A>0&(b<=0|b>0&(m < x|m>=1/2*(A*ep^2+-2*A*ep*t+A*t^2+2*x)))))|v>0&(A < 0|A>=0&(b<=0|b>0&(m < x|m>=1/2*(A*ep^2+-2*A*ep*t+A*t^2+2*ep*v+-2*t*v+2*x))))))|t>0&((ep < t|ep=t&((v < 0|v=0&(A<=0|A>0&(b<=0|b>0&((m < x|m=1/2*(A*ep^2+-2*A*ep*t+A*t^2+2*x))|m>x))))|v>0&(A < 0|A>=0&(b<=0|b>0&((m < x|m=1/2*(A*ep^2+-2*A*ep*t+A*t^2+2*ep*v+-2*t*v+2*x))|m>x)))))|ep>t&((v < 0|v=0&(A<=0|A>0&(b<=0|b>0&(m < x|m>=1/2*(A*ep^2+-2*A*ep*t+A*t^2+2*x)))))|v>0&(A < 0|A>=0&(b<=0|b>0&(m < x|m>=1/2*(A*ep^2+-2*A*ep*t+A*t^2+2*ep*v+-2*t*v+2*x)))))))".asFormula
    //@todo simplify with transform
  }

  "A searchy tactic" should "prove both a simple and a complicated model" in withMathematica { _ =>
    def tactic(j: Formula) = implyR('R) & (andL('L)*) & loop(j)('R) <(
      print("Base case") & closeId,
      print("Use case") & QE,
      print("Step") & normalize & OnAll(diffSolve('R) & QE)
      )

    val simple = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/01_robo1-full.kyx"))
    proveBy(simple, tactic("v^2<=2*b*(m-x)".asFormula)) shouldBe 'proved

    val harder = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/06_robo2-full.kyx"))
    proveBy(harder, tactic("v^2<=2*b*(m-x)".asFormula)) shouldBe 'proved
  }

  "2D Car" should "be provable" in withMathematica { _ =>
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

  it should "be provable from parsed tactic" in withMathematica { _ => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/cpsweek/07_robo3-full.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/cpsweek/07_robo3-full.kyt")).mkString)
    val result = db.proveBy(modelContent, tactic)
    result.subgoals should have size 1
  }}

  it should "be provable from parsed tactic with Z3" in withZ3 { _ => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/cpsweek/07_robo3-full.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/cpsweek/07_robo3-full.kyt")).mkString)
    val result = db.proveBy(modelContent, tactic)
    result.subgoals should have size 1
  }}

  "Motzkin" should "be provable with DI+DW" in withMathematica { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/motzkin.kyx"))
    val tactic = implyR('R) & diffInvariant("x1^4*x2^2+x1^2*x2^4-3*x1^2*x2^2+1 <= c".asFormula)('R) & diffWeaken('R) & prop
    proveBy(s, tactic) shouldBe 'proved
  }

  it should "be provable from parsed tactic" in withMathematica { _ => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/cpsweek/motzkin.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/cpsweek/motzkin.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable from parsed tactic Z3" in withZ3 { _ => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/cpsweek/motzkin.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/cpsweek/motzkin.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  "Damped oscillator" should "be provable with DI+DW" in withMathematica { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/08_dampedosc.kyx"))
    val tactic = implyR('R) & diffInd()('R)
    proveBy(s, tactic) shouldBe 'proved
  }

  it should "be provable from parsed tactic" in withMathematica { _ => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/cpsweek/08_dampedosc.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/cpsweek/08_dampedosc.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable from parsed tactic with Z3" in withZ3 { _ => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/cpsweek/08_dampedosc.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/cpsweek/08_dampedosc.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  "Self crossing" should "be provable with DI+DW" in withMathematica { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/10-diffinv-self-crossing.kyx"))
    val tactic = implyR('R) & diffInvariant("x^2+x^3-y^2-c=0".asFormula)('R) & diffWeaken('R) & prop
    proveBy(s, tactic) shouldBe 'proved
  }

}
