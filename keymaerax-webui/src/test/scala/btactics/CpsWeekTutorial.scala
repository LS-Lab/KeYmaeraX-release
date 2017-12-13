/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.bellerophon.OnAll
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics.print
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.core.{DotTerm, Formula, Function, Real, SubstitutionPair, USubst, Unit}
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXArchiveParser, KeYmaeraXProblemParser}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import testHelper.ParserFactory._

import scala.language.postfixOps
import org.scalatest.LoneElement._

/**
 * Tutorial test cases.
 *
 * @author Stefan Mitsch
 */
@SlowTest
class CpsWeekTutorial extends TacticTestBase {

  "Example 0" should "prove with abstract invariant J(x)" in withQE { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/00_robosimple.kyx"))
    val tactic = implyR('R) & (andL('L)*) & loop("J(v)".asFormula)('R) <(
      skip,
      skip,
      print("Step") & normalize & OnAll(solve('R) partial) partial
      ) & US(USubst(SubstitutionPair(
            "J(v)".asFormula.replaceFree("v".asTerm, DotTerm()), "v<=10".asFormula.replaceFree("v".asTerm, DotTerm()))::Nil)) & OnAll(QE)

    proveBy(s, tactic) shouldBe 'proved
  }

  "Example 1" should "have 4 open goals for abstract invariant J(x,v)" in withQE { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/01_robo1.kyx"))
    val tactic = implyR('R) & (andL('L)*) & loop("J(x,v)".asFormula)('R) <(
      print("Base case"),
      print("Use case"),
      print("Step") & normalize & OnAll(solve('R))
      )
    val result = proveBy(s, tactic)
    result.subgoals should have size 4
    result.subgoals(0) shouldBe "x!=m(), b()>0 ==> J(x,v)".asSequent
    result.subgoals(1) shouldBe "J(x,v), b()>0 ==> x!=m()".asSequent
    result.subgoals(2) shouldBe "J(x,v), b()>0 ==> \\forall t_ (t_>=0 -> J(a/2*t_^2+v*t_+x,a*t_+v)), SB(x,m())".asSequent
    result.subgoals(3) shouldBe "J(x,v), b()>0 ==> \\forall t_ (t_>=0 -> J((-b())/2*t_^2+v*t_+x,(-b())*t_+v))".asSequent
  }

  it should "have 4 open goals for abstract invariant J(x,v) with master" in withQE { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/01_robo1.kyx"))
    val result = proveBy(s, master(keepQEFalse=false))
    result.subgoals should have size 4
    result.subgoals(0) shouldBe "x!=m(), b()>0 ==> J(x,v)".asSequent
    result.subgoals(1) shouldBe "J(x,v), b()>0 ==> x!=m()".asSequent
    result.subgoals(2) shouldBe "J(x,v), b()>0, t_>=0 ==> SB(x,m()), J(a/2*t_^2+v*t_+x,a*t_+v)".asSequent
    result.subgoals(3) shouldBe "J(x,v), b()>0, t_>=0 ==> J((-b())/2*t_^2+v*t_+x,(-b())*t_+v)".asSequent
  }

  it should "prove automatically with the correct conditions" in withQE { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/01_robo1-full.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "prove with a manually written searchy tactic" in withMathematica { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/01_robo1-full.kyx"))
    val tactic = implyR('R) & (andL('L)*) & loop("v^2<=2*b()*(m()-x)".asFormula)('R) <(
      print("Base case") & closeId,
      print("Use case") & QE,
      print("Step") & normalize & solve('R) & QE
      )
    proveBy(s, tactic) shouldBe 'proved
  }

  it should "stop after ODE to let users inspect a counterexample with false speed sb condition" in withQE { _ =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/cpsweek/01_robo1-falsespeedsb.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/cpsweek/01_robo1-falsespeedsb.kyt")).mkString)
    val result = proveBy(KeYmaeraXProblemParser(modelContent), tactic)
    result.subgoals should have size 2
  }

  "Example 2" should "have expected open goal and a counter example" in withMathematica { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/02_robo2-justbrakenaive.kyx"))
    val result = proveBy(s, master(keepQEFalse=false))
    result.isProved shouldBe false //@note This assertion is a soundness check!
    result.subgoals.loneElement shouldBe "x<=m(), b()>0, t_>=0, \\forall s_ (0<=s_&s_<=t_ -> (-b())*s_+v>=0) ==> (-b())/2*t_^2+v*t_+x <= m()".asSequent

    // counter example
    tool.findCounterExample(result.subgoals.head.toFormula).get.keySet should contain only (Function("b", None, Unit, Real),
      "x".asVariable, "v".asVariable, Function("m", None, Unit, Real), "t_".asVariable, "s_".asVariable)
    // can't actually check cex values, may differ from run to run

    // cut in concrete values to get nicer CEX
    val cutFml = "x=1 & v=2 & m()=x+3".asFormula
    val afterCut = proveBy(result.subgoals.head, cut(cutFml))
    afterCut.subgoals should have size 2
    afterCut.subgoals.head.ante should contain (cutFml)
    val cex = tool.findCounterExample(afterCut.subgoals.head.toFormula).get
    cex.keySet should contain only (Function("b", None, Unit, Real), "x".asVariable, "v".asVariable,
      Function("m", None, Unit, Real), "t_".asVariable, "s_".asVariable)
    cex.get("x".asVariable) should contain ("1".asTerm)
    cex.get("v".asVariable) should contain ("2".asTerm)
    cex.get(Function("m", None, Unit, Real)) should contain ("4".asTerm)
  }

  it should "find the braking condition" in withMathematica { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/02_robo2-justbrakenaive.kyx"))
    val result = proveBy(s, master(keepQEFalse=false))
    result.subgoals.loneElement shouldBe "x<=m(), b()>0, t_>=0, \\forall s_ (0<=s_&s_<=t_ -> (-b())*s_+v>=0) ==> (-b())/2*t_^2+v*t_+x <= m()".asSequent

    val initCond = proveBy(result.subgoals.head, TactixLibrary.partialQE)
    initCond.subgoals.loneElement shouldBe "==> b()<=0|b()>0&(v<=0|v>0&((t_<=0|(0 < t_&t_<=v*b()^-1)&(x<=1/2*(-2*t_*v+t_^2*b()+2*m())|x>m()))|t_>v*b()^-1))".asSequent
    // explain in tutorial: mostly crap that violates our assumptions, but m>=... and b=t_^-1*v_0 look interesting -> transform

    val simpler = proveBy(initCond.subgoals.head, TactixLibrary.transform("b()=v/t_ & t_>0 & m() >= -b()/2*t_^2+v*t_+x".asFormula)(1))
    simpler.subgoals.loneElement shouldBe "==> b()=v/t_ & t_>0 & m() >= -b()/2*t_^2+v*t_+x".asSequent

    // now let's transform once again and put in t_ = v/b
    val cond = proveBy(simpler.subgoals.head, TactixLibrary.transform("b()>0 & t_=v/b() & v>0 & m()-x >= v^2/(2*b())".asFormula)(1))
    cond.subgoals.loneElement shouldBe "==> b()>0 & t_=v/b() & v>0 & m()-x >= v^2/(2*b())".asSequent
  }

  it should "prove braking automatically with the correct condition" in withQE { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/03_robo2-justbrake.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "find the acceleration condition" in withMathematica { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/04_robo2-justaccnaive.kyx"))
    val result = proveBy(s, master(keepQEFalse=false))
    result.subgoals.loneElement shouldBe "A()>=0, b()>0, v^2<=2*b()*(m()-x), ep()>0, Q(x,v), t=0, t_>=0, \\forall s_ (0<=s_&s_<=t_ -> A()*s_+v>=0 & s_+0<=ep()) ==> (A()*t_+v)^2 <= 2*b()*(m()-(A()/2*t_^2+v*t_+x))".asSequent

    val initCond = proveBy(result.subgoals.head, hideL(-5, "Q(x,v)".asFormula) & TactixLibrary.partialQE)
    initCond.subgoals.loneElement shouldBe "==> t_<=0|t_>0&((v < 0|v=0&(A()<=0|A()>0&(b()<=0|b()>0&(ep() < t_|ep()>=t_&((t < 0|t=0&(x<=1/2*b()^-1*(-1*t_^2*A()^2+-1*t_^2*A()*b()+2*b()*m())|x>m()))|t>0)))))|v>0&(A() < 0|A()>=0&(b()<=0|b()>0&(ep() < t_|ep()>=t_&((t < 0|t=0&(x<=1/2*b()^-1*(-1*v^2+-2*t_*v*A()+-1*t_^2*A()^2+-2*t_*v*b()+-1*t_^2*A()*b()+2*b()*m())|x>1/2*b()^-1*(-1*v^2+2*b()*m())))|t>0)))))".asSequent

    // now get rid of stuff that violates our assumptions and transform into nicer shape
    val simpler = proveBy(initCond.subgoals.head, TactixLibrary.transform("b()>0 & A()>=0 & t_>=0 & m()>=1/2*b()^-1*(A()^2*t_^2+A()*b()*t_^2+2*A()*t_*v+2*b()*t_*v+v^2+2*b()*x)".asFormula)(1))
    simpler.subgoals.loneElement shouldBe "==> b()>0 & A()>=0 & t_>=0 & m()>=1/2*b()^-1*(A()^2*t_^2+A()*b()*t_^2+2*A()*t_*v+2*b()*t_*v+v^2+2*b()*x)".asSequent

    val cond = proveBy(simpler.subgoals.head, TactixLibrary.transform("b()>0 & A()>=0 & t_>=0 & m()-x >= v^2/(2*b())+(A()/b()+1)*(A()/2*t_^2 + v*t_)".asFormula)(1))
    cond.subgoals.loneElement shouldBe "==> b()>0 & A()>=0 & t_>=0 & m()-x >= v^2/(2*b())+(A()/b()+1)*(A()/2*t_^2 + v*t_)".asSequent
  }

  it should "prove acceleration automatically with the correct condition" in withQE { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/05_robo2-justacc.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "prove the full model" in withQE { _ =>
    val s = KeYmaeraXArchiveParser.getEntry("CPSWeek Tutorial Example 1", io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/tutorials/cpsweek/cpsweek.kyx")).mkString).get.model.asInstanceOf[Formula]
    proveBy(s, master()) shouldBe 'proved
  }

  it should "be provable from parsed tactic" in withQE { _ => withDatabase { db =>
    val entry = KeYmaeraXArchiveParser.getEntry("CPSWeek Tutorial Example 1", io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/tutorials/cpsweek/cpsweek.kyx")).mkString).get
    val modelContent = entry.fileContent
    val tactic = entry.tactics.head._2
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "find a hint for SB from parsed tactic" in withMathematica { _ =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/cpsweek/06_robo2-fullnaive.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/cpsweek/06_robo2-fullnaive.kyt")).mkString)
    val result = proveBy(KeYmaeraXProblemParser(modelContent), tactic)
    result.subgoals should have size 2
    //unsimplified
    result.subgoals.last.succ should contain only "(m() < 0&(t<=0&((v < 0|v=0&(ep()<=0|ep()>0&(A()<=0|A()>0&(b()<=0|b()>0&(x<=1/2*(-1*t^2*A()+2*t*A()*ep()+-1*A()*ep()^2+2*m())|x>m())))))|v>0&(ep()<=0|ep()>0&(A() < 0|A()>=0&(b()<=0|b()>0&(x<=1/2*(2*t*v+-1*t^2*A()+-2*v*ep()+2*t*A()*ep()+-1*A()*ep()^2+2*m())|x>m())))))|t>0&((v < 0|v=0&((ep() < t|ep()=t&(A()<=0|A()>0&(b()<=0|b()>0&((x < m()|x=1/2*(-1*t^2*A()+2*t*A()*ep()+-1*A()*ep()^2+2*m()))|x>m()))))|ep()>t&(A()<=0|A()>0&(b()<=0|b()>0&(x<=1/2*(-1*t^2*A()+2*t*A()*ep()+-1*A()*ep()^2+2*m())|x>m())))))|v>0&((ep() < t|ep()=t&(A() < 0|A()>=0&(b()<=0|b()>0&((x < m()|x=1/2*(2*t*v+-1*t^2*A()+-2*v*ep()+2*t*A()*ep()+-1*A()*ep()^2+2*m()))|x>m()))))|ep()>t&(A() < 0|A()>=0&(b()<=0|b()>0&(x<=1/2*(2*t*v+-1*t^2*A()+-2*v*ep()+2*t*A()*ep()+-1*A()*ep()^2+2*m())|x>m()))))))|m()=0&(t<=0&((v < 0|v=0&(ep()<=0|ep()>0&(A()<=0|A()>0&(b()<=0|b()>0&(x<=1/2*(-1*t^2*A()+2*t*A()*ep()+-1*A()*ep()^2)|x>0)))))|v>0&(ep()<=0|ep()>0&(A() < 0|A()>=0&(b()<=0|b()>0&(x<=1/2*(2*t*v+-1*t^2*A()+-2*v*ep()+2*t*A()*ep()+-1*A()*ep()^2)|x>0)))))|t>0&((v < 0|v=0&(ep()<=t|ep()>t&(A()<=0|A()>0&(b()<=0|b()>0&(x<=1/2*(-1*t^2*A()+2*t*A()*ep()+-1*A()*ep()^2)|x>0)))))|v>0&(ep()<=t|ep()>t&(A() < 0|A()>=0&(b()<=0|b()>0&(x<=1/2*(2*t*v+-1*t^2*A()+-2*v*ep()+2*t*A()*ep()+-1*A()*ep()^2)|x>0)))))))|m()>0&((t < 0&((v < 0|v=0&(ep()<=0|ep()>0&(A()<=0|A()>0&(b()<=0|b()>0&(x<=1/2*(-1*t^2*A()+2*t*A()*ep()+-1*A()*ep()^2+2*m())|x>m())))))|v>0&(ep()<=0|ep()>0&(A() < 0|A()>=0&(b()<=0|b()>0&(x<=1/2*(2*t*v+-1*t^2*A()+-2*v*ep()+2*t*A()*ep()+-1*A()*ep()^2+2*m())|x>m())))))|t=0&((v < 0|v=0&(ep()<=0|ep()>0&(A()<=0|A()>0&(b()<=0|b()>0&(x<=1/2*(-1*A()*ep()^2+2*m())|x>m())))))|v>0&(ep()<=0|ep()>0&(A() < 0|A()>=0&(b()<=0|b()>0&(x<=1/2*(-2*v*ep()+-1*A()*ep()^2+2*m())|x>m()))))))|t>0&((v < 0|v=0&(ep()<=t|ep()>t&(A()<=0|A()>0&(b()<=0|b()>0&(x<=1/2*(-1*t^2*A()+2*t*A()*ep()+-1*A()*ep()^2+2*m())|x>m())))))|v>0&(ep()<=t|ep()>t&(A() < 0|A()>=0&(b()<=0|b()>0&(x<=1/2*(2*t*v+-1*t^2*A()+-2*v*ep()+2*t*A()*ep()+-1*A()*ep()^2+2*m())|x>m()))))))".asFormula
    //@todo simplify with transform
  }

  "A searchy tactic" should "prove both a simple and a complicated model" in withMathematica { _ =>
    def tactic(j: Formula) = implyR('R) & (andL('L)*) & loop(j)('R) <(
      print("Base case") & closeId,
      print("Use case") & QE,
      print("Step") & normalize & OnAll(solve('R) & QE)
      )

    val simple = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/01_robo1-full.kyx"))
    proveBy(simple, tactic("v^2<=2*b()*(m()-x)".asFormula)) shouldBe 'proved

    val harder = KeYmaeraXArchiveParser.getEntry("CPSWeek Tutorial Example 1", io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/tutorials/cpsweek/cpsweek.kyx")).mkString).get.model.asInstanceOf[Formula]
    proveBy(harder, tactic("v^2<=2*b()*(m()-x)".asFormula)) shouldBe 'proved
  }

  "2D Car" should "be provable" in withQE { _ =>
    val s = KeYmaeraXArchiveParser.getEntry("CPSWeek Tutorial Example 4", io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/tutorials/cpsweek/cpsweek.kyx")).mkString).get.model.asInstanceOf[Formula]

    def di(a: String) = diffInvariant("dx^2+dy^2=1".asFormula, "t>=0".asFormula, s"v=old(v)+$a*t".asFormula,
      s"-t*(v-$a/2*t)<=x-old(x) & x-old(x)<=t*(v-$a/2*t)".asFormula,
      s"-t*(v-$a/2*t)<=y-old(y) & y-old(y)<=t*(v-$a/2*t)".asFormula)('R)

    val dw = exhaustiveEqR2L(hide=true)('Llast)*3 /* 3 old(...) in DI */ & (andL('L)*) &
      print("Before diffWeaken") & dW(1) & print("After diffWeaken")

    val tactic = implyR('R) & (andL('L)*) & loop("r!=0 & v>=0 & dx^2+dy^2=1 & (2*b()*abs(mx-x)>v^2 | 2*b()*abs(my-y)>v^2)".asFormula)('R) <(
      print("Base case") & QE,
      print("Use case") & QE,
      print("Step") & chase('R) & andR('R) <(
        allR('R) & implyR('R) & di("-b()") & dw & QE,
        // in tutorial: only show braking branch, acceleration takes too long (needs abs and hiding and cuts etc.)
        allR('R)*2 & implyR('R) & allR('R)*2 & implyR('R) & allR('R) & implyR('R) & di("A()") & dw
        )
      )
    val result = proveBy(s, tactic)
    result.subgoals should have size 1
  }

  it should "be provable from parsed tactic" in withQE { _ => withDatabase { db =>
    val entry = KeYmaeraXArchiveParser.getEntry("CPSWeek Tutorial Example 4", io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/tutorials/cpsweek/cpsweek.kyx")).mkString).get
    val modelContent = entry.fileContent
    val tactic = entry.tactics.head._2
    val result = db.proveBy(modelContent, tactic)
    result.subgoals should have size 1
  }}

  "Motzkin" should "be provable with DI+DW" in withQE { _ =>
    val s = KeYmaeraXArchiveParser.getEntry("CPSWeek Tutorial Example 3", io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/tutorials/cpsweek/cpsweek.kyx")).mkString).get.model.asInstanceOf[Formula]
    val tactic = implyR('R) & diffInvariant("x1^4*x2^2+x1^2*x2^4-3*x1^2*x2^2+1 <= c".asFormula)('R) & dW('R) & prop
    proveBy(s, tactic) shouldBe 'proved
  }

  it should "be provable from parsed tactic" in withQE { _ => withDatabase { db =>
    val entry = KeYmaeraXArchiveParser.getEntry("CPSWeek Tutorial Example 3", io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/tutorials/cpsweek/cpsweek.kyx")).mkString).get
    val modelContent = entry.fileContent
    val tactic = entry.tactics.head._2
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  "Damped oscillator" should "be provable with DI+DW" in withQE { _ =>
    val s = KeYmaeraXArchiveParser.getEntry("CPSWeek Tutorial Example 2", io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/tutorials/cpsweek/cpsweek.kyx")).mkString).get.model.asInstanceOf[Formula]
    val tactic = implyR('R) & dI()('R)
    proveBy(s, tactic) shouldBe 'proved
  }

  it should "be provable from parsed tactic" in withQE { _ => withDatabase { db =>
    val entry = KeYmaeraXArchiveParser.getEntry("CPSWeek Tutorial Example 2", io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/tutorials/cpsweek/cpsweek.kyx")).mkString).get
    val modelContent = entry.fileContent
    val tactic = entry.tactics.head._2
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  "Self crossing" should "be provable with DI+DW" in withQE { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/cpsweek/10-diffinv-self-crossing.kyx"))
    val tactic = implyR('R) & diffInvariant("x^2+x^3-y^2-c=0".asFormula)('R) & dW('R) & prop
    proveBy(s, tactic) shouldBe 'proved
  }

}
