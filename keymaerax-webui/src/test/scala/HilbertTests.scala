/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/


import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser
import edu.cmu.cs.ls.keymaerax.tactics.DerivedAxioms._

import edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.ApplyRule
import edu.cmu.cs.ls.keymaerax.tags.{UsualTest, SummaryTest}
import edu.cmu.cs.ls.keymaerax.tools.{KeYmaera, Mathematica, Tool}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import test.RandomFormula
import testHelper.KeYmaeraXTestTags.SummaryTest
import testHelper.KeYmaeraXTestTags.{SummaryTest, CheckinTest}
import testHelper.ParserFactory._
import testHelper.ProvabilityTestHelper

import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.core._
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}

/**
 * Tests Hilbert Calculus.
 * @author Andre Platzer
 */
@SummaryTest
@UsualTest
class HilbertTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  import HilbertCalculus._

  val randomTrials = 10
  val randomComplexity = 3
  val rand = new RandomFormula() //(-4317240407825764493L)

  val helper = new ProvabilityTestHelper((x) => println(x))
  val mathematicaConfig : Map[String, String] = helper.mathematicaConfig

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
    Tactics.MathematicaScheduler = new Interpreter(new Mathematica)
    Tactics.MathematicaScheduler.init(mathematicaConfig)
    Tactics.KeYmaeraScheduler.init(Map())
  }

  override def afterEach() = {
    Tactics.MathematicaScheduler.shutdown()
    Tactics.KeYmaeraScheduler.shutdown()
    Tactics.MathematicaScheduler = null
    Tactics.KeYmaeraScheduler = null
  }

  "Hilbert calculus" should "prove x>=5 -> [{x'=2&x<=9}]x<=9" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2&x<=9}]x<=9".asFormula)),
      implyR(1) &
        DW(1) &
        TacticLibrary.abstractionT(1) & allR(1) & prop
    ) shouldBe 'proved
  }

  it should "prove x>=5 -> [{x'=2&x<=9}]x<=10" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2&x<=9}]x<=10".asFormula)),
      implyR(1) &
        DW(1) &
        TacticLibrary.abstractionT(1) & QE
    ) shouldBe 'proved
  }

  it should "prove x>=5 -> [{x'=2}](x>=5)'" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2}](x>=5)'".asFormula)),
      implyR(1) &
        DE(1) &
        Dgreaterequal(1, 1::1::Nil) &
        Dvariable(1, 1::1:: 0::Nil) &
        Dconst(1, 1::1:: 1::Nil) &
        Dassignb(SuccPosition(0, 1::Nil)) &
          TacticLibrary.abstractionT(1) & QE
    ) shouldBe 'proved
  }

  it should "prove (x+2*y)'=x'+2*y'" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("(x+2*y)'=x'+2*y'".asFormula)),
    Dplus(SuccPosition(0, 0::Nil)) &
      Dvariable(SuccPosition(0, 0::0::Nil)) &
      useAt(Dlinear)(SuccPosition(0, 0::1::Nil)) & // Dtimes(SuccPosition(0, 0::1::Nil))
      Dvariable(SuccPosition(0, 0::1::1::Nil)) &
      byUS("= reflexive")
    ) shouldBe 'proved
  }

  it should "prove (y)'=y forward" in {
    val x = Variable("y")
    TactixLibrary.proveBy(
      Sequent(Nil,IndexedSeq(), IndexedSeq(Equal(Differential(x), DifferentialSymbol(x)))),
      Dvariable(SuccPosition(0,0::Nil)) & byUS("= reflexive")) shouldBe 'proved
    TactixLibrary.proveBy(
      Sequent(Nil,IndexedSeq(), IndexedSeq(Equal(Differential(x), DifferentialSymbol(x)))),
      Dvariable(SuccPosition(0,0::Nil)) & byUS("= reflexive")) shouldBe 'proved
  }

  it should "derive (y)'=y'" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("(y)'=y'".asFormula)),
      derive(1,0::Nil) & byUS("= reflexive")
    ) shouldBe 'proved
  }

  it should "derive (x+y)'=x'+y'" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("(x+y)'=x'+y'".asFormula)),
      derive(1,0::Nil) & byUS("= reflexive")
    ) shouldBe 'proved
  }

  it should "derive (x*y)'=x'*y+x*y'" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("(x*y)'=x'*y+x*y'".asFormula)),
      derive(1,0::Nil) & byUS("= reflexive")
    ) shouldBe 'proved
  }

  it should "derive (x+2*y)'=x'+2*y'" taggedAs(CheckinTest) in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("(x+2*y)'=x'+2*y'".asFormula)),
      derive(1,0::Nil) & byUS("= reflexive")
    ) shouldBe 'proved
  }

  ignore should "derive (5*3+2*9)'=0*3+5*0+(0*9+2*0) unless optimized" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("(5*3+2*9)'=0*3+5*0+(0*9+2*0)".asFormula)),
      derive(1,0::Nil)  //@todo & QE
    ) shouldBe 'proved
  }

  ignore should "derive (5*3+2*9)'=5*0+2*0 if optimized (left linear preferred but not const optimized)" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("(5*3+2*9)'=5*0+2*0".asFormula)),
      derive(1,0::Nil) & byUS("= reflexive")
    ) shouldBe 'proved
  }

  it should "derive (5*3+2*9)'=0 if optimized (const optimized)" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("(5*3+2*9)'=0".asFormula)),
      derive(1,0::Nil) & byUS("= reflexive")
    ) shouldBe 'proved
  }

  it should "derive (5*x+2*y)'=5*x'+2*y'" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("(5*x+2*y)'=5*x'+2*y'".asFormula)),
      derive(1,0::Nil) & byUS("= reflexive")
    ) shouldBe 'proved
  }

  it should "derive (5*x+2*y>=6)' <-> 5*x'+2*y'>=0" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("(5*x+2*y>=6)' <-> 5*x'+2*y'>=0".asFormula)),
      derive(1,0::Nil) & byUS("<-> reflexive")
    ) shouldBe 'proved
  }

  it should "derive (7*x<2*y & 22*x=4*y+8)' <-> (7*x'<=2*y' & 22*x'=4*y'+0)" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("(7*x<2*y & 22*x=4*y+8)' <-> (7*x'<=2*y' & 22*x'=4*y'+0)".asFormula)),
      derive(1,0::Nil) & byUS("<-> reflexive")
    ) shouldBe 'proved
  }

  it should "derive (x*x<2*y & 5*x+2*y>=6+z & 22*x=4*y+8)' <-> (x'*x+x*x'<=2*y' & 5*x'+2*y'>=0+z' & 22*x'=4*y'+0)" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("(x*x<2*y & 5*x+2*y>=6+z & 22*x=4*y+8)' <-> (x'*x+x*x'<=2*y' & 5*x'+2*y'>=0+z' & 22*x'=4*y'+0)".asFormula)),
      derive(1,0::Nil) & byUS("<-> reflexive")
    ) shouldBe 'proved
  }

  it should "derive [{x'=7,y'=-9,z'=2}](x*x<2*y & 5*x+2*y>=6+z & 22*x=4*y+8)' <-> [{x'=7,y'=-9,z'=2}](x'*x+x*x'<=2*y' & 5*x'+2*y'>=0+z' & 22*x'=4*y'+0)" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("[{x'=7,y'=-9,z'=2}](x*x<2*y & 5*x+2*y>=6+z & 22*x=4*y+8)' <-> [{x'=7,y'=-9,z'=2}](x'*x+x*x'<=2*y' & 5*x'+2*y'>=0+z' & 22*x'=4*y'+0)".asFormula)),
      derive(1,0::1::Nil) & byUS("<-> reflexive")
    ) shouldBe 'proved
  }

  it should "reduce [{x'=7}](5*x>=6)' to [{x'=7}]5*x'>=0" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("[{x'=7}](5*x>=6)'".asFormula)),
      derive(1,1::Nil)
    ).subgoals shouldBe List(Sequent(Nil, IndexedSeq(), IndexedSeq("[{x'=7}]5*x'>=0".asFormula)))
  }

  it should "reduce [{x'=99,y'=-3}](7*x<2*y & 22*x=4*y+8)' to [{x'=99,y'=-3}](7*x'<=2*y' & 22*x'=4*y'+0)" taggedAs(SummaryTest) in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("[{x'=99,y'=-3}](7*x<2*y & 22*x=4*y+8)'".asFormula)),
      derive(1,1::Nil)
    ).subgoals shouldBe List(Sequent(Nil, IndexedSeq(), IndexedSeq("[{x'=99,y'=-3}](7*x'<=2*y' & 22*x'=4*y'+0)".asFormula)))
  }

  it should "prove x>=5 -> [{x'=2}]x>=5" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2}]x>=5".asFormula)),
      implyR(1) &
        DI(1) & (step(1) & step(1)) && (
        prop,
        DE(1) &
          Dgreaterequal(1, 1::1::Nil) &
          Dvariable(1, 1::1:: 0::Nil) &
          Dconst(1, 1::1:: 1::Nil) &
          Dassignb(SuccPosition(0, 1::Nil)) & TacticLibrary.abstractionT(1) & QE
      )
    ) shouldBe 'proved
  }

  it should "prove/derive x>=5 -> [{x'=2}]x>=5" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2}]x>=5".asFormula)),
      implyR(1) &
        DI(1) & (step(1) & step(1)) && (
        prop,
        DE(1) & derive(1, 1::1::Nil) &
          Dassignb(SuccPosition(0, 1::Nil)) & TacticLibrary.abstractionT(1) & QE
        )
    ) shouldBe 'proved
  }

  it should "auto-prove x>=5 -> [{x'=2}]x>=5" taggedAs(SummaryTest) in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2}]x>=5".asFormula)),
      implyR(1) & diffInd(1)
    ) shouldBe 'proved
  }

  it should "auto-prove x>=5 -> [{x'=2&x<=10}](5<=x)" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2&x<=10}](5<=x)".asFormula)),
      implyR(1) & diffInd(1)
    ) shouldBe 'proved
  }

//  it should "auto-prove x>=5 -> [{x'=2&x<=10}](5<=x&x<=10)" in {
//    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2&x<=10}](5<=x&x<=10)".asFormula)),
//      implyR(1) & diffCut(1)
//    ) shouldBe 'proved
//  }

  it should "auto-prove x*x+y*y>=8 -> [{x'=5*y,y'=-5*x}]x*x+y*y>=8" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x*x+y*y>=8 -> [{x'=5*y,y'=-5*x}]x*x+y*y>=8".asFormula)),
      implyR(1) & diffInd(1)
    ) shouldBe 'proved
  }


  ignore should "prove x>=5 -> [{x'=2&x<=9}](5<=x&x<=10)" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2&x<=9}](5<=x&x<=10)".asFormula)),
      implyR(1) &
        DC("5<=x".asFormula)(1) & debug("after DC") &
        //@todo needs more branching to handle DI
        //@todo DC should not do absolute proof of implication but contextual
        DW(1) & debug("after DW") &
        TacticLibrary.abstractionT(1) & debug("after abstraction") & QE
    ) shouldBe 'proved
  }

  ignore should "auto-prove x>=5 -> [{x'=2&x<=9}](5<=x&x<=10) with DC" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2&x<=9}](5<=x&x<=10)".asFormula)),
      implyR(1) &
        //@todo the problem is that DI should be used in show prereq branch of useAt instead of defaulting to master
        DC("5<=x".asFormula)(1) && (
        debug("DC to DI") & diffInd(1),
        debug("DC to DW") & DW(1) & TacticLibrary.abstractionT(1) & QE
        )
    ) shouldBe 'proved
  }

  ignore should "prove x>=5 -> [x:=x+1;{x'=2}]x>=5" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x>=5 -> [x:=x+1;{x'=2}]x>=5".asFormula)),
      implyR(1) & //ind
        useAt("[;] compose")(1) &
        useAt("[:=] assign equational")(1) &
        step(1) & step(1) &
        useAt("DI differential invariant")(1) & //@todo diffInd(1)
        (l(step)*) & TacticLibrary.abstractionT(1) & master
    ) shouldBe 'proved
  }

  it should "prove x>=5 |- [x:=x+1][{x'=2}]x>=5" in {
    proveBy(Sequent(Nil, IndexedSeq("x>=5".asFormula), IndexedSeq("[x:=x+1;][{x'=2}]x>=5".asFormula)),
      //@todo need to locate diffInd to after update prefix
      diffInd(1, 1::Nil) &
        assignb(1) & // handle updates
        QE
    ) shouldBe 'proved
  }

  it should "prove x>0 -> [x:=x+1;]x>0" in {
    proveBy("x>0 -> [x:=x+1;]x>0".asFormula, stepAt(1, 1::Nil) & QE) shouldBe 'proved
  }



  "Chase" should "prove [?x>0;x:=x+1; ++ ?x=0;x:=1;]x>0 by chase" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("[?x>0;x:=x+1; ++ ?x=0;x:=1;]x>0".asFormula)),
      chase(1,Nil) & QE
    ) shouldBe 'proved
  }

  it should "prove [?x>0;x:=x+1; ++ ?x=0;x:=1;]x>=1 by chase" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("[?x>0;x:=x+1; ++ ?x=0;x:=1;]x>=1".asFormula)),
      chase(1,Nil) & QE
    ) shouldBe 'proved
  }

  it should "prove [?x>0;x:=x+1; ++ ?x=0;x:=1; ++ x:=99; ++ ?x>=0;{{x:=x+1;++x:=x+2;};{y:=0;++y:=1;}}]x>=1 by chase" taggedAs(SummaryTest) in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("[?x>0;x:=x+1; ++ ?x=0;x:=1; ++ x:=99; ++ ?x>=0;{{x:=x+1;++x:=x+2;};{y:=0;++y:=1;}}]x>=1".asFormula)),
      chase(1,Nil) & QE
    ) shouldBe 'proved
  }

  it should "chase [?x>0;x:=x+1; ++ ?x=0;x:=1; ++ x:=0;x:=x+1; ++ x:=1;?x>=2;]x>=1" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("[?x>0;x:=x+1; ++ ?x=0;x:=1; ++ x:=0;x:=x+1; ++ x:=1;?x>=2;]x>=1".asFormula)),
      // chaseWide(3) works like an update calculus
      chase(3,3)(1) &
        QE
    ) shouldBe 'proved
  }

  it should "auto-prove x>=5 -> [x:=x+1;{x'=2}]x>=5" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x>=5 -> [x:=x+1;{x'=2}]x>=5".asFormula)),
      implyR(1) &
        chase(3,3)(1) &
        //@todo need to locate diffInd to after update prefix
        diffInd(1, 1::Nil) &
        assignb(1) & // handle updates
        QE
    ) shouldBe 'proved
  }

  it should "chase [{x'=22}](2*x+x*y>=5)'" taggedAs(CheckinTest) in {
    proveBy("[{x'=22}](2*x+x*y>=5)'".asFormula,
      chase(1, 1 :: Nil)
    ).subgoals shouldBe List(Sequent(Nil, IndexedSeq(), IndexedSeq("[{x'=22}]2*x'+(x'*y+x*y')>=0".asFormula)))
  }

  it should "chase [{x'=22}][?x>0;x:=x+1; ++ ?x=0;x:=1;]x>=1" taggedAs(CheckinTest) in {
    proveBy("[{x'=22}][?x>0;x:=x+1; ++ ?x=0;x:=1;]x>=1".asFormula,
      chase(1, 1 :: Nil)
    ).subgoals shouldBe List(Sequent(Nil, IndexedSeq(), IndexedSeq("[{x'=22}]((x>0->x+1>=1) & (x=0->1>=1))".asFormula)))
  }

  it should "prove x>=5 -> [x:=x+1;{x'=2}]x>=5" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x>=5 -> [x:=x+1;{x'=2}]x>=5".asFormula)),
      implyR(1) & chase(1) &
      //@todo need to locate diffInd to after update prefix
      diffInd(1, 1::Nil) &
        assignb(1) & // handle updates
        QE
    ) shouldBe 'proved
  }

  "Chase generalizations" should "modelplex llc by updateCalculus" in {
    println(proveBy(parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/fm11/llc-ctrl.key")),
      implyR(1) & updateCalculus(1)
    ))
  }

  ignore should "modelplex llc by updateCalculus implicationally" in {
    println(proveBy(parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/fm11/llc-ctrl.key")),
      updateCalculus(SuccPosition(0, PosInExpr(1 :: Nil)))))
    //@todo not sure how to test whether it's the right output
    true shouldBe false
  }

    /*it should "modelplex llc by updateCalculus after turning it backwards" in {
      updateCalculus(SuccPosition(0, PosInExpr(1::Nil))) (Provable.startProof(parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/fm11/llc-ctrl.key")))).
      conclusion shouldBe false
    }*/

  "CMon monotonicity" should "prove x<99 -> y<2 & x>5 |- x<99 -> y<2 & x>2 from x>5 |- x>2" in {
    val done = CMon(Context("x<99 -> y<2 & ⎵".asFormula)) (Provable.startProof(Sequent(Nil, IndexedSeq("x>5".asFormula), IndexedSeq("x>2".asFormula))))
    done.subgoals shouldBe List(Sequent(Nil, IndexedSeq("x>5".asFormula), IndexedSeq("x>2".asFormula)))
    done.conclusion shouldBe Sequent(Nil, IndexedSeq("x<99 -> y<2 & x>5".asFormula), IndexedSeq("x<99 -> y<2 & x>2".asFormula))
  }

  it should "prove x<99 -> y<2 & x>5 |- x<99 -> y<2 & x>2 from provable x>5 |- x>2" in {
    val done = CMon(Context("x<99 -> y<2 & ⎵".asFormula)) (proveBy(Sequent(Nil, IndexedSeq("x>5".asFormula), IndexedSeq("x>2".asFormula)), QE))
    done shouldBe 'proved
    done.conclusion shouldBe Sequent(Nil, IndexedSeq("x<99 -> y<2 & x>5".asFormula), IndexedSeq("x<99 -> y<2 & x>2".asFormula))
  }

  private def shouldCMon(ctx: Context[Formula], basic: Provable = basicImpl): Unit = {
    require(basic.isProved)
    require(basic.conclusion.ante.length==1 && basic.conclusion.succ.length==1)
    val done = CMon(ctx)(basic)
    done shouldBe 'proved
    done.conclusion shouldBe Sequent(Nil, IndexedSeq(ctx(basic.conclusion.ante.head)), IndexedSeq(ctx(basic.conclusion.succ.head)))
  }

  private def shouldCMonA(ctx: Context[Formula], basic: Provable = basicImpl): Unit = {
    require(basic.isProved)
    require(basic.conclusion.ante.length==1 && basic.conclusion.succ.length==1)
    val done = CMon(ctx)(basic)
    done shouldBe 'proved
    done.conclusion shouldBe Sequent(Nil, IndexedSeq(ctx(basic.conclusion.succ.head)), IndexedSeq(ctx(basic.conclusion.ante.head)))
  }

  it should "prove y<2 & x>5 |- y<2 & x>2 from x>5 |- x>2" in {shouldCMon(Context("y<2 & ⎵".asFormula))}
  it should "prove x>5 & y<2 |- x>2 & y<2 from x>5 |- x>2" in {shouldCMon(Context("⎵ & y<2".asFormula))}
  it should "prove x<99 -> x>5 |- x<99 -> x>2 from x>5 |- x>2" in {shouldCMon(Context("x<99 -> ⎵".asFormula))}
  it should "prove x<99 | x>5 |- x<99 | x>2 from x>5 |- x>2" in {shouldCMon(Context("x<99 | ⎵".asFormula))}
  it should "prove in monotone context x<99 | _ & y<2" in {shouldCMon(Context("x<99 | ⎵ & y<2".asFormula))}
  it should "prove in monotone context (x<99 | _) & y<2" in {shouldCMon(Context("(x<99 | ⎵) & y<2".asFormula))}
  it should "prove in monotone context x<7 -> (x<99 | _) & y<2" in {shouldCMon(Context("x<7 -> (x<99 | ⎵) & y<2".asFormula))}
  it should "prove in monotone context x<y -> x<7 -> (x<99 | x<10 -> (_ & z=2 | x=5 & y=3)) & y<2" in {shouldCMon(Context("x<y -> x<7 -> (x<99 | x<10 -> (⎵ & z=2 | x=5 & y=3)) & y<2".asFormula))}
  it should "prove in monotone context \\forall y _" in {shouldCMon(Context("\\forall y ⎵".asFormula))}
  it should "prove in monotone context \\forall x _" in {shouldCMon(Context("\\forall x ⎵".asFormula))}
  it should "prove in monotone context \\exists y _" in {shouldCMon(Context("\\exists y ⎵".asFormula))}
  it should "prove in monotone context \\exists x _" in {shouldCMon(Context("\\exists x ⎵".asFormula))}
  it should "prove in monotone context \\forall y (_ | x<y)" in {shouldCMon(Context("\\forall y (⎵ | x<y)".asFormula))}
  it should "prove in monotone context \\forall x (_ | x<y)" in {shouldCMon(Context("\\forall x (⎵ | x<y)".asFormula))}
  it should "prove in monotone context \\exists y (_ | x<y)" in {shouldCMon(Context("\\exists y (⎵ | x<y)".asFormula))}
  it should "prove in monotone context \\exists x (_ | x<y)" in {shouldCMon(Context("\\exists x (⎵ | x<y)".asFormula))}
  it should "prove in antimonotone context _ -> y<2" in {shouldCMonA(Context("⎵ -> y<2".asFormula))}
  it should "prove in antimonotone context _ -> y<2 & x<10" in {shouldCMonA(Context("⎵ -> y<2 & x<10".asFormula))}
  it should "prove in antimonotone context (_ -> y<2) & x<10" in {shouldCMonA(Context("(⎵ -> y<2) & x<10".asFormula))}
  it should "prove in antimonotone context (_ -> y<2) & x<10 | x=7" in {shouldCMonA(Context("(⎵ -> y<2) & x<10 | x=7".asFormula))}
  it should "prove in antiantimonotone context ((_ -> y<2) -> z=0) & x<10 | x=7 " in {shouldCMonA(Context("((⎵ -> y<2) -> z=0) & x<10 | x=7".asFormula))}

  lazy val basicImpl = proveBy(Sequent(Nil, IndexedSeq("x>5".asFormula), IndexedSeq("x>2".asFormula)), QE)


  it should "prove C{x>5} |- C{x>2} from provable x>5 |- x>2 in random positive contexts" in {
    println("Starting random contexts\n\n")
    for (i <- 1 to randomTrials) {
      val ctx = rand.nextFormulaContext(randomComplexity)
      if (ctx.isFormulaContext) {
        println("Context: " + ctx)
        //@todo discard ctx unless positive
        //@todo discard ctx if DotFormula within a program
        //@todo discard ctx if DotFormula somewhere underneath an Equiv
        try {
          val done = CMon(ctx)(basicImpl)
          done shouldBe 'proved
          done.conclusion shouldBe Sequent(Nil, IndexedSeq(ctx("x>5".asFormula)), IndexedSeq(ctx("x>2".asFormula)))
        } catch {
          case e: ProverException => if (e.toString.startsWith("No monotone context")) println("context discarded") else throw e
        }
      }
    }
  }

  lazy val basicEq = TactixLibrary.proveBy("1=0*x+1".asFormula, QE)
  lazy val basicEquiv = TactixLibrary.proveBy("-2<x&x<2 <-> x^2<4".asFormula, QE)

  private def shouldReduceTo(input: Formula, pos: Position, result: Formula, fact: Provable = basicEq): Unit =
    TactixLibrary.proveBy(input, HilbertCalculus.CE(fact)(pos)).subgoals shouldBe (
      List(new Sequent(Nil, IndexedSeq(), IndexedSeq(result)))
      )

  "CE(Provable) equation magic" should "reduce 0*x+1<=3 to 1<=3" in {
    shouldReduceTo("0*x+1<=3".asFormula, SuccPosition(0, PosInExpr(0::Nil)), "1<=3".asFormula)
  }

  it should "reduce x<5 & 0*x+1<=3 | x>=2 to x<5 & 1<=3 | x>=2" taggedAs(SummaryTest) in {
    shouldReduceTo("x<5 & 0*x+1<=3 | x>=2".asFormula, SuccPosition(0, PosInExpr(0::1::0::Nil)), "x<5 & 1<=3 | x>=2".asFormula)
  }

  it should "reduce \\forall x 0*x+1<=3 to \\forall x 1<=3" in {
    shouldReduceTo("\\forall x 0*x+1<=3".asFormula, SuccPosition(0, PosInExpr(0::0::Nil)), "\\forall x 1<=3".asFormula)
  }

  it should "reduce x<5 & \\forall x 0*x+1<=3 | x>=2 to x<5 & \\forall x 1<=3 | x>=2" taggedAs(SummaryTest) in {
    shouldReduceTo("x<5 & \\forall x 0*x+1<=3 | x>=2".asFormula, SuccPosition(0, PosInExpr(0::1::0::0::Nil)), "x<5 & \\forall x 1<=3 | x>=2".asFormula)
  }

  it should "reduce [x:=7;]0*x+1<=3 to [x:=7;]1<=3" in {
    shouldReduceTo("[x:=7;]0*x+1<=3".asFormula, SuccPosition(0, PosInExpr(1::0::Nil)), "[x:=7;]1<=3".asFormula)
  }

  it should "reduce [x:=7;?0*x+1<=3;]x<9 to [x:=7;?1<=3;]x<9" in {
    shouldReduceTo("[x:=7;?0*x+1<=3;]x<9".asFormula, SuccPosition(0, PosInExpr(0::1::0::0::Nil)), "[x:=7;?1<=3;]x<9".asFormula)
  }

  it should "reduce [x:=0*x+1;]x<9 to [x:=1;]x<9" in {
    shouldReduceTo("[x:=0*x+1;]x<9".asFormula, SuccPosition(0, PosInExpr(0::1::Nil)), "[x:=1;]x<9".asFormula)
  }

  it should "reduce [x:=7;x:=0*x+1;]x<9 to [x:=7;x:=1;]x<9" in {
    shouldReduceTo("[x:=7;x:=0*x+1;]x<9".asFormula, SuccPosition(0, PosInExpr(0::1::1::Nil)), "[x:=7;x:=1;]x<9".asFormula)
  }

  it should "reduce [{x' = 7 & 0*x+1<2}]x>=2 to [{x' = 7 & 1<2}]x>=2" in {
    shouldReduceTo("[{x' = 7 & 0*x+1<2}]x>=2".asFormula, SuccPosition(0, PosInExpr(0::1::0::Nil)), "[{x' = 7 & 1<2}]x>=2".asFormula)
  }

  it should "reduce [{x' = 0*x+1 & 5=5}]x>=2 to [{x' = 1 & 5=5}]x>=2" in {
    shouldReduceTo("[{x' = 0*x+1 & 5=5}]x>=2".asFormula, SuccPosition(0, PosInExpr(0::0::1::Nil)), "[{x' = 1 & 5=5}]x>=2".asFormula)
  }


  "CE(Provable) equivalence magic" should "reduce x^2<4 to -2<x&x<2" in {
    shouldReduceTo("x^2<4".asFormula, SuccPosition(0, PosInExpr(Nil)), "-2<x&x<2".asFormula, basicEquiv)
  }

  it should "reduce !(x^2<4) to !(-2<x&x<2)" in {
    shouldReduceTo("!x^2<4".asFormula, SuccPosition(0, PosInExpr(0::Nil)), "!(-2<x&x<2)".asFormula, basicEquiv)
  }

  it should "reduce x<5 & x^2<4 | x>=2 to x<5 & (-2<x&x<2) | x>=2" in {
    shouldReduceTo("x<5 & x^2<4| x>=2".asFormula, SuccPosition(0, PosInExpr(0::1::Nil)), "x<5 & (-2<x&x<2) | x>=2".asFormula, basicEquiv)
  }

  it should "reduce x<5 & \\forall x x^2<4 | x>=2 to x<5 & \\forall x (-2<x&x<2) | x>=2" in {
    shouldReduceTo("x<5 & \\forall x x^2<4| x>=2".asFormula, SuccPosition(0, PosInExpr(0::1::0::Nil)), "x<5 & \\forall x (-2<x&x<2) | x>=2".asFormula, basicEquiv)
  }

  it should "reduce [{x' = 5*x & x^2<4}]x>=1 to [{x' = 5*x & -2<x&x<2}]x>=1" taggedAs(SummaryTest) in {
    shouldReduceTo("[{x' = 5*x & x^2<4}]x>=1".asFormula, SuccPosition(0, PosInExpr(0::1::Nil)), "[{x' = 5*x & -2<x&x<2}]x>=1".asFormula, basicEquiv)
  }

  "useFor" should "use DX to forward (true&x=y) to <{x'=2}>x=y" in {
    useFor("DX diamond differential skip", PosInExpr(0::Nil),
      (us:RenUSubst) => us++RenUSubst(Seq((DifferentialProgramConst("c"), KeYmaeraXParser.differentialProgramParser("x'=2"))))
    )(SuccPosition(0, PosInExpr(Nil))) (
      Provable.startProof(Sequent(Nil,IndexedSeq(), IndexedSeq("(true&x=y)".asFormula)))
    ).conclusion shouldBe Sequent(Nil,IndexedSeq(), IndexedSeq("<{x'=2}>x=y".asFormula))
  }

  it should "use DX to forward <{x'=2}>x=y -> bla() to (true&x=y) -> bla()" in {
    useFor("DX diamond differential skip")(SuccPosition(0, PosInExpr(0::Nil))) (
      Provable.startProof(Sequent(Nil,IndexedSeq(), IndexedSeq("<{x'=2}>x=y -> bla()".asFormula)))
    ).conclusion shouldBe Sequent(Nil,IndexedSeq(), IndexedSeq("(true&x=y) -> bla()".asFormula))
  }

  it should "use DX to forward <{x'=2}>x=y <-> bla() to (true&x=y) -> bla()" in {
    useFor("DX diamond differential skip")(SuccPosition(0, PosInExpr(0::Nil))) (
      Provable.startProof(Sequent(Nil,IndexedSeq(), IndexedSeq("<{x'=2}>x=y <-> bla()".asFormula)))
    ).conclusion shouldBe Sequent(Nil,IndexedSeq(), IndexedSeq("(true&x=y) -> bla()".asFormula))
  }

  // with context

  it should "use <*> approx to forward <x:=x+1;>x=y to <{x:=x+1;}*>x=y" in {
    useFor("<*> approx", PosInExpr(0::Nil))(SuccPosition(0, PosInExpr(Nil))) (
      Provable.startProof(Sequent(Nil,IndexedSeq(), IndexedSeq("<x:=x+1;>x=y".asFormula)))
    ).conclusion shouldBe Sequent(Nil,IndexedSeq(), IndexedSeq("<{x:=x+1;}*>x=y".asFormula))
  }

  it should "use <*> approx to forward <{x:=x+1;}*>x=y -> bla() to <x:=x+1;>x=y -> bla()" in {
    useFor("<*> approx")(SuccPosition(0, PosInExpr(0::Nil))) (
      Provable.startProof(Sequent(Nil,IndexedSeq(), IndexedSeq("<{x:=x+1;}*>x=y -> bla()".asFormula)))
    ).conclusion shouldBe Sequent(Nil,IndexedSeq(), IndexedSeq("<x:=x+1;>x=y -> bla()".asFormula))
  }

  it should "use <*> approx to forward <{x:=x+1;}*>x=y <-> bla() to <x:=x+1;>x=y -> bla()" in {
    useFor("<*> approx")(SuccPosition(0, PosInExpr(0::Nil))) (
      Provable.startProof(Sequent(Nil,IndexedSeq(), IndexedSeq("<{x:=x+1;}*>x=y <-> bla()".asFormula)))
    ).conclusion shouldBe Sequent(Nil,IndexedSeq(), IndexedSeq("<x:=x+1;>x=y -> bla()".asFormula))
  }

  it should "use <*> approx to forward bla() <-> <{x:=x+1;}*>x=y to <x:=x+1;>x=y -> bla()" in {
    useFor("<*> approx")(SuccPosition(0, PosInExpr(1::Nil))) (
      Provable.startProof(Sequent(Nil,IndexedSeq(), IndexedSeq("bla() <-> <{x:=x+1;}*>x=y".asFormula)))
    ).conclusion shouldBe Sequent(Nil,IndexedSeq(), IndexedSeq("<x:=x+1;>x=y -> bla()".asFormula))
  }

  it should "use DX to forward <x:=1;>(true&x=y) to <x:=1;><{x'=2}>x=y" in {
    useFor("DX diamond differential skip", PosInExpr(0::Nil))(SuccPosition(0, PosInExpr(1::Nil))) (
      Provable.startProof(Sequent(Nil,IndexedSeq(), IndexedSeq("<x:=1;>(true&x=y)".asFormula)))
    ).conclusion shouldBe Sequent(Nil,IndexedSeq(), IndexedSeq("<x:=1;><{c}>x=y".asFormula))
  }

  it should "use DX to forward <x:=1;><{x'=2}>x=y -> bla() to <x:=1;>(true&x=y) -> bla()" in {
    useFor("DX diamond differential skip")(SuccPosition(0, PosInExpr(0::1::Nil))) (
      Provable.startProof(Sequent(Nil,IndexedSeq(), IndexedSeq("<x:=1;><{x'=2}>x=y -> bla()".asFormula)))
    ).conclusion shouldBe Sequent(Nil,IndexedSeq(), IndexedSeq("<x:=1;>(true&x=y) -> bla()".asFormula))
  }

  it should "use DX to forward <x:=1;><{x'=2}>x=y <-> bla() to <x:=1;>(true&x=y) -> bla()" in {
    useFor("DX diamond differential skip")(SuccPosition(0, PosInExpr(0::1::Nil))) (
      Provable.startProof(Sequent(Nil,IndexedSeq(), IndexedSeq("<x:=1;><{x'=2}>x=y <-> bla()".asFormula)))
    ).conclusion shouldBe Sequent(Nil,IndexedSeq(), IndexedSeq("<x:=1;>(true&x=y) -> bla()".asFormula))
  }

  it should "use <*> approx to forward <x:=1;>x=1 to <{x:=1;}*>x=1" in {
    useFor("<*> approx", PosInExpr(0::Nil))(SuccPosition(0, PosInExpr(Nil))) (
      Provable.startProof(Sequent(Nil,IndexedSeq(), IndexedSeq("<x:=1;>x=1".asFormula)))
    ).conclusion shouldBe Sequent(Nil,IndexedSeq(), IndexedSeq("<{x:=1;}*>x=1".asFormula))
  }

  it should "use <*> approx to forward <x:=1;><x:=x+1;>x=y to <x:=1;><{x:=x+1;}*>x=y" in {
    useFor("<*> approx", PosInExpr(0::Nil))(SuccPosition(0, PosInExpr(1::Nil))) (
      Provable.startProof(Sequent(Nil,IndexedSeq(), IndexedSeq("<x:=1;><x:=x+1;>x=y".asFormula)))
    ).conclusion shouldBe Sequent(Nil,IndexedSeq(), IndexedSeq("<x:=1;><{x:=x+1;}*>x=y".asFormula))
  }

  it should "use <*> approx to forward <x:=1;><{x:=x+1;}*>x=y -> bla() to <x:=1;><x:=x+1;>x=y -> bla()" in {
    useFor("<*> approx", PosInExpr(1::Nil))(SuccPosition(0, PosInExpr(0::1::Nil))) (
      Provable.startProof(Sequent(Nil,IndexedSeq(), IndexedSeq("<x:=1;><{x:=x+1;}*>x=y -> bla()".asFormula)))
    ).conclusion shouldBe Sequent(Nil,IndexedSeq(), IndexedSeq("<x:=1;><x:=x+1;>x=y -> bla()".asFormula))
  }

  it should "use <*> approx to forward bla() -> <x:=1;><x:=x+1;>x=y to bla() -> <x:=1;><{x:=x+1;}*>x=y" in {
    useFor("<*> approx", PosInExpr(0::Nil))(SuccPosition(0, PosInExpr(1::1::Nil))) (
      Provable.startProof(Sequent(Nil,IndexedSeq(), IndexedSeq("bla() -> <x:=1;><x:=x+1;>x=y".asFormula)))
    ).conclusion shouldBe Sequent(Nil,IndexedSeq(), IndexedSeq("bla() -> <x:=1;><{x:=x+1;}*>x=y".asFormula))
  }

  it should "use <*> approx to forward bla() -> (<x:=1;><{x:=x+1;}*>x=y -> foo()) to bla() -> (<x:=1;><x:=x+1;>x=y -> foo())" in {
    useFor("<*> approx", PosInExpr(1::Nil))(SuccPosition(0, PosInExpr(1::0::1::Nil))) (
      Provable.startProof(Sequent(Nil,IndexedSeq(), IndexedSeq("bla() -> (<x:=1;><{x:=x+1;}*>x=y -> foo())".asFormula)))
    ).conclusion shouldBe Sequent(Nil,IndexedSeq(), IndexedSeq("bla() -> (<x:=1;><x:=x+1;>x=y -> foo())".asFormula))
  }

  it should "use <*> approx to forward (<x:=1;><x:=x+1;>x=y -> bla()) -> foo() to (<x:=1;><{x:=x+1;}*>x=y -> bla()) -> foo()" in {
    useFor("<*> approx", PosInExpr(0::Nil))(SuccPosition(0, PosInExpr(0::0::1::Nil))) (
      Provable.startProof(Sequent(Nil,IndexedSeq(), IndexedSeq("(<x:=1;><x:=x+1;>x=y -> bla()) -> foo()".asFormula)))
    ).conclusion shouldBe Sequent(Nil,IndexedSeq(), IndexedSeq("(<x:=1;><{x:=x+1;}*>x=y -> bla()) -> foo()".asFormula))
  }

  it should "use <*> approx to forward <x:=1;><{x:=x+1;}*>x=y <-> bla() to <x:=1;><x:=x+1;>x=y -> bla()" in {
    useFor("<*> approx")(SuccPosition(0, PosInExpr(0::1::Nil))) (
      Provable.startProof(Sequent(Nil,IndexedSeq(), IndexedSeq("<x:=1;><{x:=x+1;}*>x=y <-> bla()".asFormula)))
    ).conclusion shouldBe Sequent(Nil,IndexedSeq(), IndexedSeq("<x:=1;><x:=x+1;>x=y -> bla()".asFormula))
  }
}
