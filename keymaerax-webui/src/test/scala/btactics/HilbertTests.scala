package edu.cmu.cs.ls.keymaerax.btactics

/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/


import edu.cmu.cs.ls.keymaerax.bellerophon.{RenUSubst, TheType, Position, PosInExpr, SuccPosition}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, UsualTest}
import testHelper.KeYmaeraXTestTags

import scala.collection.immutable._

/**
 * Tests Hilbert Calculus.
 * @author Andre Platzer
 */
@SummaryTest
@UsualTest
class HilbertTests extends TacticTestBase {
  import HilbertCalculus.Derive._

  object TestLib extends UnifyUSCalculus

  import TestLib.{CEat, CMon, useAt, useFor}

  val randomTrials = 50
  val randomComplexity = 3
  val rand = new RandomFormula() //(-4317240407825764493L)

  "Hilbert calculus" should "prove x>=5 -> [{x'=2&x<=9}]x<=9" in {
    proveBy(Sequent(IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2&x<=9}]x<=9".asFormula)),
      implyR(1) &
        DW(1) &
        abstractionb(1) & allR(1) & prop
    ) shouldBe 'proved
  }

  it should "prove x>=5 -> [{x'=2&x<=9}]x<=10" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2&x<=9}]x<=10".asFormula)),
      implyR(1) &
        DW(1) &
        abstractionb(1) & QE
    ) shouldBe 'proved
  }

  //@todo not everything ported yet
  it should "prove x>=5 -> [{x'=2}](x>=5)'" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2}](x>=5)'".asFormula)),
      implyR(1) &
        DE(1) &
        Dgreaterequal(1, 1::1::Nil) &
        Dvar(1, 1::1:: 0::Nil) &
        Dconst(1, 1::1:: 1::Nil) &
        Dassignb(1, 1::Nil) &
        abstractionb(1) & QE
    ) shouldBe 'proved
  }

  it should "prove (x+2*y)'=x'+2*y'" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("(x+2*y)'=x'+2*y'".asFormula)),
      Dplus(1, 0::Nil) &
        Dvar(1, 0::0::Nil) &
        useAt("' linear")(1, 0::1::Nil) & // Dtimes(SuccPosition(0, 0::1::Nil))
        Dvar(1, 0::1::1::Nil) &
        byUS("= reflexive")
    ) shouldBe 'proved
  }

  it should "prove (y)'=y forward" in withMathematica { qeTool =>
    val x = Variable("y")
    proveBy(
      Sequent(IndexedSeq(), IndexedSeq(Equal(Differential(x), DifferentialSymbol(x)))),
      Dvar(1,0::Nil) & byUS("= reflexive")) shouldBe 'proved
    proveBy(
      Sequent(IndexedSeq(), IndexedSeq(Equal(Differential(x), DifferentialSymbol(x)))),
      Dvar(1,0::Nil) & byUS("= reflexive")) shouldBe 'proved
  }

  it should "derive (y)'=y'" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("(y)'=y'".asFormula)),
      derive(1,0::Nil) & byUS("= reflexive")
    ) shouldBe 'proved
  }

  it should "derive (x+y)'=x'+y'" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("(x+y)'=x'+y'".asFormula)),
      derive(1,0::Nil) & byUS("= reflexive")
    ) shouldBe 'proved
  }

  it should "derive (x*y)'=x'*y+x*y'" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("(x*y)'=x'*y+x*y'".asFormula)),
      derive(1,0::Nil) & byUS("= reflexive")
    ) shouldBe 'proved
  }

  it should "derive (x+2*y)'=x'+2*y'" taggedAs KeYmaeraXTestTags.CheckinTest in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("(x+2*y)'=x'+2*y'".asFormula)),
      derive(1,0::Nil) & byUS("= reflexive")
    ) shouldBe 'proved
  }

  it should "derive (x^2)' >= 7 without crashing" in withMathematica{ qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("(x^2)' >= 7".asFormula)),
      stepAt(1, 0::Nil)
    ).subgoals shouldBe List(Sequent(IndexedSeq(), IndexedSeq("(2 * (x^(2-1))) * (x)' >= 7".asFormula)))
  }

  //@todo we only support optimized
  ignore should "derive (5*3+2*9)'=0*3+5*0+(0*9+2*0) unless optimized" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("(5*3+2*9)'=0*3+5*0+(0*9+2*0)".asFormula)),
      derive(1,0::Nil) & byUS("= reflexive")
    ) shouldBe 'proved
  }

  //@todo we only support optimized
  ignore should "derive (5*3+2*9)'=5*0+2*0 if optimized (left linear preferred but not const optimized)" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("(5*3+2*9)'=5*0+2*0".asFormula)),
      derive(1,0::Nil) & byUS("= reflexive")
    ) shouldBe 'proved
  }

  it should "derive (5*3+2*9)'=0 if optimized (const optimized)" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("(5*3+2*9)'=0".asFormula)),
      derive(1,0::Nil) & byUS("= reflexive")
    ) shouldBe 'proved
  }

  it should "derive (5*x+2*y)'=5*x'+2*y'" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("(5*x+2*y)'=5*x'+2*y'".asFormula)),
      derive(1,0::Nil) & byUS("= reflexive")
    ) shouldBe 'proved
  }

  it should "derive (5*x+2*y>=6)' <-> 5*x'+2*y'>=0" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("(5*x+2*y>=6)' <-> 5*x'+2*y'>=0".asFormula)),
      derive(1,0::Nil) & byUS("<-> reflexive")
    ) shouldBe 'proved
  }

  it should "derive (7*x<2*y & 22*x=4*y+8)' <-> (7*x'<=2*y' & 22*x'=4*y'+0)" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("(7*x<2*y & 22*x=4*y+8)' <-> (7*x'<=2*y' & 22*x'=4*y'+0)".asFormula)),
      derive(1,0::Nil) & byUS("<-> reflexive")
    ) shouldBe 'proved
  }

  it should "derive (x*x<2*y & 5*x+2*y>=6+z & 22*x=4*y+8)' <-> (x'*x+x*x'<=2*y' & 5*x'+2*y'>=0+z' & 22*x'=4*y'+0)" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("(x*x<2*y & 5*x+2*y>=6+z & 22*x=4*y+8)' <-> (x'*x+x*x'<=2*y' & 5*x'+2*y'>=0+z' & 22*x'=4*y'+0)".asFormula)),
      derive(1,0::Nil) & byUS("<-> reflexive")
    ) shouldBe 'proved
  }

  it should "derive [{x'=7,y'=-9,z'=2}](x*x<2*y & 5*x+2*y>=6+z & 22*x=4*y+8)' <-> [{x'=7,y'=-9,z'=2}](x'*x+x*x'<=2*y' & 5*x'+2*y'>=0+z' & 22*x'=4*y'+0)" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("[{x'=7,y'=-9,z'=2}](x*x<2*y & 5*x+2*y>=6+z & 22*x=4*y+8)' <-> [{x'=7,y'=-9,z'=2}](x'*x+x*x'<=2*y' & 5*x'+2*y'>=0+z' & 22*x'=4*y'+0)".asFormula)),
      derive(1,0::1::Nil) & byUS("<-> reflexive")
    ) shouldBe 'proved
  }

  it should "reduce [{x'=7}](5*x>=6)' to [{x'=7}]5*x'>=0" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("[{x'=7}](5*x>=6)'".asFormula)),
      derive(1,1::Nil)
    ).subgoals shouldBe List(Sequent(IndexedSeq(), IndexedSeq("[{x'=7}]5*x'>=0".asFormula)))
  }

  it should "reduce [{x'=99,y'=-3}](7*x<2*y & 22*x=4*y+8)' to [{x'=99,y'=-3}](7*x'<=2*y' & 22*x'=4*y'+0)" taggedAs KeYmaeraXTestTags.SummaryTest in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("[{x'=99,y'=-3}](7*x<2*y & 22*x=4*y+8)'".asFormula)),
      derive(1,1::Nil)
    ).subgoals shouldBe List(Sequent(IndexedSeq(), IndexedSeq("[{x'=99,y'=-3}](7*x'<=2*y' & 22*x'=4*y'+0)".asFormula)))
  }

  it should "prove x>=5 -> [{x'=2}]x>=5" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2}]x>=5".asFormula)),
      implyR(1) &
        DI(1) & (implyR(1) & andR(1)) <(
        prop,
        DE(1) &
          Dgreaterequal(1, 1::1::Nil) &
          Dvar(1, 1::1:: 0::Nil) &
          Dconst(1, 1::1:: 1::Nil) &
          Dassignb(1, 1::Nil) & abstractionb(1) & QE
        )
    ) shouldBe 'proved
  }

  it should "prove/derive x>=5 -> [{x'=2}]x>=5" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2}]x>=5".asFormula)),
      implyR(1) &
        DI(1) & (implyR(1) & andR(1)) <(
        prop,
        DE(1) & derive(1, 1::1::Nil) &
          Dassignb(1, 1::Nil) & abstractionb(1) & QE
        )
    ) shouldBe 'proved
  }

  //  it should "auto-prove x>=5 -> [{x'=2&x<=10}](5<=x&x<=10)" in {
  //    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2&x<=10}](5<=x&x<=10)".asFormula)),
  //      implyR(1) & diffCut(1)
  //    ) shouldBe 'proved
  //  }

  ignore should "prove x>=5 -> [{x'=2&x<=9}](5<=x&x<=10)" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2&x<=9}](5<=x&x<=10)".asFormula)),
      implyR(1) &
        DC("5<=x".asFormula)(1) & debug("after DC") &
        //@todo needs more branching to handle DI
        //@todo DC should not do absolute proof of implication but contextual
        DW(1) & debug("after DW") &
        abstractionb(1) & debug("after abstraction") & QE
    ) shouldBe 'proved
  }

  ignore should "auto-prove x>=5 -> [{x'=2&x<=9}](5<=x&x<=10) with DC" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2&x<=9}](5<=x&x<=10)".asFormula)),
      implyR(1) &
        //@todo the problem is that DI should be used in show prereq branch of useAt instead of defaulting to master
        DC("5<=x".asFormula)(1) <(
        debug("DC to DI") & diffInd()(1),
        debug("DC to DW") & DW(1) & abstractionb(1) & QE
        )
    ) shouldBe 'proved
  }

  ignore should "prove x>=5 -> [x:=x+1;{x'=2}]x>=5" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("x>=5 -> [x:=x+1;{x'=2}]x>=5".asFormula)),
      implyR(1) & //ind
        useAt("[;] compose")(1) &
        useAt("[:=] assign equational")(1) &
        step(1) & step(1) &
        useAt("DI differential invariant")(1) & //@todo diffInd(1)
        ((step('L) | step('R))*) & abstractionb(1) & master()
    ) shouldBe 'proved
  }

  it should "prove x>0 -> [x:=x+1;]x>0" in withMathematica { qeTool =>
    proveBy("x>0 -> [x:=x+1;]x>0".asFormula, step(1, 1::Nil) & QE) shouldBe 'proved
  }

  "UseAt" should "reduce x>5 |- [x:=x+1;x:=2*x;]x>1 to x>5 |- [x:=x+1;][x:=2*x;]x>1 by useAt" in {
    proveBy("[x:=x+1;x:=2*x;]x>1".asFormula, useAt("[;] compose")(1)).subgoals should contain only
      Sequent(IndexedSeq(), IndexedSeq("[x:=x+1;][x:=2*x;]x>1".asFormula))
  }

  it should "reduce x>5 |- [x:=x+1;][x:=2*x;]x>1 to x>5 |- [x:=x+1;x:=2*x;]x>1 by useAt backwards" in {
    proveBy(Sequent(IndexedSeq("x>5".asFormula), IndexedSeq("[x:=x+1;][x:=2*x;]x>1".asFormula)),
      useAt("[;] compose", PosInExpr(1::Nil))(SuccPos(0))).subgoals should contain only Sequent(IndexedSeq("x>5".asFormula), IndexedSeq("[x:=x+1;x:=2*x;]x>1".asFormula))
  }

  it should "reduce [x:=x+1;x:=2*x;]x>1 |- x>5 to [x:=x+1;][x:=2*x;]x>1 |- x>5 by useAt" in {
    proveBy(Sequent(IndexedSeq("[x:=x+1;x:=2*x;]x>1".asFormula), IndexedSeq("x>5".asFormula)),
      useAt("[;] compose")(AntePos(0))).subgoals should contain only Sequent(IndexedSeq("[x:=x+1;][x:=2*x;]x>1".asFormula), IndexedSeq("x>5".asFormula))
  }

  it should "reduce [x:=x+1;][x:=2*x;]x>1 |- x>5 to [x:=x+1;x:=2*x;]x>1 |- x>5 by useAt backwards" in {
    proveBy(Sequent(IndexedSeq("[x:=x+1;][x:=2*x;]x>1".asFormula), IndexedSeq("x>5".asFormula)),
      useAt("[;] compose", PosInExpr(1::Nil))(AntePos(0))).subgoals should contain only Sequent(IndexedSeq("[x:=x+1;x:=2*x;]x>1".asFormula), IndexedSeq("x>5".asFormula))
  }


  it should "reduce x>5 |- [c;d;]x>1 to x>5 |- [c;][d;]x>1 by useAt" in {
    proveBy(Sequent(IndexedSeq("x>5".asFormula), IndexedSeq("[c;d;]x>1".asFormula)),
      useAt("[;] compose")(SuccPos(0))).subgoals should contain only Sequent(IndexedSeq("x>5".asFormula), IndexedSeq("[c;][d;]x>1".asFormula))
  }

  it should "reduce x>5 |- [c;][d;]x>1 to x>5 |- [c;d;]x>1 by useAt backwards" in {
    proveBy(Sequent(IndexedSeq("x>5".asFormula), IndexedSeq("[c;][d;]x>1".asFormula)),
      useAt("[;] compose", PosInExpr(1::Nil))(SuccPos(0))).subgoals should contain only Sequent(IndexedSeq("x>5".asFormula), IndexedSeq("[c;d;]x>1".asFormula))
  }

  it should "reduce [c;d;]x>1 |- x>5 to [c;][d;]x>1 |- x>5 by useAt" in {
    proveBy(Sequent(IndexedSeq("[c;d;]x>1".asFormula), IndexedSeq("x>5".asFormula)),
      useAt("[;] compose")(AntePos(0))).subgoals should contain only Sequent(IndexedSeq("[c;][d;]x>1".asFormula), IndexedSeq("x>5".asFormula))
  }

  it should "reduce [c;][d;]x>1 |- x>5 to [c;d;]x>1 |- x>5 by useAt backwards" in {
    proveBy(Sequent(IndexedSeq("[c;][d;]x>1".asFormula), IndexedSeq("x>5".asFormula)),
      useAt("[;] compose", PosInExpr(1::Nil))(AntePos(0))).subgoals should contain only Sequent(IndexedSeq("[c;d;]x>1".asFormula), IndexedSeq("x>5".asFormula))
  }

  "Chase" should "prove [?x>0;x:=x+1; ++ ?x=0;x:=1;]x>0 by chase" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("[?x>0;x:=x+1; ++ ?x=0;x:=1;]x>0".asFormula)),
      chase(1,Nil) & QE
    ) shouldBe 'proved
  }

  it should "prove [?x>0;x:=x+1; ++ ?x=0;x:=1;]x>=1 by chase" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("[?x>0;x:=x+1; ++ ?x=0;x:=1;]x>=1".asFormula)),
      chase(1,Nil) & QE
    ) shouldBe 'proved
  }

  it should "prove [?x>0;x:=x+1; ++ ?x=0;x:=1; ++ x:=99; ++ ?x>=0;{{x:=x+1;++x:=x+2;};{y:=0;++y:=1;}}]x>=1 by chase" taggedAs KeYmaeraXTestTags.SummaryTest in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("[?x>0;x:=x+1; ++ ?x=0;x:=1; ++ x:=99; ++ ?x>=0;{{x:=x+1;++x:=x+2;};{y:=0;++y:=1;}}]x>=1".asFormula)),
      chase(1,Nil) & QE
    ) shouldBe 'proved
  }

  it should "prove [?x>0;x:=x+1;?x!=2; ++ ?x=0;x:=1;]x>=1 by chase" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("[?x>0;x:=x+1;?x!=2; ++ ?x=0;x:=1;]x>=1".asFormula)),
      chase(1,Nil) & QE
    ) shouldBe 'proved
  }

  it should "prove [?x>0;x:=x+1;x:=2*x; ++ ?x=0;x:=1;]x>=1 by chase" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("[?x>0;x:=x+1;x:=2*x; ++ ?x=0;x:=1;]x>=1".asFormula)),
      chase(1,Nil) & QE
    ) shouldBe 'proved
  }

  it should "chase [?x>0;x:=x+1; ++ ?x=0;x:=1; ++ x:=0;x:=x+1; ++ x:=1;?x>=2;]x>=1" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("[?x>0;x:=x+1; ++ ?x=0;x:=1; ++ x:=0;x:=x+1; ++ x:=1;?x>=2;]x>=1".asFormula)),
      // chaseWide(3) works like an update calculus
      chase(3,3)(1) &
        QE
    ) shouldBe 'proved
  }

  it should "auto-prove x>=5 -> [x:=x+1;{x'=2}]x>=5" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("x>=5 -> [x:=x+1;{x'=2}]x>=5".asFormula)),
      implyR(1) &
        chase(3,3)(1) &
        //@todo need to locate diffInd to after update prefix
        diffInd()(1, 1::Nil) &
        assignb(1) & // handle updates
        QE
    ) shouldBe 'proved
  }

  it should "chase [{x'=22}](2*x+x*y>=5)'" taggedAs KeYmaeraXTestTags.CheckinTest in withMathematica { qeTool =>
    proveBy("[{x'=22}](2*x+x*y>=5)'".asFormula,
      chase(1, 1 :: Nil)
    ).subgoals shouldBe List(Sequent(IndexedSeq(), IndexedSeq("[{x'=22}]2*x'+(x'*y+x*y')>=0".asFormula)))
  }

  it should "chase [{x'=22}][?x>0;x:=x+1; ++ ?x=0;x:=1;]x>=1" taggedAs KeYmaeraXTestTags.CheckinTest in {
    proveBy("[{x'=22}][?x>0;x:=x+1; ++ ?x=0;x:=1;]x>=1".asFormula,
      chase(1, 1 :: Nil)
    ).subgoals shouldBe List(Sequent(IndexedSeq(), IndexedSeq("[{x'=22}]((x>0->x+1>=1) & (x=0->1>=1))".asFormula)))
  }

  it should "prove x>=5 -> [x:=x+1;{x'=2}]x>=5" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("x>=5 -> [x:=x+1;{x'=2}]x>=5".asFormula)),
      implyR(1) & chase(1) &
        //@todo need to locate diffInd to after update prefix
        diffInd()(1, 1::Nil) &
        assignb(1) & // handle updates
        QE
    ) shouldBe 'proved
  }

  "CMon monotonicity" should "prove x<99 -> y<2 & x>5 |- x<99 -> y<2 & x>2 from x>5 |- x>2" in {
    val done = CMon(Context("x<99 -> y<2 & ⎵".asFormula)) (Provable.startProof(Sequent(IndexedSeq("x>5".asFormula), IndexedSeq("x>2".asFormula))))
    done.subgoals shouldBe List(Sequent(IndexedSeq("x>5".asFormula), IndexedSeq("x>2".asFormula)))
    done.conclusion shouldBe Sequent(IndexedSeq("x<99 -> y<2 & x>5".asFormula), IndexedSeq("x<99 -> y<2 & x>2".asFormula))
  }

  it should "prove x<99 -> y<2 & x>5 |- x<99 -> y<2 & x>2 from provable x>5 |- x>2" in withMathematica { qeTool =>
    val done = CMon(Context("x<99 -> y<2 & ⎵".asFormula)) (basicImpl)
    done shouldBe 'proved
    done.conclusion shouldBe Sequent(IndexedSeq("x<99 -> y<2 & x>5".asFormula), IndexedSeq("x<99 -> y<2 & x>2".asFormula))
  }

  private def shouldCMon(ctx: Context[Formula], basic: Provable = basicImpl): Unit = {
    require(basic.isProved)
    require(basic.conclusion.ante.length==1 && basic.conclusion.succ.length==1)
    val done = CMon(ctx)(basic)
    done shouldBe 'proved
    done.conclusion shouldBe Sequent(IndexedSeq(ctx(basic.conclusion.ante.head)), IndexedSeq(ctx(basic.conclusion.succ.head)))
  }

  private def shouldCMonA(ctx: Context[Formula], basic: Provable = basicImpl): Unit = {
    require(basic.isProved)
    require(basic.conclusion.ante.length==1 && basic.conclusion.succ.length==1)
    val done = CMon(ctx)(basic)
    done shouldBe 'proved
    done.conclusion shouldBe Sequent(IndexedSeq(ctx(basic.conclusion.succ.head)), IndexedSeq(ctx(basic.conclusion.ante.head)))
  }

  it should "prove y<2 & x>5 |- y<2 & x>2 from x>5 |- x>2" in withMathematica { qeTool => shouldCMon(Context("y<2 & ⎵".asFormula))}
  it should "prove x>5 & y<2 |- x>2 & y<2 from x>5 |- x>2" in withMathematica { qeTool => shouldCMon(Context("⎵ & y<2".asFormula))}
  it should "prove x<99 -> x>5 |- x<99 -> x>2 from x>5 |- x>2" in withMathematica { qeTool => shouldCMon(Context("x<99 -> ⎵".asFormula))}
  it should "prove x<99 | x>5 |- x<99 | x>2 from x>5 |- x>2" in withMathematica { qeTool => shouldCMon(Context("x<99 | ⎵".asFormula))}
  it should "prove in monotone context x<99 | _ & y<2" in withMathematica { qeTool => shouldCMon(Context("x<99 | ⎵ & y<2".asFormula))}
  it should "prove in monotone context (x<99 | _) & y<2" in withMathematica { qeTool => shouldCMon(Context("(x<99 | ⎵) & y<2".asFormula))}
  it should "prove in monotone context x<7 -> (x<99 | _) & y<2" in withMathematica { qeTool => shouldCMon(Context("x<7 -> (x<99 | ⎵) & y<2".asFormula))}
  it should "prove in monotone context x<y -> x<7 -> (x<99 | x<10 -> (_ & z=2 | x=5 & y=3)) & y<2" in withMathematica { qeTool => shouldCMon(Context("x<y -> x<7 -> (x<99 | x<10 -> (⎵ & z=2 | x=5 & y=3)) & y<2".asFormula))}
  it should "prove in monotone context \\forall y _" in withMathematica { qeTool => shouldCMon(Context("\\forall y ⎵".asFormula))}
  it should "prove in monotone context \\forall x _" in withMathematica { qeTool => shouldCMon(Context("\\forall x ⎵".asFormula))}
  it should "prove in monotone context \\exists y _" in withMathematica { qeTool => shouldCMon(Context("\\exists y ⎵".asFormula))}
  it should "prove in monotone context \\exists x _" in withMathematica { qeTool => shouldCMon(Context("\\exists x ⎵".asFormula))}
  it should "prove in monotone context !!\\exists x _" in withMathematica { qeTool => shouldCMon(Context("!!\\exists x ⎵".asFormula))}
  it should "prove in monotone context ![a:=2;]!\\exists x _" in withMathematica { qeTool => shouldCMon(Context("![a:=2;]!\\exists x ⎵".asFormula))}
  it should "prove in monotone context \\forall y (_ | x<y)" in withMathematica { qeTool => shouldCMon(Context("\\forall y (⎵ | x<y)".asFormula))}
  it should "prove in monotone context \\forall x (_ | x<y)" in withMathematica { qeTool => shouldCMon(Context("\\forall x (⎵ | x<y)".asFormula))}
  it should "prove in monotone context \\exists y (_ | x<y)" in withMathematica { qeTool => shouldCMon(Context("\\exists y (⎵ | x<y)".asFormula))}
  it should "prove in monotone context \\exists x (_ | x<y)" in withMathematica { qeTool => shouldCMon(Context("\\exists x (⎵ | x<y)".asFormula))}
  it should "prove in antimonotone context _ -> y<2" in withMathematica { qeTool => shouldCMonA(Context("⎵ -> y<2".asFormula))}
  it should "prove in antimonotone context _ -> y<2 & x<10" in withMathematica { qeTool => shouldCMonA(Context("⎵ -> y<2 & x<10".asFormula))}
  it should "prove in antimonotone context (_ -> y<2) & x<10" in withMathematica { qeTool => shouldCMonA(Context("(⎵ -> y<2) & x<10".asFormula))}
  it should "prove in antimonotone context (_ -> y<2) & x<10 | x=7" in withMathematica { qeTool => shouldCMonA(Context("(⎵ -> y<2) & x<10 | x=7".asFormula))}
  it should "prove in antimonotone context (<x:=5;>_ -> y<2) & x<10 | x=7" in withMathematica { qeTool => shouldCMonA(Context("(<x:=5;>⎵ -> y<2) & x<10 | x=7".asFormula))}
  it should "prove in antimonotone context (a=3|<x:=5;>_ -> y<2) & x<10 | x=7" in withMathematica { qeTool => shouldCMonA(Context("(a=3|<x:=5;>⎵ -> y<2) & x<10 | x=7".asFormula))}
  it should "prove in antimonotone context (<x:=5;>_&a=3 -> y<2) & x<10 | x=7" in withMathematica { qeTool => shouldCMonA(Context("(<x:=5;>⎵&a=3 -> y<2) & x<10 | x=7".asFormula))}
  it should "prove in antiantimonotone context ((_ -> y<2) -> z=0) & x<10 | x=7" in withMathematica { qeTool => shouldCMon(Context("((⎵ -> y<2) -> z=0) & x<10 | x=7".asFormula))}

  lazy val basicImpl = TactixLibrary.proveBy(Sequent(IndexedSeq("x>5".asFormula), IndexedSeq("x>2".asFormula)),
    TactixLibrary.QE)

  it should "prove C{x>5} |- C{x>2} from provable x>5 |- x>2 in most random positive contexts" in withMathematica { qeTool =>
    println("Starting random contexts\n\n")
    for (i <- 1 to randomTrials) {
      val ctx = rand.nextFormulaContext(randomComplexity)
      if (ctx.isFormulaContext) {
        println("Context: " + ctx)
        try {
          //@todo discard ctx unless positive
          if (FormulaTools.polarityAt(ctx.ctx, FormulaTools.posOf(ctx.ctx, DotFormula).getOrElse(
            throw new InterruptedException("skip"))) > 0) {
            //@todo discard ctx if DotFormula within a program
            //@todo discard ctx if DotFormula somewhere underneath an Equiv
            val done = CMon(ctx)(basicImpl)
            done shouldBe 'proved
            done.conclusion shouldBe Sequent(IndexedSeq(ctx("x>5".asFormula)), IndexedSeq(ctx("x>2".asFormula)))
          }
        } catch {
          case e: ProverException => if (e.toString.startsWith("No monotone context")) println("context discarded") else throw e
          //case e: IllegalArgumentException if e.getMessage.startsWith("requirement failed:") => println("Requirement not met: " + e)
          case e: InterruptedException =>
        }
      }
    }
  }

  lazy val basicEq = TactixLibrary.proveBy("1=0*x+1".asFormula, TactixLibrary.QE)
  lazy val basicEquiv = TactixLibrary.proveBy("-2<x&x<2 <-> x^2<4".asFormula, TactixLibrary.QE)

  private def shouldReduceTo(input: Formula, pos: Int, inExpr: PosInExpr, result: Formula, fact: Provable = basicEq): Unit =
    proveBy(input, CEat(fact)(pos, inExpr.pos)).subgoals should contain only
      new Sequent(IndexedSeq(), IndexedSeq(result))

  private def shouldReduceTo(input: Formula, pos: Int, inExpr: PosInExpr, result: Formula, fact: Provable, C: Context[Formula]): Unit =
    proveBy(input, CEat(fact, C)(pos, inExpr.pos)).subgoals should contain only
      new Sequent(IndexedSeq(), IndexedSeq(result))

  "CE(Provable) equation magic" should "reduce 0*x+1<=3 to 1<=3" in withMathematica { qeTool =>
    shouldReduceTo("0*x+1<=3".asFormula, 1, PosInExpr(0::Nil), "1<=3".asFormula)
  }

  it should "reduce x<5 & 0*x+1<=3 | x>=2 to x<5 & 1<=3 | x>=2" taggedAs KeYmaeraXTestTags.SummaryTest in withMathematica { qeTool =>
    shouldReduceTo("x<5 & 0*x+1<=3 | x>=2".asFormula, 1, PosInExpr(0::1::0::Nil), "x<5 & 1<=3 | x>=2".asFormula)
  }

  it should "reduce \\forall x 0*x+1<=3 to \\forall x 1<=3" in withMathematica { qeTool =>
    shouldReduceTo("\\forall x 0*x+1<=3".asFormula, 1, PosInExpr(0::0::Nil), "\\forall x 1<=3".asFormula)
  }

  ignore should "reduce x<5 & \\forall x 0*x+1<=3 | x>=2 to x<5 & \\forall x 1<=3 | x>=2" taggedAs KeYmaeraXTestTags.SummaryTest in withMathematica { qeTool =>
    shouldReduceTo("x<5 & \\forall x 0*x+1<=3 | x>=2".asFormula, 1, PosInExpr(0::1::0::0::Nil), "x<5 & \\forall x 1<=3 | x>=2".asFormula)
  }

  it should "reduce [x:=7;]0*x+1<=3 to [x:=7;]1<=3" in withMathematica { qeTool =>
    shouldReduceTo("[x:=7;]0*x+1<=3".asFormula, 1, PosInExpr(1::0::Nil), "[x:=7;]1<=3".asFormula)
  }

  it should "reduce [x:=7;?0*x+1<=3;]x<9 to [x:=7;?1<=3;]x<9" in withMathematica { qeTool =>
    shouldReduceTo("[x:=7;?0*x+1<=3;]x<9".asFormula, 1, PosInExpr(0::1::0::0::Nil), "[x:=7;?1<=3;]x<9".asFormula)
  }

  it should "reduce [x:=0*x+1;]x<9 to [x:=1;]x<9" in withMathematica { qeTool =>
    shouldReduceTo("[x:=0*x+1;]x<9".asFormula, 1, PosInExpr(0::1::Nil), "[x:=1;]x<9".asFormula)
  }

  ignore should "reduce [x:=7;x:=0*x+1;]x<9 to [x:=7;x:=1;]x<9" in withMathematica { qeTool =>
    shouldReduceTo("[x:=7;x:=0*x+1;]x<9".asFormula, 1, PosInExpr(0::1::1::Nil), "[x:=7;x:=1;]x<9".asFormula)
  }

  it should "reduce [{x' = 7 & 0*x+1<2}]x>=2 to [{x' = 7 & 1<2}]x>=2" in withMathematica { qeTool =>
    shouldReduceTo("[{x' = 7 & 0*x+1<2}]x>=2".asFormula, 1, PosInExpr(0::1::0::Nil), "[{x' = 7 & 1<2}]x>=2".asFormula)
  }

  ignore should "reduce [{x' = 0*x+1 & 5=5}]x>=2 to [{x' = 1 & 5=5}]x>=2" in withMathematica { qeTool =>
    shouldReduceTo("[{x' = 0*x+1 & 5=5}]x>=2".asFormula, 1, PosInExpr(0::0::1::Nil), "[{x' = 1 & 5=5}]x>=2".asFormula)
  }


  "CE(Provable) equivalence magic" should "reduce x^2<4 to -2<x&x<2" in withMathematica { qeTool =>
    shouldReduceTo("x^2<4".asFormula, 1, PosInExpr(Nil), "-2<x&x<2".asFormula, basicEquiv)
  }

  it should "reduce !(x^2<4) to !(-2<x&x<2)" in withMathematica { qeTool =>
    shouldReduceTo("!x^2<4".asFormula, 1, PosInExpr(0::Nil), "!(-2<x&x<2)".asFormula, basicEquiv)
  }

  it should "reduce x<5 & x^2<4 | x>=2 to x<5 & (-2<x&x<2) | x>=2" in withMathematica { qeTool =>
    shouldReduceTo("x<5 & x^2<4| x>=2".asFormula, 1, PosInExpr(0::1::Nil), "x<5 & (-2<x&x<2) | x>=2".asFormula, basicEquiv)
  }

  it should "reduce x<5 & \\forall x x^2<4 | x>=2 to x<5 & \\forall x (-2<x&x<2) | x>=2" in withMathematica { qeTool =>
    shouldReduceTo("x<5 & \\forall x x^2<4| x>=2".asFormula, 1, PosInExpr(0::1::0::Nil), "x<5 & \\forall x (-2<x&x<2) | x>=2".asFormula, basicEquiv)
  }

  it should "reduce [{x' = 5*x & x^2<4}]x>=1 to [{x' = 5*x & -2<x&x<2}]x>=1" taggedAs KeYmaeraXTestTags.SummaryTest in withMathematica { qeTool =>
    shouldReduceTo("[{x' = 5*x & x^2<4}]x>=1".asFormula, 1, PosInExpr(0::1::Nil), "[{x' = 5*x & -2<x&x<2}]x>=1".asFormula, basicEquiv)
  }

  it should "reduce x<5 & x^2<4 -> [{x' = 5*x & x^2<4}](x^2<4 & x>=1) to x<5 & (-2<x&x<2) -> [{x' = 5*x & -2<x&x<2}]((-2<x&x<2) & x>=1)" in withMathematica { qeTool =>
    val C = Context("x<5 & ⎵ -> [{x' = 5*x & ⎵}](⎵ & x>=1)".asFormula)
    shouldReduceTo("x<5 & x^2<4 -> [{x' = 5*x & x^2<4}](x^2<4 & x>=1)".asFormula, 1, PosInExpr(), "x<5 & (-2<x&x<2) -> [{x' = 5*x & -2<x&x<2}]((-2<x&x<2) & x>=1)".asFormula, basicEquiv, C)
  }

  "useFor" should "use DX to forward (true&x=y) to <{x'=2}>x=y" in {
    useFor("DX diamond differential skip", PosInExpr(0::Nil),
      (us:RenUSubst) => us++RenUSubst(Seq((DifferentialProgramConst("c", AnyArg), KeYmaeraXParser.differentialProgramParser("x'=2"))))
    )(SuccPosition(1, Nil)) (
      Provable.startProof(Sequent(IndexedSeq(), IndexedSeq("(true&x=y)".asFormula)))
    ).conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("<{x'=2}>x=y".asFormula))
  }

  it should "use DX to forward <{x'=2}>x=y -> bla() to (true&x=y) -> bla()" in {
    useFor("DX diamond differential skip")(SuccPosition(1, 0::Nil)) (
      Provable.startProof(Sequent(IndexedSeq(), IndexedSeq("<{x'=2}>x=y -> bla()".asFormula)))
    ).conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("(true&x=y) -> bla()".asFormula))
  }

  it should "use DX to forward <{x'=2}>x=y <-> bla() to (true&x=y) -> bla()" in {
    useFor("DX diamond differential skip")(SuccPosition(1, 0::Nil)) (
      Provable.startProof(Sequent(IndexedSeq(), IndexedSeq("<{x'=2}>x=y <-> bla()".asFormula)))
    ).conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("(true&x=y) -> bla()".asFormula))
  }

  // with context

  it should "use <*> approx to forward <x:=x+1;>x=y to <{x:=x+1;}*>x=y" in {
    useFor("<*> approx", PosInExpr(0::Nil))(SuccPosition(1, Nil)) (
      Provable.startProof(Sequent(IndexedSeq(), IndexedSeq("<x:=x+1;>x=y".asFormula)))
    ).conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("<{x:=x+1;}*>x=y".asFormula))
  }

  it should "use <*> approx to forward <{x:=x+1;}*>x=y -> bla() to <x:=x+1;>x=y -> bla()" in {
    useFor("<*> approx")(SuccPosition(1, 0::Nil)) (
      Provable.startProof(Sequent(IndexedSeq(), IndexedSeq("<{x:=x+1;}*>x=y -> bla()".asFormula)))
    ).conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("<x:=x+1;>x=y -> bla()".asFormula))
  }

  it should "use <*> approx to forward <{x:=x+1;}*>x=y <-> bla() to <x:=x+1;>x=y -> bla()" in {
    useFor("<*> approx")(SuccPosition(1, (0::Nil))) (
      Provable.startProof(Sequent(IndexedSeq(), IndexedSeq("<{x:=x+1;}*>x=y <-> bla()".asFormula)))
    ).conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("<x:=x+1;>x=y -> bla()".asFormula))
  }

  it should "use <*> approx to forward bla() <-> <{x:=x+1;}*>x=y to <x:=x+1;>x=y -> bla()" in {
    useFor("<*> approx")(SuccPosition(1, (1::Nil))) (
      Provable.startProof(Sequent(IndexedSeq(), IndexedSeq("bla() <-> <{x:=x+1;}*>x=y".asFormula)))
    ).conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("<x:=x+1;>x=y -> bla()".asFormula))
  }

  it should "use DX to forward <x:=1;>(true&x=y) to <x:=1;><{x'=2}>x=y" in {
    useFor("DX diamond differential skip", PosInExpr(0::Nil))(SuccPosition(1, (1::Nil))) (
      Provable.startProof(Sequent(IndexedSeq(), IndexedSeq("<x:=1;>(true&x=y)".asFormula)))
    ).conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("<x:=1;><{c}>x=y".asFormula))
  }

  it should "use DX to forward <x:=1;><{x'=2}>x=y -> bla() to <x:=1;>(true&x=y) -> bla()" in {
    useFor("DX diamond differential skip")(SuccPosition(1, (0::1::Nil))) (
      Provable.startProof(Sequent(IndexedSeq(), IndexedSeq("<x:=1;><{x'=2}>x=y -> bla()".asFormula)))
    ).conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("<x:=1;>(true&x=y) -> bla()".asFormula))
  }

  it should "use DX to forward <x:=1;><{x'=2}>x=y <-> bla() to <x:=1;>(true&x=y) -> bla()" in {
    useFor("DX diamond differential skip")(SuccPosition(1, (0::1::Nil))) (
      Provable.startProof(Sequent(IndexedSeq(), IndexedSeq("<x:=1;><{x'=2}>x=y <-> bla()".asFormula)))
    ).conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("<x:=1;>(true&x=y) -> bla()".asFormula))
  }

  it should "use <*> approx to forward <x:=1;>x=1 to <{x:=1;}*>x=1" in {
    useFor("<*> approx", PosInExpr(0::Nil))(SuccPosition(1, (Nil))) (
      Provable.startProof(Sequent(IndexedSeq(), IndexedSeq("<x:=1;>x=1".asFormula)))
    ).conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("<{x:=1;}*>x=1".asFormula))
  }

  it should "use <*> approx to forward <x:=1;><x:=x+1;>x=y to <x:=1;><{x:=x+1;}*>x=y" in {
    useFor("<*> approx", PosInExpr(0::Nil))(SuccPosition(1, (1::Nil))) (
      Provable.startProof(Sequent(IndexedSeq(), IndexedSeq("<x:=1;><x:=x+1;>x=y".asFormula)))
    ).conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("<x:=1;><{x:=x+1;}*>x=y".asFormula))
  }

  it should "use <*> approx to forward <x:=1;><{x:=x+1;}*>x=y -> bla() to <x:=1;><x:=x+1;>x=y -> bla()" in {
    useFor("<*> approx", PosInExpr(1::Nil))(SuccPosition(1, (0::1::Nil))) (
      Provable.startProof(Sequent(IndexedSeq(), IndexedSeq("<x:=1;><{x:=x+1;}*>x=y -> bla()".asFormula)))
    ).conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("<x:=1;><x:=x+1;>x=y -> bla()".asFormula))
  }

  it should "use <*> approx to forward bla() -> <x:=1;><x:=x+1;>x=y to bla() -> <x:=1;><{x:=x+1;}*>x=y" in {
    useFor("<*> approx", PosInExpr(0::Nil))(SuccPosition(1, (1::1::Nil))) (
      Provable.startProof(Sequent(IndexedSeq(), IndexedSeq("bla() -> <x:=1;><x:=x+1;>x=y".asFormula)))
    ).conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("bla() -> <x:=1;><{x:=x+1;}*>x=y".asFormula))
  }

  it should "use <*> approx to forward bla() -> (<x:=1;><{x:=x+1;}*>x=y -> foo()) to bla() -> (<x:=1;><x:=x+1;>x=y -> foo())" in {
    useFor("<*> approx", PosInExpr(1::Nil))(SuccPosition(1, (1::0::1::Nil))) (
      Provable.startProof(Sequent(IndexedSeq(), IndexedSeq("bla() -> (<x:=1;><{x:=x+1;}*>x=y -> foo())".asFormula)))
    ).conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("bla() -> (<x:=1;><x:=x+1;>x=y -> foo())".asFormula))
  }

  it should "use <*> approx to forward (<x:=1;><x:=x+1;>x=y -> bla()) -> foo() to (<x:=1;><{x:=x+1;}*>x=y -> bla()) -> foo()" in {
    useFor("<*> approx", PosInExpr(0::Nil))(SuccPosition(1, (0::0::1::Nil))) (
      Provable.startProof(Sequent(IndexedSeq(), IndexedSeq("(<x:=1;><x:=x+1;>x=y -> bla()) -> foo()".asFormula)))
    ).conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("(<x:=1;><{x:=x+1;}*>x=y -> bla()) -> foo()".asFormula))
  }

  it should "use <*> approx to forward <x:=1;><{x:=x+1;}*>x=y <-> bla() to <x:=1;><x:=x+1;>x=y -> bla()" in {
    useFor("<*> approx")(SuccPosition(1, (0::1::Nil))) (
      Provable.startProof(Sequent(IndexedSeq(), IndexedSeq("<x:=1;><{x:=x+1;}*>x=y <-> bla()".asFormula)))
    ).conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("<x:=1;><x:=x+1;>x=y -> bla()".asFormula))
  }

  it should "use ^' derive power to forward (x^2)'=0 to 2*x^(2-1)*(x)'=0" in withMathematica { qeTool =>
    useFor("^' derive power")(SuccPosition(1, 0::Nil)) (
      Provable.startProof(Sequent(IndexedSeq(), IndexedSeq("(x^2)'=0".asFormula)))
    ).conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("(2*x^(2-1))*(x)'=0".asFormula))
  }
}
