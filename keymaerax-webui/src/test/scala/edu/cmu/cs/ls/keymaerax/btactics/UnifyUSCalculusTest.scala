/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.btactics.EqualityTactics.eqL2R
import edu.cmu.cs.ls.keymaerax.btactics.SequentCalculus._
import edu.cmu.cs.ls.keymaerax.btactics.UnifyUSCalculus._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.{QE, prop}
import edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfoAugmentors.ProvableInfoAugmentor
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tags.{CheckinTest, SummaryTest, UsualTest}
import testHelper.KeYmaeraXTestTags
import org.scalatest.LoneElement._

import scala.collection.immutable._

/**
  * Tests UnifyUSCalculus useAt parts.
  * @see [[UnifyUSCalculus]]
  * @author Andre Platzer
  */
@SummaryTest
@UsualTest
@CheckinTest
class UnifyUSCalculusTest extends TacticTestBase {
  val randomTrials = 10
  val randomComplexity = 3
  val rand = new RandomFormula() //(-4317240407825764493L)

  "useAt" should "prove ([a;][b;]p(x)) ==> [a;b;]p(x)" in withTactics {
    proveBy("([a;][b;]p(x)) ==> [a;b;]p(x)".asSequent, useAt(Ax.composeb)(1) & id) shouldBe Symbol("proved")
  }

  it should "prove ([a;][b;]p(x)) -> [a;b;]p(x)" in withTactics {
    proveBy("([a;][b;]p(x)) -> [a;b;]p(x)".asFormula, useAt(Ax.composeb)(1, 1::Nil) & implyR(1) & id) shouldBe Symbol("proved")
  }

  it should "prove [a;b;]p(x) ==> ([a;][b;]p(x))" in withTactics {
    proveBy("[a;b;]p(x) ==> ([a;][b;]p(x))".asSequent, useAt(Ax.composeb)(-1) & id) shouldBe Symbol("proved")
  }

  it should "prove [a;b;]p(x) -> ([a;][b;]p(x))" in withTactics {
    proveBy("[a;b;]p(x) -> ([a;][b;]p(x))".asFormula, useAt(Ax.composeb)(1, 0::Nil) & implyR(1) & id) shouldBe Symbol("proved")
  }

  it should "prove (p()->q()) ==> [?p();]q()" in withTactics {
    proveBy("(p()->q()) ==> [?p();]q()".asSequent, useAt(Ax.testb)(1) & id) shouldBe Symbol("proved")
  }

  it should "prove (p()->q()) -> [?p();]q()" in withTactics {
    proveBy("(p()->q()) -> [?p();]q()".asFormula, useAt(Ax.testb)(1, 1::Nil) & implyR(1) & id) shouldBe Symbol("proved")
  }

  it should "prove [?p();]q() ==> (p()->q())" in withTactics {
    proveBy("[?p();]q() ==> (p()->q())".asSequent, useAt(Ax.testb)(-1) & id) shouldBe Symbol("proved")
  }

  it should "prove [?p();]q() -> (p()->q())" in withTactics {
    proveBy("[?p();]q() -> (p()->q())".asFormula, useAt(Ax.testb)(1, 0::Nil) & implyR(1) & id) shouldBe Symbol("proved")
  }

  it should "prove (1>=1) ==> 1+0>=1" in withTactics {
    proveBy("(1>=1) ==> 1+0>=1".asSequent, useAt(Ax.plusZero)(1,0::Nil) & id) shouldBe Symbol("proved")
  }

  it should "prove (1>=1) -> 1+0>=1" in withTactics {
    proveBy("(1>=1) -> 1+0>=1".asFormula, useAt(Ax.plusZero)(1,1::0::Nil) & implyR(1) & id) shouldBe Symbol("proved")
  }

  it should "prove 1+0>=1 ==> 1>=1" in withTactics {
    proveBy("1+0>=1 ==> 1>=1".asSequent, useAt(Ax.plusZero)(-1,0::Nil) & id) shouldBe Symbol("proved")
  }

  it should "prove 1+0>=1 -> 1>=1" in withTactics {
    proveBy("1+0>=1 -> 1>=1".asFormula, useAt(Ax.plusZero)(1,0::0::Nil) & implyR(1) & id) shouldBe Symbol("proved")
  }


  it should "prove x+1>0 -> [x:=x+1;]x>0" in withTactics {
    proveBy("x+1>0 -> [x:=x+1;]x>0".asFormula, useAt(Ax.assignbAxiom)(1, 1::Nil) & implyR(1) & id) shouldBe Symbol("proved")
  }

  "UseAt" should "reduce x>5 |- [x:=x+1;x:=2*x;]x>1 to x>5 |- [x:=x+1;][x:=2*x;]x>1 by useAt" in withTactics {
    proveBy("[x:=x+1;x:=2*x;]x>1".asFormula, useAt(Ax.composeb)(1)).subgoals should contain only
      Sequent(IndexedSeq(), IndexedSeq("[x:=x+1;][x:=2*x;]x>1".asFormula))
  }

  it should "reduce x>5 |- [x:=x+1;][x:=2*x;]x>1 to x>5 |- [x:=x+1;x:=2*x;]x>1 by useAt backwards" in withTactics {
    proveBy(Sequent(IndexedSeq("x>5".asFormula), IndexedSeq("[x:=x+1;][x:=2*x;]x>1".asFormula)),
      useAt(Ax.composeb, PosInExpr(1::Nil))(SuccPos(0))).subgoals should contain only Sequent(IndexedSeq("x>5".asFormula), IndexedSeq("[x:=x+1;x:=2*x;]x>1".asFormula))
  }

  it should "reduce [x:=x+1;x:=2*x;]x>1 |- x>5 to [x:=x+1;][x:=2*x;]x>1 |- x>5 by useAt" in withTactics {
    proveBy(Sequent(IndexedSeq("[x:=x+1;x:=2*x;]x>1".asFormula), IndexedSeq("x>5".asFormula)),
      useAt(Ax.composeb)(AntePos(0))).subgoals should contain only Sequent(IndexedSeq("[x:=x+1;][x:=2*x;]x>1".asFormula), IndexedSeq("x>5".asFormula))
  }

  it should "reduce [x:=x+1;][x:=2*x;]x>1 |- x>5 to [x:=x+1;x:=2*x;]x>1 |- x>5 by useAt backwards" in withTactics {
    proveBy(Sequent(IndexedSeq("[x:=x+1;][x:=2*x;]x>1".asFormula), IndexedSeq("x>5".asFormula)),
      useAt(Ax.composeb, PosInExpr(1::Nil))(AntePos(0))).subgoals should contain only Sequent(IndexedSeq("[x:=x+1;x:=2*x;]x>1".asFormula), IndexedSeq("x>5".asFormula))
  }


  it should "reduce x>5 |- [c;d;]x>1 to x>5 |- [c;][d;]x>1 by useAt" in withTactics {
    proveBy(Sequent(IndexedSeq("x>5".asFormula), IndexedSeq("[c;d;]x>1".asFormula)),
      useAt(Ax.composeb)(SuccPos(0))).subgoals should contain only Sequent(IndexedSeq("x>5".asFormula), IndexedSeq("[c;][d;]x>1".asFormula))
  }

  it should "reduce x>5 |- [c;][d;]x>1 to x>5 |- [c;d;]x>1 by useAt backwards" in withTactics {
    proveBy(Sequent(IndexedSeq("x>5".asFormula), IndexedSeq("[c;][d;]x>1".asFormula)),
      useAt(Ax.composeb, PosInExpr(1::Nil))(SuccPos(0))).subgoals should contain only Sequent(IndexedSeq("x>5".asFormula), IndexedSeq("[c;d;]x>1".asFormula))
  }

  it should "reduce [c;d;]x>1 |- x>5 to [c;][d;]x>1 |- x>5 by useAt" in withTactics {
    proveBy(Sequent(IndexedSeq("[c;d;]x>1".asFormula), IndexedSeq("x>5".asFormula)),
      useAt(Ax.composeb)(AntePos(0))).subgoals should contain only Sequent(IndexedSeq("[c;][d;]x>1".asFormula), IndexedSeq("x>5".asFormula))
  }

  it should "reduce [c;][d;]x>1 |- x>5 to [c;d;]x>1 |- x>5 by useAt backwards" in withTactics {
    proveBy(Sequent(IndexedSeq("[c;][d;]x>1".asFormula), IndexedSeq("x>5".asFormula)),
      useAt(Ax.composeb, PosInExpr(1::Nil))(AntePos(0))).subgoals should contain only Sequent(IndexedSeq("[c;d;]x>1".asFormula), IndexedSeq("x>5".asFormula))
  }

  it should "use a conditional equivalence subproof" in withTactics {
    val mainProof = ProvableSig.startPlainProof("x=1 ==> !y*x>0 <-> !y>0".asSequent)
    val subProof = ProvableSig.startPlainProof("==> x=1 -> (y*x>0 <-> y>0)".asSequent)(
      implyR(1), 0)(
      eqL2R(-1)(SuccPosition(1, List(0))), 0)(
      useAt(Ax.timesIdentity)(SuccPosition(1, List(0, 0))), 0)(
      CoHideRight(SuccPos(0)), 0)(
      byUS(Ax.equivReflexive.provable), 0)
    proveBy(mainProof, useAt(subProof, PosInExpr(List(1,0)))(1, PosInExpr(List(0,0)))).subgoals.
      loneElement shouldBe "x=1 ==> !y>0 <-> !y>0".asSequent
  }

  it should "use an unproved conditional equivalence subproof" in withTactics {
    val mainProof = ProvableSig.startPlainProof("P ==> !Q <-> !R".asSequent)
    val subProof = ProvableSig.startPlainProof("==> P -> (Q<->R)".asSequent)
    proveBy(mainProof, useAt(subProof, PosInExpr(List(1,0)))(1, PosInExpr(List(0, 0)))).subgoals should
      contain theSameElementsInOrderAs List(
      "==> P -> (Q<->R)".asSequent,
      "P ==> !R <-> !R".asSequent
    )
  }

  it should "use a conditional equality subproof" in withTactics {
    val mainProof = ProvableSig.startPlainProof("x=1 ==> !(y*x!=y)".asSequent)
    val subProof = ProvableSig.startPlainProof("==> x=1 -> y*x=y".asSequent)(
      implyR(1), 0)(
      eqL2R(-1)(SuccPosition(1, List(0))), 0)(
      useAt(Ax.timesIdentity)(SuccPosition(1, List(0))), 0)(
      CoHideRight(SuccPos(0)), 0)(
      byUS(Ax.equalReflexive.provable), 0)
    proveBy(mainProof, useAt(subProof, PosInExpr(List(1,0)))(1, PosInExpr(List(0,0)))).subgoals.
      loneElement shouldBe "x=1 ==> !(y!=y)".asSequent
  }

  "Chase" should "prove [?p();?(p()->q());]p() by chase" in withTactics {
    proveBy(Sequent(IndexedSeq(), IndexedSeq("[?p();?(p()->q());]p()".asFormula)),
      chase(1) & prop
    ) shouldBe Symbol("proved")
  } 
    
  it should "prove [?p();?(p()->q()); ++ ?r();?q();]q() by chase" in withTactics {
    proveBy(Sequent(IndexedSeq(), IndexedSeq("[?p();?(p()->q()); ++ ?r();?q();]q()".asFormula)),
      chase(1) & prop
    ) shouldBe Symbol("proved")
  }

  it should "prove [?p();?(p()->q()); ++ ?!p();](p()->q()) by chase" in withTactics {
    //assert(AxIndex.axiomIndex(Ax.composeb)._1==PosInExpr(0::Nil))
    //assert(AxIndex.axiomIndex(Ax.composeb)._2==PosInExpr(1::Nil)::PosInExpr(Nil)::Nil)
    proveBy(Sequent(IndexedSeq(), IndexedSeq("[?p();?(p()->q()); ++ ?!p();](p()->q())".asFormula)),
      chase(1,Nil) & prop
    ) shouldBe Symbol("proved")
  }
  
  it should "prove [?p();?(p()->q()); ++ ?r();?q(); ++ ?!p()&!r();](p()|r()->q()) by chase" in withTactics {
    proveBy(Sequent(IndexedSeq(), IndexedSeq("[?p();?(p()->q()); ++ ?r();?q(); ++ ?!p()&!r();](p()|r()->q())".asFormula)),
      chase(1,Nil) & prop
    ) shouldBe Symbol("proved")
  }

  it should "prove [?x>0;x:=x+1; ++ ?x=0;x:=1;]x>0 by chase" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("[?x>0;x:=x+1; ++ ?x=0;x:=1;]x>0".asFormula)),
      chase(1,Nil) & QE
    ) shouldBe Symbol("proved")
  }

  it should "prove [?x>0;x:=x+1; ++ ?x=0;x:=1;]x>=1 by chase" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("[?x>0;x:=x+1; ++ ?x=0;x:=1;]x>=1".asFormula)),
      chase(1,Nil) & QE
    ) shouldBe Symbol("proved")
  }

  it should "prove [?x>0;x:=x+1; ++ ?x=0;x:=1; ++ x:=99; ++ ?x>=0;{{x:=x+1;++x:=x+2;};{y:=0;++y:=1;}}]x>=1 by chase" taggedAs KeYmaeraXTestTags.SummaryTest in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("[?x>0;x:=x+1; ++ ?x=0;x:=1; ++ x:=99; ++ ?x>=0;{{x:=x+1;++x:=x+2;};{y:=0;++y:=1;}}]x>=1".asFormula)),
      chase(1,Nil) & QE
    ) shouldBe Symbol("proved")
  }

  it should "prove [?x>0;x:=x+1;?x!=2; ++ ?x=0;x:=1;]x>=1 by chase" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("[?x>0;x:=x+1;?x!=2; ++ ?x=0;x:=1;]x>=1".asFormula)),
      chase(1,Nil) & QE
    ) shouldBe Symbol("proved")
  }

  it should "prove [?x>0;x:=x+1;x:=2*x; ++ ?x=0;x:=1;]x>=1 by chase" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("[?x>0;x:=x+1;x:=2*x; ++ ?x=0;x:=1;]x>=1".asFormula)),
      chase(1,Nil) & QE
    ) shouldBe Symbol("proved")
  }

  it should "chase [?x>0;x:=x+1; ++ ?x=0;x:=1; ++ x:=0;x:=x+1; ++ x:=1;?x>=2;]x>=1" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("[?x>0;x:=x+1; ++ ?x=0;x:=1; ++ x:=0;x:=x+1; ++ x:=1;?x>=2;]x>=1".asFormula)),
      // chaseWide(3) works like an update calculus
      chase(3,3)(1) &
        QE
    ) shouldBe Symbol("proved")
  }

  it should "chase games" in {
    proveBy("==> <a;--b;>P()".asSequent, chase(1)).subgoals.loneElement shouldBe "==> <a;>P() & <b;>P()".asSequent
    proveBy("==> <a;b;--c;>P()".asSequent, chase(1)).subgoals.loneElement shouldBe "==> <a;><b;>P() & <c;>P()".asSequent
    proveBy("==> <{{a;^@}*}^@>P()".asSequent, chase(1)).subgoals.loneElement shouldBe "==> [{a;^@}*]P()".asSequent
  }

  it should "chase inside quantifiers" in {
    proveBy("==> \\exists x [x:=x+1;]\\exists y [y:=y-1;]x>=y".asSequent, deepChase(1)).subgoals.loneElement shouldBe "==> \\exists x \\exists y x+1>=y-1".asSequent
    proveBy("\\forall x \\forall y [x:=x+y;]x>=0 ==>".asSequent, deepChase(-1)).subgoals.loneElement shouldBe "\\forall x \\forall y x+y>=0 ==>".asSequent
  }

  it should "chase more inside quantifiers" in {
    proveBy("\\forall m \\forall z (b()>0->[a:=A();][t:=0;{z'=v,v'=a,t'=1}]z>=0) ==>".asSequent, deepChase(-1)).subgoals.
      loneElement shouldBe "\\forall m \\forall z (b()>0->\\forall t (t=0->[{z'=v,v'=A(),t'=1}]z>=0)) ==>".asSequent
  }

  "CMon monotonicity" should "prove x<99 -> y<2 & x>5 |- x<99 -> y<2 & x>2 from x>5 |- x>2" in withTactics {
    val done = CMon(Context("x<99 -> y<2 & ⎵".asFormula)) (ProvableSig.startPlainProof(Sequent(IndexedSeq("x>5".asFormula), IndexedSeq("x>2".asFormula))))
    done.subgoals shouldBe List(Sequent(IndexedSeq("x>5".asFormula), IndexedSeq("x>2".asFormula)))
    done.conclusion shouldBe Sequent(IndexedSeq("x<99 -> y<2 & x>5".asFormula), IndexedSeq("x<99 -> y<2 & x>2".asFormula))
  }

  it should "prove x<99 -> y<2 & x>5 |- x<99 -> y<2 & x>2 from provable x>5 |- x>2" in withMathematica { qeTool =>
    val done = CMon(Context("x<99 -> y<2 & ⎵".asFormula)) (basicImpl)
    done shouldBe Symbol("proved")
    done.conclusion shouldBe Sequent(IndexedSeq("x<99 -> y<2 & x>5".asFormula), IndexedSeq("x<99 -> y<2 & x>2".asFormula))
  }

  private def shouldCMon(ctx: Context[Formula], basic: ProvableSig = basicImpl): Unit = {
    require(basic.isProved)
    require(basic.conclusion.ante.length==1 && basic.conclusion.succ.length==1)
    val done = CMon(ctx)(basic)
    done shouldBe Symbol("proved")
    done.conclusion shouldBe Sequent(IndexedSeq(ctx(basic.conclusion.ante.head)), IndexedSeq(ctx(basic.conclusion.succ.head)))
  }

  private def shouldCMonA(ctx: Context[Formula], basic: ProvableSig = basicImpl): Unit = {
    require(basic.isProved)
    require(basic.conclusion.ante.length==1 && basic.conclusion.succ.length==1)
    val done = CMon(ctx)(basic)
    done shouldBe Symbol("proved")
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
            done shouldBe Symbol("proved")
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

  private def shouldReduceTo(input: Formula, pos: Int, inExpr: PosInExpr, result: Formula, fact: ProvableSig = basicEq): Unit =
    proveBy(input, CEat(fact)(pos, inExpr.pos)).subgoals should contain only
      new Sequent(IndexedSeq(), IndexedSeq(result))

  private def shouldReduceTo(input: Formula, pos: Int, inExpr: PosInExpr, result: Formula, fact: ProvableSig, C: Context[Formula]): Unit =
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

  "US" should "uniformly substitute in a single goal" in {
    proveBy("J(x) ==> J(x+1)".asSequent, USX("J(.) ~> .>=0".asSubstitutionPair :: Nil)).subgoals.loneElement shouldBe "x>=0 ==> x+1>=0".asSequent
  }

  it should "uniformly substitute in all goals" in {
    proveBy("J(x) ==> J(x+1) & J(x+2)".asSequent, andR(1) & USX("J(.) ~> .>=0".asSubstitutionPair :: Nil)).subgoals shouldBe
      List("x>=0 ==> x+1>=0".asSequent, "x>=0 ==> x+2>=0".asSequent)
  }

}
