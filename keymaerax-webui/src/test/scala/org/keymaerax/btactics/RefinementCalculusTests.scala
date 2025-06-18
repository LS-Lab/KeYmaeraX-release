/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon.TacticInapplicableFailure
import org.keymaerax.btactics.Ax.{notGreaterEqual, timesInverse}
import org.keymaerax.btactics.RefinementCalculus.*
import org.keymaerax.btactics.UnifyUSCalculus.{useAt, CMon}
import org.keymaerax.btactics.macros.DerivationInfoAugmentors.ProvableInfoAugmentor
import org.keymaerax.infrastruct.PosInExpr
import org.keymaerax.parser.StringConverter.StringToStringConverter

class RefinementCalculusTests extends TacticTestBase {
  "Auxiliary axioms" should "prove" in {
    val axioms = List(
      congrChoiceL,
      congrChoiceR,
      congrSeqL,
      congrSeqR,
      congrODEDom,
      refDiamond.provable,
      hideChoiceL.provable,
      hideChoiceR.provable,
      refEq,
      prgEqSym,
      testSeq.provable,
      testChoice.provable,
      skipRandom.provable,
      doubleLoop.provable,
      refUnloopWeak.provable,
    )
    axioms.map(axiom => axiom.isProved shouldBe true)
  }

  "refOde" should "apply to one-dimensional odes" in {
    val pr = TactixLibrary.proveBy("{x'=y & x>=0} == {x'=y+0 & x>=0}".asFormula, refOde(1))
    pr.subgoals.head shouldBe " ==> [{x'=y & x>=0}](y = y+0)".asSequent
  }

  it should "extend to two-dimensional odes" in {
    val pr = TactixLibrary.proveBy("{x'=y, y'=-x & x>=0} == {x'=y+0, y'=-1*x & x>=0}".asFormula, refOde(1))
    pr.subgoals.head shouldBe " ==> [{x'=y, y'=-x & x>=0}](y = y+0 & -x = -1*x)".asSequent
  }

  it should "extend to three-dimensional odes" in {
    val pr = TactixLibrary
      .proveBy("{x'=y, y'=-x, t'=1 & x>=0} == {x'=y+0, y'=-1*x, t'=(-1)^2 & x>=0}".asFormula, refOde(1))
    pr.subgoals.head shouldBe " ==> [{x'=y, y'=-x, t'=1 & x>=0}](y = y+0 & -x = -1*x & 1 = (-1)^2)".asSequent
  }

  it should "fail if the dimensions do not match" in {
    val e = the[TacticInapplicableFailure] thrownBy
      TactixLibrary.proveBy("{x'=y, y'=-x & x>=0} == {x'=y+0, y'=-1*x, t'=(-1)^2 & x>=0}".asFormula, refOde(1))
    e.getMessage shouldBe "ODEs do not have compatible shape: {x'=y,y'=-x} and {x'=y+0,y'=-1*x,t'=(-1)^2}"
  }

  it should "fail if the variables do not match" in {
    val e = the[TacticInapplicableFailure] thrownBy
      TactixLibrary.proveBy("{x'=y, y'=-x, v'=1 & x>=0} == {x'=y+0, y'=-1*x, t'=(-1)^2 & x>=0}".asFormula, refOde(1))
    e.getMessage shouldBe "ODEs do not have compatible variables: v' and t'"
  }

  "useAt" should "transform formulas within discrete programs" in {
    val pr = TactixLibrary.proveBy(
      "[{y:=0;++x:=*;{?(true -> x!=0);++?x=0;};x:=*;}*]y>0".asFormula,
      useAt(timesInverse)(1, List(0, 0, 1, 1, 0, 0, 0, 1)),
    )
    pr.subgoals.head shouldBe " ==> [{y:=0;++x:=*;{?(true -> x*(x^(-1)) = 1);++?x=0;};x:=*;}*]y>0".asSequent

    val pr2 = TactixLibrary.proveBy(
      "<{y:=0;++x:=*;{?(true -> x*(x^(-1)) = 1);++?x=0;};x:=*;}*>y>0".asFormula,
      useAt(timesInverse, PosInExpr(1 :: Nil))(1, List(0, 0, 1, 1, 0, 0, 0, 1)),
    )
    pr2.subgoals.head shouldBe " ==> <{y:=0;++x:=*;{?(true -> x!= 0);++?x=0;};x:=*;}*>y>0".asSequent

    val pr3 = TactixLibrary.proveBy(
      "[{y:=0;++x:=*;{?(x*(x^(-1)) = 1 -> true);++?x=0;};x:=*;}*]y>0".asFormula,
      useAt(timesInverse, PosInExpr(1 :: Nil))(1, List(0, 0, 1, 1, 0, 0, 0, 0)),
    )
    pr3.subgoals.head shouldBe " ==> [{y:=0;++x:=*;{?(x!=0 -> true);++?x=0;};x:=*;}*]y>0".asSequent

    val pr4 = TactixLibrary.proveBy(
      "<{y:=0;++x:=*;{?(x!=0 -> true);++?x=0;};x:=*;}*>y>0".asFormula,
      useAt(timesInverse)(1, List(0, 0, 1, 1, 0, 0, 0, 0)),
    )
    pr4.subgoals.head shouldBe " ==> <{y:=0;++x:=*;{?(x*(x^(-1)) = 1 -> true);++?x=0;};x:=*;}*>y>0".asSequent

  }

  it should "transform formulas in domain" in {
    val pr = TactixLibrary.proveBy("[{x' = y^2 & true -> x!=0}]y>0".asFormula, useAt(timesInverse)(1, List(0, 1, 1)))
    pr.subgoals.head shouldBe " ==> [{x' = y^2 & true -> x*(x^(-1)) = 1}]y>0".asSequent

    val pr2 = TactixLibrary.proveBy("[{y' = y^2 & true -> y!=0}]y>0".asFormula, useAt(timesInverse)(1, List(0, 1, 1)))
    pr2.subgoals.head shouldBe " ==> [{y' = y^2 & true -> y*(y^(-1)) = 1}]y>0".asSequent

    val pr3 = TactixLibrary.proveBy(
      "<{x' = y^2 & true -> x*(x^(-1)) = 1}>y>0".asFormula,
      useAt(timesInverse, PosInExpr(1 :: Nil))(1, List(0, 1, 1)),
    )
    pr3.subgoals.head shouldBe " ==> <{x' = y^2 & true -> x!= 0}>y>0".asSequent

    val prs = TactixLibrary
      .proveBy("[{x' = y^2, y' = 1 & true -> x!=0}]y>0".asFormula, useAt(timesInverse)(1, List(0, 1, 1)))
    prs.subgoals.head shouldBe " ==> [{x' = y^2, y' = 1 & true -> x*(x^(-1)) = 1}]y>0".asSequent

    val pr2s = TactixLibrary
      .proveBy("[{z' = y^2, y' = 1 & true -> z!=0}]y>0".asFormula, useAt(timesInverse)(1, List(0, 1, 1)))
    pr2s.subgoals.head shouldBe " ==> [{z' = y^2, y' = 1 & true -> z*(z^(-1)) = 1}]y>0".asSequent

    val pr3s = TactixLibrary.proveBy(
      "<{x' = y^2, y' = 1 & true -> x*(x^(-1)) = 1}>y>0".asFormula,
      useAt(timesInverse, PosInExpr(1 :: Nil))(1, List(0, 1, 1)),
    )
    pr3s.subgoals.head shouldBe " ==> <{x' = y^2, y' = 1 & true -> x!= 0}>y>0".asSequent
  }

  it should "transform formulas in refinements" in {
    val pr = TactixLibrary
      .proveBy("?x=0; <= x:=0;?x*(x^(-1)) = 1;".asFormula, useAt(timesInverse, PosInExpr(1 :: Nil))(1, List(1, 1, 0)))
    pr.subgoals.head shouldBe " ==> ?x=0; <= x:=0;?x!=0;".asSequent

    val pr2 = TactixLibrary.proveBy("x:=0;?x!=0; <= ?x=0;".asFormula, useAt(timesInverse)(1, List(0, 1, 0)))
    pr2.subgoals.head shouldBe " ==> x:=0;?x*(x^(-1)) = 1; <= ?x=0;".asSequent
  }

  it should "transform equivalent formulas in refinements" in {
    val pr = TactixLibrary
      .proveBy("?x=0; <= x:=0;?x < 1;".asFormula, useAt(notGreaterEqual, PosInExpr(1 :: Nil))(1, List(1, 1, 0)))
    pr.subgoals.head shouldBe " ==> ?x=0; <= x:=0;?!(x>= 1);".asSequent
    val pr2 = TactixLibrary.proveBy("x:=0;?!(x>= 1); <= ?x=0;".asFormula, useAt(notGreaterEqual)(1, List(0, 1, 0)))
    pr2.subgoals.head shouldBe " ==> x:=0;?x < 1; <= ?x=0;".asSequent
  }

  it should "transform programs in modality" in {
    val pr = TactixLibrary.proveBy("[x':=2;?(x>=0);]x > 0".asFormula, useAt(refDX, PosInExpr(0 :: Nil))(1, 0 :: Nil))
    pr.subgoals.head shouldBe " ==> [{x'=2 & x>=0}] x > 0".asSequent

    val pr2 = TactixLibrary.proveBy("<x:=*;++y:=*;>x > 0".asFormula, useAt(hideChoiceL)(1, 0 :: Nil))
    pr2.subgoals.head shouldBe " ==> <y:=*;> x > 0".asSequent

    val pr3 = TactixLibrary.proveBy("[x:=*;++y:=*;]x > 0 ==> false".asSequent, useAt(hideChoiceL)(-1, 0 :: Nil))
    pr3.subgoals.head shouldBe "[y:=*;]x > 0 ==> false".asSequent
  }

  it should "transform equivalent programs in modality" in {
    val pr = TactixLibrary.proveBy("[x:=2;?true;]x > 0".asFormula, useAt(refSeqIdR, PosInExpr(0 :: Nil))(1, 0 :: Nil))
    pr.subgoals.head shouldBe " ==> [x:=2;] x > 0".asSequent

    val pr2 = TactixLibrary.proveBy("[x:=2;]x > 0".asFormula, useAt(refSeqIdR, PosInExpr(1 :: Nil))(1, 0 :: Nil))
    pr2.subgoals.head shouldBe " ==> [x:=2;?true;] x > 0".asSequent
  }

  it should "transform programs in refinement" in {
    val pr = TactixLibrary
      .proveBy("x':=2;?(x>=0); <= x:=*;++y:=*;".asFormula, useAt(refDX, PosInExpr(0 :: Nil))(1, 0 :: Nil))
    pr.subgoals.head shouldBe " ==> {x'=2 & x>=0} <= x:=*;++y:=*;".asSequent

    val pr2 = TactixLibrary.proveBy("x:=2; <= x:=*;++y:=*;".asFormula, useAt(hideChoiceL)(1, 1 :: Nil))
    pr2.subgoals.head shouldBe " ==> x:=2; <= y:=*;".asSequent
  }

  it should "transform equivalent programs in refinement" in {
    val pr = TactixLibrary
      .proveBy("x:=2;?true; <= x:=*;++y:=*;".asFormula, useAt(refSeqIdR, PosInExpr(0 :: Nil))(1, 0 :: Nil))
    pr.subgoals.head shouldBe " ==> x:=2; <= x:=*;++y:=*;".asSequent

    val pr2 = TactixLibrary
      .proveBy("x:=2; <= x:=*;++y:=*;".asFormula, useAt(refSeqIdR, PosInExpr(1 :: Nil))(1, 0 :: Nil))
    pr2.subgoals.head shouldBe " ==> x:=2;?true; <= x:=*;++y:=*;".asSequent
  }

  "CMon" should "allow contextual refinement in positive context" in {
    val pr = TactixLibrary
      .proveBy("x:=10;{x'=-x & x > 5}; <= x:=10;{x'=-x & x > 2};".asFormula, CMon(PosInExpr(1 :: 1 :: Nil)))
    pr.subgoals.head shouldBe " ==> x > 5 -> x > 2".asSequent
  }

  it should "allow contextual refinement in negative context" in {
    val pr = TactixLibrary
      .proveBy("x:=-10;{x'=x & !(x > 2)}; <= x:=-10;{x'=x & !(x > 5)};".asFormula, CMon(PosInExpr(1 :: 1 :: 0 :: Nil)))
    pr.subgoals.head shouldBe " ==> x > 5 -> x > 2".asSequent
  }

  it should "allow argument refinement in positive context" in {
    val pr = TactixLibrary.proveBy(
      "<x:=10;{x'=-x & x > 5};> x = 6 -> <x:=10;{x'=-x & x > 2};> x = 6".asFormula,
      CMon(PosInExpr(0 :: 1 :: Nil)),
    )
    pr.subgoals.head shouldBe " ==> {x'=-x & x > 5}; <= {x'=-x & x > 2};".asSequent
  }

  it should "allow argument refinement in negative context" in {
    val pr = TactixLibrary.proveBy(
      "[x:=10;{x'=-x & x > 2};] x > 0 -> [x:=10;{x'=-x & x > 5};] x > 0".asFormula,
      CMon(PosInExpr(0 :: 1 :: Nil)),
    )
    pr.subgoals.head shouldBe " ==> {x'=-x & x > 5}; <= {x'=-x & x > 2};".asSequent
  }

  it should "allow both contextual and argument refinement in positive context" in {
    val pr = TactixLibrary
      .proveBy("x:=10;{x'=-x & x > 5}; <= x:=10;{x'=-x & x > 2};".asFormula, CMon(PosInExpr(1 :: Nil)))
    pr.subgoals.head shouldBe " ==> {x'=-x & x > 5}; <= {x'=-x & x > 2};".asSequent
  }

  "focus" should "simplify programs refinement" in {
    val pr = TactixLibrary.proveBy("x:=2;y:=1; ++ z:=3; <= x:=*;y:=1; ++ z:=3;".asFormula, focus(1, 0 :: 0 :: 0 :: Nil))
    pr.subgoals.head shouldBe "==> x:=2; <= x:=*;".asSequent
  }

  it should "behave identically if given the position of the other program" in {
    val pr = TactixLibrary.proveBy("x:=2;y:=1; ++ z:=3; <= x:=*;y:=1; ++ z:=3;".asFormula, focus(1, 1 :: 0 :: 0 :: Nil))
    pr.subgoals.head shouldBe "==> x:=2; <= x:=*;".asSequent
  }

  it should "add modalities to preserve assumptions" in {
    val pr = TactixLibrary
      .proveBy("x > 0 ==> {y:=1;x:=2; ++ z:=3;}* <= {y:=1;x:=*; ++ z:=3;}*".asSequent, focus(1, List(0, 0, 0, 1)))
    pr.subgoals.head shouldBe "x > 0 ==> [{y:=1;x:=2; ++ z:=3;}*][y:=1;]x:=2; <= x:=*;".asSequent
  }

  it should "simplify down to formula implication in test" in {
    val pr = TactixLibrary
      .proveBy("x > 0 ==> ?(true);y:=1; ++ z:=3; <= ?(x=2);y:=1; ++ z:=3;".asSequent, focus(1, List(0, 0, 0, 0)))
    pr.subgoals.head shouldBe "x > 0 ==> true -> x=2".asSequent
  }

  it should "simplify down to formula implication in ODE's domain" in {
    val pr = TactixLibrary.proveBy("x > 0 ==> {x'= x & x < 5} <= {x'= x & x < 10}".asSequent, focus(1, 0 :: 1 :: Nil))
    pr.subgoals.head shouldBe "x > 0 ==> [{x'= x & x < 5}](x < 5 -> x < 10)".asSequent
  }
}
