/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.btactics.Ax.timesInverse
import org.keymaerax.btactics.Derive.{useAt, useFor, CMon}
import org.keymaerax.btactics.RefinementCalculus._
import org.keymaerax.btactics.TacticTestBase
import org.keymaerax.btactics.TactixLibrary.implyR
import org.keymaerax.btactics.macros.DerivationInfoAugmentors.ProvableInfoAugmentor
import org.keymaerax.core.SuccPos
import org.keymaerax.infrastruct.{Context, PosInExpr, Position}
import org.keymaerax.parser.StringConverter.StringToStringConverter
import org.keymaerax.pt.ProvableSig

class RefinementCalculusTests extends TacticTestBase {
  "Auxiliary axioms" should "prove" in {
    val axioms = List(
      congrChoiceL,
      congrChoiceR,
      congrSeqL,
      congrSeqR,
      congrODEDom,
      congrODEDoms,
      refDiamond.provable,
    )
    axioms.map(axiom => axiom.isProved shouldBe true)
  }

  "useAt" should "transform formulas within discrete programs" in {
    val pr = TactixLibrary.proveBy(
      "[{y:=0;++x:=*;{?(true -> x!=0);++?x=0;};x:=*;}*]y>0".asFormula,
      useAt(timesInverse)(Position(1, List(0, 0, 1, 1, 0, 0, 0, 1))),
    )
    pr.subgoals.head shouldBe " ==> [{y:=0;++x:=*;{?(true -> x*(x^(-1)) = 1);++?x=0;};x:=*;}*]y>0".asSequent

    val pr2 = TactixLibrary.proveBy(
      "<{y:=0;++x:=*;{?(true -> x*(x^(-1)) = 1);++?x=0;};x:=*;}*>y>0".asFormula,
      useAt(timesInverse, PosInExpr(1 :: Nil))(Position(1, List(0, 0, 1, 1, 0, 0, 0, 1))),
    )
    pr2.subgoals.head shouldBe " ==> <{y:=0;++x:=*;{?(true -> x!= 0);++?x=0;};x:=*;}*>y>0".asSequent

    val pr3 = TactixLibrary.proveBy(
      "[{y:=0;++x:=*;{?(x*(x^(-1)) = 1 -> true);++?x=0;};x:=*;}*]y>0".asFormula,
      useAt(timesInverse, PosInExpr(1 :: Nil))(Position(1, List(0, 0, 1, 1, 0, 0, 0, 0))),
    )
    pr3.subgoals.head shouldBe " ==> [{y:=0;++x:=*;{?(x!=0 -> true);++?x=0;};x:=*;}*]y>0".asSequent

    val pr4 = TactixLibrary.proveBy(
      "<{y:=0;++x:=*;{?(x!=0 -> true);++?x=0;};x:=*;}*>y>0".asFormula,
      useAt(timesInverse)(Position(1, List(0, 0, 1, 1, 0, 0, 0, 0))),
    )
    pr4.subgoals.head shouldBe " ==> <{y:=0;++x:=*;{?(x*(x^(-1)) = 1 -> true);++?x=0;};x:=*;}*>y>0".asSequent

  }

  "useAt" should "transform formulas in domain" in {
    val pr = TactixLibrary
      .proveBy("[{x' = y^2 & true -> x!=0}]y>0".asFormula, useAt(timesInverse)(Position(1, List(0, 1, 1))))
    pr.subgoals.head shouldBe " ==> [{x' = y^2 & true -> x*(x^(-1)) = 1}]y>0".asSequent

    val pr2 = TactixLibrary
      .proveBy("[{y' = y^2 & true -> y!=0}]y>0".asFormula, useAt(timesInverse)(Position(1, List(0, 1, 1))))
    pr2.subgoals.head shouldBe " ==> [{y' = y^2 & true -> y*(y^(-1)) = 1}]y>0".asSequent

    val pr3 = TactixLibrary.proveBy(
      "<{x' = y^2 & true -> x*(x^(-1)) = 1}>y>0".asFormula,
      useAt(timesInverse, PosInExpr(1 :: Nil))(Position(1, List(0, 1, 1))),
    )
    pr3.subgoals.head shouldBe " ==> <{x' = y^2 & true -> x!= 0}>y>0".asSequent

    val prs = TactixLibrary
      .proveBy("[{x' = y^2, y' = 1 & true -> x!=0}]y>0".asFormula, useAt(timesInverse)(Position(1, List(0, 1, 1))))
    prs.subgoals.head shouldBe " ==> [{x' = y^2, y' = 1 & true -> x*(x^(-1)) = 1}]y>0".asSequent

    val pr2s = TactixLibrary
      .proveBy("[{z' = y^2, y' = 1 & true -> z!=0}]y>0".asFormula, useAt(timesInverse)(Position(1, List(0, 1, 1))))
    pr2s.subgoals.head shouldBe " ==> [{z' = y^2, y' = 1 & true -> z*(z^(-1)) = 1}]y>0".asSequent

    val pr3s = TactixLibrary.proveBy(
      "<{x' = y^2, y' = 1 & true -> x*(x^(-1)) = 1}>y>0".asFormula,
      useAt(timesInverse, PosInExpr(1 :: Nil))(Position(1, List(0, 1, 1))),
    )
    pr3s.subgoals.head shouldBe " ==> <{x' = y^2, y' = 1 & true -> x!= 0}>y>0".asSequent
  }

  "useAt" should "transform formulas in refinements" in {
    val pr = TactixLibrary.proveBy(
      "?x=0; <= x:=0;?x*(x^(-1)) = 1;".asFormula,
      useAt(timesInverse, PosInExpr(1 :: Nil))(Position(1, List(1, 1, 0))),
    )
    pr.subgoals.head shouldBe " ==> ?x=0; <= x:=0;?x!=0;".asSequent

    val pr2 = TactixLibrary.proveBy("x:=0;?x!=0; <= ?x=0;".asFormula, useAt(timesInverse)(Position(1, List(0, 1, 0))))
    pr2.subgoals.head shouldBe " ==> x:=0;?x*(x^(-1)) = 1; <= ?x=0;".asSequent
  }
}
