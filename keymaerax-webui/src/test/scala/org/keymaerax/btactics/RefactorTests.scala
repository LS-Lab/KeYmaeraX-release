/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.btactics.Refactor.*
import org.keymaerax.btactics.RefinementCalculus.*
import org.keymaerax.btactics.UnifyUSCalculus.useAt
import org.keymaerax.btactics.macros.DerivationInfoAugmentors.ProvableInfoAugmentor
import org.keymaerax.core.Sequent
import org.keymaerax.infrastruct.Augmentors.SequentAugmentor
import org.keymaerax.infrastruct.{PosInExpr, Position}
import org.keymaerax.parser.StringConverter.StringToStringConverter
import org.keymaerax.pt.ProvableSig

class RefactorTests extends TacticTestBase {
  "Refactor axioms" should "prove" in {
    val axioms = List(
      congrAndL,
      congrAndR,
      congrOrL,
      congrOrR,
      congrImpL,
      congrImpR,
      congrRefL,
      congrRefR,
      prgEqBoundRandom,
      prgEqBoundRandomD,
      prgEqBoundAssign,
      prgEqBoundAssignD,
      fuseLoopAux,
      fuseLoopAuxD,
      fuseLoop,
      fuseLoopD,
      moveRandomLoop,
      moveRandomLoopD,
      prgEqLoopComm,
      prgEqIsolComm,
      prgEqIsolCommFix,
    )
    axioms.map(axiom => axiom.isProved shouldBe true)
  }

  def checkFocus(seq: Sequent, pos: Position): Unit = {
    val pr = TactixLibrary.proveBy(seq, focus(pos))
    val (updatedPos, ctxt) = focusPos(seq(pos.top), pos.inExpr)

    pr.subgoals.head.ante shouldBe seq.ante
    pr.subgoals.head.at(pos.topLevel ++ updatedPos)._1 shouldBe ctxt
  }

  "focus" should "simplify programs refinement" in {
    checkFocus("==> x:=2;y:=1; ++ z:=3; <= x:=*;y:=1; ++ z:=3;".asSequent, Position(1, 0 :: 0 :: 0 :: Nil))
  }

  it should "behave identically if given the position of the other program" in {
    checkFocus("==> x:=2;y:=1; ++ z:=3; <= x:=*;y:=1; ++ z:=3;".asSequent, Position(1, 1 :: 0 :: 0 :: Nil))
  }

  it should "add modalities to preserve assumptions" in {
    checkFocus("x > 0 ==> {y:=1;x:=2; ++ z:=3;}* <= {y:=1;x:=*; ++ z:=3;}*".asSequent, Position(1, List(0, 0, 0, 1)))
  }

  it should "simplify down to formula implication in test" in {
    checkFocus(
      "x > 0 ==> ?(true & z = 2);y:=1; ++ z:=3; <= ?(x=2 & z = 2);y:=1; ++ z:=3;".asSequent,
      Position(1, List(0, 0, 0, 0, 0)),
    )
  }

  it should "simplify down to formula implication in ODE's domain" in {
    checkFocus(
      "x > 0 ==> {x'= x & x < 5 & x > 0} <= {x'= x & x < 10 & x > 0}".asSequent,
      Position(1, 0 :: 1 :: 0 :: Nil),
    )
  }

  it should "simplify implication" in {
    checkFocus(
      "x > 0 ==> [x:=x+2;](x > 2 & z < 0) -> [x:=x+2;](x > 1 & z < 0)".asSequent,
      Position(1, 0 :: 1 :: 0 :: Nil),
    )
  }

  it should "simplify add binder to preserve assumption" in {
    checkFocus(
      "x > 0 ==> \\forall z (x > 2 & z < 0) -> \\forall z (x > 1 & z < 0)".asSequent,
      Position(1, 0 :: 0 :: 0 :: Nil),
    )
  }

  it should "simplify down to refinement in box" in {
    checkFocus(
      "x > 0 ==> [{x:=x+2;y:=*;}*](x > 2) -> [{x:=x+2;y:=0;}*](x > 2)".asSequent,
      // [[focusPos]] fails using `List(0, 0, 0, 1)` because of the loop
      Position(1, List(1, 0, 0, 1)),
    )
  }

  it should "simplify down to refinement in diamond" in {
    checkFocus(
      "x > 0 ==> <{x:=x+2;y:=0;}*>(x > 2) -> <{x:=x+2;y:=*;}*>(x > 2)".asSequent,
      Position(1, List(0, 0, 0, 1)),
    )
  }

  it should "simplify down to refinement in refinement" in {
    checkFocus(
      "x > 0 ==> {x:=x+2;y:=*;}* <= x:=*;y:=*; -> {x:=x+2;y:=0;}* <= x:=*;y:=*;".asSequent,
      // [[focusPos]] fails using `List(0, 0, 0, 1)` because of the loop
      Position(1, List(1, 0, 0, 1)),
    )
  }

  it should "simplify in presence of loops with different polarities" in {
    // Because the two loops have different polarities, [[focusPos]] fails to generate the final context.
    val pr = TactixLibrary
      .proveBy("x > 0 ==> {?[{x:=*;}*]x = 0;}* <= {?[{x:=0;}*]x = 0;}*".asSequent, focus(1, List(1, 0, 0, 0, 0)))
    pr.subgoals.head shouldBe "x > 0 ==> [{?[{x:=*;}*]x=0;}*][{x:=0;}*]{x:=0;}<={x:=*;}".asSequent
  }

  "dropODE" should "apply on box" in {
    val pr = TactixLibrary.proveBy("[{x'=y & x>=0 & x <= 0}]x >= 0".asFormula, dropODEr(1, 0 :: Nil))
    pr.subgoals.head shouldBe "==> [{x'=y & x>=0}]x >= 0".asSequent
    pr.subgoals.length shouldBe 1
  }

  it should "apply on diamond" in {
    val seq = "==> <{x'=y & x>=0 & x <= 0}>x >= 0".asSequent
    val pr = TactixLibrary.proveBy(seq, dropODEr(1, 0 :: Nil))
    pr.subgoals.head shouldBe "==> <{x'=y & x>=0}> x >= 0".asSequent
    pr.subgoals.length shouldBe 2
    val (pos, ctxt) = focusPos("<{x'=y & x>=0}> x >= 0".asFormula, PosInExpr(0 :: 1 :: Nil))
    pr.subgoals.tail.head.at(Position(1) ++ pos) shouldBe (ctxt, "x<=0".asFormula)
  }

  it should "apply on an antecedent diamond" in {
    val pr = TactixLibrary.proveBy("<{x'=y & x>=0 & x <= 0}>x >= 0 ==> x >= 0".asSequent, dropODEr(-1, 0 :: Nil))
    pr.subgoals.head shouldBe "<{x'=y & x>=0}>x >= 0 ==> x >= 0".asSequent
    pr.subgoals.length shouldBe 1
  }

  it should "apply on an antecedent box" in {
    val seq = "[{x'=y & x>=0 & x <= 0}]x >= 0 ==> x >= 0".asSequent
    val pr = TactixLibrary.proveBy(seq, dropODEr(-1, 0 :: Nil))
    pr.subgoals.head shouldBe "[{x'=y & x>=0}]x >= 0 ==> x >= 0".asSequent
    pr.subgoals.length shouldBe 2
    val (pos, ctxt) = focusPos("[{x'=y & x>=0}]x >= 0".asFormula, PosInExpr(0 :: 1 :: Nil))
    pr.subgoals.tail.head.at(Position(2) ++ pos) shouldBe (ctxt, "x<=0".asFormula)
  }

  "introduceODE" should "apply on diamond" in {
    val pr = TactixLibrary.proveBy("<{x'=y & x>=0}>x >= 0".asFormula, introduceODE("x <= 0".asFormula)(1, 0 :: Nil))
    pr.subgoals.head shouldBe "==> <{x'=y & x>=0 & x <= 0}>x >= 0".asSequent
    pr.subgoals.length shouldBe 1
  }

  it should "apply on box" in {
    val seq = "==> [{x'=y & x>=0}]x >= 0".asSequent
    val pr = TactixLibrary.proveBy(seq, introduceODE("x <= 0".asFormula)(1, 0 :: Nil))
    pr.subgoals.head shouldBe "==> [{x'=y & x>=0 & x <= 0}] x >= 0".asSequent
    pr.subgoals.length shouldBe 2
    val (pos, ctxt) = focusPos("[{x'=y & x>=0}] x >= 0".asFormula, PosInExpr(0 :: 1 :: Nil))
    pr.subgoals.tail.head.at(Position(1) ++ pos) shouldBe (ctxt, "x<=0".asFormula)
  }

  it should "apply on an antecedent box" in {
    val pr = TactixLibrary
      .proveBy("[{x'=y & x>=0}]x >= 0 ==> x >= 0".asSequent, introduceODE("x <= 0".asFormula)(-1, 0 :: Nil))
    pr.subgoals.head shouldBe "[{x'=y & x>=0 & x <= 0}]x >= 0 ==> x >= 0".asSequent
    pr.subgoals.length shouldBe 1
  }

  it should "apply on an antecedent diamond" in {
    val seq = "<{x'=y & x>=0}>x >= 0 ==> x >= 0".asSequent
    val pr = TactixLibrary.proveBy(seq, introduceODE("x <= 0".asFormula)(-1, 0 :: Nil))
    pr.subgoals.head shouldBe "<{x'=y & x>=0 & x <= 0}>x >= 0 ==> x >= 0".asSequent
    pr.subgoals.length shouldBe 2
    val (pos, ctxt) = focusPos("<{x'=y & x>=0}>x >= 0".asFormula, PosInExpr(0 :: 1 :: Nil))
    pr.subgoals.tail.head.at(Position(2) ++ pos) shouldBe (ctxt, "x<=0".asFormula)
  }

  "moveRandom" should "prove correct equivalences" in {
    val pr = moveRandom("{x:=*;y:=*; ++ x:=0;};z:=*;".asProgram, PosInExpr(0 :: 0 :: 1 :: Nil))
    pr.proved shouldBe "==>  {{x:=*;y:=*;z:=*;++x:=0;}z:=*;}=={{x:=*;y:=*;++x:=0;}z:=*;}".asSequent
    val pr2 = moveRandom("{x:=*;y:=*; ++ x:=0;};z:=*;".asProgram, PosInExpr(0 :: 0 :: 0 :: Nil))
    pr2.proved shouldBe "==>  {{{x:=*;z:=*;}y:=*;++x:=0;}z:=*;}=={{x:=*;y:=*;++x:=0;}z:=*;}".asSequent
    val pr3 = moveRandom("{x:=*;y:=*; ++ x:=0;};z:=*;".asProgram, PosInExpr(0 :: 1 :: Nil))
    pr3.proved shouldBe "==>  {{x:=*;y:=*;++x:=0;z:=*;}z:=*;}=={{x:=*;y:=*;++x:=0;}z:=*;}".asSequent
    val pr4 = moveRandom("{x:=*;y:=*; ++ x:=0;}*;z:=*;".asProgram, PosInExpr(0 :: 0 :: 1 :: Nil))
    pr4.proved shouldBe "==>  {{x:=*;y:=*;++x:=0;z:=*;}*z:=*;}=={{x:=*;y:=*;++x:=0;}*z:=*;}".asSequent
  }

  "refAnyGenAux" should "prove correct program" in {
    val pr = refAnyGenAux("x:=*;y:=*; ++ x:=0;".asProgram, "z".asVariable)
    pr.proved shouldBe "==> z:=*;{x:=*;y:=*;++x:=0;} == {x:=*;y:=*;++x:=0;}z:=*;".asSequent
    val pr2 = refAnyGenAux("x:=*;y:=*; ++ x:=0;".asProgram, "y".asVariable)
    pr2.proved shouldBe "==> y:=*;{x:=*;y:=*;++x:=0;} == {x:=*;y:=*;++x:=0;}y:=*;".asSequent
    val pr3 = refAnyGenAux("{x:=*;y:=*; ++ x:=0;}*".asProgram, "y".asVariable)
    pr3.proved shouldBe "==> y:=*;{x:=*;y:=*;++x:=0;}* == {x:=*;y:=*;++x:=0;}*y:=*;".asSequent

    val pr4 = refAnyGenAux("{x:=0;t:=0;{t'=1};t:=*;}*".asProgram, "t".asVariable)
    pr4.proved shouldBe "==> t:=*;{x:=0;t:=0;{t'=1};t:=*;}* == {x:=0;t:=0;{t'=1};t:=*;}*t:=*;".asSequent
  }

  it should "prove correct program with primes" in {
    val pr = refAnyGenAux("x:=*;y:=*; ++ x:=0;".asProgram, "z'".asVariable)
    pr.proved shouldBe "==> z':=*;{x:=*;y:=*;++x:=0;} == {x:=*;y:=*;++x:=0;}z':=*;".asSequent
    val pr2 = refAnyGenAux("x:=*;y':=*; ++ x:=0;".asProgram, "y'".asVariable)
    pr2.proved shouldBe "==> y':=*;{x:=*;y':=*;++x:=0;} == {x:=*;y':=*;++x:=0;}y':=*;".asSequent
    val pr3 = refAnyGenAux("{x:=*;y':=*; ++ x:=0;}*".asProgram, "y'".asVariable)
    pr3.proved shouldBe "==> y':=*;{x:=*;y':=*;++x:=0;}* == {x:=*;y':=*;++x:=0;}*y':=*;".asSequent
  }
  it should "fail as some axioms don't have a differential variable version" ignore {
    val pr4 = refAnyGenAux("{x:=0;t':=1;{t'=1};t':=*;}*".asProgram, "t'".asVariable)
    pr4.proved shouldBe "==> t':=*;{x:=0;t':=1;{t'=1};t':=*;}* == {x:=0;t':=1;{t'=1};t':=*;}*t':=*;".asSequent
  }

  "fuseAux" should "prove correct program" in {
    val pr = fuseRandom("x:=*;y:=*; ++ x:=0;".asProgram, "z".asVariable)
    pr.proved shouldBe "==> z:=*;{x:=*;y:=*;++x:=0;}z:=*; == {x:=*;y:=*;++x:=0;}z:=*;".asSequent
    val pr2 = fuseRandom("x:=*;y:=*; ++ x:=0;".asProgram, "y".asVariable)
    pr2.proved shouldBe "==> y:=*;{x:=*;y:=*;++x:=0;}y:=*; == {x:=*;y:=*;++x:=0;}y:=*;".asSequent
    val pr3 = fuseRandom("{x:=*;y:=2;z:=0; ++ x:=0;}*".asProgram, "y".asVariable)
    pr3.proved shouldBe "==> y:=*;{x:=*;y:=2;z:=0;++x:=0;}*y:=*; == {x:=*;y:=2;z:=0;++x:=0;}*y:=*;".asSequent

    val pr4 = fuseRandom("{x:=0;t:=0;{t'=1};t:=*;}*".asProgram, "t".asVariable)
    pr4.proved shouldBe "==> t:=*;{x:=0;t:=0;{t'=1};t:=*;}*t:=*; == {x:=0;t:=0;{t'=1};t:=*;}*t:=*;".asSequent
  }

  it should "prove correct program with primes" in {
    val pr = fuseRandom("x:=*;y:=*; ++ x:=0;".asProgram, "z'".asVariable)
    pr.proved shouldBe "==> z':=*;{x:=*;y:=*;++x:=0;}z':=*; == {x:=*;y:=*;++x:=0;}z':=*;".asSequent
    val pr2 = fuseRandom("x:=*;y':=*; ++ x:=0;".asProgram, "y'".asVariable)
    pr2.proved shouldBe "==> y':=*;{x:=*;y':=*;++x:=0;}y':=*; == {x:=*;y':=*;++x:=0;}y':=*;".asSequent
    val pr3 = fuseRandom("{x:=*;y':=*;z:=0; ++ x:=0;}*".asProgram, "y'".asVariable)
    pr3.proved shouldBe "==> y':=*;{x:=*;y':=*;z:=0;++x:=0;}*y':=*; == {x:=*;y':=*;z:=0;++x:=0;}*y':=*;".asSequent

    val pr4 = fuseRandom("{x:=0;t:=0;{x'=x,t'=1};t':=*;}*".asProgram, "t'".asVariable)
    pr4.proved shouldBe
      "==> t':=*;{x:=0;t:=0;{x'=x,t'=1};t':=*;}*t':=*; == {x:=0;t:=0;{x'=x,t'=1};t':=*;}*t':=*;".asSequent
  }
  "refDGCst" should "be applicable locally by moving nondeterministic assignment" in {
    val pr = TactixLibrary.proveBy(
      "{x:=0;{x'=1};}*;t:=*;t':=*; == {x:=0;t:=0;{x'=1,t'=1};}*;t:=*;t':=*;".asFormula,
      useAt(refSeqAssoc, PosInExpr(0 :: Nil))(1, 0 :: Nil) &
        moveRandomIn(PosInExpr(0 :: 0 :: 1 :: Nil))(1, 0 :: 0 :: Nil) &
        moveRandomIn(PosInExpr(List(0, 0, 0, 1, 1)))(1, 0 :: Nil) &
        refDGCst("t".asVariable, "0".asTerm, "1".asTerm)(1, 0 :: 0 :: 0 :: 0 :: 1 :: Nil) &
        moveRandomOut(PosInExpr(List(0, 0, 0, 1, 1, 1)))(1, 0 :: Nil) &
        moveRandomOut(PosInExpr(List(0, 0, 1, 1)))(1, 0 :: 0 :: Nil) & useAt(refSeqAssoc)(1, 0 :: Nil) &
        useAt(prgEqRefl)(1),
    )
    pr.isProved shouldBe true
  }

}
