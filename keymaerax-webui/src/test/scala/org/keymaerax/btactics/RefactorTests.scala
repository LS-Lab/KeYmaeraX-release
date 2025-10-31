/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.btactics.Refactor.*
import org.keymaerax.btactics.macros.DerivationInfoAugmentors.ProvableInfoAugmentor
import org.keymaerax.core.Sequent
import org.keymaerax.infrastruct.Augmentors.SequentAugmentor
import org.keymaerax.infrastruct.Position
import org.keymaerax.parser.StringConverter.StringToStringConverter

class RefactorTests extends TacticTestBase {
  "Refactor axioms" should "prove" in {
    val axioms = List(congrAndL, congrAndR, congrOrL, congrOrR, congrImpL, congrImpR, congrRefL, congrRefR)
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
}
