/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.btactics.Refactor.*
import org.keymaerax.btactics.macros.DerivationInfoAugmentors.ProvableInfoAugmentor
import org.keymaerax.parser.StringConverter.StringToStringConverter

class RefactorTests extends TacticTestBase {
  "Refactor axioms" should "prove" in {
    val axioms = List(congrAndL, congrAndR, congrOrL, congrOrR, congrImpL, congrImpR, congrRefL, congrRefR)
    axioms.map(axiom => axiom.isProved shouldBe true)
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
    val pr = TactixLibrary.proveBy(
      "x > 0 ==> ?(true & z = 2);y:=1; ++ z:=3; <= ?(x=2 & z = 2);y:=1; ++ z:=3;".asSequent,
      focus(1, List(0, 0, 0, 0, 0)),
    )
    pr.subgoals.head shouldBe "x > 0 ==> true -> x=2".asSequent
  }

  it should "simplify down to formula implication in ODE's domain" in {
    val pr = TactixLibrary
      .proveBy("x > 0 ==> {x'= x & x < 5 & x > 0} <= {x'= x & x < 10 & x > 0}".asSequent, focus(1, 0 :: 1 :: 0 :: Nil))
    pr.subgoals.head shouldBe "x > 0 ==> [{x'= x & x < 5 & x > 0}](x < 5 -> x < 10)".asSequent
  }

  it should "simplify implication" in {
    val pr = TactixLibrary
      .proveBy("x > 0 ==> [x:=x+2;](x > 2 & z < 0) -> [x:=x+2;](x > 1 & z < 0)".asSequent, focus(1, 0 :: 1 :: 0 :: Nil))
    pr.subgoals.head shouldBe "x > 0 ==> [x:=x+2;](x > 2 -> x > 1)".asSequent
  }

  it should "simplify add binder to preserve assumption" in {
    val pr = TactixLibrary.proveBy(
      "x > 0 ==> \\forall z (x > 2 & z < 0) -> \\forall z (x > 1 & z < 0)".asSequent,
      focus(1, 0 :: 0 :: 0 :: Nil),
    )
    pr.subgoals.head shouldBe "x > 0 ==> \\forall z (x > 2 -> x > 1)".asSequent
  }
  it should "simplify down to refinement in box" in {
    val pr = TactixLibrary
      .proveBy("x > 0 ==> [{x:=x+2;y:=*;}*](x > 2) -> [{x:=x+2;y:=0;}*](x > 2)".asSequent, focus(1, List(0, 0, 0, 1)))
    pr.subgoals.head shouldBe "x > 0 ==> [{x:=x+2;y:=0;}*][x:=x+2;](y:=0; <= y:=*;)".asSequent
  }

  it should "simplify down to refinement in diamond" in {
    val pr = TactixLibrary
      .proveBy("x > 0 ==> <{x:=x+2;y:=0;}*>(x > 2) -> <{x:=x+2;y:=*;}*>(x > 2)".asSequent, focus(1, List(0, 0, 0, 1)))
    pr.subgoals.head shouldBe "x > 0 ==> [{x:=x+2;y:=0;}*][x:=x+2;](y:=0; <= y:=*;)".asSequent
  }

  it should "simplify down to refinement in refinement" in {
    val pr = TactixLibrary.proveBy(
      "x > 0 ==> {x:=x+2;y:=*;}* <= x:=*;y:=*; -> {x:=x+2;y:=0;}* <= x:=*;y:=*;".asSequent,
      focus(1, List(0, 0, 0, 1)),
    )
    pr.subgoals.head shouldBe "x > 0 ==> [{x:=x+2;y:=0;}*][x:=x+2;](y:=0; <= y:=*;)".asSequent
  }
}
