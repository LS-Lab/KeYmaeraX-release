/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{Context, PosInExpr}
import edu.cmu.cs.ls.keymaerax.tags.SummaryTest
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.collection.immutable._
import org.scalatest.LoneElement._

/**
 * Tactic Examples with different proof styles.
 * @author
 *   Andre Platzer
 */
@SummaryTest
class BTacticExamples extends TacticTestBase {

  "Explicit Proof Certificates" should "prove !!p() <-> p()" in {
    import edu.cmu.cs.ls.keymaerax.core._
    // explicit proof certificate construction of |- !!p() <-> p()
    val proof = (ProvableSig.startPlainProof("==> !!p() <-> p()".asSequent)(EquivRight(SuccPos(0)), 0)
    // right branch
    (NotRight(SuccPos(0)), 1)(NotLeft(AntePos(1)), 1)(Close(AntePos(0), SuccPos(0)), 1)
    // left branch
    (NotLeft(AntePos(0)), 0)(NotRight(SuccPos(1)), 0)(Close(AntePos(0), SuccPos(0)), 0))
    proof shouldBe Symbol("proved")
    proof.proved shouldBe "==> !!p() <-> p()".asSequent
  }

  "Explicit Proof" should "prove !!p() <-> p()" in withTactics {
    import TactixLibrary._
    // Explicit proof tactic for |- !!p() <-> p()
    val proof = TactixLibrary.proveBy(
      "==> !!p() <-> p()".asSequent,
      equivR(SuccPos(0)) < ((notL(AntePos(0)) & notR(SuccPos(1)) & id), (notR(SuccPos(0)) & notL(AntePos(1)) & id)),
    )
    proof shouldBe Symbol("proved")
    proof.proved shouldBe "==> !!p() <-> p()".asSequent
  }

  it should "prove !!p() <-> p() with modern index" in withTactics {
    import TactixLibrary._
    // Explicit proof tactic for |- !!p() <-> p()
    val proof = TactixLibrary
      .proveBy("==> !!p() <-> p()".asSequent, equivR(1) < ((notL(-1) & notR(2) & id), (notR(1) & notL(-2) & id)))
    proof shouldBe Symbol("proved")
    proof.proved shouldBe "==> !!p() <-> p()".asSequent
  }

  // @todo more tests like this because this is one of the few simple tests that fails when master/prop have the * inside the OnAll instead of outside the OnAll.
  "Proof by Search" should "prove (p() & q()) & r() <-> p() & (q() & r())" in withTactics {
    import TactixLibrary._
    // Proof by search of |- (p() & q()) & r() <-> p() & (q() & r())
    val proof = TactixLibrary
      .proveBy(Sequent(IndexedSeq(), IndexedSeq("(p() & q()) & r() <-> p() & (q() & r())".asFormula)), prop)
    proof shouldBe Symbol("proved")
    proof.proved shouldBe Sequent(IndexedSeq(), IndexedSeq("(p() & q()) & r() <-> p() & (q() & r())".asFormula))
  }

  "Proof by Pointing" should "prove <v:=2*v+1;>q(v) <-> q(2*v+1)" in withTactics {
    import TactixLibrary._
    import Ax._
    // Proof by pointing of  |- <v:=2*v+1;>v!=0 <-> 2*v+1!=0
    val proof = TactixLibrary.proveBy(
      Sequent(IndexedSeq(), IndexedSeq("<v:=2*v+1;>q(v) <-> q(2*v+1)".asFormula)),
      // use "<> diamond" axiom backwards at the indicated position on
      // |- __<v:=2*v+1;>q(v)__ <-> q(2*v+1)
      useAt(Ax.diamond, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
        // use "[:=] assign" axiom forward at the indicated position on
        // |- !__[v:=2*v+1;]!q(v)__ <-> q(2*v+1)
        useAt(Ax.assignbAxiom)(1, 0 :: 0 :: Nil) &
        // use double negation at the indicated position on
        // |- __!!q(2*v+1)__ <-> q(2*v+1)
        useAt(doubleNegation)(1, 0 :: Nil) &
        // close by (an instance of) reflexivity |- p() <-> p()
        // |- q(2*v+1) <-> q(2*v+1)
        byUS(equivReflexive),
    )
    proof shouldBe Symbol("proved")
    proof.proved shouldBe Sequent(IndexedSeq(), IndexedSeq("<v:=2*v+1;>q(v) <-> q(2*v+1)".asFormula))
  }

  it should "prove <a;++b;>p(x) <-> (<a;>p(x) | <b;>p(x))" in withTactics {
    import TactixLibrary._
    // Proof by pointing of  |- <a;++b;>p(x) <-> (<a;>p(x) | <b;>p(x))
    val proof = TactixLibrary.proveBy(
      Sequent(IndexedSeq(), IndexedSeq("<a;++b;>p(x) <-> (<a;>p(x) | <b;>p(x))".asFormula)),
      // use "<> diamond" axiom backwards at the indicated position on
      // |- __<a;++b;>p(x)__  <->  <a;>p(x) | <b;>p(x)
      useAt(Ax.diamond, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
        // use "[++] choice" axiom forward at the indicated position on
        // |- !__[a;++b;]!p(x)__  <->  <a;>p(x) | <b;>p(x)
        useAt(Ax.choiceb)(1, 0 :: 0 :: Nil) &
        // use "<> diamond" axiom forward at the indicated position on
        // |- !([a;]!p(x) & [b;]!p(x))  <->  __<a;>p(x)__ | <b;>p(x)
        useAt(Ax.diamond, PosInExpr(1 :: Nil))(1, 1 :: 0 :: Nil) &
        // use "<> diamond" axiom forward at the indicated position on
        // |- !([a;]!p(x) & [b;]!p(x))  <->  ![a;]!p(x) | __<b;>p(x)__
        useAt(Ax.diamond, PosInExpr(1 :: Nil))(1, 1 :: 1 :: Nil) &
        // use propositional logic to show
        // |- !([a;]!p(x) & [b;]!p(x))  <->  ![a;]!p(x) | ![b;]!p(x)
        prop,
    )
    proof shouldBe Symbol("proved")
    proof.proved shouldBe Sequent(IndexedSeq(), IndexedSeq("<a;++b;>p(x) <-> (<a;>p(x) | <b;>p(x))".asFormula))
  }

  it should "prove with steps <a;++b;>p(x) <-> (<a;>p(x) | <b;>p(x))" in withTactics {
    import TactixLibrary._
    // Proof by pointing with steps of  |- <a;++b;>p(x) <-> (<a;>p(x) | <b;>p(x))
    val proof = TactixLibrary.proveBy(
      Sequent(IndexedSeq(), IndexedSeq("<a;++b;>p(x) <-> (<a;>p(x) | <b;>p(x))".asFormula)),
      // use "<> diamond" axiom backwards at the indicated position on
      // |- __<a;++b;>p(x)__  <->  <a;>p(x) | <b;>p(x)
      useAt(Ax.diamond, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
        // |- !__[a;++b;]!p(x)__  <->  <a;>p(x) | <b;>p(x)
        // step "[++] choice" axiom forward at the indicated position
        stepAt(1, 0 :: 0 :: Nil) &
        // |- __!([a;]!p(x) & [b;]!p(x))__  <-> <a;>p(x) | <b;>p(x)
        // step deMorgan forward at the indicated position
        stepAt(1, 0 :: Nil) &
        // |- __![a;]!p(x)__ | ![b;]!p(x)  <-> <a;>p(x) | <b;>p(x)
        // step "<> diamond" forward at the indicated position
        stepAt(1, 0 :: 0 :: Nil) &
        // |- <a;>p(x) | __![b;]!p(x)__  <-> <a;>p(x) | <b;>p(x)
        // step "<> diamond" forward at the indicated position
        stepAt(1, 0 :: 1 :: Nil) &
        // |- <a;>p(x) | <b;>p(x)  <-> <a;>p(x) | <b;>p(x)
        byUS(Ax.equivReflexive),
    )
    proof shouldBe Symbol("proved")
    proof.proved shouldBe Sequent(IndexedSeq(), IndexedSeq("<a;++b;>p(x) <-> (<a;>p(x) | <b;>p(x))".asFormula))
  }

  "Proof by Congruence" should "prove x*(x+1)>=0 -> [y:=0;x:=x^2+x;]x>=y" in withQE { _ =>
    import TactixLibrary._
    // |- x*(x+1)>=0 -> [y:=0;x:=x^2+x;]x>=y
    val proof = TactixLibrary.proveBy(
      "x*(x+1)>=0 -> [y:=0;x:=x^2+x;]x>=y".asFormula,
      CEat(TactixLibrary.proveBy("x*(x+1)=x^2+x".asFormula, QE))(1, 1 :: 0 :: 1 :: 1 :: Nil) &
        // |- x*(x+1)>=0 -> [y:=0;x:=x*(x+1);]x>=y by CE/CQ using x*(x+1)=x^2+x
        // step uses top-level operator [;]
        stepAt(1, 1 :: Nil) &
        // |- x*(x+1)>=0 -> [y:=0;][x:=x*(x+1);]x>=y
        // step uses top-level operator [:=]
        stepAt(1, 1 :: Nil) &
        // |- x*(x+1)>=0 -> [x:=x*(x+1);]x>=0
        // step uses top-level [:=]
        stepAt(1, 1 :: Nil) &
        // |- x*(x+1)>=0 -> x*(x+1)>=0
        prop,
    )
    proof shouldBe Symbol("proved")
    proof.proved shouldBe Sequent(IndexedSeq(), IndexedSeq("x*(x+1)>=0 -> [y:=0;x:=x^2+x;]x>=y".asFormula))
  }

  it should "prove x^2<4 -> [{x'=9*x^2-x&x^2<4}](-2<x&x<2)" in withQE { _ =>
    import TactixLibrary._
    // |- x^2<4 -> [{x'=9*x^2-x&x^2<4}](-2<x&x<2)
    val proof = TactixLibrary.proveBy(
      "x^2<4 -> [{x'=9*x^2-x&x^2<4}](-2<x&x<2)".asFormula,
      CEat(TactixLibrary.proveBy("-2<x&x<2<->x^2<4".asFormula, QE))(1, 1 :: 0 :: 1 :: Nil) &
        // |- x^2<4 -> [{x'=9*x^2-x&(-2<x&<2)}](-2<x&x<2) by CE using -2<x&x<2<->x^2<4
        useAt(Ax.DWbase)(1, 1 :: Nil) &
        // |- x^2<4 -> true by DW
        prop,
    )
    proof shouldBe Symbol("proved")
    proof.proved shouldBe Sequent(IndexedSeq(), IndexedSeq("x^2<4 -> [{x'=9*x^2-x&x^2<4}](-2<x&x<2)".asFormula))
  }

  it should
    "reduce x<5 & x^2<4 -> [{x' = 5*x & x^2<4}](x^2<4 & x>=1) to x<5 & (-2<x&x<2) -> [{x' = 5*x & -2<x&x<2}]((-2<x&x<2) & x>=1)" in
    withQE { _ =>
      import TactixLibrary._
      val C = Context("x<5 & ⎵ -> [{x' = 5*x & ⎵}](⎵ & x>=1)".asFormula)
      // |- x<5 & __x^2<4__ -> [{x' = 5*x & __x^2<4__}](__x^2<4__ & x>=1)
      val proof = TactixLibrary.proveBy(
        "x<5 & x^2<4 -> [{x' = 5*x & x^2<4}](x^2<4 & x>=1)".asFormula,
        CEat(TactixLibrary.proveBy("-2<x&x<2<->x^2<4".asFormula, QE), C)(1),
      )
      // |- x<5 & (__-2<x&x<2__) -> [{x' = 5*x & __-2<x&x<2__}]((__-2<x&x<2__) & x>=1) by CE
      proof.subgoals.loneElement shouldBe "==> x<5 & (-2<x&x<2) -> [{x' = 5*x & -2<x&x<2}]((-2<x&x<2) & x>=1)".asSequent
    }

  "Proof by Chase" should "chase the prime away in [{x'=22}](2*x+x*y>=5)'" in withQE { _ =>
    import TactixLibrary._
    val proof = TactixLibrary.proveBy(
      "[{x'=22}](2*x+x*y>=5)'".asFormula,
      // chase the differential prime away in the postcondition
      chase(1, 1 :: Nil),
      // |- [{x'=22}]2*x'+(x'*y+x*y')>=0
    )
    proof.subgoals.loneElement shouldBe "==> [{x'=22}]2*x'+(x'*y+x*y')>=0".asSequent
  }

  it should "prove [{x'=22}](2*x+x*y>=5)' <-> [{x'=22}]2*x'+(x'*y+x*y')>=0" in withQE { _ =>
    import TactixLibrary._
    val proof = TactixLibrary.proveBy(
      "[{x'=22}](2*x+x*y>=5)' <-> [{x'=22}]2*x'+(x'*y+x*y')>=0".asFormula,
      // chase the differential prime away in the left postcondition
      chase(1, 0 :: 1 :: Nil) &
        // |- [{x'=22}]2*x'+(x'*y+x*y')>=0 <-> [{x'=22}]2*x'+(x'*y+x*y')>=0
        byUS(Ax.equivReflexive),
    )
    proof shouldBe Symbol("proved")
    proof.proved shouldBe "==> [{x'=22}](2*x+x*y>=5)' <-> [{x'=22}]2*x'+(x'*y+x*y')>=0".asSequent
  }

  it should "prove [?x>0;x:=x+1;x:=2*x; ++ ?x=0;x:=1;]x>=1" in withQE { _ =>
    import TactixLibrary._
    // proof by chase of |- [?x>0;x:=x+1;x:=2*x; ++ ?x=0;x:=1;]x>=1
    val proof = TactixLibrary.proveBy(
      "==> [?x>0;x:=x+1;x:=2*x; ++ ?x=0;x:=1;]x>=1".asSequent,
      // chase the box in the succedent away
      chase(1, Nil) &
        // |- (x>0->2*(x+1)>=1)&(x=0->1>=1)
        QE,
    )
    proof shouldBe Symbol("proved")
    proof.proved shouldBe "==> [?x>0;x:=x+1;x:=2*x; ++ ?x=0;x:=1;]x>=1".asSequent
  }
}
