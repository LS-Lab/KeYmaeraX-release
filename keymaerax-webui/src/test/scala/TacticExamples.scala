/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/

import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tags.SummaryTest
import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.tools.{KeYmaera, Mathematica}
import testHelper.{KeYmaeraXTestTags, ProvabilityTestHelper}
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}

import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable.Map

/**
 * Tactic Examples with different proof styles.
 * @author Andre Platzer
 * @see [[edu.cmu.cs.ls.keymaerax.tactics]]
 */
@SummaryTest
class TacticExamples extends FlatSpec with Matchers with BeforeAndAfterEach {
  //import Augmentors._
  val helper = new ProvabilityTestHelper()
  //import helper._ // import helper methods for tests.

  //Mathematica
  val mathematicaConfig: Map[String, String] = helper.mathematicaConfig

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
    Tactics.MathematicaScheduler = new Interpreter(new Mathematica)

    Tactics.KeYmaeraScheduler.init(Map())
    Tactics.MathematicaScheduler.init(mathematicaConfig)
  }

  override def afterEach() = {
    Tactics.KeYmaeraScheduler.shutdown()
    Tactics.MathematicaScheduler.shutdown()
    Tactics.KeYmaeraScheduler = null
    Tactics.MathematicaScheduler = null
  }

  "Explicit Proof Certificates" should "prove !!p() <-> p()" in {
    import edu.cmu.cs.ls.keymaerax.core._
    // explicit proof certificate construction of |- !!p() <-> p()
    val proof = (Provable.startProof(
      Sequent(Nil, IndexedSeq(), IndexedSeq("!!p() <-> p()".asFormula)))
      (EquivRight(SuccPos(0)), 0)
      // right branch
      (NotRight(SuccPos(0)), 1)
      (NotLeft(AntePos(1)), 1)
      (Close(AntePos(0),SuccPos(0)), 1)
      // left branch
      (NotLeft(AntePos(0)), 0)
      (NotRight(SuccPos(1)), 0)
      (Close(AntePos(0),SuccPos(0)), 0)
      )
    proof shouldBe 'proved
    proof.proved shouldBe Sequent(Nil, IndexedSeq(), IndexedSeq("!!p() <-> p()".asFormula))
  }


  "Explicit Proof" should "prove !!p() <-> p()" in {
    import TactixLibrary._
    import BranchLabels._
    // Explicit proof tactic for |- !!p() <-> p()
    val proof = TactixLibrary.proveBy(
      Sequent(Nil, IndexedSeq(), IndexedSeq("!!p() <-> p()".asFormula)),
      equivR(SuccPos(0)) & onBranch(
        (equivRightLbl,
          notR(SuccPos(0)) &
            notL(AntePos(1)) &
            closeId),
        (equivLeftLbl,
          notL(AntePos(0)) &
            notR(SuccPos(1)) &
            closeId)
      )
    )
    proof shouldBe 'proved
    proof.proved shouldBe Sequent(Nil, IndexedSeq(), IndexedSeq("!!p() <-> p()".asFormula))
  }


  "Proof by Search" should "prove (p() & q()) & r() <-> p() & (q() & r())" in {
    import TactixLibrary._
    // Proof by search of |- (p() & q()) & r() <-> p() & (q() & r())
    val proof = TactixLibrary.proveBy(
      Sequent(Nil, IndexedSeq(), IndexedSeq("(p() & q()) & r() <-> p() & (q() & r())".asFormula)),
      prop
    )
    proof shouldBe 'proved
    proof.proved shouldBe Sequent(Nil, IndexedSeq(), IndexedSeq("(p() & q()) & r() <-> p() & (q() & r())".asFormula))
  }


  "Proof by Pointing" should "prove <v:=2*v+1;>q(v) <-> q(2*v+1)" in {
    import TactixLibrary._
    import DerivedAxioms._
    // Proof by pointing of  |- <v:=2*v+1;>v!=0 <-> 2*v+1!=0
    val proof = TactixLibrary.proveBy(
      Sequent(Nil, IndexedSeq(), IndexedSeq("<v:=2*v+1;>q(v) <-> q(2*v+1)".asFormula)),
      // use "<> dual" axiom backwards at the indicated position on
      // |- __<v:=2*v+1;>q(v)__ <-> q(2*v+1)
      useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 0::Nil)) &
        // use "[:=] assign" axiom forward at the indicated position on
        // |- !__[v:=2*v+1;]!q(v)__ <-> q(2*v+1)
        useAt("[:=] assign")(SuccPosition(0, 0::0::Nil)) &
        // use double negation at the indicated position on
        // |- __!!q(2*v+1)__ <-> q(2*v+1)
        useAt(doubleNegationAxiom)(SuccPosition(0, 0::Nil)) &
        // close by (an instance of) reflexivity |- p() <-> p()
        // |- q(2*v+1) <-> q(2*v+1)
        byUS(equivReflexiveAxiom)
    )
    proof shouldBe 'proved
    proof.proved shouldBe Sequent(Nil, IndexedSeq(), IndexedSeq("<v:=2*v+1;>q(v) <-> q(2*v+1)".asFormula))
  }

  it should "prove <a;++b;>p(x) <-> (<a;>p(x) | <b;>p(x))" in {
    import TactixLibrary._
    // Proof by pointing of  |- <a;++b;>p(x) <-> (<a;>p(x) | <b;>p(x))
    val proof = TactixLibrary.proveBy(
      Sequent(Nil, IndexedSeq(), IndexedSeq("<a;++b;>p(x) <-> (<a;>p(x) | <b;>p(x))".asFormula)),
      // use "<> dual" axiom backwards at the indicated position on
      // |- __<a;++b;>p(x)__  <->  <a;>p(x) | <b;>p(x)
      useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 0::Nil)) &
        // use "[++] choice" axiom forward at the indicated position on
        // |- !__[a;++b;]!p(x)__  <->  <a;>p(x) | <b;>p(x)
        useAt("[++] choice")(SuccPosition(0, 0::0::Nil)) &
        // use "<> dual" axiom forward at the indicated position on
        // |- !([a;]!p(x) & [b;]!p(x))  <->  __<a;>p(x)__ | <b;>p(x)
        useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 1::0::Nil)) &
        // use "<> dual" axiom forward at the indicated position on
        // |- !([a;]!p(x) & [b;]!p(x))  <->  ![a;]!p(x) | __<b;>p(x)__
        useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 1::1::Nil)) &
        // use propositional logic to show
        // |- !([a;]!p(x) & [b;]!p(x))  <->  ![a;]!p(x) | ![b;]!p(x)
        prop
    )
    proof shouldBe 'proved
    proof.proved shouldBe Sequent(Nil, IndexedSeq(), IndexedSeq("<a;++b;>p(x) <-> (<a;>p(x) | <b;>p(x))".asFormula))
  }


  "Proof by Congruence" should "prove x*(x+1)>=0 -> [y:=0;x:=x^2+x;]x>=y" in {
    import TactixLibrary._
    // |- x*(x+1)>=0 -> [y:=0;x:=x^2+x;]x>=y
    val proof = proveBy("x*(x+1)>=0 -> [y:=0;x:=x^2+x;]x>=y".asFormula,
      CE(proveBy("x*(x+1)=x^2+x".asFormula, QE)) (SuccPosition(0, 1::0::1::1::Nil)) &
        // |- x*(x+1)>=0 -> [y:=0;x:=x*(x+1);]x>=y by CE/CQ using x*(x+1)=x^2+x
        // step uses top-level operator [;]
      stepAt(SuccPosition(0, 1::Nil)) &
        // |- x*(x+1)>=0 -> [y:=0;][x:=x*(x+1);]x>=y
        // step uses top-level operator [:=]
        stepAt(SuccPosition(0, 1::Nil)) &
        // |- x*(x+1)>=0 -> [x:=x*(x+1);]x>=0
        // step uses top-level [:=]
        stepAt(SuccPosition(0, 1::Nil)) &
        // |- x*(x+1)>=0 -> x*(x+1)>=0
        prop
    )
    proof shouldBe 'proved
    proof.proved shouldBe Sequent(Nil, IndexedSeq(), IndexedSeq("x*(x+1)>=0 -> [y:=0;x:=x^2+x;]x>=y".asFormula))
  }

  it should "prove x^2<4 -> [{x'=9*x^2-x&x^2<4}](-2<x&x<2)" in {
    import TactixLibrary._
    // |- x^2<4 -> [{x'=9*x^2-x&x^2<4}](-2<x&x<2)
    val proof = proveBy("x^2<4 -> [{x'=9*x^2-x&x^2<4}](-2<x&x<2)".asFormula,
      CE(proveBy("-2<x&x<2<->x^2<4".asFormula, QE)) (SuccPosition(0, 1::0::1::Nil)) &
        // |- x^2<4 -> [{x'=9*x^2-x&(-2<x&<2)}](-2<x&x<2) by CE using -2<x&x<2<->x^2<4
        useAt("DW")(SuccPosition(0, 1::Nil)) &
        // |- x^2<4 -> true by DW
        prop
    )
    proof shouldBe 'proved
    proof.proved shouldBe Sequent(Nil, IndexedSeq(), IndexedSeq("x^2<4 -> [{x'=9*x^2-x&x^2<4}](-2<x&x<2)".asFormula))
  }

  it should "reduce x<5 & x^2<4 -> [{x' = 5*x & x^2<4}](x^2<4 & x>=1) to x<5 & (-2<x&x<2) -> [{x' = 5*x & -2<x&x<2}]((-2<x&x<2) & x>=1)" in {
    import TactixLibrary._
    val C = Context("x<5 & ⎵ -> [{x' = 5*x & ⎵}](⎵ & x>=1)".asFormula)
    // |- x<5 & __x^2<4__ -> [{x' = 5*x & __x^2<4__}](__x^2<4__ & x>=1)
    val proof = proveBy("x<5 & x^2<4 -> [{x' = 5*x & x^2<4}](x^2<4 & x>=1)".asFormula,
      CE(proveBy("-2<x&x<2<->x^2<4".asFormula, QE), C) (SuccPosition(0)))
    // |- x<5 & (__-2<x&x<2__) -> [{x' = 5*x & __-2<x&x<2__}]((__-2<x&x<2__) & x>=1) by CE
    proof.subgoals should contain only (
      new Sequent(Nil, IndexedSeq(), IndexedSeq("x<5 & (-2<x&x<2) -> [{x' = 5*x & -2<x&x<2}]((-2<x&x<2) & x>=1)".asFormula))
      )
  }


  "Proof by Chase" should "chase the prime away in [{x'=22}](2*x+x*y>=5)'" in {
    import TactixLibrary._
    val proof = proveBy("[{x'=22}](2*x+x*y>=5)'".asFormula,
      // chase the differential prime away in the postcondition
      chase(1, 1 :: Nil)
      // |- [{x'=22}]2*x'+(x'*y+x*y')>=0
    )
    proof.subgoals shouldBe List(Sequent(Nil, IndexedSeq(), IndexedSeq("[{x'=22}]2*x'+(x'*y+x*y')>=0".asFormula)))
  }

  it should "prove [{x'=22}](2*x+x*y>=5)' <-> [{x'=22}]2*x'+(x'*y+x*y')>=0" in {
    import TactixLibrary._
    val proof = proveBy("[{x'=22}](2*x+x*y>=5)' <-> [{x'=22}]2*x'+(x'*y+x*y')>=0".asFormula,
      // chase the differential prime away in the left postcondition
      chase(1, 0:: 1 :: Nil) &
      // |- [{x'=22}]2*x'+(x'*y+x*y')>=0 <-> [{x'=22}]2*x'+(x'*y+x*y')>=0
      byUS("<-> reflexive")
    )
    proof shouldBe 'proved
    proof.proved shouldBe Sequent(Nil, IndexedSeq(), IndexedSeq("[{x'=22}](2*x+x*y>=5)' <-> [{x'=22}]2*x'+(x'*y+x*y')>=0".asFormula))
  }

  it should "prove [?x>0;x:=x+1;x:=2*x; ++ ?x=0;x:=1;]x>=1" in {
    import TactixLibrary._
    // proof by chase of |- [?x>0;x:=x+1;x:=2*x; ++ ?x=0;x:=1;]x>=1
    val proof = TactixLibrary.proveBy(
      Sequent(Nil, IndexedSeq(), IndexedSeq("[?x>0;x:=x+1;x:=2*x; ++ ?x=0;x:=1;]x>=1".asFormula)),
        // chase the box in the succedent away
        chase(1,Nil) &
        // |- (x>0->2*(x+1)>=1)&(x=0->1>=1)
        QE
    )
    proof shouldBe 'proved
    proof.proved shouldBe Sequent(Nil, IndexedSeq(), IndexedSeq("[?x>0;x:=x+1;x:=2*x; ++ ?x=0;x:=1;]x>=1".asFormula))
  }
}
