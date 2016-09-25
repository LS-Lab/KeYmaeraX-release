package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleError
import edu.cmu.cs.ls.keymaerax.btactics.EqualityTactics._
import edu.cmu.cs.ls.keymaerax.core.{Variable, Sequent}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable.IndexedSeq

/**
 * Tests [[edu.cmu.cs.ls.keymaerax.btactics.EqualityTactics]]
 */
class EqualityTests extends TacticTestBase {

  "eqL2R" should "rewrite x*y=0 to 0*y=0 using x=0" in {
    val result = proveBy(Sequent(IndexedSeq("x=0".asFormula), IndexedSeq("x*y=0".asFormula)), eqL2R(-1)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=0".asFormula
    result.subgoals.head.succ should contain only "0*y=0".asFormula
  }

  it should "rewrite entire formula" in {
    val result = proveBy(Sequent(IndexedSeq("x=0".asFormula), IndexedSeq("x*y=x&x+1=1".asFormula, "x+1>0".asFormula)), eqL2R(-1)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=0".asFormula
    result.subgoals.head.succ should contain only ("0*y=0&0+1=1".asFormula, "x+1>0".asFormula)
  }

  it should "rewrite entire formula at specified position" in {
    val result = proveBy(Sequent(IndexedSeq("x=0".asFormula), IndexedSeq("x*y=x&x+1=1".asFormula, "x+1>0".asFormula)), eqL2R(-1)(1, 0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=0".asFormula
    result.subgoals.head.succ should contain only ("0*y=0&x+1=1".asFormula, "x+1>0".asFormula)
  }

  it should "rewrite entire term at specified position" in {
    val result = proveBy(Sequent(IndexedSeq("x=0".asFormula), IndexedSeq("x*x*y=x".asFormula, "x+1>0".asFormula)), eqL2R(-1)(1, 0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=0".asFormula
    result.subgoals.head.succ should contain only ("0*0*y=x".asFormula, "x+1>0".asFormula)
  }

  it should "rewrite only at very specified position" in {
    val result = proveBy(Sequent(IndexedSeq("x=0".asFormula), IndexedSeq("x*y=x".asFormula, "x+1>0".asFormula)), eqL2R(-1)(1, 0::0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=0".asFormula
    result.subgoals.head.succ should contain only ("0*y=x".asFormula, "x+1>0".asFormula)
  }

  it should "keep positions stable" in {
    val result = proveBy(Sequent(IndexedSeq("x=0".asFormula), IndexedSeq("x*y=0".asFormula, "x+1>0".asFormula)), eqL2R(-1)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=0".asFormula
    result.subgoals.head.succ shouldBe IndexedSeq("0*y=0".asFormula, "x+1>0".asFormula)
  }

  it should "rewrite complicated" in {
    val result = proveBy(Sequent(IndexedSeq("x=0".asFormula), IndexedSeq("x*y=0 & x+3>2 | \\forall y y+x>=0".asFormula)), eqL2R(-1)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=0".asFormula
    result.subgoals.head.succ should contain only "0*y=0 & 0+3>2 | \\forall y y+0>=0".asFormula
  }

  it should "rewrite complicated exhaustively" in {
    val result = proveBy(Sequent(IndexedSeq("x=0".asFormula), IndexedSeq("x*y=0 & x+3>2 | \\forall y y+x>=0 & \\exists x x>0".asFormula)),
      eqL2R(-1)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=0".asFormula
    result.subgoals.head.succ should contain only "0*y=0 & 0+3>2 | \\forall y y+0>=0 & \\exists x x>0".asFormula
  }

  "Exhaustive eqR2L" should "rewrite x*y=0 to 0*y=0 using 0=x" in {
    val result = proveBy(Sequent(IndexedSeq("0=x".asFormula), IndexedSeq("x*y=0".asFormula)), exhaustiveEqR2L(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "0=x".asFormula
    result.subgoals.head.succ should contain only "0*y=0".asFormula
  }

  "Exhaustive eqL2R" should "rewrite a single formula exhaustively" in {
    val result = proveBy(Sequent(IndexedSeq("x=0".asFormula), IndexedSeq("x*y=0".asFormula, "z>2".asFormula, "z<x+1".asFormula)), exhaustiveEqL2R(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=0".asFormula
    result.subgoals.head.succ should contain only ("0*y=0".asFormula, "z>2".asFormula, "z<0+1".asFormula)
  }

  it should "not fail when there are no applicable positions" in {
    val result = proveBy(Sequent(IndexedSeq("x=0".asFormula), IndexedSeq("z>2".asFormula)), exhaustiveEqL2R(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=0".asFormula
    result.subgoals.head.succ should contain only "z>2".asFormula
  }

  it should "rewrite a single formula exhaustively for a single applicable position" in {
    val result = proveBy(Sequent(IndexedSeq("x=0".asFormula), IndexedSeq("x*y=0".asFormula, "z>2".asFormula)), exhaustiveEqL2R(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=0".asFormula
    result.subgoals.head.succ should contain only ("0*y=0".asFormula, "z>2".asFormula)
  }

  it should "rewrite formulas exhaustively" in {
    val result = proveBy(Sequent(IndexedSeq("x=0".asFormula, "z=x".asFormula), IndexedSeq("x*y=0".asFormula, "z>2".asFormula, "z<x+1".asFormula)), exhaustiveEqL2R(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x=0".asFormula, "z=0".asFormula)
    result.subgoals.head.succ should contain only ("0*y=0".asFormula, "z>2".asFormula, "z<0+1".asFormula)
  }

  it should "rewrite formulas exhaustively everywhere" in {
    val result = proveBy(Sequent(IndexedSeq("z=x".asFormula, "x=0".asFormula), IndexedSeq("x*y=0".asFormula, "z>2".asFormula, "z<x+1".asFormula)), exhaustiveEqL2R(-2))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x=0".asFormula, "z=0".asFormula)
    result.subgoals.head.succ should contain only ("0*y=0".asFormula, "z>2".asFormula, "z<0+1".asFormula)
  }

  it should "work even if there is only one other formula" in {
    val result = proveBy(Sequent(IndexedSeq("x<5".asFormula, "x=0".asFormula), IndexedSeq()), exhaustiveEqL2R(-2))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("0<5".asFormula, "x=0".asFormula)
    result.subgoals.head.succ shouldBe empty
  }

  it should "replace arbitary terms" in {
    val result = proveBy(Sequent(IndexedSeq("a+b<5".asFormula, "a+b=c".asFormula), IndexedSeq()), exhaustiveEqL2R(-2))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("c<5".asFormula, "a+b=c".asFormula)
    result.subgoals.head.succ shouldBe empty
  }

  // rewriting numbers is disallowed, because otherwise we run into endless rewriting
  it should "not rewrite numbers" in {
    a [BelleError] should be thrownBy proveBy(Sequent(IndexedSeq("0<5".asFormula, "0=0".asFormula), IndexedSeq()), exhaustiveEqL2R(-2))
  }

  it should "not try to rewrite bound occurrences" in {
    val result = proveBy(Sequent(IndexedSeq("a=1".asFormula), IndexedSeq("[a:=2;]a=1".asFormula)), exhaustiveEqL2R(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "a=1".asFormula
    result.subgoals.head.succ should contain only "[a:=2;]a=1".asFormula
  }

  it should "rewrite multiple occurrences of a term in one shot" in {
    val result = proveBy(Sequent(IndexedSeq("x+2<=x+3".asFormula, "x=y".asFormula), IndexedSeq()), exhaustiveEqL2R(-2))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe IndexedSeq("y+2<=y+3".asFormula, "x=y".asFormula)
    result.subgoals.head.succ shouldBe empty
  }

}
