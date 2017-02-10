package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.UsualTest

import scala.collection.immutable.{IndexedSeq, _}

/**
 * Tests automatic
 * [[edu.cmu.cs.ls.keymaerax.btactics.ToolTactics]].
 */
@UsualTest
class ToolTacticsTests extends TacticTestBase {
  "Transform" should "transform top-level" in withMathematica { _ =>
    val result = proveBy("x>=0".asFormula, transform("x>=1".asFormula)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "x>=1".asFormula
  }

  it should "transform top-level in ante" in withMathematica { _ =>
    val result = proveBy(Sequent(IndexedSeq("x>=0".asFormula), IndexedSeq()), transform("x>=-1".asFormula)(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x>=-1".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "work with non-FO formulas present" in withMathematica { _ =>
    val result = proveBy(Sequent(IndexedSeq("[a:=2;]a>=1".asFormula), IndexedSeq("x>=0".asFormula, "[b:=3;]b>1".asFormula)),
      transform("x>=1".asFormula)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "[a:=2;]a>=1".asFormula
    result.subgoals.head.succ should contain only ("x>=1".asFormula, "[b:=3;]b>1".asFormula)
  }

  it should "retain global facts for transformation" in withMathematica { _ =>
    val result = proveBy(Sequent(IndexedSeq("c>0".asFormula), IndexedSeq("x/c>=0".asFormula)),
      transform("x/c>=1".asFormula)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "c>0".asFormula
    result.subgoals.head.succ should contain only "x/c>=1".asFormula
  }

  it should "retain all global facts for transformation" in withMathematica { _ =>
    val result = proveBy(Sequent(IndexedSeq("a=0".asFormula, "c+a>0".asFormula), IndexedSeq("x/c>=0".asFormula)),
      transform("x/c>=1".asFormula)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("a=0".asFormula, "c+a>0".asFormula)
    result.subgoals.head.succ should contain only "x/c>=1".asFormula
  }

  it should "retain global facts for transformation in ante" in withMathematica { _ =>
    val result = proveBy(Sequent(IndexedSeq("c>0".asFormula, "x/c>=1".asFormula), IndexedSeq()),
      transform("x/c>=0".asFormula)(-2))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("c>0".asFormula, "x/c>=0".asFormula)
    result.subgoals.head.succ shouldBe empty
  }

  "Transform in context" should "exploit equivalence" in withMathematica { _ =>
    val result = proveBy("[x:=4;]x>=v*v".asFormula, transform("x>=v^2".asFormula)(1, 1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[x:=4;]x>=v^2".asFormula
  }

  it should "exploit conditional equivalence from global facts" in withMathematica { _ =>
    val result = proveBy(Sequent(IndexedSeq("b>0".asFormula), IndexedSeq("[x:=4;]2*x*b>=v*v".asFormula)),
      transform("x>=v^2/(2*b)".asFormula)(1, 1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "b>0".asFormula
    result.subgoals.head.succ should contain only "[x:=4;]x>=v^2/(2*b)".asFormula
  }

  it should "exploit conditional equivalence from unmodified global facts deeply nested" in withMathematica { _ =>
    val result = proveBy(Sequent(IndexedSeq("b>0".asFormula), IndexedSeq("[x:=4;][v:=2;][a:=3;]2*x*b>=v*v".asFormula)),
      transform("x>=v^2/(2*b)".asFormula)(1, 1::1::1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "b>0".asFormula
    result.subgoals.head.succ should contain only "[x:=4;][v:=2;][a:=3;]x>=v^2/(2*b)".asFormula
  }

  it should "exploit conditional equivalence from global facts retained deeply nested 2" in withMathematica { _ =>
    val result = proveBy(Sequent(IndexedSeq("b>0".asFormula), IndexedSeq("[x:=4;][b:=2*b;][a:=3;]2*x*b>=v*v".asFormula)),
      transform("x>=v^2/(2*b)".asFormula)(1, 1::1::1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "b>0".asFormula
    result.subgoals.head.succ should contain only "[x:=4;][b:=2*b;][a:=3;]x>=v^2/(2*b)".asFormula
  }

  it should "exploit conditional equivalence from global facts retained deeply nested 3" in withMathematica { _ =>
    val result = proveBy(Sequent(IndexedSeq("b>0".asFormula), IndexedSeq("[x:=4;][b:=2*b;][a:=3;][{b'=a}][{b:=b+1;}*][?c=4;]2*x*b>=v*v".asFormula)),
      transform("x>=v^2/(2*b)".asFormula)(1, 1::1::1::1::1::1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "b>0".asFormula
    result.subgoals.head.succ should contain only "[x:=4;][b:=2*b;][a:=3;][{b'=a}][{b:=b+1;}*][?c=4;]x>=v^2/(2*b)".asFormula
  }

  //@todo invariant generation
  it should "exploit conditional equivalence from global facts retained deeply nested 4" ignore withMathematica { _ =>
    val result = proveBy(Sequent(IndexedSeq("b>0".asFormula), IndexedSeq("[x:=4;][b:=2*b;][a:=3;][{a:=a+1;}*][{b'=a}][{b:=b+1;}*][?c=4;]2*x*b>=v*v".asFormula)),
      transform("x>=v^2/(2*b)".asFormula)(1, 1::1::1::1::1::1::1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "b>0".asFormula
    result.subgoals.head.succ should contain only "[x:=4;][b:=2*b;][a:=3;][{a:=a+1;}*][{b'=a}][{b:=b+1;}*][?c=4;]x>=v^2/(2*b)".asFormula
  }

  it should "exploit conditional equivalence from global facts propositionally nested" in withMathematica { _ =>
    val result = proveBy(Sequent(IndexedSeq("b>0".asFormula), IndexedSeq("x=4 | 2*x*b>=v*v".asFormula)),
      transform("x>=v^2/(2*b)".asFormula)(1, 1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "b>0".asFormula
    result.subgoals.head.succ should contain only "x=4 | x>=v^2/(2*b)".asFormula
  }

  //@todo how to prove precondition b>0 still holds in context when initial question is false already?
  it should "exploit conditional equivalence from global facts propositionally nested with false" ignore withMathematica { _ =>
    val result = proveBy(Sequent(IndexedSeq("b>0".asFormula), IndexedSeq("false & 2*x*b>=v*v".asFormula)),
      transform("x>=v^2/(2*b)".asFormula)(1, 1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "b>0".asFormula
    result.subgoals.head.succ should contain only "false & x>=v^2/(2*b)".asFormula
  }

  it should "retain context in universal quantifier" in withMathematica { _ =>
    val result = proveBy(Sequent(IndexedSeq("b>0".asFormula), IndexedSeq("\\forall x x>=0".asFormula)),
      transform("y/b>0 & x*y>=0".asFormula)(1, 0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "b>0".asFormula
    result.subgoals.head.succ should contain only "\\forall x (y/b>0 & x*y>=0)".asFormula
  }

  it should "retain context in existential quantifier" ignore withMathematica { _ =>
    val result = proveBy(Sequent(IndexedSeq("b>0".asFormula), IndexedSeq("\\exists x x>=0".asFormula)),
      transform("y/b>0 & x*y>=0".asFormula)(1, 0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "b>0".asFormula
    result.subgoals.head.succ should contain only "\\exists x (y/b>0 & x*y>=0)".asFormula
  }

  it should "introduce new variables in results of DG" in withMathematica { _ =>
    val result = proveBy("x>0 -> \\exists y [{x'=-x,y'=1/2}]x>0".asFormula, implyR(1) & transform("x*y^2=1".asFormula)(1, 0::1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x>0".asFormula
    result.subgoals.head.succ should contain only "\\exists y [{x'=-x,y'=1/2}]x*y^2=1".asFormula
  }

  it should "retain context when introducing new variables in results of DG" ignore withMathematica { _ =>
    val result = proveBy(Sequent(IndexedSeq("b>0".asFormula), IndexedSeq("\\exists y [{x'=2,y'=1}]x>=0".asFormula)), transform("y/b>0 & x*y>=0".asFormula)(1, 0::1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "b>0".asFormula
    result.subgoals.head.succ should contain only "\\exists y [{x'=2,y'=1}](y/b>0 & x*y>=0)".asFormula
  }
}
