package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleError
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.DLBySubst.assignbExists
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, UsualTest}

import scala.collection.immutable.IndexedSeq
import scala.language.postfixOps

/**
 * Tests [[edu.cmu.cs.ls.keymaerax.btactics.DLBySubst]]
 */
@SummaryTest
@UsualTest
class DLTests extends TacticTestBase {

  // ordered up here since used indirectly in many places
  "self assign" should "introduce self assignments for simple formula" in {
    val result = proveBy("x>0".asFormula, DLBySubst.selfAssign("x".asVariable)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[x:=x;]x>0".asFormula
  }

  it should "introduce self assignments for simple formula in antecedent" in {
    val result = proveBy(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq()), DLBySubst.selfAssign("x".asVariable)(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "[x:=x;]x>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "introduce self assignments in context in antecedent" in {
    val result = proveBy(Sequent(IndexedSeq("[x:=2;]x>0".asFormula), IndexedSeq()), DLBySubst.selfAssign("x".asVariable)(-1, 1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "[x:=2;][x:=x;]x>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }


  "Box abstraction" should "work on top-level" in {
    val result = proveBy("[x:=2;]x>0".asFormula, abstractionb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\forall x x>0".asFormula
  }

  it should "work in context" in {
    val result = proveBy("x>0 & z=1 -> [z:=y;][x:=2;]x>0".asFormula, abstractionb(1, 1::1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "x>0 & z=1 -> [z:=y;]\\forall x x>0".asFormula
  }

  it should "work with loops" in {
    val result = proveBy("[{x:=2;}*]x>0".asFormula, abstractionb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\forall x x>0".asFormula
  }

  it should "not introduce a quantifier when the variables are not bound" in {
    val result = proveBy("[x:=2;]y>0".asFormula, abstractionb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "y>0".asFormula
  }

  it should "work with ODEs" in withMathematica { qeTool =>
    val result = proveBy("[{x'=2}]x>0".asFormula, abstractionb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\forall x x>0".asFormula
  }

  it should "work with ODEs followed by derived diff assigns" in withMathematica { qeTool =>
    val result = proveBy("[{x'=2}][x':=2;]x'>0".asFormula, abstractionb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    //@note x' is not x, hence no \\forall x
    result.subgoals.head.succ should contain only "[x':=2;]x'>0".asFormula
  }

  it should "work with ODEs followed by diff assigns" in withMathematica { qeTool =>
    val result = proveBy("[{x'=2}][x':=2;](x>0)'".asFormula, abstractionb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\forall x [x':=2;](x>0)'".asFormula
  }

  it should "work with ODEs followed by diff assigns, multi-var case" in withMathematica { qeTool =>
    val result = proveBy("[{x'=2,y'=3,z'=4}][x':=2;][y':=3;][z':=4;](x>0&y=17&z<4)'".asFormula, abstractionb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\forall x \\forall y \\forall z [x':=2;][y':=3;][z':=4;](x>0&y=17&z<4)'".asFormula
  }

  it should "work with cyclic ODEs" in withMathematica { qeTool =>
    val result = proveBy("[{x'=y,y'=z,z'=x^2&y>=0}](y>=0->[z':=x^2;][y':=z;][x':=y;]x'>=0)".asFormula, abstractionb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\forall x \\forall y \\forall z (y>=0->[z':=x^2;][y':=z;][x':=y;]x'>=0)".asFormula
  }

  "withAbstraction" should "work on top-level when abstraction produces no quantifiers" in {
    val result = proveBy("[{x'=2}]x>0".asFormula, withAbstraction(DW)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "true->x>0".asFormula
  }

  it should "work on top-level" in {
    val result = proveBy("[{x'=2&x>0}]x>0".asFormula, withAbstraction(DW)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "x>0->x>0".asFormula
  }

  it should "instantiate all abstraction-generated quantifiers" in {
    val result = proveBy("[{x'=2,y'=3&y>x}]y>x".asFormula, withAbstraction(DW)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "y>x->y>x".asFormula
  }

  "assignb" should "[y:=1;]y>0 to 1>0" in {
    val result = proveBy("[y:=1;]y>0".asFormula, assignb(1))
    println(result)
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "1>0".asFormula
  }

  it should "[y:=1;]y>0 to 1>0 in the antecedent" in {
    val result = proveBy(Sequent(IndexedSeq("[y:=1;]y>0".asFormula), IndexedSeq()), assignb(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "1>0".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "[y:=1;][z:=2;](y>0 & z>0)" in {
    val result = proveBy("[y:=1;][z:=2;](y>0 & z>0)".asFormula, assignb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[z:=2;](1>0 & z>0)".asFormula
  }

  it should "not replace bound variables" in {
    val result = proveBy("[y:=1;][y:=2;]y>0".asFormula, assignb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[y:=2;]y>0".asFormula
  }

  it should "only replace free but not bound variables with new universally quantified variable" in {
    val result = proveBy("[y:=1;][y:=2+y;]y>0".asFormula, assignb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[y:=2+1;]y>0".asFormula
  }

  it should "replace free variables in ODEs with new universally quantified variable" in {
    val result = proveBy("[y:=1;][{z'=2+y}](y>0 & z>0)".asFormula, assignb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{z'=2+1}](1>0 & z>0)".asFormula
  }

  it should "work when ODE does not write variable, even if it is not top-level" in {
    val result = proveBy("[x:=1;][t:=0;{y'=1}{z:=2;}*]x>0".asFormula, assignb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[t:=0;{y'=1}{z:=2;}*]1>0".asFormula
  }

  it should "work with ODE" in {
    val result = proveBy("[x:=x+1;][{x'=1}]x>0".asFormula, assignb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=x_0+1".asFormula
    result.subgoals.head.succ should contain only "[{x'=1}]x>0".asFormula
  }

  it should "work when must-bound before ODE, even if it is somewhere in propositional context" in {
    val result = proveBy("[x:=1;](y>2 -> \\forall x [{x'=1}]x>0)".asFormula, assignb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "y>2 -> \\forall x [{x'=1}]x>0".asFormula
  }

  it should "[y:=y+1;]y>0 to y+1>0" in {
    val result = proveBy("[y:=y+1;]y>0".asFormula, assignb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "y+1>0".asFormula
  }

  it should "work in front of a loop" in {
    val result = proveBy("[x:=1;][{x:=x+1;}*]x>0".asFormula, assignb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=1".asFormula
    result.subgoals.head.succ should contain only "[{x:=x+1;}*]x>0".asFormula
  }

  it should "not touch other assignments flatly" in {
    val result = proveBy(Sequent(IndexedSeq("x=1".asFormula, "[x:=2;]x=2".asFormula), IndexedSeq("[x:=3;]x>0".asFormula, "[x:=5;]x>6".asFormula, "x=7".asFormula)), HilbertCalculus.assignb(1))
    println(result)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x=1".asFormula, "[x:=2;]x=2".asFormula)
    result.subgoals.head.succ should contain only ("3>0".asFormula, "[x:=5;]x>6".asFormula, "x=7".asFormula)

    val result2 = proveBy(Sequent(IndexedSeq("x=1".asFormula, "[x:=2;]x=2".asFormula), IndexedSeq("[x:=3;]x>0".asFormula, "[x:=5;]x>6".asFormula, "x=7".asFormula)), DLBySubst.assignEquality(1))
    result2.subgoals should have size 1
    result2.subgoals.head.ante should contain only ("x_0=1".asFormula, "[x_0:=2;]x_0=2".asFormula, "x=3".asFormula)
    result2.subgoals.head.succ should contain only ("x>0".asFormula, "[x_0:=5;]x_0>6".asFormula, "x_0=7".asFormula)
  }

  it should "not touch other assignments" in {
    val result = proveBy(Sequent(
      IndexedSeq("x=1".asFormula, "[x:=2;]x=2".asFormula),
      IndexedSeq("[x:=3;][{x'=x}]x>0".asFormula, "[x:=5;]x>6".asFormula, "x=7".asFormula)), assignb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x_0=1".asFormula, "[x_0:=2;]x_0=2".asFormula, "x=3".asFormula)
    result.subgoals.head.succ should contain only ("[{x'=x}]x>0".asFormula, "[x_0:=5;]x_0>6".asFormula, "x_0=7".asFormula)
  }


  it should "not touch other assignments and formulas when undoing stuttering" in {
    val result = proveBy(Sequent(IndexedSeq("x=2".asFormula, "[x:=2;]x=2".asFormula), IndexedSeq("[x:=1;][{x:=x+1;}*]x>0".asFormula, "[x:=3;]x>2".asFormula)), assignb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x_0=2".asFormula, "[x_0:=2;]x_0=2".asFormula, "x=1".asFormula)
    result.subgoals.head.succ should contain only ("[{x:=x+1;}*]x>0".asFormula, "[x_0:=3;]x_0>2".asFormula)
  }

  it should "work in front of a loop in the antecedent" in {
    val result = proveBy(Sequent(IndexedSeq("[x:=1;][{x:=x+1;}*]x>0".asFormula), IndexedSeq()), assignb(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "\\forall x (x=1 -> [{x:=x+1;}*]x>0)".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "work in front of a loop in context" in {
    val result = proveBy(Sequent(IndexedSeq("x=2".asFormula), IndexedSeq("[y:=2;][x:=1;][{x:=x+1;}*]x>0".asFormula)), assignb(1, 1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x_0=2".asFormula
    result.subgoals.head.succ should contain only "[y:=2;]\\forall x (x=1 -> [{x:=x+1;}*]x>0)".asFormula
  }

  it should "work in front of a loop in context that binds x" in {
    val result = proveBy("[x:=3;][y:=2;][x:=1;][{x:=x+1;}*]x>0".asFormula, assignb(1, 1::1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[x_0:=3;][y:=2;]\\forall x (x=1 -> [{x:=x+1;}*]x>0)".asFormula
  }

  it should "work in front of an ODE, even if it is not top-level" in {
    val result = proveBy("[x:=1;][t:=0;{x'=1}]x>0".asFormula, assignb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=1".asFormula
    result.subgoals.head.succ should contain only "[t:=0;{x'=1}]x>0".asFormula
  }

  it should "work in front of an ODE system, even if it is not top-level" in {
    val result = proveBy("[x:=1;][t:=0;{x'=1,y'=2}]x>0".asFormula, assignb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=1".asFormula
    result.subgoals.head.succ should contain only "[t:=0;{x'=1,y'=2}]x>0".asFormula
  }

  it should "work in front of an ODE, even if it is not in the next box" in {
    val result = proveBy("[x:=1;][t:=0;][t:=1;{x'=1}]x>0".asFormula, assignb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=1".asFormula
    result.subgoals.head.succ should contain only "[t:=0;][t:=1;{x'=1}]x>0".asFormula
  }

  it should "work in front of an ODE, even if it is somewhere in propositional context" in {
    val result = proveBy("[x:=1;](y>2 -> [{x'=1}]x>0)".asFormula, assignb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=1".asFormula
    result.subgoals.head.succ should contain only "y>2 -> [{x'=1}]x>0".asFormula
  }

  it should "not rename assignment lhs in may-bound" in {
    val result = proveBy("[x:=z;][y:=y_0;{y:=y+1; ++ x:=x-1;}]x<=y".asFormula, assignb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=z".asFormula
    result.subgoals.head.succ should contain only "[y:=y_0;{y:=y+1; ++ x:=x-1;}]x<=y".asFormula
  }

  it should "not rename must-bound x" in {
    val result = proveBy("[x:=z;][y:=y_0;{x:=x;y:=y+1; ++ x:=x-1;}]x<=y".asFormula, assignb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[y:=y_0;{x:=z;y:=y+1; ++ x:=z-1;}]x<=y".asFormula
  }

  it should "handle use self-assign in assignb" in {
    val result = proveBy("[x:=x;][x':=2;](x>0)'".asFormula, assignb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[x':=2;](x>0)'".asFormula
  }

  "generalize" should "introduce intermediate condition" in {
    val result = proveBy("[x:=2;][y:=x;]y>1".asFormula, generalize("x>1".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[x:=2;]x>1".asFormula
    result.subgoals(1).ante should contain only "x>1".asFormula
    result.subgoals(1).succ should contain only "[y:=x;]y>1".asFormula
  }

  it should "introduce intermediate condition in context" in {
    val result = proveBy("a=2 -> [z:=3;][x:=2;][y:=x;]y>1".asFormula, generalize("x>1".asFormula)(1, 1::1::Nil))
    result.subgoals should have size 2
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "a=2 -> [z:=3;][x:=2;]x>1".asFormula
    result.subgoals(1).ante should contain only "x>1".asFormula
    result.subgoals(1).succ should contain only "[y:=x;]y>1".asFormula
  }

  "postCut" should "introduce implication in simple example" in {
    val result = proveBy("[a:=5;]a>0".asFormula, postCut("a>1".asFormula)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[a:=5;](a>1->a>0) & [a:=5;]a>1".asFormula
  }

  it should "introduce implication" in {
    val result = proveBy("[x:=2;][y:=x;]y>1".asFormula, postCut("x>1".asFormula)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[x:=2;](x>1 -> [y:=x;]y>1) & [x:=2;]x>1".asFormula
  }

  it should "introduce implication in context" in {
    val result = proveBy("a=2 -> [z:=3;][x:=2;][y:=x;]y>1".asFormula, postCut("x>1".asFormula)(1, 1::1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "a=2 -> [z:=3;]([x:=2;](x>1 -> [y:=x;]y>1) & [x:=2;]x>1)".asFormula
  }

  it should "work with non-empty antecedent" in {
    val result = proveBy(Sequent(IndexedSeq("x=2".asFormula), IndexedSeq("[a:=5;]a>0".asFormula)), postCut("a>1".asFormula)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=2".asFormula
    result.subgoals.head.succ should contain only "[a:=5;](a>1->a>0) & [a:=5;]a>1".asFormula
  }

  "I" should "work on a simple example" in {
    val result = proveBy(Sequent(IndexedSeq("x>2".asFormula), IndexedSeq("[{x:=x+1;}*]x>0".asFormula)),
      I("x>1".asFormula)(1))

    result.subgoals should have size 3
    // init
    result.subgoals.head.ante should contain only "x>2".asFormula
    result.subgoals.head.succ should contain only "x>1".asFormula
    // use case
    result.subgoals(1).ante should contain only "x>1".asFormula
    result.subgoals(1).succ should contain only "x>0".asFormula
    // step
    result.subgoals(2).ante should contain only "x>1".asFormula
    result.subgoals(2).succ should contain only "[x:=x+1;]x>1".asFormula
  }

  it should "keep constants around" in {
    val result = proveBy(Sequent(IndexedSeq("x>2".asFormula, "y>0".asFormula), IndexedSeq("[{x:=x+y;}*]x>0".asFormula)),
      I("x>1".asFormula)(1))

    result.subgoals should have size 3
    // init
    result.subgoals.head.ante should contain only ("x>2".asFormula, "y>0".asFormula)
    result.subgoals.head.succ should contain only "x>1".asFormula
    // use case
    result.subgoals(1).ante should contain only ("x>1".asFormula, "y>0".asFormula)
    result.subgoals(1).succ should contain only "x>0".asFormula
    // step
    result.subgoals(2).ante should contain only ("x>1".asFormula, "y>0".asFormula)
    result.subgoals(2).succ should contain only "[x:=x+y;]x>1".asFormula
  }

  it should "wipe all formulas mentioning bound variables from the context" in {
    val result = proveBy(Sequent(IndexedSeq("x>0".asFormula, "y>1".asFormula, "z>7".asFormula), IndexedSeq("[{x:=2;}*]x>2".asFormula, "x<3".asFormula, "y<4".asFormula)), I("x*y>5".asFormula)(1))

    result.subgoals should have size 3
    // init
    result.subgoals.head.ante should contain only ("x>0".asFormula, "y>1".asFormula, "z>7".asFormula)
    result.subgoals.head.succ should contain only ("x<3".asFormula, "y<4".asFormula, "x*y>5".asFormula)
    // use case
    result.subgoals(1).ante should contain only ("x*y>5".asFormula, "y>1".asFormula, "z>7".asFormula)
    result.subgoals(1).succ should contain only "x>2".asFormula
    // step
    result.subgoals(2).ante should contain only ("x*y>5".asFormula, "y>1".asFormula, "z>7".asFormula)
    result.subgoals(2).succ should contain only "[x:=2;]x*y>5".asFormula
  }

  it should "do the same with a slightly more complicated formula" in {
    val result = proveBy(Sequent(IndexedSeq("x>0".asFormula, "y>1".asFormula, "z>7".asFormula), IndexedSeq("[{x:=2; ++ y:=z;}*]x>2".asFormula, "x<3".asFormula, "y<4".asFormula)), I("x*y>5".asFormula)(1))

    result.subgoals should have size 3
    // init
    result.subgoals.head.ante should contain only ("x>0".asFormula, "y>1".asFormula, "z>7".asFormula)
    result.subgoals.head.succ should contain only ("x<3".asFormula, "y<4".asFormula, "x*y>5".asFormula)
    // use case
    result.subgoals(1).ante should contain only ("x*y>5".asFormula, "z>7".asFormula)
    result.subgoals(1).succ should contain only "x>2".asFormula
    // step
    result.subgoals(2).ante should contain only ("x*y>5".asFormula, "z>7".asFormula)
    result.subgoals(2).succ should contain only "[x:=2; ++ y:=z;]x*y>5".asFormula
  }

  it should "apply alpha rule to extract subformulas before wiping from the context" in {
    val result = proveBy(Sequent(IndexedSeq("x>0&y>1&z>7".asFormula), IndexedSeq("x<3".asFormula, "[{x:=2;}*]x>2".asFormula, "x>5|y<4".asFormula)), I("x*y>5".asFormula)(2))

    result.subgoals should have size 3
    // init
    result.subgoals.head.ante should contain only ("x>0".asFormula, "y>1".asFormula, "z>7".asFormula)
    result.subgoals.head.succ should contain only ("x<3".asFormula, "x>5".asFormula, "y<4".asFormula, "x*y>5".asFormula)
    // use case
    result.subgoals(1).ante should contain only ("x*y>5".asFormula, "y>1".asFormula, "z>7".asFormula)
    result.subgoals(1).succ should contain only "x>2".asFormula
    // step
    result.subgoals(2).ante should contain only ("x*y>5".asFormula, "y>1".asFormula, "z>7".asFormula)
    result.subgoals(2).succ should contain only "[x:=2;]x*y>5".asFormula
  }

  it should "remove duplicated formulas" in {
    val result = proveBy(Sequent(IndexedSeq("x>0".asFormula, "x>0".asFormula, "y>1".asFormula, "z>7".asFormula), IndexedSeq("[{x:=2;}*]x>2".asFormula, "x<3".asFormula, "x<3".asFormula, "y<4".asFormula)), I("x*y>5".asFormula)(1))

    result.subgoals should have size 3
    // init
    result.subgoals.head.ante should contain only ("x>0".asFormula, "y>1".asFormula, "z>7".asFormula)
    result.subgoals.head.succ should contain only ("x<3".asFormula, "y<4".asFormula, "x*y>5".asFormula)
    // use case
    result.subgoals(1).ante should contain only ("x*y>5".asFormula, "y>1".asFormula, "z>7".asFormula)
    result.subgoals(1).succ should contain only "x>2".asFormula
    // step
    result.subgoals(2).ante should contain only ("x*y>5".asFormula, "y>1".asFormula, "z>7".asFormula)
    result.subgoals(2).succ should contain only "[x:=2;]x*y>5".asFormula
  }

  "I gen" should "work on a simple example" in {
    val succ@Box(prg, _) = "[{x:=x+1;}*]x>0".asFormula
    val result = proveBy(Sequent(IndexedSeq("x>2".asFormula), IndexedSeq(succ)),
      loop(new ConfigurableGenerate[Formula](Map((prg, "x>1".asFormula))))(1))

    result.subgoals should have size 3
    // init
    result.subgoals.head.ante should contain only "x>2".asFormula
    result.subgoals.head.succ should contain only "x>1".asFormula
    // use case
    result.subgoals(1).ante should contain only "x>1".asFormula
    result.subgoals(1).succ should contain only "x>0".asFormula
    // step
    result.subgoals(2).ante should contain only "x>1".asFormula
    result.subgoals(2).succ should contain only "[x:=x+1;]x>1".asFormula
  }

  "Loop" should "work with abstract invariant" in {
    val fml = "x>0 -> [{x:=x+1;}*]x>0".asFormula
    val tactic = implyR('R) & loop("J(x)".asFormula)('R) <(skip, skip, assignb('R) partial)
    val result = proveBy(fml, tactic)

    result.subgoals should have size 3
    // init
    result.subgoals.head.ante should contain only "x>0".asFormula
    result.subgoals.head.succ should contain only "J(x)".asFormula
    // use case
    result.subgoals(1).ante should contain only "J(x)".asFormula
    result.subgoals(1).succ should contain only "x>0".asFormula
    // step
    result.subgoals(2).ante should contain only "J(x)".asFormula
    result.subgoals(2).succ should contain only "J(x+1)".asFormula

    val subst = USubst(SubstitutionPair(
      "J(x)".asFormula.replaceFree("x".asTerm, DotTerm()),
      "x>=1".asFormula.replaceFree("x".asTerm, DotTerm()))::Nil)
    val substResult = result(subst)

    // init
    substResult.subgoals.head.ante should contain only "x>0".asFormula
    substResult.subgoals.head.succ should contain only "x>=1".asFormula
    // use case
    substResult.subgoals(1).ante should contain only "x>=1".asFormula
    substResult.subgoals(1).succ should contain only "x>0".asFormula
    // step
    substResult.subgoals(2).ante should contain only "x>=1".asFormula
    substResult.subgoals(2).succ should contain only "x+1>=1".asFormula
  }

  ignore should "work with multi-variate abstract invariant" in {
    val fml = "x>1 & y < -1 -> [{x:=x+1;y:=y-1;}*](x>0&y<0)".asFormula
    val tactic = implyR('R) & loop("J(x,y)".asFormula)('R) <(skip, skip, normalize partial)
    val result = proveBy(fml, tactic)

    result.subgoals should have size 3
    // init
    result.subgoals.head.ante should contain only ("x>1".asFormula, "y < -1".asFormula)
    result.subgoals.head.succ should contain only "J(x,y)".asFormula
    // use case
    result.subgoals(1).ante should contain only "J(x,y)".asFormula
    result.subgoals(1).succ should contain only "x>0&y<0".asFormula
    // step
    result.subgoals(2).ante should contain only "J(x,y)".asFormula
    result.subgoals(2).succ should contain only "J(x+1,y-1)".asFormula

    val dot = DotTerm(Tuple(Real, Real))

    //@todo fst/snd not yet available
    val subst = USubst(SubstitutionPair(
      PredOf(Function("J", None, Tuple(Real, Real), Bool), dot),
      "x>=1&y<=-1".asFormula.replaceFree("x".asTerm, "fst(.(.,.))".asTerm).replaceFree("y".asTerm, "snd(.(.,.))".asTerm))::Nil)
    val substResult = result(subst)

    // init
    substResult.subgoals.head.ante should contain only ("x>1".asFormula, "y< -1".asFormula)
    substResult.subgoals.head.succ should contain only "x>=1&y<=-1".asFormula
    // use case
    substResult.subgoals(1).ante should contain only "x>=1&y<=-1".asFormula
    substResult.subgoals(1).succ should contain only "x>0&y<0".asFormula
    // step
    substResult.subgoals(2).ante should contain only "x>=1&y<=-1".asFormula
    substResult.subgoals(2).succ should contain only "x+1>=1&y-1<=-1".asFormula
  }

  it should "keep constant context" in {
    val succ@Box(prg, _) = "[{x:=A+B+1;}*]x>0".asFormula
    val result = proveBy(Sequent(IndexedSeq("A>0".asFormula, "x>2".asFormula, "B>0".asFormula), IndexedSeq("C<1".asFormula, succ, "D<1".asFormula)),
      loop(new ConfigurableGenerate[Formula](Map((prg, "x>1".asFormula))))(2))

    result.subgoals should have size 3
    // init
    result.subgoals.head.ante should contain only ("A>0".asFormula, "x>2".asFormula, "B>0".asFormula)
    result.subgoals.head.succ should contain only ("C<1".asFormula, "x>1".asFormula, "D<1".asFormula)
    // use case
    result.subgoals(1).ante should contain only ("A>0".asFormula, "x>1".asFormula, "B>0".asFormula)
    result.subgoals(1).succ should contain only "x>0".asFormula
    // step
    result.subgoals(2).ante should contain only ("A>0".asFormula, "x>1".asFormula, "B>0".asFormula)
    result.subgoals(2).succ should contain only "[x:=A+B+1;]x>1".asFormula
  }

  "Discrete ghost" should "introduce assignment to fresh variable" in {
    val result = proveBy("y>0".asFormula, discreteGhost("y".asVariable)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[y_0:=y;]y_0>0".asFormula
  }

  it should "assign term t to fresh variable" in {
    val result = proveBy("y+1>0".asFormula, discreteGhost("y+1".asTerm, Some("z".asVariable))(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[z:=y+1;]z>0".asFormula
  }

  it should "allow arbitrary terms t when a ghost name is specified" in {
    val result = proveBy("y>0".asFormula, discreteGhost("x+5".asTerm, Some("z".asVariable))(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[z:=x+5;]y>0".asFormula
  }

  it should "not allow arbitrary terms t when no ghost name is specified" in {
    a [BelleError] should be thrownBy proveBy("y>0".asFormula, discreteGhost("x+5".asTerm)(1))
  }

  it should "use same variable if asked to do so" in {
    val result = proveBy("y>0".asFormula, discreteGhost("y".asVariable, Some("y".asVariable))(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[y:=y;]y>0".asFormula
  }

  it should "not accept variables present in f" in {
    a [BelleError] should be thrownBy proveBy("y>z+1".asFormula, discreteGhost("y".asVariable, Some("z".asVariable))(1))
  }

  it should "work on assignments" in {
    val result = proveBy("[y:=2;]y>0".asFormula, discreteGhost("y".asVariable)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[y_0:=y;][y:=2;]y>0".asFormula
  }

  it should "introduce ghosts in the middle of formulas" in {
    val result = proveBy("[x:=1;][y:=2;]y>0".asFormula, discreteGhost("y".asVariable)(1, 1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[x:=1;][y_0:=y;][y:=2;]y>0".asFormula
  }

  it should "introduce self-assignment ghosts in the middle of formulas when not bound before" in {
    val result = proveBy("[x:=1;][y:=2;]y>0".asFormula, discreteGhost("y".asVariable, Some("y".asVariable))(1, 1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[x:=1;][y:=y;][y:=2;]y>0".asFormula
  }

  it should "not introduce self-assignment ghosts in the middle of formulas when bound" in {
    a [BelleError] should be thrownBy proveBy("[x:=x+1;][{x'=2}]x>0".asFormula, discreteGhost("x".asVariable, Some("x".asVariable))(1, 1::Nil))
  }
//
//  ignore should "introduce ghosts in modality predicates" in {
//    // will not work because y is bound by y:=2, so equality rewriting does not work
//    val tactic = discreteGhostT(None, Variable("y", None, Real))(new SuccPosition(0, new PosInExpr(1 :: Nil)))
//    getProofSequent(tactic, new RootNode(sucSequent("[y:=2;]y>0".asFormula))) should be (
//      sucSequent("[y:=2;][y_0:=y;]y>0".asFormula))
//  }

  it should "work on loops" in {
    val result = proveBy("[{y:=y+1;}*]y>0".asFormula, discreteGhost("y".asVariable)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[y_0:=y;][{y:=y+1;}*]y>0".asFormula
  }

  it should "work on ODEs" in {
    val result = proveBy("[{y'=1}]y>0".asFormula, discreteGhost("y".asVariable)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[y_0:=y;][{y'=1}]y>0".asFormula
  }

  it should "not propagate arbitrary terms into ODEs" in {
    val result = proveBy("[{y'=1}]y>0".asFormula, discreteGhost("y+1".asTerm, Some("z".asVariable))(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[z:=y+1;][{y'=1}]y>0".asFormula
  }

  it should "abbreviate terms in a formula" in {
    val result = proveBy("[x:=5+0;]x>0".asFormula, discreteGhost("0".asTerm, Some("z".asVariable))(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[z:=0;][x:=5+z;]x>z".asFormula
  }

  "[:=] assign exists" should "turn existential quantifier into assignment" in {
    val result = proveBy("\\exists t [x:=t;]x>=0".asFormula, assignbExists("0".asTerm)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[t:=0;][x:=t;]x>=0".asFormula
  }

  it should "turn existential quantifier into assignment for ODEs" in {
    val result = proveBy("\\exists t [{x'=1,t'=1}]x>0".asFormula, assignbExists("0".asTerm)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[t:=0;][{x'=1,t'=1}]x>0".asFormula
  }

  it should "work with other formulas around" in {
    val result = proveBy(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("\\exists t [{x'=1,t'=1}]x>0".asFormula, "z=1".asFormula)),
      assignbExists("0".asTerm)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x>0".asFormula
    result.subgoals.head.succ should contain only ("[t:=0;][{x'=1,t'=1}]x>0".asFormula, "z=1".asFormula)
  }

  "assign any" should "work in a simple example" in {
    val result = proveBy("[x:=*;]x>0".asFormula, randomb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\forall x x>0".asFormula
  }
}
