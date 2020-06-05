package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.DLBySubst.assignbExists
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.InvariantGenerator.GenProduct
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.hydra.DbProofTree
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXArchiveParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, UsualTest}

import scala.collection.immutable.IndexedSeq
import scala.language.postfixOps
import org.scalatest.LoneElement._
import testHelper.KeYmaeraXTestTags.TodoTest

/**
 * Tests [[edu.cmu.cs.ls.keymaerax.btactics.DLBySubst]]
 */
@SummaryTest
@UsualTest
class DLTests extends TacticTestBase {

  // ordered up here since used indirectly in many places
  "self assign" should "introduce self assignments for simple formula" in {
    val result = proveBy("x>0".asFormula, DLBySubst.stutter("x".asVariable)(1))
    result.subgoals.loneElement shouldBe "==> [x:=x;]x>0".asSequent
  }

  it should "introduce self assignments for simple formula in antecedent" in {
    val result = proveBy(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq()), DLBySubst.stutter("x".asVariable)(-1))
    result.subgoals.loneElement shouldBe "[x:=x;]x>0 ==> ".asSequent
  }

  it should "introduce self assignments in context in antecedent" in {
    val result = proveBy(Sequent(IndexedSeq("[x:=2;]x>0".asFormula), IndexedSeq()), DLBySubst.stutter("x".asVariable)(-1, 1::Nil))
    result.subgoals.loneElement shouldBe "[x:=2;][x:=x;]x>0 ==> ".asSequent
  }


  "Box abstraction" should "work on top-level" in {
    val result = proveBy("[x:=2;]x>0".asFormula, abstractionb(1))
    result.subgoals.loneElement shouldBe "==> \\forall x x>0".asSequent
  }

  it should "work in context" in {
    val result = proveBy("x>0 & z=1 -> [z:=y;][x:=2;]x>0".asFormula, abstractionb(1, 1::1::Nil))
    result.subgoals.loneElement shouldBe "==> x>0 & z=1 -> [z:=y;]\\forall x x>0".asSequent
  }

  it should "work with loops" in {
    val result = proveBy("[{x:=2;}*]x>0".asFormula, abstractionb(1))
    result.subgoals.loneElement shouldBe "==> \\forall x x>0".asSequent
  }

  it should "not introduce a quantifier when the variables are not bound" in {
    val result = proveBy("[x:=2;]y>0".asFormula, abstractionb(1))
    result.subgoals.loneElement shouldBe "==> y>0".asSequent
  }

  it should "work with ODEs" in withMathematica { _ =>
    val result = proveBy("[{x'=2}]x>0".asFormula, abstractionb(1))
    result.subgoals.loneElement shouldBe "==> \\forall x x>0".asSequent
  }

  it should "work with ODEs followed by derived diff assigns" in withMathematica { _ =>
    val result = proveBy("[{x'=2}][x':=2;]x'>0".asFormula, abstractionb(1))
    //@note x' is not x, hence no \\forall x
    result.subgoals.loneElement shouldBe "==> [x':=2;]x'>0".asSequent
  }

  it should "work with ODEs followed by diff assigns" in withMathematica { _ =>
    val result = proveBy("[{x'=2}][x':=2;](x>0)'".asFormula, abstractionb(1))
    result.subgoals.loneElement shouldBe "==> \\forall x [x':=2;](x>0)'".asSequent
  }

  it should "work with ODEs followed by diff assigns, multi-var case" in withMathematica { _ =>
    val result = proveBy("[{x'=2,y'=3,z'=4}][x':=2;][y':=3;][z':=4;](x>0&y=17&z<4)'".asFormula, abstractionb(1))
    result.subgoals.loneElement shouldBe "==> \\forall x \\forall y \\forall z [x':=2;][y':=3;][z':=4;](x>0&y=17&z<4)'".asSequent
  }

  it should "work with cyclic ODEs" in withMathematica { _ =>
    val result = proveBy("[{x'=y,y'=z,z'=x^2&y>=0}](y>=0->[z':=x^2;][y':=z;][x':=y;]x'>=0)".asFormula, abstractionb(1))
    result.subgoals.loneElement shouldBe "==> \\forall x \\forall y \\forall z (y>=0->[z':=x^2;][y':=z;][x':=y;]x'>=0)".asSequent
  }

  "Auto abstraction" should "not lose information from tests" in {
    proveBy("[?x>0;]x>0".asFormula, abstractionb(1)).subgoals.loneElement shouldBe "==> x>0".asSequent
    //@todo need a better way of naming internal tactics, ideally with location where allocated (but avoid
    // performance penalty of accessing stack trace elements)
    the [BelleThrowable] thrownBy proveBy("[?x>0;]x>0".asFormula, DLBySubst.safeabstractionb(1)) should have message
      "Abstraction would lose information from tests and/or evolution domain constraints"
    // tests could be unsatisfiable
    the [BelleThrowable] thrownBy proveBy("[?false;]x>0".asFormula, DLBySubst.safeabstractionb(1)) should have message
      "Abstraction would lose information from tests and/or evolution domain constraints"
  }

  it should "not lose information from evolution domain constraints" in {
    proveBy("[{y'=3 & x>0}]x>0".asFormula, abstractionb(1)).subgoals.loneElement shouldBe "==> x>0".asSequent
    the [BelleThrowable] thrownBy proveBy("[{y'=3 & x>0}]x>0".asFormula, DLBySubst.safeabstractionb(1)) should have message
      "Abstraction would lose information from tests and/or evolution domain constraints"
    proveBy("[{y'=3 & y>0}]x>0".asFormula, abstractionb(1)).subgoals.loneElement shouldBe "==> x>0".asSequent
    // evolution domain constraint could be unsatisfiable or not hold initially
    the [BelleThrowable] thrownBy proveBy("[{y'=3 & 0>1}]x>0".asFormula, DLBySubst.safeabstractionb(1)) should have message
      "Abstraction would lose information from tests and/or evolution domain constraints"
    proveBy("[{y'=3}]x>0".asFormula, DLBySubst.safeabstractionb(1)).subgoals.loneElement shouldBe "==> x>0".asSequent
  }

  it should "abstract if no tests/evolution domain constraints" in {
    proveBy("[y:=3;]x>0".asFormula, DLBySubst.safeabstractionb(1)).subgoals.loneElement shouldBe "==> x>0".asSequent
  }

  it should "only abstract if no overlap between bound variables of program and free variables of postcondition" in {
    the [BelleThrowable] thrownBy proveBy("[x:=3;]x>0".asFormula, DLBySubst.safeabstractionb(1)) should have message
      "Abstraction would lose information from program"
  }

  "withAbstraction" should "work on top-level when abstraction produces no quantifiers" in {
    val result = proveBy("[{x'=2}]x>0".asFormula, withAbstraction(DW)(1))
    result.subgoals.loneElement shouldBe "==> true->x>0".asSequent
  }

  it should "work on top-level" in {
    val result = proveBy("[{x'=2&x>0}]x>0".asFormula, withAbstraction(DW)(1))
    result.subgoals.loneElement shouldBe "==> x>0->x>0".asSequent
  }

  it should "instantiate all abstraction-generated quantifiers" in {
    val result = proveBy("[{x'=2,y'=3&y>x}]y>x".asFormula, withAbstraction(DW)(1))
    result.subgoals.loneElement shouldBe "==> y>x->y>x".asSequent
  }

  "assignb" should "[y:=1;]y>0 to 1>0" in {
    val result = proveBy("[y:=1;]y>0".asFormula, assignb(1))
    result.subgoals.loneElement shouldBe "==> 1>0".asSequent
  }

  it should "[y:=1;]y>0 to 1>0 in the antecedent" in {
    val result = proveBy(Sequent(IndexedSeq("[y:=1;]y>0".asFormula), IndexedSeq()), assignb(-1))
    result.subgoals.loneElement shouldBe "1>0 ==> ".asSequent
  }

  it should "[y:=1;][z:=2;](y>0 & z>0)" in {
    val result = proveBy("[y:=1;][z:=2;](y>0 & z>0)".asFormula, assignb(1))
    result.subgoals.loneElement shouldBe "==> [z:=2;](1>0 & z>0)".asSequent
  }

  it should "not replace bound variables" in {
    val result = proveBy("[y:=1;][y:=2;]y>0".asFormula, assignb(1))
    result.subgoals.loneElement shouldBe "==> [y:=2;]y>0".asSequent
  }

  it should "only replace free but not bound variables with new universally quantified variable" in {
    val result = proveBy("[y:=1;][y:=2+y;]y>0".asFormula, assignb(1))
    result.subgoals.loneElement shouldBe "==> [y:=2+1;]y>0".asSequent
  }

  it should "replace free variables in ODEs with new universally quantified variable" in {
    val result = proveBy("[y:=1;][{z'=2+y}](y>0 & z>0)".asFormula, assignb(1))
    result.subgoals.loneElement shouldBe "==> [{z'=2+1}](1>0 & z>0)".asSequent
  }

  it should "work when ODE does not write variable, even if it is not top-level" in {
    val result = proveBy("[x:=1;][t:=0;{y'=1}{z:=2;}*]x>0".asFormula, assignb(1))
    result.subgoals.loneElement shouldBe "==> [t:=0;{y'=1}{z:=2;}*]1>0".asSequent
  }

  it should "work with ODE" in {
    val result = proveBy("[x:=x+1;][{x'=1}]x>0".asFormula, assignb(1))
    result.subgoals.loneElement shouldBe "x=x_0+1 ==> [{x'=1}]x>0".asSequent
  }

  it should "work with ODE as part of step" in {
    val result = proveBy("[x:=x+1;][{x'=1}]x>0".asFormula, step(1))
    result.subgoals.loneElement shouldBe "x=x_0+1 ==> [{x'=1}]x>0".asSequent
  }

  it should "work when must-bound before ODE, even if it is somewhere in propositional context" in {
    val result = proveBy("[x:=1;](y>2 -> \\forall x [{x'=1}]x>0)".asFormula, assignb(1))
    result.subgoals.loneElement shouldBe "==> y>2 -> \\forall x [{x'=1}]x>0".asSequent
  }

  it should "[y:=y+1;]y>0 to y+1>0" in {
    val result = proveBy("[y:=y+1;]y>0".asFormula, assignb(1))
    result.subgoals.loneElement shouldBe "==> y+1>0".asSequent
  }

  it should "work in front of a loop" in {
    val result = proveBy("[x:=1;][{x:=x+1;}*]x>0".asFormula, assignb(1))
    result.subgoals.loneElement shouldBe "x=1 ==> [{x:=x+1;}*]x>0".asSequent
  }

  it should "not touch other assignments flatly" in {
    proveBy("x=1, [x:=2;]x=2 ==> [x:=3;]x>0, [x:=5;]x>6, x=7".asSequent, HilbertCalculus.assignb(1)).
      subgoals.loneElement shouldBe "x=1, [x:=2;]x=2 ==> 3>0, [x:=5;]x>6, x=7".asSequent

    proveBy("x=1, [x:=2;]x=2 ==> [x:=3;]x>0, [x:=5;]x>6, x=7".asSequent, DLBySubst.assignEquality(1)).
      subgoals.loneElement shouldBe "x_0=1, [x_0:=2;]x_0=2, x=3 ==> [x_0:=5;]x_0>6, x_0=7, x>0".asSequent
  }

  it should "not touch other assignments" in {
    proveBy("x=1, [x:=2;]x=2 ==> [x:=3;][{x'=x}]x>0, [x:=5;]x>6, x=7".asSequent, assignb(1)).
      subgoals.loneElement shouldBe "x_0=1, [x_0:=2;]x_0=2, x=3 ==> [x_0:=5;]x_0>6, x_0=7, [{x'=x}]x>0".asSequent
  }


  it should "not touch other assignments and formulas when undoing stuttering" in {
    val result = proveBy("x=2, [x:=2;]x=2 ==> [x:=1;][{x:=x+1;}*]x>0, [x:=3;]x>2".asSequent, assignb(1))
    result.subgoals.loneElement shouldBe "x_0=2, [x_0:=2;]x_0=2, x=1 ==> [x_0:=3;]x_0>2, [{x:=x+1;}*]x>0".asSequent
  }

  it should "work in front of a loop in the antecedent" in {
    val result = proveBy("[x:=1;][{x:=x+1;}*]x>0 ==> ".asSequent, assignb(-1))
    result.subgoals.loneElement shouldBe "x=1, [{x:=x+1;}*]x>0 ==> ".asSequent
  }

  it should "work in front of a loop in context" in {
    val result = proveBy("x=2 ==> [y:=2;][x:=1;][{x:=x+1;}*]x>0".asSequent, assignb(1, 1::Nil))
    result.subgoals.loneElement shouldBe "x_0=2 ==> [y:=2;]\\forall x (x=1 -> [{x:=x+1;}*]x>0)".asSequent
  }

  it should "work in front of a loop in context that binds x" in {
    val result = proveBy("[x:=3;][y:=2;][x:=1;][{x:=x+1;}*]x>0".asFormula, assignb(1, 1::1::Nil))
    result.subgoals.loneElement shouldBe "==> [x_0:=3;][y:=2;]\\forall x (x=1 -> [{x:=x+1;}*]x>0)".asSequent
  }

  it should "work in front of an ODE, even if it is not top-level" in {
    val result = proveBy("[x:=1;][t:=0;{x'=1}]x>0".asFormula, assignb(1))
    result.subgoals.loneElement shouldBe "x=1 ==> [t:=0;{x'=1}]x>0".asSequent
  }

  it should "work in front of an ODE system, even if it is not top-level" in {
    val result = proveBy("[x:=1;][t:=0;{x'=1,y'=2}]x>0".asFormula, assignb(1))
    result.subgoals.loneElement shouldBe "x=1 ==> [t:=0;{x'=1,y'=2}]x>0".asSequent
  }

  it should "work in front of an ODE, even if it is not in the next box" in {
    val result = proveBy("[x:=1;][t:=0;][t:=1;{x'=1}]x>0".asFormula, assignb(1))
    result.subgoals.loneElement shouldBe "x=1 ==> [t:=0;][t:=1;{x'=1}]x>0".asSequent
  }

  it should "work in front of an ODE, even if it is somewhere in propositional context" in {
    val result = proveBy("[x:=1;](y>2 -> [{x'=1}]x>0)".asFormula, assignb(1))
    result.subgoals.loneElement shouldBe "x=1 ==> y>2 -> [{x'=1}]x>0".asSequent
  }

  it should "not rename assignment lhs in may-bound" in {
    val result = proveBy("[x:=z;][y:=y_0;{y:=y+1; ++ x:=x-1;}]x<=y".asFormula, assignb(1))
    result.subgoals.loneElement shouldBe "x=z ==> [y:=y_0;{y:=y+1; ++ x:=x-1;}]x<=y".asSequent
  }

  it should "not rename must-bound x" in {
    val result = proveBy("[x:=z;][y:=y_0;{x:=x;y:=y+1; ++ x:=x-1;}]x<=y".asFormula, assignb(1))
    result.subgoals.loneElement shouldBe "==> [y:=y_0;{x:=z;y:=y+1; ++ x:=z-1;}]x<=y".asSequent
  }

  it should "handle use self-assign in assignb" in {
    val result = proveBy("[x:=x;][x':=2;](x>0)'".asFormula, assignb(1))
    result.subgoals.loneElement shouldBe "==> [x':=2;](x>0)'".asSequent
  }

  it should "introduce universal quantifiers in succedent + positive polarity / antecedent + negative polarity" in {
    proveBy("==> [y:=2;][x:=3;][{x:=x+y+1;}*]x>0".asSequent, assignb(1, 1::Nil)).subgoals.
      loneElement shouldBe "==> [y:=2;]\\forall x (x=3 -> [{x:=x+y+1;}*]x>0)".asSequent
    proveBy("[y:=2;][x:=3;][{x:=x+y+1;}*]x>0 -> z>0 ==> ".asSequent, assignb(-1, 0::1::Nil)).subgoals.
      loneElement shouldBe "[y:=2;]\\forall x (x=3 -> [{x:=x+y+1;}*]x>0) -> z>0 ==> ".asSequent
  }

  it should "introduce existential quantifiers in antecedent + positive polarity / succedent + negative polarity" in {
    proveBy("[y:=2;][x:=3;][{x:=x+y+1;}*]x>0 ==> ".asSequent, assignb(-1, 1::Nil)).subgoals.
      loneElement shouldBe "[y:=2;]\\exists x (x=3 & [{x:=x+y+1;}*]x>0) ==> ".asSequent
    proveBy("==> [y:=2;][x:=3;][{x:=x+y+1;}*]x>0 -> z>0".asSequent, assignb(1, 0::1::Nil)).subgoals.
      loneElement shouldBe "==> [y:=2;]\\exists x (x=3 & [{x:=x+y+1;}*]x>0) -> z>0".asSequent
  }

  "generalize" should "introduce intermediate condition" in {
    val result = proveBy("[x:=2;][y:=x;]y>1".asFormula, generalize("x>1".asFormula)(1))
    result.subgoals shouldBe "==> [x:=2;]x>1".asSequent :: "x>1 ==> [y:=x;]y>1".asSequent :: Nil
  }

  it should "work at any succedent position" in {
    val result = proveBy("==> a=3, [x:=2;][y:=x;]y>1, b=4".asSequent, generalize("x>1".asFormula)(2))
    result.subgoals shouldBe "==> a=3, [x:=2;]x>1, b=4".asSequent :: "x>1 ==> [y:=x;]y>1".asSequent :: Nil
  }

  it should "introduce intermediate condition in context" in {
    val result = proveBy("a=2 -> [z:=3;][x:=2;][y:=x;]y>1".asFormula, generalize("x>1".asFormula)(1, 1::1::Nil))
    result.subgoals shouldBe "==> a=2 -> [z:=3;][x:=2;]x>1".asSequent :: "x>1 ==> [y:=x;]y>1".asSequent :: Nil
  }

  it should "preserve a const fact" in withMathematica { _ =>
    val result = proveBy("A>1&x>5 -> [x:=A;][y:=A*x;]y>1".asFormula, implyR(1) & generalize("x>1".asFormula)(1))
    result.subgoals shouldBe "A>1&x>5 ==> [x:=A;]x>1".asSequent :: "A>1, x>1 ==> [y:=A*x;]y>1".asSequent :: Nil
  }

  it should "preserve function facts" in withMathematica { _ =>
    val result = proveBy("A()>1&x>5 -> [x:=A();][y:=A()*x;]y>1".asFormula, implyR(1) & generalize("x>1".asFormula)(1))
    result.subgoals shouldBe "A()>1&x>5 ==> [x:=A();]x>1".asSequent :: "A()>1, x>1 ==> [y:=A()*x;]y>1".asSequent :: Nil
  }

  it should "preserve multiple facts" in withMathematica { _ =>
    val result = proveBy("A>1&A>2&x>5&A>3 -> [x:=A;][y:=A*x;]y>1".asFormula, implyR(1) & generalize("x>1".asFormula)(1))
    result.subgoals shouldBe "A>1&A>2&x>5&A>3 ==> [x:=A;]x>1".asSequent :: "A>1&A>2&A>3, x>1 ==> [y:=A*x;]y>1".asSequent :: Nil
  }

  it should "preserve const facts in context" in withMathematica { _ =>
    val result = proveBy("A>1&x>5 -> [z:=3;][{z'=A}][x:=A;][y:=A*x;]y>1".asFormula, implyR(1) & generalize("x>1".asFormula)(1, 1::1::Nil))
    //@todo cleanup in context
    result.subgoals shouldBe "A>1&x>5 ==> [z:=3;][{z'=A}](A>1&[x:=A;]x>1)".asSequent :: "A>1, x>1 ==> [y:=A*x;]y>1".asSequent :: Nil
  }

  it should "introduce ghosts for initial values old(.)" in withMathematica { _ =>
    val result = proveBy("x>=0 ==> [x:=x+1;]x>0".asSequent, generalize("x>old(x)".asFormula)(1))
    result.subgoals shouldBe "x_0>=0, x_0=x ==> [x:=x_0+1;]x>x_0".asSequent :: "x_0>=0, x>x_0 ==> x>0".asSequent :: Nil
  }

  "postCut" should "introduce implication in simple example" in {
    val result = proveBy("[a:=5;]a>0".asFormula, postCut("a>1".asFormula)(1))
    result.subgoals shouldBe "==> [a:=5;]a>1".asSequent :: "==> [a:=5;](a>1->a>0)".asSequent :: Nil
  }

  it should "introduce implication" in {
    val result = proveBy("[x:=2;][y:=x;]y>1".asFormula, postCut("x>1".asFormula)(1))
    result.subgoals shouldBe "==> [x:=2;]x>1".asSequent :: "==> [x:=2;](x>1 -> [y:=x;]y>1)".asSequent :: Nil
  }

  it should "introduce implication in context" in {
    val result = proveBy("a=2 -> [z:=3;][x:=2;][y:=x;]y>1".asFormula, postCut("x>1".asFormula)(1, 1::1::Nil))
    result.subgoals shouldBe "==> a=2 -> [z:=3;][x:=2;]x>1".asSequent :: "==> a=2 -> [z:=3;][x:=2;](x>1 -> [y:=x;]y>1)".asSequent :: Nil
  }

  it should "work with non-empty antecedent" in {
    val result = proveBy("x=2 ==> [a:=5;]a>0".asSequent, postCut("a>1".asFormula)(1))
    result.subgoals shouldBe "x=2 ==> [a:=5;]a>1".asSequent :: "x=2 ==> [a:=5;](a>1->a>0)".asSequent :: Nil
  }

  "I" should "work on a simple example" in {
    val result = proveBy("x>2 ==> [{x:=x+1;}*]x>0".asSequent, loop("x>1".asFormula)(1))

    result.subgoals should have size 3
    // init
    result.subgoals(0) shouldBe "x>2 ==> x>1".asSequent
    // use case
    result.subgoals(1) shouldBe "x>1 ==> x>0".asSequent
    // step
    result.subgoals(2) shouldBe "x>1 ==> [x:=x+1;]x>1".asSequent
  }

  it should "keep constants around" in {
    val result = proveBy("x>2, y>0 ==> [{x:=x+y;}*]x>0".asSequent, loop("x>1".asFormula)(1))

    result.subgoals should have size 3
    // init
    result.subgoals(0) shouldBe "x>2, y>0 ==> x>1".asSequent
    // use case
    result.subgoals(1) shouldBe "x>1, y>0 ==> x>0".asSequent
    // step
    result.subgoals(2) shouldBe "x>1, y>0 ==> [x:=x+y;]x>1".asSequent
  }

  it should "wipe all formulas mentioning bound variables from the context" in {
    val result = proveBy("x>0, y>1, z>7 ==> [{x:=2;}*]x>2, x<3, y<4".asSequent, loop("x*y>5".asFormula)(1))

    result.subgoals should have size 3
    // init
    result.subgoals(0) shouldBe "x>0, y>1, z>7 ==> x*y>5, x<3, y<4".asSequent
    // use case
    result.subgoals(1) shouldBe "x*y>5, y>1, z>7 ==> x>2, y<4".asSequent
    // step
    result.subgoals(2) shouldBe "x*y>5, y>1, z>7 ==> [x:=2;]x*y>5, y<4".asSequent
  }

  it should "do the same with a slightly more complicated formula" in {
    val result = proveBy("x>0, y>1, z>7 ==> [{x:=2; ++ y:=z;}*]x>2, x<3, y<4".asSequent, loop("x*y>5".asFormula)(1))

    result.subgoals should have size 3
    // init
    result.subgoals(0) shouldBe "x>0, y>1, z>7 ==> x*y>5, x<3, y<4".asSequent
    // use case
    result.subgoals(1) shouldBe "x*y>5, z>7 ==> x>2".asSequent
    // step
    result.subgoals(2) shouldBe "x*y>5, z>7 ==> [x:=2; ++ y:=z;]x*y>5".asSequent
  }

  it should "apply alpha rule to extract subformulas before wiping from the context" in {
    val result = proveBy("x>0&y>1&z>7 ==> x<3, [{x:=2;}*]x>2, x>5|y<4".asSequent, loop("x*y>5".asFormula)(2))

    result.subgoals should have size 3
    // init
    result.subgoals(0) shouldBe "x>0, y>1, z>7 ==> x<3, x*y>5, x>5, y<4".asSequent
    // use case
    result.subgoals(1) shouldBe "x*y>5, y>1, z>7 ==> x>2, y<4".asSequent
    // step
    result.subgoals(2) shouldBe "x*y>5, y>1, z>7 ==> [x:=2;]x*y>5, y<4".asSequent
  }

  it should "not remove duplicated formulas" in {
    val result = proveBy("x>0, x>0, y>1, z>7 ==> [{x:=2;}*]x>2, x<3, x<3, y<4".asSequent, loop("x*y>5".asFormula)(1))

    result.subgoals should have size 3
    // init
    result.subgoals(0) shouldBe "x>0, x>0, y>1, z>7 ==> x*y>5, x<3, x<3, y<4".asSequent
    // use case
    result.subgoals(1) shouldBe "x*y>5, y>1, z>7 ==> x>2, y<4".asSequent
    // step
    result.subgoals(2) shouldBe "x*y>5, y>1, z>7 ==> [x:=2;]x*y>5, y<4".asSequent
  }

  "I gen" should "work on a simple example" in {
    val succ@Box(prg, _) = "[{x:=x+1;}*]x>0".asFormula
    val result = proveBy(Sequent(IndexedSeq("x>2".asFormula), IndexedSeq(succ)),
      loop(new ConfigurableGenerator[GenProduct](Map((prg, ("x>1".asFormula -> None)::Nil))))(1))

    result.subgoals should have size 3
    // init
    result.subgoals(0) shouldBe "x>2 ==> x>1".asSequent
    // use case
    result.subgoals(1) shouldBe "x>1 ==> x>0".asSequent
    // step
    result.subgoals(2) shouldBe "x>1 ==> [x:=x+1;]x>1".asSequent
  }

  "assignd" should "work with ODE" in {
    val result = proveBy("<x:=x+1;><{x'=1}>x>0".asFormula, assignd(1))
    result.subgoals.loneElement shouldBe "x=x_0+1 ==> <{x'=1}>x>0".asSequent
  }

  it should "work with loop" in {
    val result = proveBy("<x:=x+1;><{x:=x+1;}*>x>0".asFormula, assignd(1))
    result.subgoals.loneElement shouldBe "x=x_0+1 ==> <{x:=x+1;}*>x>0".asSequent
  }

  it should "work with ODE in antecedent" in {
    val result = proveBy("<x:=x+1;><{x:=x+1;}*>x>0 ==> ".asSequent, assignd(-1))
    result.subgoals.loneElement shouldBe "x=x_0+1, <{x:=x+1;}*>x>0 ==> ".asSequent
  }

  it should "work with loop in antecedent and context" in {
    val result = proveBy("0>=0, <x:=x+1;><{x:=x+1;}*>x>0, 1>=1, 2>=2 ==> ".asSequent, assignd(-2))
    result.subgoals.loneElement shouldBe "0>=0, 1>=1, 2>=2, x=x_0+1, <{x:=x+1;}*>x>0 ==> ".asSequent
  }

  it should "introduce universal quantifiers in succedent + positive polarity / antecedent + negative polarity" in {
    proveBy("==> [y:=2;]<x:=3;>[{x:=x+y+1;}*]x>0".asSequent, assignd(1, 1::Nil)).subgoals.
      loneElement shouldBe "==> [y:=2;]\\forall x (x=3 -> [{x:=x+y+1;}*]x>0)".asSequent
    proveBy("[y:=2;]<x:=3;>[{x:=x+y+1;}*]x>0 -> z>0 ==> ".asSequent, assignd(-1, 0::1::Nil)).subgoals.
      loneElement shouldBe "[y:=2;]\\forall x (x=3 -> [{x:=x+y+1;}*]x>0) -> z>0 ==> ".asSequent
  }

  it should "introduce existential quantifiers in antecedent + positive polarity / succedent + negative polarity" in {
    proveBy("[y:=2;]<x:=3;>[{x:=x+y+1;}*]x>0 ==> ".asSequent, assignd(-1, 1::Nil)).subgoals.
      loneElement shouldBe "[y:=2;]\\exists x (x=3 & [{x:=x+y+1;}*]x>0) ==> ".asSequent
    proveBy("==> [y:=2;]<x:=3;>[{x:=x+y+1;}*]x>0 -> z>0".asSequent, assignd(1, 0::1::Nil)).subgoals.
      loneElement shouldBe "==> [y:=2;]\\exists x (x=3 & [{x:=x+y+1;}*]x>0) -> z>0".asSequent
  }

  "Convergence" should "work in easy case" in {
    val result = proveBy("<{x:=x-1;}*>x < 0".asFormula, DLBySubst.con("v_".asVariable, "v_>x".asFormula)(1))
    result.subgoals should have size 3
    result.subgoals(0) shouldBe "==> \\exists v_ v_>x".asSequent
    result.subgoals(1) shouldBe "v_<=0, v_>x ==> x < 0".asSequent
    result.subgoals(2) shouldBe "v_>0, v_>x ==> <x:=x-1;>v_-1>x".asSequent
  }

  it should "work with preconditions" in {
    val result = proveBy("x = 0, 0 >= 0 ==> <{x:=x-1;}*>x < 0".asSequent, DLBySubst.con("v_".asVariable, "v_>x".asFormula)(1))
    result.subgoals should have size 3
    result.subgoals(0) shouldBe "x=0, 0>=0 ==> \\exists v_ v_>x".asSequent
    result.subgoals(1) shouldBe "v_<=0, v_>x, 0>=0 ==> x < 0".asSequent
    result.subgoals(2) shouldBe "v_>0, v_>x, 0>=0 ==> <x:=x-1;>v_-1>x".asSequent
  }

  it should "rename in postcondition" in {
    val result = proveBy("x = 0, 0 >= 0 ==> <{x:=x-1;}*>v_<=2".asSequent, DLBySubst.con("v_".asVariable, "v_<=1".asFormula)(1))
    result.subgoals should have size 3
    result.subgoals(0) shouldBe "x=0, 0>=0 ==> \\exists v_ v_<=1".asSequent
    result.subgoals(1) shouldBe "v_<=0, v_<=1, 0>=0 ==> x_<=2".asSequent
    result.subgoals(2) shouldBe "v_>0, v_<=1, 0>=0 ==> <x:=x-1;>v_-1<=1".asSequent
  }

  it should "work in second position" in {
    val result = proveBy("x=0, 0>=0 ==> 0=1, <{x:=x-1;}*>x<0".asSequent, DLBySubst.con("v_".asVariable, "v_>x".asFormula)(2))
    result.subgoals should have size 3
    result.subgoals(0) shouldBe "x=0, 0>=0 ==> 0=1, \\exists v_ v_>x".asSequent
    result.subgoals(1) shouldBe "v_<=0, v_>x, 0>=0 ==> x<0".asSequent
    result.subgoals(2) shouldBe "v_>0, v_>x, 0>=0 ==> <x:=x-1;>v_-1>x".asSequent
  }

  it should "TODO: accept modal convergence conditions" taggedAs(TodoTest) in {
    val result = proveBy("<{{x'=-1}}*>x < 0".asFormula, DLBySubst.con("v_".asVariable, "<{{x'=-1};v_:=v_-1;}*>(v_>0 & x<0)".asFormula)(1))
    result.subgoals should have size 3
    result.subgoals(0) shouldBe "==> \\exists v_ <{{x'=-1};v_:=v_-1;}*>(v_>0 & x<0)".asSequent
    result.subgoals(1) shouldBe "v_<=0, <{{x'=-1};v_:=v_-1;}*>(v_>0&x < 0) ==> x < 0".asSequent
    //todo: renaming transposes v__0 to x__0
    result.subgoals(2) shouldBe "v__0>0, <{{x'=-1};v__0:=v__0-1;}*>(v__0>0&x<0) ==> <{x'=-1}>\\forall v_ (v_=v__0-1-><{{x'=-1};v_:=v_-1;}*>(v_>0&x < 0))".asSequent
  }

  it should "retain constant fact" in {
    val result = proveBy("x>y, y>0 ==> <{x:=x-y;}*>x<0".asSequent, DLBySubst.con("v_".asVariable, "v_*y>x".asFormula)(1))
    result.subgoals should have size 3
    result.subgoals(0) shouldBe "x>y, y>0 ==> \\exists v_ v_*y>x".asSequent
    result.subgoals(1) shouldBe "v_<=0, v_*y>x, y>0 ==> x < 0".asSequent
    result.subgoals(2) shouldBe "v_>0, v_*y>x, y>0 ==> <x:=x-y;>(v_-1)*y>x".asSequent
  }

  it should "retain constant fact 2" in {
    val result = proveBy("x>y, y>0 ==> <{x:=x-y; {z'=3}}*>x<0".asSequent, DLBySubst.con("v_".asVariable, "v_*y>x".asFormula)(1))
    result.subgoals should have size 3
    result.subgoals(0) shouldBe "x>y, y>0 ==> \\exists v_ v_*y>x".asSequent
    result.subgoals(1) shouldBe "v_<=0, v_*y>x, y>0 ==> x < 0".asSequent
    result.subgoals(2) shouldBe "v_>0, v_*y>x, y>0 ==> <x:=x-y; {z'=3}>(v_-1)*y>x".asSequent
  }

  it should "retain constant facts" in {
    val result = proveBy("x>y, y>0, z>1, a<2 ==> <{x:=x-y*z;}*>x<0".asSequent, DLBySubst.con("v_".asVariable, "v_*y*z>x".asFormula)(1))
    result.subgoals should have size 3
    result.subgoals(0) shouldBe "x>y, y>0, z>1, a<2 ==> \\exists v_ v_*y*z>x".asSequent
    result.subgoals(1) shouldBe "v_<=0, v_*y*z>x, y>0, z>1, a<2 ==> x < 0".asSequent
    result.subgoals(2) shouldBe "v_>0, v_*y*z>x, y>0, z>1, a<2 ==> <x:=x-y*z;>(v_-1)*y*z>x".asSequent
  }

  it should "wipe all context for games" in {
    val result = proveBy("x>y, y>0 ==> <{{x:=x-y; ++ x:=-3;}^@}*>x<0".asSequent, DLBySubst.con("v_".asVariable, "v_*y>x".asFormula)(1))
    result.subgoals should have size 3
    result.subgoals(0) shouldBe "x>y, y>0 ==> \\exists v_ v_*y>x".asSequent
    result.subgoals(1) shouldBe "v_<=0 , v_*y>x ==> x < 0".asSequent
    result.subgoals(2) shouldBe "v_>0, v_*y>x ==> <{x:=x-y; ++ x:=-3;}^@>(v_-1)*y>x".asSequent
  }

  "Loop" should "work with abstract invariant" in {
    val fml = "x>0 -> [{x:=x+1;}*]x>0".asFormula
    val tactic = implyR('R) & loop("J(x)".asFormula)('R) <(skip, skip, assignb('R))
    val result = proveBy(fml, tactic)

    result.subgoals should have size 3
    // init
    result.subgoals(0) shouldBe "x>0 ==> J(x)".asSequent
    // use case
    result.subgoals(1) shouldBe "J(x) ==> x>0".asSequent
    // step
    result.subgoals(2) shouldBe "J(x) ==> J(x+1)".asSequent

    val subst = USubst(SubstitutionPair(
      "J(x)".asFormula.replaceFree("x".asTerm, DotTerm()),
      "x>=1".asFormula.replaceFree("x".asTerm, DotTerm()))::Nil)
    val substResult = result(subst)
    substResult.subgoals should have size 3
    // init
    substResult.subgoals(0) shouldBe "x>0 ==> x>=1".asSequent
    // use case
    substResult.subgoals(1) shouldBe "x>=1 ==> x>0".asSequent
    // step
    substResult.subgoals(2) shouldBe "x>=1 ==> x+1>=1".asSequent
  }

  it should "use close correctly" in withDatabase { db =>
    //@note regression test for bug where listeners were not notified correctly because of exception in close
    val model = "ProgramVariables. R x. End.\nProblem. x>0 -> [{x:=x+1;}*]x>0 End."
    val fml = KeYmaeraXArchiveParser.parseAsProblemOrFormula(model)
    val tactic = implyR('R) & loop("x>0".asFormula)('R)

    val proofId = db.createProof(model)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))

    val BelleProvable(result, _) = interpreter(tactic, BelleProvable(ProvableSig.startProof(fml)))
    result.subgoals.size shouldBe 3
    val finalTree = DbProofTree(db.db, proofId.toString).load()
    finalTree.openGoals.flatMap(_.goal) should contain theSameElementsAs result.subgoals
    (finalTree.nodes.toSet - finalTree.root).foreach(_.maker shouldBe 'defined)
  }

  it should "work with multi-variate abstract invariant" in {
    val fml = "x>1 & y < -1 -> [{x:=x+1;y:=y-1;}*](x>0&y<0)".asFormula
    val tactic = implyR('R) & loop("J(x,y)".asFormula)('R) <(skip, skip, normalize)
    val result = proveBy(fml, tactic)

    result.subgoals should have size 3
    // init
    result.subgoals(0) shouldBe "x>1, y < -1 ==> J(x,y)".asSequent
    // use case
    result.subgoals(1) shouldBe "J(x,y) ==> x>0&y<0".asSequent
    // step
    result.subgoals(2) shouldBe "J(x,y) ==> J(x+1,y-1)".asSequent

    val subst = USubst(SubstitutionPair(
      PredOf(Function("J", None, Tuple(Real, Real), Bool), "(._1,._2)".asTerm),
      "x>=1&y<=-1".asFormula.replaceFree("x".asTerm, "._1".asTerm).replaceFree("y".asTerm, "._2".asTerm))::Nil)
    val substResult = result(subst)
    substResult.subgoals should have size 3
    // init
    substResult.subgoals(0) shouldBe "x>1, y< -1 ==> x>=1&y<=-1".asSequent
    // use case
    substResult.subgoals(1) shouldBe "x>=1&y<=-1 ==> x>0&y<0".asSequent
    // step
    substResult.subgoals(2) shouldBe "x>=1&y<=-1 ==> x+1>=1&y-1<=-1".asSequent
  }

  it should "keep constant context" in {
    val succ@Box(prg, _) = "[{x:=A+B+1;}*]x>0".asFormula
    val result = proveBy(s"A>0, x>2, !B<=0 ==> C<1, ${succ.prettyString}, D<1".asSequent,
      loop(new ConfigurableGenerator[GenProduct](Map((prg, ("x>1".asFormula, None)::Nil))))(2))

    result.subgoals should have size 3
    // init
    result.subgoals(0) shouldBe "A>0, x>2 ==> C<1, x>1, D<1, B<=0".asSequent
    // use case
    result.subgoals(1) shouldBe "x>1, A>0 ==> x>0, B<=0, D<1, C<1".asSequent
    // step
    result.subgoals(2) shouldBe "x>1, A>0 ==> [x:=A+B+1;]x>1, B<=0, D<1, C<1".asSequent
  }

  it should "not fail on program constants" in {
    val result = proveBy("A>0 ==> C<1, [{a_;}*]x>0".asSequent, loop("x>1".asFormula)(2))

    result.subgoals should have size 3
    // init
    result.subgoals(0) shouldBe "A>0 ==> C<1, x>1".asSequent
    // step
    result.subgoals(1) shouldBe "x>1 ==> [a_;]x>1".asSequent
    // use case
    result.subgoals(2) shouldBe "x>1 ==> x>0".asSequent
  }

  it should "introduce discrete ghosts on old(.) notation" in {
    val result = proveBy("x>=0 ==> [{x:=x+1;}*]x>=0".asSequent, loop("x>=old(x)".asFormula)(1))
    result.subgoals should have size 3
    // init
    result.subgoals(0) shouldBe "x_0>=0, x_0=x ==> x>=x_0".asSequent
    // use case
    result.subgoals(1) shouldBe "x>=x_0, x_0>=0 ==> x>=0".asSequent
    // step
    result.subgoals(2) shouldBe "x>=x_0, x_0>=0 ==> [x:=x+1;]x>=x_0".asSequent
  }

  it should "introduce discrete ghosts on old(.) notation and constant keep context" in {
    val result = proveBy("x>=0, A>0, !B>0 ==> C>1, [{x:=x+1;}*]x>=0, D>2".asSequent, loop("x>=old(x)".asFormula)(2))
    result.subgoals should have size 3
    // init
    result.subgoals(0) shouldBe "x_0>=0, A>0, x_0=x ==> C>1, D>2, B>0, x>=x_0".asSequent
    // use case
    result.subgoals(1) shouldBe "x>=x_0, x_0>=0, A>0 ==> x>=0, B>0, D>2, C>1".asSequent
    // step
    result.subgoals(2) shouldBe "x>=x_0, x_0>=0, A>0 ==> [x:=x+1;]x>=x_0, B>0, D>2, C>1".asSequent
  }

  "Throughout" should "split simple sequences" in {
    val result = proveBy("x>2 ==> [{x:=x+1; x:=x+2; x:=x+3;}*]x>0".asSequent, throughout("x>1".asFormula)(1))
    result.subgoals should have size 5
    result.subgoals(0) shouldBe "x>2 ==> x>1".asSequent
    result.subgoals(1) shouldBe "x>1 ==> x>0".asSequent
    result.subgoals(2) shouldBe "x>1 ==> [x:=x+1;]x>1".asSequent
    result.subgoals(3) shouldBe "x>1 ==> [x:=x+2;]x>1".asSequent
    result.subgoals(4) shouldBe "x>1 ==> [x:=x+3;]x>1".asSequent
  }

  it should "keep left-composed sequences together" in {
    val result = proveBy("x>2 ==> [{{x:=x-1;x:=x+1;} {x:=x+2;x:=x-1;} {x:=x+3;x:=x+4;}}*]x>0".asSequent, throughout("x>1".asFormula)(1))
    result.subgoals should have size 6
    result.subgoals(0) shouldBe "x>2 ==> x>1".asSequent
    result.subgoals(1) shouldBe "x>1 ==> x>0".asSequent
    result.subgoals(2) shouldBe "x>1 ==> [x:=x-1;x:=x+1;]x>1".asSequent
    result.subgoals(3) shouldBe "x>1 ==> [x:=x+2;x:=x-1;]x>1".asSequent
    result.subgoals(4) shouldBe "x>1 ==> [x:=x+3;]x>1".asSequent
    result.subgoals(5) shouldBe "x>1 ==> [x:=x+4;]x>1".asSequent
  }

  "Discrete ghost" should "introduce assignment to fresh variable" in {
    val result = proveBy("y>0".asFormula, discreteGhost("y".asVariable)(1))
    result.subgoals.loneElement shouldBe "y_0=y ==> y_0>0".asSequent
  }

  it should "introduce assignment to fresh variable in antecedent" in {
    val result = proveBy(Sequent(IndexedSeq("y>0".asFormula), IndexedSeq()), discreteGhost("y".asVariable)(-1))
    result.subgoals.loneElement shouldBe "y_0=y, y_0>0 ==> ".asSequent
  }

  it should "assign term t to fresh variable" in {
    val result = proveBy("y+1>0".asFormula, discreteGhost("y+1".asTerm, Some("z".asVariable))(1))
    result.subgoals.loneElement shouldBe "z=y+1 ==> z>0".asSequent
  }

  it should "allow arbitrary terms t when a ghost name is specified" in {
    val result = proveBy("y>0".asFormula, discreteGhost("x+5".asTerm, Some("z".asVariable))(1))
    result.subgoals.loneElement shouldBe "z=x+5 ==> y>0".asSequent
  }

  it should "use same variable if asked to do so" in {
    val result = proveBy("y>0".asFormula, DLBySubst.stutter("y".asVariable)(1))
    result.subgoals.loneElement shouldBe "==> [y:=y;]y>0".asSequent
  }

  it should "not accept variables present in f" in {
    a [BelleThrowable] should be thrownBy proveBy("y>z+1".asFormula, discreteGhost("y".asVariable, Some("z".asVariable))(1))
  }

  it should "work on assignments" in {
    val result = proveBy("[y:=2;]y>0".asFormula, discreteGhost("y".asVariable)(1))
    result.subgoals.loneElement shouldBe "y_0=y ==> [y:=2;]y>0".asSequent
  }

  it should "introduce ghosts in the middle of formulas" in {
    val result = proveBy("[x:=1;][y:=2;]y>0".asFormula, discreteGhost("y".asVariable)(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> [x:=1;]\\forall y_0 (y_0=y -> [y:=2;]y>0)".asSequent
  }

  it should "introduce self-assignment ghosts in the middle of formulas when not bound before" in {
    val result = proveBy("[x:=1;][y:=2;]y>0".asFormula, DLBySubst.stutter("y".asVariable)(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> [x:=1;][y:=y;][y:=2;]y>0".asSequent
  }

  it should "not introduce self-assignment ghosts in the middle of formulas when bound" in {
    a [BelleThrowable] should be thrownBy proveBy("[x:=x+1;][{x'=2}]x>0".asFormula, discreteGhost("x".asVariable, Some("x".asVariable))(1, 1::Nil))
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
    result.subgoals.loneElement shouldBe "y_0=y ==> [{y:=y+1;}*]y>0".asSequent
  }

  it should "work on ODEs" in {
    val result = proveBy("[{y'=1}]y>0".asFormula, discreteGhost("y".asVariable)(1))
    result.subgoals.loneElement shouldBe "y_0=y ==> [{y'=1}]y>0".asSequent
  }

  it should "work on ODEs mentioning the ghost in the evolution domain" in {
    val result = proveBy("[{y'=1 & y+1>0}]y>0".asFormula, discreteGhost("y+1".asTerm)(1))
    result.subgoals.loneElement shouldBe "ghost=y+1 ==> [{y'=1 & y+1>0}]y>0".asSequent
  }

  it should "not propagate arbitrary terms into ODEs" in {
    val result = proveBy("[{y'=1}]y>0".asFormula, discreteGhost("y+1".asTerm, Some("z".asVariable))(1))
    result.subgoals.loneElement shouldBe "z=y+1 ==> [{y'=1}]y>0".asSequent
  }

  it should "abbreviate terms in a formula" in {
    val result = proveBy("[x:=5+0;]x>0".asFormula, discreteGhost("0".asTerm, Some("z".asVariable))(1))
    result.subgoals.loneElement shouldBe "z=0 ==> [x:=5+z;]x>z".asSequent
  }

  it should "introduce anonymous ghosts for terms" in {
    val result = proveBy("x>0".asFormula, discreteGhost("y+v/1".asTerm)(1))
    result.subgoals.loneElement shouldBe "ghost=y+v/1 ==> x>0".asSequent
  }

  it should "not clash with preexisting variables when introducing anonymous ghosts" in {
    val result = proveBy("ghost>0 ==> x>0".asSequent, discreteGhost("y+v/1".asTerm)(1))
    result.subgoals.loneElement shouldBe "ghost>0, ghost_0=y+v/1 ==> x>0".asSequent
  }

  "[:=] assign exists" should "turn existential quantifier into assignment" in {
    val result = proveBy("\\exists t [x:=t;]x>=0".asFormula, assignbExists("0".asTerm)(1))
    result.subgoals.loneElement shouldBe "==> [t:=0;][x:=t;]x>=0".asSequent
  }

  it should "turn existential quantifier into assignment for ODEs" in {
    val result = proveBy("\\exists t [{x'=1,t'=1}]x>0".asFormula, assignbExists("0".asTerm)(1))
    result.subgoals.loneElement shouldBe "==> [t:=0;][{x'=1,t'=1}]x>0".asSequent
  }

  it should "work with other formulas around" in {
    val result = proveBy("x>0 ==> \\exists t [{x'=1,t'=1}]x>0, z=1".asSequent, assignbExists("0".asTerm)(1))
    result.subgoals.loneElement shouldBe "x>0 ==> [t:=0;][{x'=1,t'=1}]x>0, z=1".asSequent
  }

  "assign any" should "work in a simple example" in {
    val result = proveBy("[x:=*;]x>0".asFormula, randomb(1))
    result.subgoals.loneElement shouldBe "==> \\forall x x>0".asSequent
  }
}
