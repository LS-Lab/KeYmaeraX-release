package btactics

import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.Sequent
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable.IndexedSeq

/**
 * Tests [[edu.cmu.cs.ls.keymaerax.btactics.DLBySubst]]
 */
class DLTests extends TacticTestBase {

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

  //@todo substitution clash in V
  ignore should "not introduce a quantifier when the variables are not bound" in {
    val result = proveBy("[x:=2;]y>0".asFormula, abstractionb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "y>0".asFormula
  }

  "assignb" should "[y:=1;]y>0 to 1>0" in {
    val result = proveBy("[y:=1;]y>0".asFormula, assignb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "1>0".asFormula
  }

  it should "[y:=1;]y>0 to 1>0 in the antecedent" in {
    val result = proveBy(Sequent(Nil, IndexedSeq("[y:=1;]y>0".asFormula), IndexedSeq()), assignb(-1))
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
    result.subgoals.head.ante should contain only "x_0=1".asFormula
    result.subgoals.head.succ should contain only "[{x_0:=x_0+1;}*]x_0>0".asFormula
  }

  it should "work in front of a loop in the antecedent" in {
    val result = proveBy(Sequent(Nil, IndexedSeq("[x:=1;][{x:=x+1;}*]x>0".asFormula), IndexedSeq()), assignb(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "\\forall x_0 (x_0=1 -> [{x_0:=x_0+1;}*]x_0>0)".asFormula
    result.subgoals.head.succ shouldBe empty
  }

  it should "work in front of a loop in context" in {
    val result = proveBy("[y:=2;][x:=1;][{x:=x+1;}*]x>0".asFormula, assignb(1, 1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[y:=2;]\\forall x_0 (x_0=1 -> [{x_0:=x_0+1;}*]x_0>0)".asFormula
  }

  it should "work in front of an ODE, even if it is not top-level" in {
    val result = proveBy("[x:=1;][t:=0;{x'=1}]x>0".asFormula, assignb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x_0=1".asFormula
    result.subgoals.head.succ should contain only "[t:=0;{x_0'=1}]x_0>0".asFormula
  }

  it should "work in front of an ODE system, even if it is not top-level" in {
    val result = proveBy("[x:=1;][t:=0;{x'=1,y'=2}]x>0".asFormula, assignb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x_0=1".asFormula
    result.subgoals.head.succ should contain only "[t:=0;{x_0'=1,y'=2}]x_0>0".asFormula
  }

  it should "work in front of an ODE, even if it is not in the next box" in {
    val result = proveBy("[x:=1;][t:=0;][t:=1;{x'=1}]x>0".asFormula, assignb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x_0=1".asFormula
    result.subgoals.head.succ should contain only "[t:=0;][t:=1;{x_0'=1}]x_0>0".asFormula
  }

  it should "work in front of an ODE, even if it is somewhere in propositional context" in {
    val result = proveBy("[x:=1;](y>2 -> [{x'=1}]x>0)".asFormula, assignb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x_0=1".asFormula
    result.subgoals.head.succ should contain only "y>2 -> [{x_0'=1}]x_0>0".asFormula
  }

  it should "not rename assignment lhs in may-bound" in {
    val result = proveBy("[x:=z;][y:=y_0;{y:=y+1; ++ x:=x-1;}]x<=y".asFormula, assignb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x_0=z".asFormula
    result.subgoals.head.succ should contain only "[y:=y_0;{y:=y+1; ++ x_0:=x_0-1;}]x_0<=y".asFormula
  }

  it should "not rename must-bound x" in {
    val result = proveBy("[x:=z;][y:=y_0;{x:=x;y:=y+1; ++ x:=x-1;}]x<=y".asFormula, assignb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[y:=y_0;{x:=z;y:=y+1; ++ x:=z-1;}]x<=y".asFormula
  }
}
