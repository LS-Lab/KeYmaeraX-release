/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleThrowable
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.lemma.Lemma
import edu.cmu.cs.ls.keymaerax.parser.Declaration
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ElidingProvable
import edu.cmu.cs.ls.keymaerax.tools.ext.{CounterExampleTool, Goal, QETacticTool}
import edu.cmu.cs.ls.keymaerax.tools.{ConversionException, Tool}
import edu.cmu.cs.ls.keymaerax.tools.qe.KeYmaeraToMathematica

import scala.collection.immutable._
import org.scalatest.LoneElement._
import org.scalatest.Inside._

class ArithmeticTests extends TacticTestBase {

  private class MockTool(expected: Formula) extends Tool with QETacticTool with CounterExampleTool {
    override val name: String = "MockTool"

    private class MockQETool extends QETool {
      //@note ProvableSig forwards to Provable -> Provable has to trust our tool
      private val rcf = Class.forName(Provable.getClass.getCanonicalName).getField("MODULE$").get(null)
      private val trustedToolsField = rcf.getClass.getDeclaredField("trustedTools")
      trustedToolsField.setAccessible(true)
      private val trustedTools = trustedToolsField.get(rcf).asInstanceOf[List[String]]
      trustedToolsField.set(rcf, trustedTools :+ MockQETool.this.getClass.getCanonicalName)

      override def quantifierElimination(formula: Formula): Formula = {
        formula shouldBe expected
        False
      }
    }

    override def qe(formula: Formula): Lemma = {
      val p = ElidingProvable(Provable.proveArithmetic(new MockQETool(), formula), Declaration(Map.empty))
      Lemma(p, Lemma.requiredEvidence(p))
    }

    override def qe(g: Goal, continueOnFalse: Boolean): (Goal, Formula) = ???

    override def findCounterExample(formula: Formula): Option[Map[NamedSymbol, Term]] = {
      formula shouldBe expected
      None
    }

    override def shutdown(): Unit = {}
    override def init(config: Map[String, String]): Unit = {}
    override def restart(): Unit = {}
    override def isInitialized: Boolean = true
    override def cancel(): Boolean = true
  }

  //@todo AdvocatusTest that inserts a broken tool by reflection.

  "fullQE" should "apply equalities, transform to implication, and compute universal closure" in withTactics {
    val tool = new MockTool(
      "\\forall x_0 \\forall v_0 \\forall t \\forall s (v_0>0&x_0 < s&(-1)*(v_0^2/(2*(s-x_0)))*t+v_0>=0&t>=0->1/2*((-1)*(v_0^2/(2*(s-x_0)))*t^2+2*t*v_0+2*x_0)+((-1)*(v_0^2/(2*(s-x_0)))*t+v_0)^2/(2*(v_0^2/(2*(s-x_0))))<=s)".asFormula)
    ToolProvider.setProvider(new PreferredToolProvider(tool::Nil))
    //@note actual assertions are made by MockTool, expect a BelleThrowable since MockTool returns false as QE answer
    val result = proveBy(
      "v_0>0&x_0<s, a=v_0^2/(2*(s-x_0)), t_0=0 ==> v>=0&t>=0&v=(-1*a*t+v_0)&x=1/2*(-1*a*t^2+2*t*v_0+2*x_0)->x+v^2/(2*a)<=s".asSequent,
      TactixLibrary.QE)
    result.subgoals.loneElement shouldBe "==> false".asSequent
  }

  it should "prove after apply equalities, transform to implication, and universal closure" in withQE { _ =>
    proveBy(
      "v_0>0&x_0<s, a=v_0^2/(2*(s-x_0)), t_0=0 ==> v>=0&t>=0&v=(-1*a*t+v_0)&x=1/2*(-1*a*t^2+2*t*v_0+2*x_0)->x+v^2/(2*a)<=s".asSequent,
      TactixLibrary.QE) shouldBe 'proved
  }

  it should "only apply equalities for variables" in withTactics {
    val tool = new MockTool(
      "\\forall y \\forall x \\forall r (x^2+y^2=r^2&r>0->y<=r)".asFormula)
    ToolProvider.setProvider(new PreferredToolProvider(tool::Nil))
    val result = proveBy("x^2 + y^2 = r^2, r > 0 ==> y <= r".asSequent, TactixLibrary.QE)
    result.subgoals.loneElement shouldBe "==> false".asSequent
  }

  it should "prove after only apply equalities for variables" in withQE { _ =>
    proveBy("x^2 + y^2 = r^2, r > 0 ==> y <= r".asSequent, TactixLibrary.QE) shouldBe 'proved
  }

  it should "abbreviate differential symbols" in withQE { _ =>
    proveBy("5=5 | x' = 1".asFormula, TactixLibrary.QE) shouldBe 'proved
  }

  it should "not support differential symbols in conversion" in {
    the [ConversionException] thrownBy KeYmaeraToMathematica("5=5 | x' = 1".asFormula) should
      have message "Name conversion of differential symbols not allowed: x'"
  }

  it should "not prove differential symbols by some hidden assumption in Mathematica" in withMathematica { _ =>
    proveBy("x>=y -> x' >= y'".asFormula, TactixLibrary.QE).subgoals.loneElement shouldBe "==> false".asSequent
  }

  it should "not prove differential symbols by some hidden assumption in Z3" in withZ3 { _ =>
    the [BelleThrowable] thrownBy proveBy("x>=y -> x' >= y'".asFormula,
      TactixLibrary.QE) should have message
      """QE with Z3 gives SAT. Cannot reduce the following formula to True:
        |\forall y \forall x_1 \forall x_0 \forall x (x>=y->x_0>=x_1)
        |""".stripMargin
  }

  it should "avoid name clashes with Mathematica" in withMathematica { _ =>
    val result = proveBy("a=1, a()=2 ==> a=a()".asSequent, TactixLibrary.QE)
    result.subgoals.loneElement shouldBe "==> false".asSequent
    proveBy("a=1, a()=2 ==> a<a()".asSequent, TactixLibrary.QE) shouldBe 'proved
  }

  it should "avoid name clashes with Z3" in withZ3 { _ =>
    the [BelleThrowable] thrownBy proveBy("a=1, a()=2 ==> a=a()".asSequent, TactixLibrary.QE) should have message
      "QE with Z3 gives SAT. Cannot reduce the following formula to True:\n1=2\n"
    proveBy("a=1, a()=2 ==> a<a()".asSequent, TactixLibrary.QE) shouldBe 'proved
  }

  it should "work with functions" in withQE { _ =>
    proveBy("A()>0 -> A()>=0".asFormula, TactixLibrary.QE) shouldBe 'proved
    proveBy("ep>0 & t>=ep & abs(x_0-xo_0)*ep>v -> abs(x_0-xo_0)*t>v".asFormula, TactixLibrary.QE) shouldBe 'proved
  }

  "counterExample" should "not choke on differential symbols" in withMathematica { tool =>
    //@note less elegant expected test result, because Mathematica may return different counter examples, not -18 every the time
    inside (tool.findCounterExample("v'>=0".asFormula)) {
      case Some(m) => m.loneElement._1 shouldBe "v'".asVariable
    }
  }

  it should "not choke on function symbols" in withMathematica { tool =>
    inside (tool.findCounterExample("v>=A()".asFormula)) {
      case Some(m) =>
        m.size shouldBe 2
        m.keySet should contain theSameElementsAs  List("v".asVariable, "A()".asFunction)
        (m("v".asVariable), m("A()".asFunction)) match {
          case (v: Term, a: Term) => proveBy(Less(v, a), TactixLibrary.QE) shouldBe 'proved
          case (v, a) => fail("Unexpected counterexample result, expected terms but got: " +
            v.prettyString + ", " + a.prettyString)
        }
    }
  }

  it should "avoid name clashes between variables and parameterless functions" in withMathematica { tool =>
    inside (tool.findCounterExample("a>=a()".asFormula)) {
      case Some(m) =>
        m.size shouldBe 2
        m.keySet should contain theSameElementsAs  List("a".asVariable, "a()".asFunction)
        (m("a".asVariable), m("a()".asFunction)) match {
          case (v: Term, a: Term) => proveBy(Less(v, a), TactixLibrary.QE) shouldBe 'proved
          case (v, a) => fail("Unexpected counterexample result, expected terms but got: " +
            v.prettyString + ", " + a.prettyString)
        }
    }

    inside (tool.findCounterExample("a=1&a()=2 -> a=a()".asFormula)) {
      case Some(m) =>
        m.size shouldBe 2
        m.keySet should contain theSameElementsAs  List("a".asVariable, "a()".asFunction)
        (m("a".asVariable), m("a()".asFunction)) match {
          case (v: Term, a: Term) => proveBy(NotEqual(v, a), TactixLibrary.QE) shouldBe 'proved
          case (v, a) => fail("Unexpected counterexample result, expected terms but got: " +
            v.prettyString + ", " + a.prettyString)
        }
    }

    tool.findCounterExample("a=1&a()=2 -> a<a()".asFormula) shouldBe None
  }

  it should "support interpreted function symbols" in withMathematica { tool =>
    inside (tool.findCounterExample("abs(x) < 0".asFormula)) {
      case Some(m) =>
        m.size shouldBe 1
        m.keySet should contain theSameElementsAs  List("x".asVariable)
    }
  }

  "transform" should "prove a simple example" in withQE { _ =>
    proveBy(
      "a<b ==> b>a".asSequent,
      TactixLibrary.transform("a<b".asFormula)(1) & TactixLibrary.id) shouldBe 'proved
  }

  it should "prove a simple example with modalities in other formulas" in withQE { _ =>
    proveBy(
      "a<b ==> b>a, [x:=2;]x>0".asSequent,
      TactixLibrary.transform("a<b".asFormula)(1) & TactixLibrary.id) shouldBe 'proved
  }

  it should "keep enough context around to prove the transformation" in withQE { _ =>
    proveBy(
      "a+b<c, b>=0&[y:=3;]y=3, y>4 ==> a<c, [x:=2;]x>0".asSequent,
      TactixLibrary.transform("a+b<c".asFormula)(1) & TactixLibrary.id) shouldBe 'proved
  }

  it should "work with division by zero" in withQE { _ =>
    proveBy(
      "a/b<c, b>0 ==> c>a/b".asSequent,
      TactixLibrary.transform("a/b<c".asFormula)(1) & TactixLibrary.id) shouldBe 'proved
  }

  it should "work with division by zero even with modalities somewhere" in withQE { _ =>
    proveBy(
      "a/b<c, b>0&[y:=3;]y=3 ==> c>a/b, [x:=2;]x>0".asSequent,
      TactixLibrary.transform("a/b<c".asFormula)(1) & TactixLibrary.id) shouldBe 'proved
  }

  "simulate" should "simulate a simple example" in withMathematica { tool =>
    val simulation = tool.simulate("x>0".asFormula, "x>xpre".asFormula, 3, 2)
    simulation should have size 2
    simulation.foreach(_.size shouldBe 1+3) // initial state + 3 steps
    simulation.forall(_.forall(state => state.keySet.contains(Variable("x")))) shouldBe true
  }
}
