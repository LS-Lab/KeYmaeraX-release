package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleError
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tools.{ToolEvidence, DiffSolutionTool, CounterExampleTool, ToolBase}

import scala.collection.immutable._

class ArithmeticTests extends TacticTestBase {

  private class MockTool(expected: Formula) extends ToolBase("MockTool") with QETool with DiffSolutionTool with CounterExampleTool {
    initialized = true
    //@todo should we keep hacking ourselves into the trusted tools of the core, or should we add a TestMode where MockTool is trusted?
    val rcf = Class.forName(RCF.getClass.getCanonicalName).getField("MODULE$").get(null)
    val trustedToolsField = rcf.getClass.getDeclaredField("trustedTools")
    trustedToolsField.setAccessible(true)
    val trustedTools = trustedToolsField.get(rcf).asInstanceOf[List[String]]
    trustedToolsField.set(rcf, trustedTools :+ MockTool.this.getClass.getCanonicalName)

    override def qeEvidence(formula: Formula): (Formula, Evidence) = {
      formula shouldBe expected
      (False, ToolEvidence(Map("tool" -> "mock")))
    }

    override def findCounterExample(formula: Formula): Option[Map[NamedSymbol, Term]] = {
      formula shouldBe expected
      None
    }

    override def shutdown(): Unit = {}
    override def init(config: Map[String, String]): Unit = {}
    override def restart(): Unit = {}

    override def diffSol(diffSys: DifferentialProgram, diffArg: Variable, iv: Predef.Map[Variable, Variable]): Option[Formula] = ???
  }

  "fullQE" should "apply equalities, transform to implication, and compute universal closure" in withTool(
      new MockTool(
        "\\forall x_1 \\forall v_1 \\forall t_0 \\forall s_0 (v_1>0&x_1 < s_0&-1*(v_1^2/(2*(s_0-x_1)))*t_0+v_1>=0&t_0>=0->1/2*(-1*(v_1^2/(2*(s_0-x_1)))*t_0^2+2*t_0*v_1+2*x_1)+(-1*(v_1^2/(2*(s_0-x_1)))*t_0+v_1)^2/(2*(v_1^2/(2*(s_0-x_1))))<=s_0)".asFormula)) { tool =>
    //@note actual assertions are made by MockTool, expect a BelleError since MockTool returns false as QE answer
    the [BelleError] thrownBy proveBy(
      Sequent(Nil,
        IndexedSeq("v_0>0&x_0<s".asFormula, "a=v_0^2/(2*(s-x_0))".asFormula, "t_0=0".asFormula),
        IndexedSeq("v>=0&t>=0&v=(-1*a*t+v_0)&x=1/2*(-1*a*t^2+2*t*v_0+2*x_0)->x+v^2/(2*a)<=s".asFormula)),
      TactixLibrary.QE) should have message """[Bellerophon Runtime] Expected proved provable, but got Provable(v_0>0&x_0 < s, a=v_0^2/(2*(s-x_0)), t_0=0
                                                                            |  ==>  v>=0&t>=0&v=-1*a*t+v_0&x=1/2*(-1*a*t^2+2*t*v_0+2*x_0)->x+v^2/(2*a)<=s
                                                                            |  from     ==>  false)""".stripMargin
  }

  it should "prove after apply equalities, transform to implication, and universal closure" in withMathematica { tool =>
    proveBy(
      Sequent(Nil,
        IndexedSeq("v_0>0&x_0<s".asFormula, "a=v_0^2/(2*(s-x_0))".asFormula, "t_0=0".asFormula),
        IndexedSeq("v>=0&t>=0&v=(-1*a*t+v_0)&x=1/2*(-1*a*t^2+2*t*v_0+2*x_0)->x+v^2/(2*a)<=s".asFormula)),
      TactixLibrary.QE) shouldBe 'proved
  }

  it should "only apply equalities for variables" in withTool(
      new MockTool(
        "\\forall y_0 \\forall x_0 \\forall r_0 (x_0^2+y_0^2=r_0^2&r_0>0->y_0<=r_0)".asFormula)) { tool =>
    the [BelleError] thrownBy proveBy(
      Sequent(Nil,
        IndexedSeq("x^2 + y^2 = r^2".asFormula, "r > 0".asFormula),
        IndexedSeq("y <= r".asFormula)),
      TactixLibrary.QE) should have message """[Bellerophon Runtime] Expected proved provable, but got Provable(x^2+y^2=r^2, r>0
                                                                            |  ==>  y<=r
                                                                            |  from     ==>  false)""".stripMargin
  }

  it should "prove after only apply equalities for variables" in withMathematica { tool =>
    proveBy(
      Sequent(Nil,
        IndexedSeq("x^2 + y^2 = r^2".asFormula, "r > 0".asFormula),
        IndexedSeq("y <= r".asFormula)),
      TactixLibrary.QE) shouldBe 'proved
  }

  it should "not support differential symbols" in withMathematica { tool =>
    the [BelleError] thrownBy { proveBy(
      Sequent(Nil,
        IndexedSeq(),
        IndexedSeq("5=5 | x' = 1'".asFormula)),
      TactixLibrary.QE) } should have message "[Bellerophon Runtime] x' (of class edu.cmu.cs.ls.keymaerax.core.DifferentialSymbol)"
  }

  it should "not prove differential symbols by some hidden assumption in Mathematica" in withMathematica { tool =>
    the [BelleError] thrownBy proveBy(
      Sequent(Nil,
        IndexedSeq(),
        IndexedSeq("x' = y'".asFormula)),
      TactixLibrary.QE) should have message "[Bellerophon Runtime] x' (of class edu.cmu.cs.ls.keymaerax.core.DifferentialSymbol)"
  }

  it should "avoid name clashes" in withMathematica { tool =>
    the [BelleError] thrownBy proveBy(
      Sequent(Nil,
        IndexedSeq("a=1".asFormula, "a()=2".asFormula),
        IndexedSeq("a=a()".asFormula)),
      TactixLibrary.QE) should have message """[Bellerophon Runtime] Expected proved provable, but got Provable(a=1, a()=2
                                                                            |  ==>  a=a()
                                                                            |  from     ==>  false)""".stripMargin

    proveBy(
      Sequent(Nil,
        IndexedSeq("a=1".asFormula, "a()=2".asFormula),
        IndexedSeq("a<a()".asFormula)),
      TactixLibrary.QE) shouldBe 'proved
  }

  "counterExample" should "not choke on differential symbols" in withMathematica { tool =>
    tool.findCounterExample("v'>=0".asFormula) match {
      //@note less elegant expected test result, because Mathematica may return different counter examples, not -18 every the time
      case Some(m) =>
        m.size shouldBe 1
        m.keySet should contain only "v'".asTerm
    }
  }

  it should "not choke on function symbols" in withMathematica { tool =>
    tool.findCounterExample("v>=A()".asFormula) match {
      //@note less elegant expected test result, because Mathematica may return different counter examples, not -18 every the time
      case Some(m) =>
        m.size shouldBe 2
        m.keySet should contain only (Variable("v"), Function("A", None, Unit, Real))
    }
  }

  it should "avoid name clashes between variables and parameterless functions" in withMathematica { tool =>
    tool.findCounterExample("a>=a()".asFormula) match {
      //@note less elegant expected test result, because Mathematica may return different counter examples
      case Some(m) =>
        m.size shouldBe 2
        m.keySet should contain only (Variable("a"), Function("a", None, Unit, Real))
    }

    tool.findCounterExample("a=1&a()=2 -> a=a()".asFormula) match {
      //@note less elegant expected test result, because Mathematica may return different counter examples
      case Some(m) =>
        m.size shouldBe 2
        m.keySet should contain only (Variable("a"), Function("a", None, Unit, Real))
    }

    tool.findCounterExample("a=1&a()=2 -> a<a()".asFormula) shouldBe None
  }

  "transform" should "prove a simple example" in withMathematica { tool =>
    proveBy(
      Sequent(Nil,
        IndexedSeq("a<b".asFormula),
        IndexedSeq("b>a".asFormula)),
      ToolTactics.transform("a<b".asFormula)(tool)(1) & TactixLibrary.closeId) shouldBe 'proved
  }

  it should "prove a simple example with modalities in other formulas" in withMathematica { tool =>
    proveBy(
      Sequent(Nil,
        IndexedSeq("a<b".asFormula),
        IndexedSeq("b>a".asFormula, "[x:=2;]x>0".asFormula)),
      ToolTactics.transform("a<b".asFormula)(tool)(1) & TactixLibrary.closeId) shouldBe 'proved
  }

  it should "keep enough context around to prove the transformation" in withMathematica { tool =>
    proveBy(
      Sequent(Nil,
        IndexedSeq("a+b<c".asFormula, "b>=0&[y:=3;]y=3".asFormula, "y>4".asFormula),
        IndexedSeq("a<c".asFormula, "[x:=2;]x>0".asFormula)),
      ToolTactics.transform("a+b<c".asFormula)(tool)(1) & TactixLibrary.closeId) shouldBe 'proved
  }

  it should "work with division by zero" in withMathematica { tool =>
    proveBy(
      Sequent(Nil,
        IndexedSeq("a/b<c".asFormula, "b>0".asFormula),
        IndexedSeq("c>a/b".asFormula)),
      ToolTactics.transform("a/b<c".asFormula)(tool)(1) & TactixLibrary.closeId) shouldBe 'proved
  }

  it should "work with division by zero even with modalities somewhere" in withMathematica { tool =>
    proveBy(
      Sequent(Nil,
        IndexedSeq("a/b<c".asFormula, "b>0&[y:=3;]y=3".asFormula),
        IndexedSeq("c>a/b".asFormula, "[x:=2;]x>0".asFormula)),
      ToolTactics.transform("a/b<c".asFormula)(tool)(1) & TactixLibrary.closeId) shouldBe 'proved
  }

  "simulate" should "simulate a simple example" in withMathematica { tool =>
    val simulation = tool.simulate("x>0".asFormula, "x>xpre".asFormula, 3, 2)
    simulation should have size 2
    simulation.forall(_.size == 1+3) // initial state + 3 steps
    simulation.forall(_.forall(state => state.keySet.contains(Variable("x")))) shouldBe true
  }
}
