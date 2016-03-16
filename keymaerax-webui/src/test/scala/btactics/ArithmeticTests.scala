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
}
