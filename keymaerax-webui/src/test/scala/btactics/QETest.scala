package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleThrowable
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tools.{ToolEvidence, ODESolverTool, CounterExampleTool, ToolBase}

import scala.collection.immutable._

/**
  * Tests of direct calls to quantifier elimination tools
  */
class QETest extends TacticTestBase {

  "Standalone Mathematica QE tool" should "prove abs(5)=5" in withMathematica {qeTool =>
    qeTool.qeEvidence("abs(5)=5".asFormula)
  }

  it should "prove abs(-5)=5" in withMathematica {qeTool =>
    qeTool.qeEvidence("abs(-5)=5".asFormula)
  }

  it should "prove abs(x)^2=x^2" in withMathematica {qeTool =>
    qeTool.qeEvidence("abs(x)^2=x^2".asFormula)
  }
}
