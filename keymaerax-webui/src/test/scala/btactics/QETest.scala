package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable.Map

/**
  * Tests of direct calls to quantifier elimination tools
  */
class QETest extends TacticTestBase {

  "Standalone Mathematica QE tool" should "prove abs(5)=5" in withMathematica { qeTool =>
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      qeTool.qeEvidence("abs(5)=5".asFormula)
    }
  }

  it should "prove abs(-5)=5" in withMathematica { qeTool =>
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      qeTool.qeEvidence("abs(-5)=5".asFormula)
    }
  }

  it should "prove abs(x)^2=x^2" in withMathematica  { qeTool =>
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      qeTool.qeEvidence("abs(x)^2=x^2".asFormula)
    }
  }
}
