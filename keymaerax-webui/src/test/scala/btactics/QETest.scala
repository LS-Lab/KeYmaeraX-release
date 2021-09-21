package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import testHelper.KeYmaeraXTestTags.IgnoreInBuildTest

import scala.collection.immutable.Map

/**
  * Tests of direct calls to quantifier elimination tools
  */
class QETest extends TacticTestBase {

  "Standalone Mathematica QE tool" should "prove abs(5)=5" in withMathematica { qeTool =>
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      qeTool.qe("abs(5)=5".asFormula).fact.conclusion shouldBe "==> abs(5)=5 <-> true".asSequent
    }
  }

  it should "prove abs(-5)=5" in withMathematica { qeTool =>
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      qeTool.qe("abs(-5)=5".asFormula).fact.conclusion shouldBe "==> abs(-5)=5 <-> true".asSequent
    }
  }

  it should "prove abs(x)^2=x^2" in withMathematica  { qeTool =>
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      qeTool.qe("abs(x)^2=x^2".asFormula).fact.conclusion shouldBe "==> abs(x)^2=x^2 <-> true".asSequent
    }
  }

  it should "not get stuck on a quantified arithmetic goal" taggedAs IgnoreInBuildTest in withMathematica  { qeTool =>
    //Strange example that finishes immediately on Mathematica 12.0 but not earlier versions (11.2,11.3)
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      val formula = "\\forall t \\forall v \\forall x \\forall y  (T()>0&A()>0&B()>0&rad()>0&ox()^2+oy()^2=rad()^2&(v>=0&t<=T())&x^2+y^2=rad()^2&t>=0->x-ox()-(v*(T()-t)+A()*(T()-t)^2/2+(v+A()*(T()-t))^2/(2*B()))>0->-y*v/rad()+v>=0)".asFormula
      qeTool.qe(formula).fact.conclusion shouldBe s"==> ${formula.prettyString} <-> true".asSequent
    }
  }

  it should "neither return $Failed nor complain about stale answer if $Failed" in withMathematica { qeTool =>
    val t = "a".asVariable
    import edu.cmu.cs.ls.keymaerax.core._
    def eq(n: Int) = Equal(Times(Number(n), t), (0 until n).map(_ => t).reduce(Plus))
    val n = 250
    /** @note the reason behind this returning $Failed is triggered more directly by the
      *       "expressions deeper than 256" test case in JLinkMathematicaLinkTests */
    withTemporaryConfig(Map(Configuration.Keys.JLINK_USE_EXPR_INTERFACE -> "true")) {
      qeTool.qe(eq(n)).fact.conclusion.succ(0).asInstanceOf[Equiv].right shouldBe True
    }
  }

}
