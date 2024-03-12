/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import testHelper.KeYmaeraXTestTags.{IgnoreInBuildTest, TodoTest}

import scala.collection.immutable.Map
import scala.collection.immutable.IndexedSeq

/** Tests of direct calls to quantifier elimination tools */
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

  it should "prove abs(x)^2=x^2" in withMathematica { qeTool =>
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      qeTool.qe("abs(x)^2=x^2".asFormula).fact.conclusion shouldBe "==> abs(x)^2=x^2 <-> true".asSequent
    }
  }

  it should "not get stuck on a quantified arithmetic goal" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    // Strange example that finishes immediately on Mathematica 12.0 but not earlier versions (11.2,11.3)
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      val formula =
        "\\forall t \\forall v \\forall x \\forall y  (T()>0&A()>0&B()>0&rad()>0&ox()^2+oy()^2=rad()^2&(v>=0&t<=T())&x^2+y^2=rad()^2&t>=0->x-ox()-(v*(T()-t)+A()*(T()-t)^2/2+(v+A()*(T()-t))^2/(2*B()))>0->-y*v/rad()+v>=0)"
          .asFormula
      qeTool.qe(formula).fact.conclusion shouldBe s"==> ${formula.prettyString} <-> true".asSequent
    }
  }

  it should "neither return $Failed nor complain about stale answer if $Failed" in withMathematica { qeTool =>
    val t = "a".asVariable
    import edu.cmu.cs.ls.keymaerax.core._
    def eq(n: Int) = Equal(Times(Number(n), t), (0 until n).map(_ => t).reduce(Plus))
    val n = 250

    /**
     * @note
     *   the reason behind this returning $Failed is triggered more directly by the "expressions deeper than 256" test
     *   case in JLinkMathematicaLinkTests
     */
    withTemporaryConfig(Map(Configuration.Keys.JLINK_USE_EXPR_INTERFACE -> "true")) {
      qeTool.qe(eq(n)).fact.conclusion.succ(0).asInstanceOf[Equiv].right shouldBe True
    }
  }

  it should "FEATURE_REQUEST: prove a simple example with nested quantifier" taggedAs TodoTest in withMathematica {
    qeTool =>
      val f =
        "\\forall x \\forall t_ \\forall ep \\forall S \\forall B \\forall A (A>0&B>0&ep>0&t_>=0&\\forall s_ (0<=s_&s_<=t_->0*s_+0>=0&s_+0<=ep)&x+0^2/(2*B)<=S->0*(t_^2/2)+0*t_+x+(0*t_+0)^2/(2*B)<=S)"
          .asFormula
      withTemporaryConfig(Map(Configuration.Keys.MATHEMATICA_QE_METHOD -> "Reduce")) {
        val r = qeTool.qe(f)
        r.fact shouldBe Symbol("proved")
        r.fact.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(Equiv(f, True)))
      }
      withTemporaryConfig(Map(Configuration.Keys.MATHEMATICA_QE_METHOD -> "Resolve")) {
        val r = qeTool.qe(f)
        r.fact shouldBe Symbol("proved")
        // @note Mathematica not able to prove with Resolve!
        r.fact.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(Equiv(f, True)))
      }
  }

}
