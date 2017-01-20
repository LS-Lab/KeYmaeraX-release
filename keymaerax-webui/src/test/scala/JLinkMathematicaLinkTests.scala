/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tools.{KeYmaeraToMathematica, Mathematica}
import testHelper.KeYmaeraXTestTags.IgnoreInBuildTest

import scala.collection.immutable.Map

/**
 * Tests the JLink Mathematica implementation.
  *
  * @author Stefan Mitsch
 */
class  JLinkMathematicaLinkTests extends TacticTestBase {

  private val x = Variable("x")
  private val y = Variable("y")
  private val z = Variable("z")
  private val t = Variable("t")
  private val x0 = Variable("x", Some(0))
  private val y0 = Variable("y", Some(0))
  private val one = Number(BigDecimal(1))

  "x'=1" should "x=x0+y*t with AtomicODE" in withMathematica { link =>
    val eq = AtomicODE(DifferentialSymbol(x), one)
    val expected = Some("x=t+x_0".asFormula)
    link.odeSolve(eq, t,  Map(x->x0)) should be (expected)
  }

  "x'=y, y'=z" should "y=y0+z*t and x=x0+y0*t+z/2*t^2 with ContProduct" in withMathematica { link =>
    val eq = DifferentialProduct(
      AtomicODE(DifferentialSymbol(x), y),
      AtomicODE(DifferentialSymbol(y), z))
    val expected = Some("x=1/2*(2*x_0 + 2*t*y_0 + t^2*z) & y=y_0 + t*z".asFormula)
    link.odeSolve(eq, t, Map(x->x0, y->y0)) should be (expected)
  }

  "x'=y, t'=1" should "x=x0+y*t with ContProduct" in withMathematica { link =>
    // special treatment of t for now
    val eq = DifferentialProduct(
      AtomicODE(DifferentialSymbol(x), y),
      AtomicODE(DifferentialSymbol(t), one))
    val expected = Some("x=x_0+t*y".asFormula)
    link.odeSolve(eq, t, Map(x->x0)) should be (expected)
  }

  "abs(-5) > 4" should "be provable with QE" in withMathematica { link =>
    link.qeEvidence("abs(-5) > 4".asFormula)._1 shouldBe True
  }

  "min(1,3) = 1" should "be provable with QE" in withMathematica { link =>
    link.qeEvidence("min(1,3) = 1".asFormula)._1 shouldBe True
  }

  "max(1,3) = 3" should "be provable with QE" in withMathematica { link =>
    link.qeEvidence("max(1,3) = 3".asFormula)._1 shouldBe True
  }

  if (new java.io.File("/Applications/Mathematica9.app").exists) {
    "Mathematica 9" should "not fail activation test on MacOS" taggedAs IgnoreInBuildTest in {
      val mathematica = new Mathematica()
      mathematica.init(Map("linkName" -> "/Applications/Mathematica9.app/Contents/MacOS/MathKernel"))
      mathematica shouldBe 'initialized
    }
  }

  "Mathematica 10" should "not fail activation test on MacOS" taggedAs IgnoreInBuildTest in {
    val mathematica = new Mathematica()
    mathematica.init(Map("linkName" -> "/Applications/Mathematica.app/Contents/MacOS/MathKernel"))
    mathematica shouldBe 'initialized
  }

  "Function conversion" should "refuse to prove no-argument functions" in withMathematica { link =>
    a [MatchError] should be thrownBy link.qeEvidence("f()>0 -> f()>=0".asFormula)
  }

  it should "prove one-argument functions correctly" in withMathematica { link =>
    link.qeEvidence("f(x)>0 -> f(x)>=0".asFormula)._1 shouldBe True
  }

  it should "prove binary functions correctly" in withMathematica { link =>
    link.qeEvidence("f(x,y)>0 -> f(x,y)>=0".asFormula)._1 shouldBe True
  }

  it should "prove multi-argument functions correctly" in withMathematica { link =>
    link.qeEvidence("f(x,y,z)>0 -> f(x,y,z)>=0".asFormula)._1 shouldBe True
    link.qeEvidence("f(x,(y,z))>0 -> f(x,(y,z))>=0".asFormula)._1 shouldBe True
    link.qeEvidence("f((x,y),z)>0 -> f((x,y),z)>=0".asFormula)._1 shouldBe True
  }

  "Arithmetic" should "translate x--2 as subtraction of -2 (i.e. +2)" in withMathematica { link =>
    link.qeEvidence("5 < 5--2".asFormula)._1 shouldBe True
  }
}
