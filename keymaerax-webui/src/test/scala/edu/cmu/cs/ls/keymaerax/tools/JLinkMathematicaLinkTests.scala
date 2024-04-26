/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.tools

import com.wolfram.jlink.{Expr, KernelLink}
import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon.BelleLabel
import edu.cmu.cs.ls.keymaerax.btactics.{BelleLabels, TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tagobjects.{IgnoreInBuildTest, SlowTest, TodoTest}
import edu.cmu.cs.ls.keymaerax.tools.ext.{
  ExtMathematicaOpSpec,
  JLinkMathematicaLink,
  Mathematica,
  MathematicaLink,
  ToolExecutor,
}
import edu.cmu.cs.ls.keymaerax.tools.install.ToolConfiguration
import edu.cmu.cs.ls.keymaerax.tools.qe.{
  JLinkMathematicaCommandRunner,
  KeYmaeraToMathematica,
  MathematicaOpSpec,
  MathematicaToKeYmaera,
}
import org.scalatest.Inside._
import org.scalatest.LoneElement._
import org.scalatest.PrivateMethodTester

/**
 * Tests the JLink Mathematica implementation.
 *
 * @author
 *   Stefan Mitsch
 */
class JLinkMathematicaLinkTests extends TacticTestBase with PrivateMethodTester {

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
    link.odeSolve(eq, t, Map(x -> x0)) should be(expected)
  }

  "x'=y, y'=z" should "y=y0+z*t and x=x0+y0*t+z/2*t^2 with ContProduct" in withMathematica { link =>
    val eq = DifferentialProduct(AtomicODE(DifferentialSymbol(x), y), AtomicODE(DifferentialSymbol(y), z))
    val expected = Some("x=1/2*(2*x_0 + 2*t*y_0 + t^2*z) & y=y_0 + t*z".asFormula)
    link.odeSolve(eq, t, Map(x -> x0, y -> y0)) should be(expected)
  }

  "x'=y, t'=1" should "x=x0+y*t with ContProduct" in withMathematica { link =>
    // special treatment of t for now
    val eq = DifferentialProduct(AtomicODE(DifferentialSymbol(x), y), AtomicODE(DifferentialSymbol(t), one))
    val expected = Some("x=x_0+t*y".asFormula)
    link.odeSolve(eq, t, Map(x -> x0)) should be(expected)
  }

  "abs(-5) > 4" should "be provable with QE" in withMathematica { link =>
    inside(the[ConversionException] thrownBy link.qe("abs(-5) > 4".asFormula)) { case ConversionException(_, cause) =>
      cause should have message
        "Core requirement failed: Interpreted functions not allowed in soundness-critical conversion to Mathematica"
    }
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      link.qe("abs(-5) > 4".asFormula).fact.conclusion shouldBe "==> abs(-5) > 4 <-> true".asSequent
    }
  }

  "min(1,3) = 1" should "be provable with QE" in withMathematica { link =>
    inside(the[ConversionException] thrownBy link.qe("min(1,3) = 1".asFormula)) { case ConversionException(_, cause) =>
      cause should have message
        "Core requirement failed: Interpreted functions not allowed in soundness-critical conversion to Mathematica"
    }
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      link.qe("min(1,3) = 1".asFormula).fact.conclusion shouldBe "==> min(1,3) = 1 <-> true".asSequent
    }
  }

  "max(1,3) = 3" should "be provable with QE" in withMathematica { link =>
    inside(the[ConversionException] thrownBy link.qe("max(1,3) = 3".asFormula)) { case ConversionException(_, cause) =>
      cause should have message
        "Core requirement failed: Interpreted functions not allowed in soundness-critical conversion to Mathematica"
    }
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      link.qe("max(1,3) = 3".asFormula).fact.conclusion shouldBe "==> max(1,3) = 3 <-> true".asSequent
    }
  }

  if (new java.io.File("/Applications/Mathematica9.app").exists) {
    "Mathematica 9" should "not fail activation test on MacOS" taggedAs IgnoreInBuildTest in {
      val mathematica = new Mathematica(new JLinkMathematicaLink("Mathematica"), "Mathematica")
      mathematica.init(Map("linkName" -> "/Applications/Mathematica9.app/Contents/MacOS/MathKernel"))
      mathematica shouldBe Symbol("initialized")
      mathematica.shutdown()
    }
  }

  "Mathematica 10" should "not fail activation test on MacOS" taggedAs IgnoreInBuildTest in {
    val mathematica = new Mathematica(new JLinkMathematicaLink("Mathematica"), "Mathematica")
    mathematica.init(Map("linkName" -> "/Applications/Mathematica.app/Contents/MacOS/MathKernel"))
    mathematica shouldBe Symbol("initialized")
    mathematica.shutdown()
  }

  "Function conversion" should "prove no-argument functions correctly" in withMathematica { link =>
    link.qe("f()>0 -> f()>=0".asFormula).fact.conclusion shouldBe "==> f()>0 -> f()>=0 <-> true".asSequent
  }

  it should "prove one-argument functions correctly" in withMathematica { link =>
    link.qe("f(x)>0 -> f(x)>=0".asFormula).fact.conclusion shouldBe "==> f(x)>0 -> f(x)>=0 <-> true".asSequent
  }

  it should "prove binary functions correctly" in withMathematica { link =>
    link.qe("f(x,y)>0 -> f(x,y)>=0".asFormula).fact.conclusion shouldBe "==> f(x,y)>0 -> f(x,y)>=0 <-> true".asSequent
  }

  it should "prove multi-argument functions correctly" in withMathematica { link =>
    link.qe("f(x,y,z)>0 -> f(x,y,z)>=0".asFormula).fact.conclusion shouldBe
      "==> f(x,y,z)>0 -> f(x,y,z)>=0 <-> true".asSequent
    link.qe("f(x,(y,z))>0 -> f(x,(y,z))>=0".asFormula).fact.conclusion shouldBe
      "==> f(x,(y,z))>0 -> f(x,(y,z))>=0 <-> true".asSequent
    link.qe("f((x,y),z)>0 -> f((x,y),z)>=0".asFormula).fact.conclusion shouldBe
      "==> f((x,y),z)>0 -> f((x,y),z)>=0 <-> true".asSequent
  }

  it should "not confuse no-arg functions with variables" in withMathematica { link =>
    link.qe("f()>0 -> f>=0".asFormula).fact.conclusion shouldBe "==> f()>0 -> f>=0 <-> f>=0|f()<=0".asSequent
  }

  it should "prove functions with a decimal number argument correctly" in withMathematica { link =>
    link.qe("f(0.1)>0 -> f(0.1)>=0".asFormula).fact.conclusion shouldBe "==> f(0.1)>0 -> f(0.1)>=0 <-> true".asSequent
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      link.qe("abs(0.1)=0.1".asFormula).fact.conclusion shouldBe "==> abs(0.1)=0.1 <-> true".asSequent
    }
  }

  "Arithmetic" should "translate x--2 as subtraction of -2 (i.e. +2)" in withMathematica { link =>
    link.qe("5 < 5--2".asFormula).fact.conclusion shouldBe "==> 5 < 5--2 <-> true".asSequent
  }

  "QE" should "label branch on invalid formula" taggedAs SlowTest in withMathematica { link =>
    link.qe("5<3".asFormula).fact.conclusion shouldBe "==> 5<3 <-> false".asSequent
    val result = proveBy(
      "5<3".asFormula,
      TactixLibrary.QE,
      (s: Option[List[BelleLabel]]) =>
        s match {
          case Some(labels) => labels.loneElement shouldBe BelleLabels.QECEX
          case None => fail("Expected QE CEX label")
        },
    )
    result.subgoals.loneElement shouldBe "==> false".asSequent
  }

  "Blocking kernels" should "be detected" in withMathematica { link =>
    val lnk = PrivateMethod[MathematicaLink](Symbol("link"))
    val ml = PrivateMethod[KernelLink](Symbol("ml"))
    val theLink = link invokePrivate lnk()
    val commandRunner =
      theLink match { case j: JLinkMathematicaLink => JLinkMathematicaCommandRunner(j.invokePrivate(ml())) }
    val executor: ToolExecutor = new ToolExecutor(1)

    val workers = executor.availableWorkers()
    workers should be >= 1
    val start = System.currentTimeMillis()
    val request = () => {
      val expr: Expr = ExtMathematicaOpSpec.compoundExpression(
        MathematicaOpSpec(MathematicaOpSpec.symbol("Pause"))(MathematicaOpSpec.int(5) :: Nil),
        MathematicaOpSpec.int(7),
      )
      commandRunner.run(expr, MathematicaToKeYmaera)._2
    }
    new Thread(() => theLink.run(request, executor)).start()
    (System.currentTimeMillis() - start) should be <= 200L
    Thread.sleep(1000)
    executor.availableWorkers() shouldBe (workers - 1)
    val intermediate = System.currentTimeMillis()
    theLink.run(request, executor) shouldBe Number(7)
    // @note we wait about 1s of the 5s of the first worker (so if only 1 worker we still wait about 4s)
    // and then another 5s in the second worker (check with a little slack time around 9s for <= 1 worker or 5s for > 1 worker)
    if (workers <= 1) (System.currentTimeMillis() - intermediate) should (be >= 8500L and be <= 9500L)
    else (System.currentTimeMillis() - intermediate) should (be >= 4500L and be <= 5500L)
    executor.availableWorkers() shouldBe workers
  }

  "Restarting Mathematica" should "work from a killed kernel" taggedAs IgnoreInBuildTest in withMathematica { link =>
    // @note Kills all WolframKernel!
    val lnk = PrivateMethod[MathematicaLink](Symbol("link"))
    val ml = PrivateMethod[KernelLink](Symbol("ml"))
    val theLink = link invokePrivate lnk()
    val executor: ToolExecutor = new ToolExecutor(1)

    var compAfterRestart: Option[Expression] = None

    val t = new Thread(() => {
      the[ToolCommunicationException] thrownBy theLink.run(
        () =>
          theLink match {
            case j: JLinkMathematicaLink => JLinkMathematicaCommandRunner(j.invokePrivate(ml()))
                .run(
                  ExtMathematicaOpSpec.compoundExpression(
                    MathematicaOpSpec(MathematicaOpSpec.symbol("Pause"))(MathematicaOpSpec.int(30) :: Nil),
                    MathematicaOpSpec.int(7),
                  ),
                  MathematicaToKeYmaera,
                )
                ._2
          },
        executor,
      ) should have message "Restarted Mathematica, please rerun the failed command (error details below)"
      compAfterRestart = Some(theLink.run(
        () =>
          theLink match {
            case j: JLinkMathematicaLink => JLinkMathematicaCommandRunner(j.invokePrivate(ml()))
                .run(KeYmaeraToMathematica("2+3".asTerm), MathematicaToKeYmaera)
                ._2
          },
        executor,
      ))
    })
    t.start()
    println("Sleeping for 5s...")
    Thread.sleep(5000)
    println("Killing Mathematica...")
    val rt = Runtime.getRuntime
    if (System.getProperty("os.name").toLowerCase.indexOf("mac os x") > -1) {
      rt.exec(Array("pkill", "-9", "MathKernel"))
    } else { ??? }
    t.join()
    compAfterRestart shouldBe Some("5".asTerm)
  }

  it should "shutdown and init repeatably" in withMathematica { tool =>
    tool.shutdown()
    for (_ <- 0 to 10) {
      tool.init(ToolConfiguration.config("mathematica"))
      tool shouldBe Symbol("initialized")
      tool.qe("1>0".asFormula).fact shouldBe Symbol("proved")
      tool.shutdown()
    }
  }

  "Expressions deeper than 256" should "FEATURE_REQUEST: evaluate both as strings and expressions" taggedAs TodoTest in
    withMathematica { mathematica =>
      val lnkMethod = PrivateMethod[MathematicaLink](Symbol("link"))
      val mlMethod = PrivateMethod[KernelLink](Symbol("ml"))
      val ml = mathematica.invokePrivate(lnkMethod()).asInstanceOf[JLinkMathematicaLink].invokePrivate(mlMethod())
      val x = MathematicaOpSpec.symbol("x")
      val deepExpression = (0 until 256).map(_ => x).reduce(MathematicaOpSpec.plus(_, _))
      val res1 = ml.synchronized {
        ml.evaluate(deepExpression.toString)
        ml.waitForAnswer()
        ml.getExpr
      }
      val res2 = ml.synchronized {
        ml.evaluate(deepExpression)
        ml.waitForAnswer()
        ml.getExpr
      }
      res2.toString shouldBe "Times[256, x]"
      // @todo Mathematica returns $Failed
      res1.toString shouldBe "Times[256, x]"
    }

}
