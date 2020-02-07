/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
import com.wolfram.jlink.Expr
import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.btactics.{BelleLabels, TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tools.MathematicaConversion.{KExpr, MExpr}
import edu.cmu.cs.ls.keymaerax.tools._
import org.scalatest.PrivateMethodTester
import testHelper.KeYmaeraXTestTags.IgnoreInBuildTest

import scala.collection.immutable.Map

import org.scalatest.LoneElement._

/**
 * Tests the JLink Mathematica implementation.
  *
  * @author Stefan Mitsch
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
    the [CoreException] thrownBy link.qe("abs(-5) > 4".asFormula) should have message
      "Core requirement failed: Interpreted functions not allowed in soundness-critical conversion to Mathematica"
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      val foo = link.qe("abs(-5) > 4".asFormula).fact
      link.qe("abs(-5) > 4".asFormula).fact.conclusion shouldBe "==> abs(-5) > 4 <-> true".asSequent
    }
  }

  "min(1,3) = 1" should "be provable with QE" in withMathematica { link =>
    the [CoreException] thrownBy link.qe("min(1,3) = 1".asFormula) should have message
      "Core requirement failed: Interpreted functions not allowed in soundness-critical conversion to Mathematica"
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      link.qe("min(1,3) = 1".asFormula).fact.conclusion shouldBe "==> min(1,3) = 1 <-> true".asSequent
    }
  }

  "max(1,3) = 3" should "be provable with QE" in withMathematica { link =>
    the [CoreException] thrownBy link.qe("max(1,3) = 3".asFormula) should have message
      "Core requirement failed: Interpreted functions not allowed in soundness-critical conversion to Mathematica"
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      link.qe("max(1,3) = 3".asFormula).fact.conclusion shouldBe "==> max(1,3) = 3 <-> true".asSequent
    }
  }

  if (new java.io.File("/Applications/Mathematica9.app").exists) {
    "Mathematica 9" should "not fail activation test on MacOS" taggedAs IgnoreInBuildTest in {
      val mathematica = new Mathematica(new JLinkMathematicaLink("Mathematica"), "Mathematica")
      mathematica.init(Map("linkName" -> "/Applications/Mathematica9.app/Contents/MacOS/MathKernel"))
      mathematica shouldBe 'initialized
      mathematica.shutdown()
    }
  }

  "Mathematica 10" should "not fail activation test on MacOS" taggedAs IgnoreInBuildTest in {
    val mathematica = new Mathematica(new JLinkMathematicaLink("Mathematica"), "Mathematica")
    mathematica.init(Map("linkName" -> "/Applications/Mathematica.app/Contents/MacOS/MathKernel"))
    mathematica shouldBe 'initialized
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
    link.qe("f(x,y,z)>0 -> f(x,y,z)>=0".asFormula).fact.conclusion shouldBe "==> f(x,y,z)>0 -> f(x,y,z)>=0 <-> true".asSequent
    link.qe("f(x,(y,z))>0 -> f(x,(y,z))>=0".asFormula).fact.conclusion shouldBe "==> f(x,(y,z))>0 -> f(x,(y,z))>=0 <-> true".asSequent
    link.qe("f((x,y),z)>0 -> f((x,y),z)>=0".asFormula).fact.conclusion shouldBe "==> f((x,y),z)>0 -> f((x,y),z)>=0 <-> true".asSequent
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

  "QE" should "label branch on invalid formula" in withMathematica { link =>
    link.qe("5<3".asFormula).fact.conclusion shouldBe "==> 5<3 <-> false".asSequent
    val result = proveBy("5<3".asFormula, TactixLibrary.QE, {
      case Some(labels) => labels should contain theSameElementsAs BelleLabels.cutShow.append(BelleLabels.QECEX)::Nil
      case None => fail("Expected QE CEX label")
    })
    result.subgoals.loneElement shouldBe "==> false".asSequent
  }

  "Blocking kernels" should "be detected" in withMathematica { link =>
    val lnk = PrivateMethod[MathematicaLink]('link)
    val theLink = link invokePrivate lnk()
    val executor: ToolExecutor[(String, KExpr)] = new ToolExecutor(1)

    val trueConverter = new M2KConverter[KExpr] {
      override def k2m: K2MConverter[KExpr] = ???
      override def apply(e: MExpr): KExpr = True
      def convert(e: MExpr): KExpr = ???
    }

    val workers = executor.availableWorkers()
    workers should be >= 1
    println("Start with available workers: " + workers)
    val start = System.currentTimeMillis()
    new Thread(
      () => theLink.run(new MExpr(new MExpr(Expr.SYMBOL,  "Pause"), Array(new MExpr(5))), trueConverter, executor)
    ).start()
    println("Started first task")
    (System.currentTimeMillis() - start) should be <= 200L
    Thread.sleep(1000)
    executor.availableWorkers() shouldBe (workers - 1)
    val intermediate = System.currentTimeMillis()
    println("Second task")
    theLink.run(new MExpr(new MExpr(Expr.SYMBOL,  "Pause"), Array(new MExpr(5))), trueConverter, executor)
    //@note we wait about 1s of the 5s of the first worker (so if only 1 worker we still wait about 4s)
    // and then another 5s in the second worker (check with a little slack time around 9s for <= 1 worker or 5s for > 1 worker)
    if (workers <= 1) (System.currentTimeMillis() - intermediate) should (be >= 8500L and be <= 9500L)
    else (System.currentTimeMillis() - intermediate) should (be >= 4500L and be <= 5500L)
    executor.availableWorkers() shouldBe workers
  }

  "Restarting Mathematica" should "work from a killed kernel" taggedAs IgnoreInBuildTest in withMathematica { link =>
    //@note Kills all WolframKernel!
    val lnk = PrivateMethod[MathematicaLink]('link)
    val theLink = link invokePrivate lnk()
    val bridge = new MathematicaQETool(theLink)

    var compAfterRestart: Option[Expression] = None

    val t = new Thread(() => {
      the [ToolException] thrownBy bridge.run(
        new MExpr(new MExpr(Expr.SYMBOL, "Pause"), Array[MExpr](new MExpr(30)))
      ) should have message "Restarted Mathematica, please rerun the failed command (error details below)"
      compAfterRestart = Some(bridge.run(KeYmaeraToMathematica("2+3".asTerm))._2)
    })
    t.start()
    println("Sleeping for 5s...")
    Thread.sleep(5000)
    println("Killing Mathematica...")
    val rt = Runtime.getRuntime
    if (System.getProperty("os.name").toLowerCase.indexOf("mac os x") > -1) {
      rt.exec("pkill -9 MathKernel")
    } else {
      ???
    }
    t.join()
    compAfterRestart shouldBe Some("5".asTerm)
  }
}
