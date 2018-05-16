/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.btactics.BenchmarkTests._
import edu.cmu.cs.ls.keymaerax.core.{Formula, Program}
import edu.cmu.cs.ls.keymaerax.hydra.DatabasePopulator
import edu.cmu.cs.ls.keymaerax.hydra.DatabasePopulator.TutorialEntry
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXProblemParser}
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import edu.cmu.cs.ls.keymaerax.tools.ToolOperationManagement

import scala.language.postfixOps

import org.scalatest.{AppendedClues, Suites}
import org.scalatest.prop.TableDrivenPropertyChecks._
import org.scalatest.concurrent._
import org.scalatest.time.SpanSugar._

/**
  * Benchmarks.
  * Created by smitsch on 4/26/18.
  */
@SlowTest
class BenchmarkTests extends Suites(
  // benchmark problems from tactics and with database recording
//  new TutorialRegressionTester("Basic Benchmark", s"$GITHUB_PROJECTS_RAW_PATH/benchmarks/basic.kyx"),
//  new TutorialRegressionTester("Advanced Benchmark", s"$GITHUB_PROJECTS_RAW_PATH/benchmarks/advanced.kyx"),
//  new TutorialRegressionTester("Nonlinear Benchmark", s"$GITHUB_PROJECTS_RAW_PATH/benchmarks/nonlinear.kyx")
  // benchmark problems
  new BenchmarkTester("Basic Benchmark", s"$GITHUB_PROJECTS_RAW_PATH/benchmarks/basic.kyx"),
  new BenchmarkTester("Advanced Benchmark", s"$GITHUB_PROJECTS_RAW_PATH/benchmarks/advanced.kyx"),
//  new BenchmarkTester("Nonlinear Benchmark", s"$GITHUB_PROJECTS_RAW_PATH/benchmarks/nonlinear.kyx")
)

object BenchmarkTests {
  private val GITHUB_PROJECTS_RAW_PATH = "https://raw.githubusercontent.com/LS-Lab/KeYmaeraX-projects/master"
  // for testing changes in a locally cloned repository
//    private val GITHUB_PROJECTS_RAW_PATH = "classpath:/keymaerax-projects"
}

class BenchmarkTester(val benchmarkName: String, val url: String) extends TacticTestBase with AppendedClues with Timeouts {

  private def table(entries: List[TutorialEntry]) = {
    Table(("Benchmark name", "Entry name", "Model", "Tactic"),
      entries.map(e => (benchmarkName, e.name, e.model, e.tactic)):_*)
  }

  private val entries = table({
    println("Reading " + url)
    DatabasePopulator.readKya(url)
  })

  private val ODE_TIMEOUT = "30"
  private val TOOL_TIMEOUT = 30

  private def setTimeouts(tool: ToolOperationManagement): Unit = {
    Configuration.set(Configuration.Keys.ODE_TIMEOUT_FINALQE, ODE_TIMEOUT, saveToFile = false)
    tool.setOperationTimeout(TOOL_TIMEOUT)
  }

  it should "prove benchmarks with proof hints and Mathematica" in withMathematica { tool =>
    setTimeouts(tool)
    forEvery (entries) { (_, name, modelContent, _) => runWithHints(name, modelContent) }
  }

//  it should "prove benchmarks with proof hints and Z3" in withZ3 { tool =>
//    setTimeouts(tool)
//    forEvery (entries) { (_, name, modelContent, _) => runWithHints(name, modelContent) }
//  }

  it should "prove benchmarks without proof hints and Mathematica" in withMathematica { tool =>
    setTimeouts(tool)
    forEvery (entries) { (_, name, modelContent, _) => runAuto(name, modelContent) }
  }

//  it should "prove benchmarks without proof hints and Z3" in withZ3 { tool =>
//    setTimeouts(tool)
//    forEvery (entries) { (_, name, modelContent, _) => runAuto(name, modelContent) }
//  }

  private def runWithHints(name: String, modelContent: String) = runEntry(name, parseWithHints(modelContent))
  private def runAuto(name: String, modelContent: String) = runEntry(name, parseStripHints(modelContent))

  private def runEntry(name: String, model: Formula) = {
    withClue(benchmarkName + ": " + name) {
      println(s"Proving $name")

      val start = System.currentTimeMillis()
      val proof = failAfter(2 minutes) { proveBy(model, TactixLibrary.auto) }
      val end = System.currentTimeMillis()

      println(s"Proof Statistics (proved: ${proof.isProved})")
      println(s"$benchmarkName, model $name")
      println(s"Duration [ms]: ${end - start}")
      println("Proof steps: " + proof.steps)

      proof shouldBe 'proved withClue benchmarkName + "/" + name
    }
  }

  /** Parse model and add proof hint annotations to invariant generator. */
  private def parseWithHints(modelContent: String): Formula = {
    TactixLibrary.invGenerator = FixedGenerator(Nil)
    val generator = new ConfigurableGenerator[Formula]()
    KeYmaeraXParser.setAnnotationListener((p: Program, inv: Formula) =>
      generator.products += (p -> (generator.products.getOrElse(p, Nil) :+ inv)))
    val (_, model) = KeYmaeraXProblemParser.parseProblem(modelContent)
    TactixLibrary.invGenerator = generator
    KeYmaeraXParser.setAnnotationListener((_: Program, _: Formula) => {}) //@note cleanup for separation between tutorial entries
    model
  }

  /** Parse model but ignore all proof hints. */
  private def parseStripHints(modelContent: String): Formula = {
    TactixLibrary.invGenerator = FixedGenerator(Nil)
    KeYmaeraXParser.setAnnotationListener((_: Program, _: Formula) => {})
    val (_, model) = KeYmaeraXProblemParser.parseProblem(modelContent)
    model
  }

}

