/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import java.io.PrintWriter

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon.TacticStatistics
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics.BenchmarkTests._
import edu.cmu.cs.ls.keymaerax.core.{Formula, Program}
import edu.cmu.cs.ls.keymaerax.hydra.DatabasePopulator
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXProblemParser}
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import edu.cmu.cs.ls.keymaerax.tools.ToolOperationManagement

import scala.language.postfixOps
import org.scalatest.{AppendedClues, Suites}
import org.scalatest.prop.TableDrivenPropertyChecks._
import org.scalatest.concurrent._
import org.scalatest.exceptions.TestFailedDueToTimeoutException
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
//  new BenchmarkTester("Basic", s"$GITHUB_PROJECTS_RAW_PATH/benchmarks/basic.kyx", 2)
//  new BenchmarkTester("Advanced", s"$GITHUB_PROJECTS_RAW_PATH/benchmarks/advanced.kyx", 20),
  new BenchmarkTester("Nonlinear", s"$GITHUB_PROJECTS_RAW_PATH/benchmarks/nonlinear.kyx", 5)
)

object BenchmarkTests {
  private val GITHUB_PROJECTS_RAW_PATH = "https://raw.githubusercontent.com/LS-Lab/KeYmaeraX-projects/master"
  // for testing changes in a locally cloned repository
//    private val GITHUB_PROJECTS_RAW_PATH = "classpath:/keymaerax-projects"
}

/** Collects a benchmark result. */
case class BenchmarkResult(name: String, status: String, timeout: Int, duration: Long, proofSteps: Int, tacticSize: Int,
                           ex: Option[Throwable]) {
  override def toString: String =
    s"""Proof Statistics ($name $status, with time budget $timeout)
      |Duration [ms]: $duration
      |Proof steps: $proofSteps
      |Tactic size: $tacticSize
    """.stripMargin

def toCsv: String = s"$name,$status,$timeout,$duration,$proofSteps,$tacticSize"
}

class BenchmarkTester(val benchmarkName: String, val url: String, val timeout: Int) extends TacticTestBase with AppendedClues with Timeouts {

  private val entries = {
    println("Reading " + url)
    DatabasePopulator.readKya(url)
  }

  private def tableResults(results: Seq[BenchmarkResult]) = {
    Table(("Benchmark name", "Entry name", "Status", "Duration", "Failure Cause"),
    results.map(r => (benchmarkName, r.name, r.status, r.duration, r.ex)):_*)
  }

  private def setTimeouts(tool: ToolOperationManagement): Unit = {
    Configuration.set(Configuration.Keys.ODE_TIMEOUT_FINALQE, timeout.toString, saveToFile = false)
    Configuration.set(Configuration.Keys.PEGASUS_INVCHECK_TIMEOUT, (timeout/3).toString, saveToFile = false)
    tool.setOperationTimeout(timeout)
  }

  it should "prove interactive benchmarks" in withMathematica { tool =>
    setTimeouts(tool)
    val results = entries.map(e => runInteractive(e.name, e.model, e.tactic.map(_._2)))
    val writer = new PrintWriter(benchmarkName + "_interactive.csv")
    writer.write(
      "Name,Status,Timeout[min],Duration[ms],Proof Steps,Tactic Size\r\n" + results.map(_.toCsv).mkString("\r\n"))
    writer.close()
    forEvery(tableResults(results)) { (_, name, status, _, cause) =>
      status should (be ("proved") withClue cause or be ("skipped"))
    }
  }

  it should "prove benchmarks with proof hints and Mathematica" in withMathematica { tool =>
    setTimeouts(tool)
    val results = entries.map(e => runWithHints(e.name, e.model, e.tactic.map(_._2)))
    val writer = new PrintWriter(benchmarkName + "_withhints.csv")
    writer.write(
      "Name,Status,Timeout[min],Duration[ms],Proof Steps,Tactic Size\r\n" + results.map(_.toCsv).mkString("\r\n"))
    writer.close()
    forEvery(tableResults(results)) { (_, name, status, _, cause) =>
      if (entries.find(_.name == name).get.tactic.map(_._2.trim()).contains("master")) status shouldBe "proved" withClue cause
      else if (status == "proved") fail("Learned how to prove " + name + "; add automated tactic to benchmark")
    }
  }

//  it should "prove benchmarks with proof hints and in Z3" in withZ3 { tool =>
//    setTimeouts(tool)
//    forEvery (entries) { (_, name, modelContent, _) => runWithHints(name, modelContent) }
//  }

  it should "prove benchmarks without proof hints and in Mathematica" in withMathematica { tool =>
    setTimeouts(tool)
    val results = entries.map(e => runAuto(e.name, e.model))
    val writer = new PrintWriter(benchmarkName + "_auto.csv")
    writer.write(
      "Name,Status,Timeout[min],Duration[ms],Proof Steps,Tactic Size\r\n" + results.map(_.toCsv).mkString("\r\n"))
    writer.close()
    forEvery(tableResults(results)) { (_, name, status, _, cause) =>
      if (entries.find(_.name == name).get.tactic.map(_._2.trim()).contains("master")) status shouldBe "proved" withClue cause
      else if (status == "proved") fail("Learned how to prove " + name + "; add automated tactic to benchmark")
    }
  }

//  it should "prove benchmarks without proof hints and in Z3" in withZ3 { tool =>
//    setTimeouts(tool)
//    forEvery (entries) { (_, name, modelContent, _) => runAuto(name, modelContent) }
//  }

  private def runInteractive(name: String, modelContent: String, tactic: Option[String]) =
    runEntry(name, parseWithHints(modelContent), tactic.map(_.trim) match { case Some("master") => None case t => t })
  private def runWithHints(name: String, modelContent: String, tactic: Option[String]) =
    runEntry(name, parseWithHints(modelContent), Some("master"))
  private def runAuto(name: String, modelContent: String) =
    runEntry(name, parseStripHints(modelContent), Some("master"))

  private def runEntry(name: String, model: Formula, tactic: Option[String]): BenchmarkResult = {
    tactic match {
      case Some(t) =>
        println(s"Proving $name")

        val start = System.currentTimeMillis()
        val theTactic = BelleParser(t)
        try {
          val proof = failAfter(timeout minutes) {
            proveBy(model, theTactic)
          }
          val end = System.currentTimeMillis()
          println(s"Done proving $name")
          BenchmarkResult(name, if (proof.isProved) "proved" else "unfinished", timeout, end - start, proof.steps, TacticStatistics.size(theTactic), None)
        } catch {
          case ex: TestFailedDueToTimeoutException => BenchmarkResult(name, "timeout", timeout, -1, -1, -1, Some(ex))
          case ex => BenchmarkResult(name, "failed", timeout, -1, -1, -1, Some(ex))
        }
      case None =>
        println("Skipping " + name + " for lack of tactic")
        BenchmarkResult(name, "skipped", timeout, -1, -1, -1, None)
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

