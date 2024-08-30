/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon.TacticStatistics
import org.keymaerax.btactics.BenchmarkTests._
import org.keymaerax.core.{Box, False, Formula, Imply, ODESystem, Program, Sequent, SuccPos}
import org.keymaerax.hydra.DatabasePopulator
import org.keymaerax.hydra.DatabasePopulator.TutorialEntry
import org.keymaerax.parser._
import org.keymaerax.tags.ExtremeTest
import org.keymaerax.tools.ToolOperationManagement
import org.keymaerax.{Configuration, GlobalState}
import org.scalatest.exceptions.TestFailedDueToTimeoutException
import org.scalatest.prop.TableDrivenPropertyChecks._
import org.scalatest.time.{Seconds, Span}
import org.scalatest.{AppendedClues, Suites}

import java.io.PrintWriter
import scala.collection.immutable.{IndexedSeq, Map, Nil}
import scala.language.postfixOps
import scala.reflect.io.File

/**
 * Benchmarks.
 *
 * Created by smitsch on 4/26/18.
 */
class BenchmarkTests
    extends Suites(
      // benchmark problems from tactics and with database recording
//  new TutorialRegressionTester("Basic Benchmark", s"$GITHUB_PROJECTS_RAW_PATH/benchmarks/basic.kyx"),
//  new TutorialRegressionTester("Advanced Benchmark", s"$GITHUB_PROJECTS_RAW_PATH/benchmarks/advanced.kyx"),
//  new TutorialRegressionTester("Nonlinear Benchmark", s"$GITHUB_PROJECTS_RAW_PATH/benchmarks/nonlinear.kyx")
      // export
//  new BenchmarkExporter("Export", s"$GITHUB_PROJECTS_RAW_PATH/benchmarks/basic.kyx")
      // benchmark problems
      new BenchmarkTester("Basic", s"$GITHUB_PROJECTS_RAW_PATH/benchmarks/basic.kyx", 300, genCheck = false),
      new BenchmarkTester("Games", s"$GITHUB_PROJECTS_RAW_PATH/benchmarks/games.kyx", 300, genCheck = false),
//  new BenchmarkTester("Counterexamples", s"$GITHUB_PROJECTS_RAW_PATH/benchmarks/counterexample.kyx", 300, genCheck=false),
      new BenchmarkTester("Advanced", s"$GITHUB_PROJECTS_RAW_PATH/benchmarks/advanced.kyx", 1500, genCheck = false),
      new BenchmarkTester("Nonlinear", s"$GITHUB_PROJECTS_RAW_PATH/benchmarks/nonlinear.kyx", 300, genCheck = true),
    )

object BenchmarkTests {
//  private val GITHUB_PROJECTS_RAW_PATH = "https://raw.githubusercontent.com/LS-Lab/KeYmaeraX-projects/master"
  // for testing changes in a locally cloned repository
  private val GITHUB_PROJECTS_RAW_PATH = "classpath:/keymaerax-projects"
}

/** Collects a benchmark result. */
case class BenchmarkResult(
    name: String,
    status: String,
    timeout: Int,
    totalDuration: Long,
    qeDuration: Long,
    invGenDuration: Long,
    invCheckDuration: Long,
    proofSteps: Int,
    tacticSize: Int,
    ex: Option[Throwable],
    info: Any = Map.empty,
) {
  override def toString: String = s"""Proof Statistics ($name $status, with time budget $timeout)
                                     |Duration [ms]: $totalDuration
                                     |QE [ms]: $qeDuration
                                     |Inv Gen[ms]: $invGenDuration
                                     |Inv Check[ms]: $invCheckDuration
                                     |Proof steps: $proofSteps
                                     |Tactic size: $tacticSize
    """.stripMargin

  def toCsv(infoPrinter: Any => String = (_: Any) => ""): String =
    s"$name,$status,$timeout,$totalDuration,$qeDuration,$invGenDuration,$invCheckDuration,$proofSteps,$tacticSize" +
      infoPrinter(info)
}

/** Exports to different formats */
class BenchmarkExporter(val benchmarkName: String, val url: String) extends TacticTestBase {

  private val EXPORT_DIR = "export" + File.separator

  private val content = DatabasePopulator.loadResource(url)

  it should "export KeYmaera X legacy format" ignore withTactics {
    val entries = ArchiveParser.parse(content, parseTactics = false)
    val printer = new KeYmaeraXLegacyArchivePrinter()
    val printedContent = entries.map(printer(_)).mkString("\n\n")

    // @todo tactic legacy format (so far only id -> closeId renamed manually after export)
    val archive = File(EXPORT_DIR + "legacy")
    archive.createDirectory()
    val pw = (archive / File(url.substring(url.lastIndexOf("/") + 1))).printWriter()
    pw.write(printedContent)
    pw.close()
  }

  it should "export KeYmaera X stripped" ignore withTactics {
    def stripEntry(e: ParsedArchiveEntry): ParsedArchiveEntry = e
      .copy(defs = Declaration(Map.empty), tactics = Nil, annotations = Nil)

    val entries = ArchiveParser.parse(content, parseTactics = false)
    val printer = new KeYmaeraXArchivePrinter(PrettierPrintFormatProvider(_, 80))
    val printedStrippedContent = entries.map(stripEntry).map(printer(_)).mkString("\n\n")

    val archive = File(EXPORT_DIR + "stripped" + url.substring(url.lastIndexOf("/") + 1))
    archive.createDirectory()
    val pws = archive.printWriter()
    pws.write(printedStrippedContent)
    pws.close()
  }

  it should "export KeYmaera 3 format" in withTactics {
    val printer = KeYmaera3PrettyPrinter
    val entries = ArchiveParser.parse(content, parseTactics = false)
    val printedEntries = entries.map(e =>
      e.name.replaceAll("[ :\\/\\(\\)]", "_") ->
        (try { printer.printFile(e.model.asInstanceOf[Formula]) }
        catch {
          case ex: Throwable =>
            ex.printStackTrace()
            ""
        })
    )

    val archive = File(EXPORT_DIR + url.substring(url.lastIndexOf("/") + 1))
    archive.createDirectory()
    printedEntries.foreach(e => {
      // replace special characters in file name
      val pw = (archive / File(e._1 + ".key")).printWriter()
      pw.write(e._2)
      pw.close()
    })
  }

}

@ExtremeTest(timeout = 6)
class BenchmarkTester(val benchmarkName: String, val url: String, val timeout: Int, val genCheck: Boolean)
    extends TacticTestBase with AppendedClues {

  private lazy val entries = {
    try { DatabasePopulator.readKyx(url) }
    catch {
      case ex: Throwable =>
        ex.printStackTrace()
        Nil
    }
  }

  private def tableResults(results: Seq[BenchmarkResult]) = {
    Table(
      ("Benchmark name", "Entry name", "Status", "Duration", "Failure Cause"),
      results.map(r => (benchmarkName, r.name, r.status, r.totalDuration, r.ex)): _*
    )
  }

  private def setTimeouts(tool: ToolOperationManagement)(testcode: => Any): Unit = {
    withTemporaryConfig(Map(
      Configuration.Keys.MATHEMATICA_QE_METHOD -> "Reduce",
      Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true",
      Configuration.Keys.ODE_TIMEOUT_FINALQE -> "120",
      Configuration.Keys.Pegasus.INVGEN_TIMEOUT -> "180",
      Configuration.Keys.Pegasus.INVCHECK_TIMEOUT -> "20", // 60
      Configuration.Keys.LOG_QE_DURATION -> "true",
    )) {
      tool.setOperationTimeout(120)
      testcode
    }
  }

  it should "print benchmark index files" ignore withMathematica { _ =>
    val fileName = "./kyx/" + url.substring(url.lastIndexOf("/") + 1)
    println(entries.map(e => fileName + "#" + e.name + ";" + timeout + ";0").mkString("\n"))
  }

  it should "prove interactive benchmarks" in withMathematica { tool =>
    setTimeouts(tool) {
      val results = entries.map(e =>
        runInteractive(
          e.name,
          e.model,
          e.tactic.headOption.map(_._2),
          () => {
            // @note connect to mathematica over TCPIP for better control over shutting down kernel
            withTemporaryConfig(Map(Configuration.Keys.MATH_LINK_TCPIP -> "true")) {
              withMathematicaMatlab(_ => {}) // @HACK beforeEach and afterEach clean up tool provider
            }
          },
        )
      )
      val writer = new PrintWriter(benchmarkName + "_interactive.csv")
      writer.write(
        "Name,Status,Timeout[min],Duration[ms],Proof Steps,Tactic Size\r\n" + results.map(_.toCsv()).mkString("\r\n")
      )
      writer.close()
      forEvery(tableResults(results)) { (_, _, status, _, cause) =>
        status should (be("proved") withClue cause or be("skipped"))
      }
    }
  }

  it should "generate invariants" in withMathematica({ tool =>
    setTimeouts(tool) {
      def expectedProved(entry: TutorialEntry) = entry.tactic.map(_._1.trim()).contains("Automated proof")
      val results = entries.map(e => runInvGen(e.name, e.model, expectedProved(e)))
      val writer = new PrintWriter(benchmarkName + "_invgen.csv")
      writer.write(
        "Name,Status,Timeout[min],Duration total[ms],Duration gen[ms],Duration check[ms],Proof Steps,Tactic Size\r\n" +
          results.map(_.toCsv()).mkString("\r\n")
      )
      writer.close()
      if (genCheck) {
        forEvery(tableResults(results)) { (_, name, status, _, cause) =>
          if (expectedProved(entries.find(_.name == name).get)) status shouldBe "proved" withClue cause
          else if (status == "proved") fail("Learned how to prove " + name + "; add automated tactic to benchmark")
        }
      }
    }
  })

  it should "prove interactive benchmarks with Z3" in withZ3 { _ =>
    val results = entries
      .map(e => runInteractive(e.name, e.model, e.tactic.headOption.map(_._2), () => withZ3(_ => {})))
    val writer = new PrintWriter(benchmarkName + "_interactive_z3.csv")
    writer.write(
      "Name,Status,Timeout[min],Duration[ms],Proof Steps,Tactic Size\r\n" + results.map(_.toCsv()).mkString("\r\n")
    )
    writer.close()
    forEvery(tableResults(results)) { (_, _, status, _, cause) =>
      status should (be("proved") withClue cause or be("skipped"))
    }
  }

  private def runWithHints(filter: TutorialEntry => Boolean, check: (String, String) => Unit): Unit = {
    val results = entries
      .filter(filter)
      .map(e =>
        runWithHints(
          e.name,
          e.model,
          () => {
            // @note connect to mathematica over TCPIP for better control over shutting down kernel
            withTemporaryConfig(Map(Configuration.Keys.MATH_LINK_TCPIP -> "true")) {
              withMathematicaMatlab(_ => {}) // @HACK beforeEach and afterEach clean up tool provider
            }
          },
        )
      )
    val writer = new PrintWriter(benchmarkName + "_withhints.csv")
    writer.write(
      "Name,Status,Timeout[min],Duration total[ms],Duration QE[ms],Duration gen[ms],Duration check[ms],Proof Steps,Tactic Size\r\n" +
        results.map(_.toCsv()).mkString("\r\n")
    )
    writer.close()
    forEvery(tableResults(results)) { (_, name, status, _, cause) =>
      cause match {
        case Some(c) => throw c
        case None => check(name, status)
      }
    }
  }

  it should "prove benchmarks with proof hints and Mathematica" in withMathematica { tool =>
    setTimeouts(tool) {
      runWithHints(
        _.tactic
          .exists(_._2.trim match {
            case "auto" | "autoClose" | "master" => true
            case _ => false
          }),
        (_: String, status: String) => status shouldBe "proved",
      )
    }
  }

  it should "try unmarked benchmarks with proof hints and Mathematica" ignore withMathematica { tool =>
    setTimeouts(tool) {
      runWithHints(
        !_.tactic
          .exists(_._2.trim match {
            case "auto" | "autoClose" | "master" => true
            case _ => false
          }),
        (name: String, status: String) =>
          if (status == "proved") fail("Learned how to prove " + name + "; add automated tactic to benchmark"),
      )
    }
  }

//  it should "prove benchmarks with proof hints and in Z3" in withZ3 { tool =>
//    setTimeouts(tool)
//    forEvery (entries) { (_, name, modelContent, _) => runWithHints(name, modelContent) }
//  }

  private def runWithoutHints(filter: TutorialEntry => Boolean, check: (String, String) => Unit): Unit = {
    val results = entries
      .filter(filter)
      .map(e =>
        runAuto(
          e.name,
          e.model,
          () => {
            // @note connect to mathematica over TCPIP for better control over shutting down kernel
            withTemporaryConfig(Map(Configuration.Keys.MATH_LINK_TCPIP -> "true")) {
              withMathematicaMatlab(_ => {}) // @HACK beforeEach and afterEach clean up tool provider
            }
          },
        )
      )
    val writer = new PrintWriter(benchmarkName + "_auto.csv")
    writer.write(
      "Name,Status,Timeout[min],Duration total[ms],Duration QE[ms],Duration gen[ms],Duration check[ms],Proof Steps,Tactic Size\r\n" +
        results.map(_.toCsv()).mkString("\r\n")
    )
    writer.close()
    forEvery(tableResults(results)) { (_, name, status, _, cause) =>
      if (cause.isDefined) throw cause.get else check(name, status)
    }
  }

  it should "prove benchmarks without proof hints and in Mathematica" in withMathematica({ tool =>
    setTimeouts(tool) {
      runWithoutHints(
        _.tactic.exists(_._1.trim() == "Automated proof"),
        (_: String, status: String) => status shouldBe "proved",
      )
    }
  })

  it should "try all benchmarks without proof hints and in Mathematica" ignore withMathematica { tool =>
    setTimeouts(tool) {
      runWithoutHints(
        !_.tactic
          .exists(_._2 match {
            case "auto" | "autoClose" | "master" => true
            case _ => false
          }),
        (name: String, status: String) =>
          if (status == "proved") fail("Learned how to prove " + name + "; add automated tactic to benchmark"),
      )
    }
  }

//  it should "prove benchmarks without proof hints and in Z3" in withZ3 { tool =>
//    setTimeouts(tool)
//    forEvery (entries) { (_, name, modelContent, _) => runAuto(name, modelContent) }
//  }

  private def runInteractive(name: String, modelContent: String, tactic: Option[String], initToolProvider: () => Unit) =
    runEntry(
      name,
      modelContent,
      parseStripHints,
      tactic.map(_.trim) match {
        case Some("master") => None
        case Some("auto") => None
        case Some("autoClose") => None
        case t => t
      },
      initToolProvider,
    )
  private def runWithHints(name: String, modelContent: String, initToolProvider: () => Unit) =
    runEntry(name, modelContent, parseWithHints, Some("autoClose"), initToolProvider)
  private def runAuto(name: String, modelContent: String, initToolProvider: () => Unit) =
    runEntry(name, modelContent, parseStripHints, Some("autoClose"), initToolProvider)

  private def runInvGen(name: String, modelContent: String, expectedProved: Boolean) = {
    if (genCheck) {
      beforeEach()
      withMathematica(_ => {}) // @HACK beforeEach and afterEach clean up tool provider
      val (model, defs) = parseStripHints(modelContent)

      try {
        val Imply(ante, succ) = defs.exhaustiveSubst(model)
        succ match {
          case Box(_: ODESystem, _) =>
            val seq = Sequent(IndexedSeq(ante), IndexedSeq(succ))
            println(s"Generating invariants $name")
            val invGenStart = System.currentTimeMillis()
            val candidates = InvariantGenerator.pegasusCandidates.generate(seq, SuccPos(0), defs).toList
            val invGenEnd = System.currentTimeMillis()
            println(s"Done generating (${invGenEnd - invGenStart}ms: ${candidates
                .map(c => c.formula.prettyString + " (proof hint " + c.hint + ")")
                .mkString(",")}) $name")
            if (candidates.nonEmpty) {
              println(s"Checking $name with candidates " + candidates.map(_.formula.prettyString).mkString(","))
              // @note invSupplier is expected to a diff-cut chain and fails if they are not provable in exactly the presented order;
              // a generator can provide candidates, unprovable candidates are skipped
              TactixInit.invSupplier = FixedGenerator(Nil)
              TactixInit.differentialInvGenerator = FixedGenerator(candidates)
              val checkStart = System.currentTimeMillis()
              val proof = proveBy(seq, TactixLibrary.autoClose)
              val checkEnd = System.currentTimeMillis()
              println(
                s"Done checking $name (" + (checkEnd - checkStart) + "ms: " +
                  (if (proof.isProved) "proved)" else "unfinished)")
              )

              val result =
                if (proof.isProved) "proved"
                else if (proof.subgoals.exists(s => s.ante.isEmpty && s.succ.size == 1 && s.succ.head == False))
                  "disproved"
                else "unfinished"
              BenchmarkResult(
                name,
                result,
                timeout,
                checkEnd - invGenStart,
                qeDurationListener.duration,
                invGenEnd - invGenStart,
                checkEnd - checkStart,
                proof.steps,
                1,
                None,
              )
            } else {
              BenchmarkResult(
                name,
                "unfinished (gen)",
                timeout,
                invGenEnd - invGenStart,
                invGenEnd - invGenStart,
                -1,
                -1,
                0,
                1,
                None,
              )
            }
          case _ =>
            println("Skipping " + name + " for unknown shape, expected [{x'=f(x)}]p(x), but got " + ante.prettyString)
            BenchmarkResult(name, "skipped", timeout, -1, -1, -1, -1, -1, -1, None)
        }
      } catch {
        case ex: TestFailedDueToTimeoutException =>
          println(s"Done $name (failed: timeout)")
          BenchmarkResult(name, "timeout", timeout, -1, qeDurationListener.duration, -1, -1, -1, -1, Some(ex))
        case ex: Throwable =>
          if (expectedProved) println(s"Done $name (failed)")
          else println(s"Done $name (feature request: not generated and/or not proved)")
          BenchmarkResult(name, "failed", timeout, -1, qeDurationListener.duration, -1, -1, -1, -1, Some(ex))
      }
    } else { BenchmarkResult(name, "skipped", timeout, -1, -1, -1, -1, -1, -1, None) }
  }

  private def runEntry(
      name: String,
      modelContent: String,
      modelParser: String => (Formula, Declaration),
      tactic: Option[String],
      initToolProvider: () => Unit,
  ): BenchmarkResult = {
    beforeEach()
    initToolProvider()
    val (model, defs) = modelParser(modelContent)
    val result = tactic match {
      case Some(t) =>
        println(s"Proving $name")

        val theTactic = ArchiveParser.tacticParser(t, defs)

        qeDurationListener.reset()
        val start = System.currentTimeMillis()
        try {
          val proof =
            failAfter(Span(timeout, Seconds))({ proveBy(model, theTactic, defs = defs) })((testThread: Thread) => {
              theInterpreter.kill()
              testThread.interrupt()
            })
          val end = System.currentTimeMillis()
          val result =
            if (proof.isProved) "proved"
            else if (proof.subgoals.exists(s => s.ante.isEmpty && s.succ.size == 1 && s.succ.head == False)) "disproved"
            else "unfinished"
          println(s"Done proving $name: " + result + " in " + (end - start) + "ms")
          BenchmarkResult(
            name,
            result,
            timeout,
            end - start,
            qeDurationListener.duration,
            -1,
            -1,
            proof.steps,
            TacticStatistics.size(theTactic),
            None,
          )
        } catch {
          case ex: TestFailedDueToTimeoutException =>
            BenchmarkResult(name, "timeout", timeout, -1, qeDurationListener.duration, -1, -1, -1, -1, Some(ex))
          case ex: Throwable =>
            ex.printStackTrace()
            BenchmarkResult(name, "failed", timeout, -1, qeDurationListener.duration, -1, -1, -1, -1, Some(ex))
        }
      case None =>
        println("Skipping " + name + " for lack of tactic")
        BenchmarkResult(name, "skipped", timeout, -1, -1, -1, -1, -1, -1, None)
    }
    afterEach()
    result
  }

  /** Parse model and add proof hint annotations to invariant generator. */
  private def parseWithHints(modelContent: String): (Formula, Declaration) = {
    TactixInit.invSupplier = FixedGenerator(Nil)
    val generator = new ConfigurableGenerator()
    GlobalState
      .parser
      .setAnnotationListener((p: Program, inv: Formula) =>
        generator.products += (p -> (generator.products.getOrElse(p, Nil) :+ Invariant(inv)))
      )
    val entry = ArchiveParser.parser(modelContent).head
    TactixInit.invSupplier = generator
    TactixInit.differentialInvGenerator = FixedGenerator(Nil)
    TactixInit.loopInvGenerator = FixedGenerator(Nil)
    GlobalState
      .parser
      .setAnnotationListener((_: Program, _: Formula) => {}) // @note cleanup for separation between tutorial entries
    (entry.model.asInstanceOf[Formula], entry.defs)
  }

  /** Parse model but ignore all proof hints. */
  private def parseStripHints(modelContent: String): (Formula, Declaration) = {
    TactixInit.invSupplier = FixedGenerator(Nil)
    TactixInit.differentialInvGenerator = InvariantGenerator.cached(InvariantGenerator.differentialInvariantGenerator)
    TactixInit.loopInvGenerator = InvariantGenerator.cached(InvariantGenerator.loopInvariantGenerator)
    GlobalState.parser.setAnnotationListener((_: Program, _: Formula) => {})
    val entry = ArchiveParser.parser(modelContent).head
    (entry.model.asInstanceOf[Formula], entry.defs)
  }

}
