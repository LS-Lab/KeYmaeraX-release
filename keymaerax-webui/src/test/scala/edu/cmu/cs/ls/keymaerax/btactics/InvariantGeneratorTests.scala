package edu.cmu.cs.ls.keymaerax.btactics

import java.io.PrintWriter

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.bellerophon.{SuccPosition, TacticStatistics}
import edu.cmu.cs.ls.keymaerax.btactics.InvariantGenerator.{AnnotationProofHint, GenProduct, PegasusProofHint, ProofHint}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.hydra.DatabasePopulator
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXArchiveParser, KeYmaeraXParser}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.{SlowTest, UsualTest}
import edu.cmu.cs.ls.keymaerax.tools.{PegasusM2KConverter, ToolOperationManagement}
import edu.cmu.cs.ls.keymaerax.btactics.NonlinearExamplesTests._
import org.scalatest.{AppendedClues, Suites}
import org.scalatest.LoneElement._
import org.scalatest.concurrent.Timeouts
import org.scalatest.exceptions.TestFailedDueToTimeoutException
import org.scalatest.prop.TableDrivenPropertyChecks._
import org.scalatest.time.{Seconds, Span}

import scala.collection.immutable
import scala.collection.immutable.{IndexedSeq, Map, Nil}

/**
 * Tests invariant generators.
 * [[edu.cmu.cs.ls.keymaerax.btactics.InvariantGenerator]].
 */
@UsualTest
class InvariantGeneratorTests extends TacticTestBase {

  "Loop invariants" should "be generated from pre and postconditions" in {
    InvariantGenerator.loopInvariantGenerator("x>=1 ==> [{x:=x+1;}*][x:=x+1;]x>=2".asSequent, SuccPos(0)).toList should
      contain theSameElementsAs(("[x:=x+1;]x>=2".asFormula, None) :: ("x>=1".asFormula, None) ::Nil)
  }

  "Differential invariant generator" should "use Pegasus lazily" in {
    //@note pegasusInvariantGenerator asks ToolProvider.invGenTool

    val mockProvider = new NoneToolProvider {
      var requestedInvGenerators: List[Option[String]] = Nil
      override def invGenTool(name: Option[String]): Option[InvGenTool] = {
        requestedInvGenerators = requestedInvGenerators :+ name
        super.invGenTool(name)
      }
    }

    ToolProvider.setProvider(mockProvider)

    val gen = InvariantGenerator.differentialInvariantGenerator("x>0 ==> [{x'=x^2&true}]x>=0".asSequent, SuccPos(0))
    mockProvider.requestedInvGenerators shouldBe 'empty
    gen should not be 'empty
    gen.head shouldBe ("x>0".asFormula, None)
  }

  it should "not fail if Mathematica is unavailable" in {
    val gen = InvariantGenerator.pegasusInvariants("x>0 ==> [{x'=x^2&true}]x>=0".asSequent, SuccPos(0))
    gen shouldBe 'empty
  }

  it should "use Pegasus if available" in withMathematica { _ =>
    val gen = InvariantGenerator.pegasusInvariants("x>0 ==> [{x'=x^2&true}]x>=0".asSequent, SuccPos(0))
    gen should not be 'empty
    gen.head shouldBe ("x>0".asFormula, Some(PegasusProofHint(isInvariant = true, None)))
  }

  it should "split formulas correctly" in {
    FormulaTools.leftConjuncts("(1=1&2=2)&3=3".asFormula, 1) should contain theSameElementsInOrderAs
      "(1=1&2=2)&3=3".asFormula :: Nil
    FormulaTools.leftConjuncts("(1=1&2=2)&3=3".asFormula, 2) should contain theSameElementsInOrderAs
      "1=1&2=2".asFormula :: "3=3".asFormula :: Nil
    FormulaTools.leftConjuncts("(1=1&2=2)&3=3".asFormula, 3) should contain theSameElementsInOrderAs
      "1=1".asFormula :: "2=2".asFormula :: "3=3".asFormula :: Nil
    FormulaTools.leftConjuncts("(1=1&2=2)&3=3".asFormula, -1) should contain theSameElementsInOrderAs
      "1=1".asFormula :: "2=2".asFormula :: "3=3".asFormula :: Nil
  }

  it should "not generate duplicate invariants" in {
    val s = "x>=0&x<=H(), g()>0, 1>=c(), c()>=0, x>=0&x=H()&v=0&g()>0&1>=c()&c()>=0 ==> [{x'=v,v'=-g()&x>=0}]((x=0->x>=0&x<=H())&(x!=0->x>=0&x<=H()))".asSequent
    InvariantGenerator.defaultInvariantGenerator(s, SuccPos(0)).toList.loneElement shouldBe ("v=0".asFormula, None)
  }

  it should "provide conjunctive candidates on diffcut chains with strict or mixed inequalities" in {
    //@note replaces Pegasus with mock provider
    val mockProvider = new NoneToolProvider {
      var requestedInvGenerators: List[Option[String]] = Nil
      override def invGenTool(name: Option[String]): Option[InvGenTool] = {
        requestedInvGenerators = requestedInvGenerators :+ name
        Some(new InvGenTool {
          override def invgen(ode: ODESystem, assumptions: immutable.Seq[Formula], postCond: Formula): immutable.Seq[Either[immutable.Seq[(Formula, String)], immutable.Seq[(Formula, String)]]] = {
            Left(("x>0".asFormula, "Unknown") :: ("y>1".asFormula, "Unknown") :: Nil) :: Nil
          }
          override def lzzCheck(ode: ODESystem, inv: Formula): Boolean = ???
          override def refuteODE(ode: ODESystem, assumptions: immutable.Seq[Formula], postCond: Formula): Option[Map[NamedSymbol, Expression]] = ???
        })
      }
    }
    ToolProvider.setProvider(mockProvider)

    val gen = InvariantGenerator.pegasusCandidates("x>0 & y>1 ==> [{x'=1, y'=1}]x + y > 1".asSequent, SuccPos(0))
    gen.toList should contain theSameElementsInOrderAs ("x>0".asFormula, Some(PegasusProofHint(isInvariant=true, None))) ::
      ("y>1".asFormula, Some(PegasusProofHint(isInvariant=true, None))) ::
      ("x>0&y>1".asFormula, Some(PegasusProofHint(isInvariant=false, None))) :: Nil
  }

  "Auto with invariant generator" should "prove simple loop from precondition invariant" in withQE { _ =>
    proveBy("x=0 -> [{x:=-x;}*]x>=0".asFormula, auto) shouldBe 'proved
  }

  it should "prove simple loop from postcondition invariant" in withQE { _ =>
    proveBy("x=1 -> [{x:=x+1;}*]x>=1".asFormula, auto) shouldBe 'proved
  }

  "Configurable generator" should "return annotated conditional invariants" in withQE { _ =>
    val fml = "y>0 ==> [{x:=2; ++ x:=-2;}{{y'=x*y}@invariant((y'=2*y -> y>=old(y)), (y'=-2*y -> y<=old(y)))}]y>0".asSequent
    TactixLibrary.invGenerator("==> [{y'=2*y&true}]y>0".asSequent, SuccPosition(1)).loneElement shouldBe ("y>=old(y)".asFormula, Some(AnnotationProofHint(tryHard = true)))
    TactixLibrary.invGenerator("==> [{y'=-2*y&true}]y>0".asSequent, SuccPosition(1)).loneElement shouldBe ("y<=old(y)".asFormula, Some(AnnotationProofHint(tryHard = true)))
  }

  "Pegasus" should "return invariant postcondition if sanity timeout > 0" in withMathematica { _ =>
    val seq = "x^2+y^2=2 ==> [{x'=-x,y'=-y}]x^2+y^2<=2".asSequent
    withTemporaryConfig(Map(Configuration.Keys.PEGASUS_SANITY_TIMEOUT -> "0")) {
      InvariantGenerator.pegasusInvariants(seq, SuccPosition(1)).toList should contain theSameElementsInOrderAs Nil
    }
    withTemporaryConfig(Map(Configuration.Keys.PEGASUS_SANITY_TIMEOUT -> "5")) {
      InvariantGenerator.pegasusInvariants(seq, SuccPosition(1)).toList should contain theSameElementsInOrderAs ("2+-1*x^2+-1*y^2>=0".asFormula -> PegasusProofHint(isInvariant = true, None)) :: Nil
    }
  }

}

object NonlinearExamplesTests {
  private val GITHUB_PROJECTS_RAW_PATH = "file:/Users/smitsch/Documents/projects/keymaera/documents/Papers/pegasus_paper"
}

@SlowTest
class NonlinearExamplesTests extends Suites(
  new NonlinearExamplesTester("Nonlinear", s"$GITHUB_PROJECTS_RAW_PATH/benchmarks/nonlinear.kyx", 300, genCheck=true)
//  new NonlinearExamplesTester("Invariant", s"$GITHUB_PROJECTS_RAW_PATH/benchmarks/invariant.kyx", 300, genCheck=true)
)

@SlowTest
class NonlinearExamplesTester(val benchmarkName: String, val url: String, val timeout: Int,
                              val genCheck: Boolean) extends TacticTestBase with AppendedClues with Timeouts {

  private val entries = {
    println("Reading " + url)
    try {
      DatabasePopulator.readKya(url)
    } catch {
      case ex: Throwable =>
        println("Failed reading: " + ex.getMessage)
        ex.printStackTrace()
        Nil
    }
  }

  private def tableResults(results: Seq[BenchmarkResult]) = {
    Table(("Benchmark name", "Entry name", "Status", "Duration", "Failure Cause"),
      results.map(r => (benchmarkName, r.name, r.status, r.totalDuration, r.ex)):_*)
  }

  private def setTimeouts(tool: ToolOperationManagement)(testcode: => Any): Unit = {
    withTemporaryConfig(Map(
      Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true",
      Configuration.Keys.ODE_TIMEOUT_FINALQE -> "120",
      Configuration.Keys.PEGASUS_INVGEN_TIMEOUT -> "120",
      Configuration.Keys.PEGASUS_INVCHECK_TIMEOUT ->"60",
      Configuration.Keys.LOG_QE_DURATION -> "true")) {
      tool.setOperationTimeout(120)
      testcode
    }
  }

  private val infoPrinter = (info: Any) => info match {
    case i: Map[String, Any] => i.values.mkString(",")
  }

  it should "generate invariants" in withMathematica { tool => setTimeouts(tool) {
    val results = entries.map(e => runInvGen(e.name, e.model))
    val writer = new PrintWriter(benchmarkName + "_invgen_saturate_proofhints.csv")
    writer.write(
      "Name,Status,Timeout[min],Duration total[ms],Duration QE[ms],Duration gen[ms],Duration check[ms],Proof Steps,Tactic Size,Info\r\n" + results.map(_.toCsv(infoPrinter)).mkString("\r\n"))
    writer.close()
  }
  }

  it should "generate invariants with Barrier only" ignore withMathematica { tool => setTimeouts(tool) {
    withTemporaryConfig(Map(Configuration.Keys.PEGASUS_MAIN_FILE -> "Pegasus_BarrierOnly.m")) {
      val results = entries.map(e => runInvGen(e.name, e.model))
      val writer = new PrintWriter(benchmarkName + "_invgen_barrier_proofhints.csv")
      writer.write(
        "Name,Status,Timeout[min],Duration total[ms],Duration QE[ms],Duration gen[ms],Duration check[ms],Proof Steps,Tactic Size,Info\r\n" + results.map(_.toCsv(infoPrinter)).mkString("\r\n"))
      writer.close()
    }
  }
  }

  it should "generate invariants with Darboux only" ignore withMathematica { tool => setTimeouts(tool) {
    withTemporaryConfig(Map(Configuration.Keys.PEGASUS_MAIN_FILE -> "Pegasus_DbxOnly.m")) {
      val results = entries.map(e => runInvGen(e.name, e.model))
      val writer = new PrintWriter(benchmarkName + "_invgen_dbx_proofhints.csv")
      writer.write(
        "Name,Status,Timeout[min],Duration total[ms],Duration QE[ms],Duration gen[ms],Duration check[ms],Proof Steps,Tactic Size,Info\r\n" + results.map(_.toCsv(infoPrinter)).mkString("\r\n"))
      writer.close()
    }
  }
  }

  it should "generate invariants with summands only" ignore withMathematica { tool => setTimeouts(tool) {
    withTemporaryConfig(Map(Configuration.Keys.PEGASUS_MAIN_FILE -> "Pegasus_SummandsOnly.m")) {
      val results = entries.map(e => runInvGen(e.name, e.model))
      val writer = new PrintWriter(benchmarkName + "_invgen_summands_proofhints.csv")
      writer.write(
        "Name,Status,Timeout[min],Duration total[ms],Duration QE[ms],Duration gen[ms],Duration check[ms],Proof Steps,Tactic Size,Info\r\n" + results.map(_.toCsv(infoPrinter)).mkString("\r\n"))
      writer.close()
    }
  }
  }

  it should "generate invariants with first integrals only" ignore withMathematica { tool => setTimeouts(tool) {
    withTemporaryConfig(Map(Configuration.Keys.PEGASUS_MAIN_FILE ->"Pegasus_FIOnly.m")) {
      val results = entries.map(e => runInvGen(e.name, e.model))
      val writer = new PrintWriter(benchmarkName + "_invgen_firstintegrals_proofhints.csv")
      writer.write(
        "Name,Status,Timeout[min],Duration total[ms],Duration QE[ms],Duration gen[ms],Duration check[ms],Proof Steps,Tactic Size,Info\r\n" + results.map(_.toCsv(infoPrinter)).mkString("\r\n"))
      writer.close()
    }
  }
  }

  private def pegasusGen(name: String, model: Formula) = {
    model match {
      case Imply(ante, succ@Box(_: ODESystem, _)) =>
        val seq = Sequent(IndexedSeq(ante), IndexedSeq(succ))
        println(s"Generating invariants $name")
        val invGenStart = System.currentTimeMillis()
        val candidates = InvariantGenerator.pegasusCandidates(seq, SuccPos(0)).toList
        val invGenEnd = System.currentTimeMillis()
        println(s"Done generating (${candidates.map(c => c._1.prettyString + " (proof hint " + c._2 + ")").mkString(",")}) $name")
        Some((candidates, invGenStart, invGenEnd))
      case _ => None
    }
  }

  private def runCheckCandidates(name: String, modelContent: String, tactic: Option[String], candidates: List[(Formula, Option[ProofHint])]): BenchmarkResult = {
    beforeEach()
    withMathematica(_ => {}) //@HACK beforeEach and afterEach clean up tool provider
    qeDurationListener.reset()
    if (candidates.nonEmpty) {
      println(s"Checking $name with candidates " + candidates.mkString(","))
      val (model, _) = parseStripHints(modelContent)
      TactixLibrary.invGenerator = FixedGenerator(candidates)
      TactixLibrary.differentialInvGenerator = FixedGenerator(candidates)
      val start = System.currentTimeMillis()
      try {
        val proof = failAfter(Span(timeout, Seconds))({
          proveBy(model, TactixLibrary.master())
        })((testThread: Thread) => {
          theInterpreter.kill()
          testThread.interrupt()
        })
        val end = System.currentTimeMillis()
        println(s"Done checking $name " + (if (proof.isProved) "(proved)" else "(unfinished)"))
        val result =
          if (proof.isProved) "proved"
          else if (proof.subgoals.exists(s => s.ante.isEmpty && s.succ.size == 1 && s.succ.head == False)) "disproved"
          else "unfinished"
        BenchmarkResult(name, result, timeout, end-start, qeDurationListener.duration, 0, end-start, proof.steps, 1, None)
      } catch {
        case ex: TestFailedDueToTimeoutException =>
          println(s"Timeout checking $name")
          BenchmarkResult(name, "timeout", timeout, -1, -1, -1, -1, -1, -1, Some(ex))
      }
    } else if (tactic.isDefined) {
      println(s"Checking $name with tactic script")
      val (model, defs) = parseStripHints(modelContent)
      val t = BelleParser.parseWithInvGen(tactic.get, None, defs)
      val start = System.currentTimeMillis()
      try {
        val proof = failAfter(Span(timeout, Seconds))({
          proveBy(model, t)
        })((testThread: Thread) => {
          theInterpreter.kill()
          testThread.interrupt()
        })
        val end = System.currentTimeMillis()
        println(s"Done checking $name " + (if (proof.isProved) "(proved)" else "(unfinished)"))
        val result =
          if (proof.isProved) "proved"
          else if (proof.subgoals.exists(s => s.ante.isEmpty && s.succ.size == 1 && s.succ.head == False)) "disproved"
          else "unfinished"
        BenchmarkResult(name, result, timeout, end - start, qeDurationListener.duration, 0, end - start, proof.steps,
          TacticStatistics.size(t), None)
      } catch {
        case ex: TestFailedDueToTimeoutException =>
          println(s"Timeout checking $name")
          BenchmarkResult(name, "timeout", timeout, -1, -1, -1, -1, -1, -1, Some(ex))
      }
    } else {
      BenchmarkResult(name, "skipped", timeout, -1, -1, -1, -1, -1, -1, None)
    }
  }

  private def runInvGen(name: String, modelContent: String) = {
    if (genCheck) {
      beforeEach()
      withMathematica(_ => {}) //@HACK beforeEach and afterEach clean up tool provider
      qeDurationListener.reset()
      val (model, _) = parseStripHints(modelContent)

      try {
        pegasusGen(name, model) match {
          case Some((candidates, invGenStart, invGenEnd)) =>
            if (candidates.nonEmpty) {
              println(s"Checking $name with candidates " + candidates.map(_._1.prettyString).mkString(","))
              TactixLibrary.invGenerator = FixedGenerator(candidates)
              TactixLibrary.differentialInvGenerator = FixedGenerator(candidates)
              val checkStart = System.currentTimeMillis()
              //val proof = proveBy(seq, TactixLibrary.master())
              try {
                val proof = failAfter(Span(timeout, Seconds))({
                  proveBy(model, TactixLibrary.master())
                })((testThread: Thread) => {
                  theInterpreter.kill()
                  testThread.interrupt()
                })

                val checkEnd = System.currentTimeMillis()
                println(s"Done checking $name " + (if (proof.isProved) "(proved)" else "(unfinished)"))

                val result =
                  if (proof.isProved) "proved"
                  else if (proof.subgoals.exists(s => s.ante.isEmpty && s.succ.size == 1 && s.succ.head == False)) "disproved"
                  else "unfinished"
                BenchmarkResult(name, result, timeout, checkEnd - invGenStart,
                  qeDurationListener.duration, invGenEnd - invGenStart, checkEnd - checkStart, proof.steps, 1, None,
                  Map("dchainlength" -> (candidates.length-1)))
              } catch {
                case ex: TestFailedDueToTimeoutException =>
                  println(s"Timeout checking $name")
                  BenchmarkResult(name, "timeout", timeout, -1, -1, -1, -1, -1, -1, Some(ex))
              }
            } else {
              BenchmarkResult(name, "unfinished (gen)", timeout, invGenEnd - invGenStart, invGenEnd - invGenStart, -1, -1, 0, 1, None)
            }
          case None =>
            println("Skipping " + name + " for unknown shape, expected A -> [{x'=f(x)}]p(x), but got " + model.prettyString)
            BenchmarkResult(name, "skipped", timeout, -1, -1, -1, -1, -1, -1, None)
        }
      } catch {
        case ex: TestFailedDueToTimeoutException => BenchmarkResult(name, "timeout", timeout,
          -1, qeDurationListener.duration, -1, -1, -1, -1, Some(ex))
        case ex => BenchmarkResult(name, "failed", timeout, -1, qeDurationListener.duration, -1, -1, -1, -1, Some(ex))
      }
    } else {
      BenchmarkResult(name, "skipped", timeout, -1, -1, -1, -1, -1, -1, None)
    }
  }

  /** Parse model but ignore all proof hints. */
  private def parseStripHints(modelContent: String): (Formula, KeYmaeraXArchiveParser.Declaration) = {
    TactixLibrary.invGenerator = FixedGenerator(Nil)
    TactixLibrary.differentialInvGenerator = FixedGenerator(Nil)
    KeYmaeraXParser.setAnnotationListener((_: Program, _: Formula) => {})
    val entry = KeYmaeraXArchiveParser(modelContent).head
    (entry.model.asInstanceOf[Formula], entry.defs)
  }

}
