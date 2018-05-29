package edu.cmu.cs.ls.keymaerax.btactics

import java.io.File

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon.IOListeners.{QEFileLogListener, QELogListener, StopwatchListener}
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BellePrettyPrinter
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.hydra._
import edu.cmu.cs.ls.keymaerax.launcher.DefaultConfiguration
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXArchiveParser.ParsedArchiveEntry
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXArchiveParser, KeYmaeraXParser, KeYmaeraXPrettyPrinter}
import edu.cmu.cs.ls.keymaerax.pt.{ElidingProvable, ProvableSig}
import edu.cmu.cs.ls.keymaerax.tools._
import org.scalactic.{AbstractStringUniformity, Uniformity}
import org.scalatest._

import scala.collection.immutable._

/**
 * Base class for tactic tests.
 */
class TacticTestBase extends FlatSpec with Matchers with BeforeAndAfterEach with BeforeAndAfterAll with AppendedClues {
  protected def theInterpreter: Interpreter = BelleInterpreter.interpreter
  private var interpreters: List[Interpreter] = _

  class Lazy[T](f: => T) {
    private var option: Option[T] = None
    def apply(): T = option match {
      case Some(t) => t
      case None => val t = f; option = Some(t); t
    }
    def isInitialized: Boolean = option.isDefined
    def asOption: Option[T] = option
  }

  //@note Initialize once per test class, but only if requested in a withMathematica call
  private val mathematicaProvider = new Lazy(new MathematicaToolProvider(DefaultConfiguration.currentMathematicaConfig))
  //@note setup lazy in beforeEach, automatically initialize in withDatabase, tear down in afterEach if initialized
  private var dbTester: Lazy[TempDBTools] = _

  private val LOG_EARLIEST_QE = Configuration(Configuration.Keys.LOG_ALL_FO) == "true"
  private val LOG_QE = Configuration(Configuration.Keys.LOG_QE) == "true"
  private val LOG_QE_DURATION = Configuration(Configuration.Keys.LOG_QE_DURATION) == "true"
  private val LOG_QE_STDOUT = Configuration(Configuration.Keys.LOG_QE_STDOUT) == "true"

  protected val qeLogPath: String = Configuration.path(Configuration.Keys.QE_LOG_PATH)
  private val allPotentialQEListener = new QEFileLogListener(qeLogPath + "wantqe.txt", (p, _) => { p.subgoals.size == 1 && p.subgoals.head.isFOL })
  private val qeListener = new QEFileLogListener(qeLogPath + "haveqe.txt", (_, t) => t match { case DependentTactic("rcf") => true case _ => false })
  private val qeStdOutListener = new QELogListener((_: Sequent, g: Sequent, s: String) => println(s"$s: ${g.prettyString}"), (_, t) => t match { case DependentTactic("rcf") => true case _ => false })
  protected val qeDurationListener = new StopwatchListener((_, t) => t match {
    case DependentTactic("QE") => true
    case DependentTactic("smartQE") => true
    case _ => false
  })

  if (LOG_QE) println("QE log path: " + qeLogPath + " (enabled: " + LOG_QE + ")")

  /** For tests that want to record proofs in the database. */
  def withDatabase(testcode: TempDBTools => Any): Unit = testcode(dbTester())

  /**
   * Creates and initializes Mathematica for tests that want to use QE. Also necessary for tests that use derived
   * axioms that are proved by QE.
   * @example{{{
   *    "My test" should "prove something with Mathematica" in withMathematica { qeTool =>
   *      // ... your test code here
   *    }
   * }}}
   * */
  def withMathematica(testcode: Mathematica => Any, timeout: Int = -1) {
    val mathLinkTcp = System.getProperty("MATH_LINK_TCPIP", "true") // JVM parameter -DMATH_LINK_TCPIP=[true,false]
    Configuration.set("MATH_LINK_TCPIP", mathLinkTcp, saveToFile = false)
    val provider = mathematicaProvider() // new MathematicaToolProvider(DefaultConfiguration.currentMathematicaConfig)
    ToolProvider.setProvider(provider)
    //@todo timeout
    testcode(provider.tool())
  }

  /**
    * Creates and initializes Z3 for tests that want to use QE. Also necessary for tests that use derived
    * axioms that are proved by QE.
    * Note that Mathematica should also ne initialized in order to perform DiffSolution and CounterExample
    * @example{{{
    *    "My test" should "prove something with Z3" in withZ3 { qeTool =>
    *      // ... your test code here
    *    }
    * }}}
    * */
  def withZ3(testcode: Z3 => Any, timeout: Int = -1) {
    val provider = new Z3ToolProvider
    ToolProvider.setProvider(provider)
    provider.tool().setOperationTimeout(timeout)
    testcode(provider.tool())
  }

  /** Tests with both Mathematica and Z3 as QE tools. */
  def withQE(testcode: QETool => Any, timeout: Int = -1): Unit = {
    withClue("Mathematica") { withMathematica(testcode) }
    afterEach()
    beforeEach()
    withClue("Z3") { withZ3(testcode) }
  }

  /**
    * Creates and initializes Polya for tests that want to use QE. Also necessary for tests that use derived
    * axioms that are proved by QE.
    * Note that Mathematica should also ne initialized in order to perform DiffSolution and CounterExample
    * @example{{{
    *    "My test" should "prove something with Mathematica" in withPolya { implicit qeTool =>
    *      // ... your test code here
    *    }
    * }}}
    * */
  def withPolya(testcode: Polya => Any) {
    val provider = new PolyaToolProvider
    ToolProvider.setProvider(provider)
    testcode(provider.tool())
  }

  /** Test setup */
  override def beforeEach(): Unit = {
    interpreters = Nil
    val listeners =
      (if (LOG_QE) qeListener::Nil else Nil) ++
      (if (LOG_EARLIEST_QE) allPotentialQEListener::Nil else Nil) ++
      (if (LOG_QE_DURATION) qeDurationListener::Nil else Nil) ++
      (if (LOG_QE_STDOUT) qeStdOutListener::Nil else Nil)
    dbTester = new Lazy(new TempDBTools(listeners))
    BelleInterpreter.setInterpreter(registerInterpreter(LazySequentialInterpreter(listeners)))
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
    val generator = new ConfigurableGenerator[Formula]()
    KeYmaeraXParser.setAnnotationListener((p: Program, inv: Formula) =>
      generator.products += (p->(generator.products.getOrElse(p, Nil) :+ inv)))
    TactixLibrary.invGenerator = generator
    ToolProvider.setProvider(new NoneToolProvider())
  }

  /* Test teardown */
  override def afterEach(): Unit = {
    try {
      interpreters.foreach(i => try { i.kill() } catch { case ex: Throwable => ex.printStackTrace() })
      interpreters = Nil
    } finally {
      PrettyPrinter.setPrinter(e => e.getClass.getName)
      if (!mathematicaProvider.isInitialized) {
        //@note only shutdown non-Mathematica tool providers; Mathematica is shutdown in afterAll()
        ToolProvider.shutdown()
      }
      if (dbTester.isInitialized) {
        dbTester().db.session.close()
        dbTester = null
      }
      ToolProvider.setProvider(new NoneToolProvider())
      TactixLibrary.invGenerator = FixedGenerator(Nil)
    }
  }

  /* Test suite tear down */
  override def afterAll(): Unit = {
    //@note reduce number of zombie MathKernels: init and tear down Mathematica once per test class
    if (mathematicaProvider.isInitialized) {
      ToolProvider.shutdown()
      ToolProvider.setProvider(new NoneToolProvider())
      mathematicaProvider().shutdown()
    }
  }

  /** Registers an interpreter for cleanup after test. Returns the registered interpreter. */
  protected def registerInterpreter[T <: Interpreter](i: T): T = {
    interpreters = interpreters :+ i
    i
  }

  /** Proves a formula using the specified tactic. Fails the test when tactic fails.
    * @todo remove proveBy in favor of [[TactixLibrary.proveBy]] to avoid incompatibilities or meaingless tests if they do something else
    */
  //@deprecated("TactixLibrary.proveBy should probably be used instead of TacticTestBase")
  def proveBy(fml: Formula, tactic: BelleExpr, labelCheck: Option[List[BelleLabel]]=>Unit = _ => {}): ProvableSig = {
    val v = BelleProvable(ProvableSig.startProof(fml))
    theInterpreter(tactic, v) match {
      case BelleProvable(provable, labels) =>
        provable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(fml))
        labelCheck(labels)
        provable
      case r => fail("Unexpected tactic result " + r)
    }
  }

  /** Proves a sequent using the specified tactic. Fails the test when tactic fails. */
  //@deprecated("TactixLibrary.proveBy should probably be used instead of TacticTestBase")
  def proveBy(s: Sequent, tactic: BelleExpr): ProvableSig = {
    val v = BelleProvable(ProvableSig.startProof(s))
    theInterpreter(tactic, v) match {
      case BelleProvable(provable, _) => provable
      case r => fail("Unexpected tactic result " + r)
    }
  }

  def proveBy(p: Provable, tactic: BelleExpr): ProvableSig = {
    val v = BelleProvable(ElidingProvable(p))
    theInterpreter(tactic, v) match {
      case BelleProvable(provable, _) => provable
      case r => fail("Unexpected tactic result " + r)
    }
  }

  //@deprecated("TactixLibrary.proveBy should probably be used instead of TacticTestBase")
  def proveBy(p: ProvableSig, tactic: BelleExpr): ProvableSig = {
    val v = BelleProvable(p)
    theInterpreter(tactic, v) match {
      case BelleProvable(provable, _) => provable
      case r => fail("Unexpected tactic result " + r)
    }
  }

  /** Filters the archive entries that should be provable with the `tool`. */
  def toolArchiveEntries(entries: List[ParsedArchiveEntry], tool: Tool): List[ParsedArchiveEntry] = {
    // finds all specific QE({`tool`}) entries, but ignores the generic QE that works with any tool
    val qeFinder = """QE\(\{`([^`]+)`\}\)""".r("toolName")
    entries.
      filter(e => e.tactics.nonEmpty &&
        qeFinder.findAllMatchIn(BellePrettyPrinter(e.tactics.head._2)).forall(p => p.group("toolName") == tool.name))
  }

  /** Checks a specific entry from a bundled archive. Uses the first tactic if tacticName is None. */
  def checkArchiveEntry(archive: String, entryName: String, tacticName: Option[String] = None): Unit = {
    val entry = KeYmaeraXArchiveParser.getEntry(entryName, io.Source.fromInputStream(
      getClass.getResourceAsStream(archive)).mkString).get

    val tactic = tacticName match {
      case Some(tn) => entry.tactics.find(_._1 == tn).get._2
      case None => entry.tactics.head._2
    }

    val start = System.currentTimeMillis()
    qeDurationListener.reset()
    val proof = proveBy(entry.model.asInstanceOf[Formula], tactic)
    val end = System.currentTimeMillis()

    tactic match {
      case _: PartialTactic => // nothing to do, tactic deliberately allowed to result in a non-proof
      case _ => proof shouldBe 'proved withClue entryName + "/" + tacticName
    }

    if (entry.kind == "lemma") {
      val lemmaName = "user" + File.separator + entry.name
      if (LemmaDBFactory.lemmaDB.contains(lemmaName)) LemmaDBFactory.lemmaDB.remove(lemmaName)
      val evidence = Lemma.requiredEvidence(proof, ToolEvidence(List(
        "tool" -> "KeYmaera X",
        "model" -> entry.fileContent,
        "tactic" -> entry.tactics.head._2.prettyString
      )) :: Nil)
      LemmaDBFactory.lemmaDB.add(new Lemma(proof, evidence, Some(lemmaName)))
    }

    println("Proof duration [ms]: " + (end-start))
    println("QE duration [ms]: " + qeDurationListener.duration)
    println("Tactic size: " + TacticStatistics.size(tactic))
    println("Tactic lines: " + TacticStatistics.lines(tactic))
    println("Proof steps: " + proof.steps)
  }

  /** Checks all entries from a bundled archive. */
  def checkArchiveEntries(archive: String): Unit = {
    val entries = KeYmaeraXArchiveParser.parse(io.Source.fromInputStream(
      getClass.getResourceAsStream(archive)).mkString)
    checkArchiveEntries(entries)
  }

  def checkArchiveEntries(entries: List[ParsedArchiveEntry]): Unit = {
    val statistics = scala.collection.mutable.LinkedHashMap[String, (Long, Long, Int, Int, Int)]()

    def printStatistics(v: (Long, Long, Int, Int, Int)): Unit = {
      println("Proof duration [ms]: " + v._1)
      println("QE duration [ms]: " + v._2)
      println("Tactic size: " + v._3)
      println("Tactic lines: " + v._4)
      println("Proof steps: " + v._5)
    }

    for (entry <- entries.filter(_.tactics.nonEmpty)) {
      val tacticName = entry.tactics.head._1
      val tactic = entry.tactics.head._2

      val statisticName = entry.name + " with " + tacticName
      println("Proving " + statisticName)

      qeDurationListener.reset()
      val start = System.currentTimeMillis()
      val proof = proveBy(entry.model.asInstanceOf[Formula], tactic)
      val end = System.currentTimeMillis()
      val qeDuration = qeDurationListener.duration

      tactic match {
        case _: PartialTactic => // nothing to do, tactic deliberately allowed to result in a non-proof
        case _ => proof shouldBe 'proved withClue entry.name + "/" + tacticName
      }

      if (entry.kind == "lemma") {
        val lemmaName = "user" + File.separator + entry.name
        if (LemmaDBFactory.lemmaDB.contains(lemmaName)) LemmaDBFactory.lemmaDB.remove(lemmaName)
        val evidence = Lemma.requiredEvidence(proof, ToolEvidence(List(
          "tool" -> "KeYmaera X",
          "model" -> entry.fileContent,
          "tactic" -> entry.tactics.head._2.prettyString
        )) :: Nil)
        LemmaDBFactory.lemmaDB.add(new Lemma(proof, evidence, Some(lemmaName)))
      }

      statistics(statisticName) = (end-start, qeDuration, TacticStatistics.size(tactic), TacticStatistics.lines(tactic), proof.steps)

      println("Done " + statisticName)
      printStatistics(statistics(statisticName))
    }

    for ((k,v) <- statistics) {
      println("Proof of " + k)
      printStatistics(v)
    }
  }

  /** A listener that stores proof steps in the database `db` for proof `proofId`. */
  def listener(db: DBAbstraction)(proofId: Int)(tacticName: String, parentInTrace: Int, branch: Int): Seq[IOListener] = DBTools.listener(db)(proofId)(tacticName, parentInTrace, branch)

  /** Removes all whitespace for string comparisons in tests.
    * @example{{{
    *     "My string with     whitespace" should equal ("Mystring   with whitespace") (after being whiteSpaceRemoved)
    * }}}
    */
  val whiteSpaceRemoved: Uniformity[String] =
    new AbstractStringUniformity {
      def normalized(s: String): String = s.replaceAll("\\s+", "")
      override def toString: String = "whiteSpaceRemoved"
    }

  def loneSucc(p: ProvableSig): Formula = {
    assert(p.subgoals.length==1)
    assert(p.subgoals.last.succ.length==1)
    p.subgoals.last.succ.last
  }
}