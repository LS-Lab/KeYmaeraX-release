package edu.cmu.cs.ls.keymaerax.btactics

import java.io.File

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon.IOListeners.{PrintProgressListener, QEFileLogListener, QELogListener, StopwatchListener}
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BellePrettyPrinter
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.InvariantGenerator.{AnnotationProofHint, GenProduct}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.hydra._
import edu.cmu.cs.ls.keymaerax.lemma.{Lemma, LemmaDBFactory}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXArchiveParser.{Declaration, ParsedArchiveEntry}
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXArchiveParser, KeYmaeraXParser, KeYmaeraXPrettyPrinter}
import edu.cmu.cs.ls.keymaerax.pt.{ElidingProvable, ProvableSig}
import edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaConversion.{KExpr, MExpr}
import edu.cmu.cs.ls.keymaerax.tools._
import edu.cmu.cs.ls.keymaerax.tools.ext.{JLinkMathematicaLink, Mathematica, QETacticTool, Z3}
import edu.cmu.cs.ls.keymaerax.tools.install.DefaultConfiguration
import edu.cmu.cs.ls.keymaerax.tools.qe.{K2MConverter, M2KConverter}
import org.scalactic.{AbstractStringUniformity, Uniformity}
import org.scalatest._
import org.scalatest.concurrent.{Signaler, TimeLimitedTests, TimeLimits}
import org.scalatest.time._

import scala.collection.immutable._

/**
 * Base class for tactic tests.
 */
class TacticTestBase extends FlatSpec with Matchers with BeforeAndAfterEach with BeforeAndAfterAll
    with AppendedClues with TimeLimitedTests with TimeLimits with PrivateMethodTester {

  /** Default signaler for failAfter in tests without tools. */
  protected implicit val signaler: Signaler = { t: Thread =>
    theInterpreter.kill(); t.interrupt()
  }

  override def timeLimit: Span = {
    val simpleNames = this.getClass.getAnnotations.map(_.annotationType().getSimpleName)
    if (simpleNames.contains("ExtremeTest")) {
      Span(3, Hours)
    } else if (simpleNames.contains("SlowTest")) {
      Span(1, Hour)
    } else {
      Span(20, Minutes)
    }
  }

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

  def configFileMathematicaConfig: Map[String, String] = {
    if (!Configuration.contains(Configuration.Keys.MATHEMATICA_LINK_NAME)) {
      Configuration.set(Configuration.Keys.MATHEMATICA_LINK_NAME, DefaultConfiguration.defaultMathematicaConfig("linkName"), saveToFile = false)
    }
    if (!Configuration.contains(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR)) {
      Configuration.set(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR, DefaultConfiguration.defaultMathematicaConfig("libDir"), saveToFile = false)
    }
    if (!Configuration.contains(Configuration.Keys.MATH_LINK_TCPIP)) {
      Configuration.set(Configuration.Keys.MATH_LINK_TCPIP, DefaultConfiguration.defaultMathematicaConfig("tcpip"), saveToFile = false)
    }
    Map(
      "linkName" -> Configuration(Configuration.Keys.MATHEMATICA_LINK_NAME),
      "libDir" -> Configuration(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR),
      "tcpip" -> Configuration(Configuration.Keys.MATH_LINK_TCPIP))
  }

  def configFileWolframEngineConfig: Map[String, String] = {
    if (!Configuration.contains(Configuration.Keys.WOLFRAMENGINE_LINK_NAME)) {
      Configuration.set(Configuration.Keys.WOLFRAMENGINE_LINK_NAME, DefaultConfiguration.defaultWolframEngineConfig("linkName"), saveToFile = false)
    }
    if (!Configuration.contains(Configuration.Keys.WOLFRAMENGINE_JLINK_LIB_DIR)) {
      Configuration.set(Configuration.Keys.WOLFRAMENGINE_JLINK_LIB_DIR, DefaultConfiguration.defaultWolframEngineConfig("libDir"), saveToFile = false)
    }
    if (!Configuration.contains(Configuration.Keys.WOLFRAMENGINE_TCPIP)) {
      Configuration.set(Configuration.Keys.WOLFRAMENGINE_TCPIP, DefaultConfiguration.defaultWolframEngineConfig("tcpip"), saveToFile = false)
    }
    Map(
      "linkName" -> Configuration(Configuration.Keys.WOLFRAMENGINE_LINK_NAME),
      "libDir" -> Configuration(Configuration.Keys.WOLFRAMENGINE_JLINK_LIB_DIR),
      "tcpip" -> Configuration(Configuration.Keys.WOLFRAMENGINE_TCPIP))
  }

  /** A tool provider that does not shut down on `shutdown`, but defers to `doShutdown`. */
  class DelayedShutdownToolProvider(p: ToolProvider) extends PreferredToolProvider(p.tools()) {
    override def shutdown(): Unit = {} // do not shut down between tests and when switching providers in ToolProvider.setProvider
    def doShutdown(): Unit = super.shutdown()
  }

  // start test with -DWOLFRAM=... (one of 'Mathematica' or 'WolframEngine') to select the Wolfram backend.
  private val WOLFRAM = System.getProperty("WOLFRAM", "Mathematica")

  //@note Initialize once per test class in beforeAll, but only if requested in a withMathematica call
  private var mathematicaProvider: Lazy[DelayedShutdownToolProvider] = _
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
   * @example {{{
   *    "My test" should "prove something with Mathematica" in withMathematica { qeTool =>
   *      // ... your test code here
   *    }
   * }}}
   * */
  def withMathematica(testcode: Mathematica => Any, timeout: Int = -1, initLibrary: Boolean = true): Unit = mathematicaProvider.synchronized {
    val mathLinkTcp = System.getProperty(Configuration.Keys.MATH_LINK_TCPIP, Configuration(Configuration.Keys.MATH_LINK_TCPIP)) // JVM parameter -DMATH_LINK_TCPIP=[true,false]
    val common = Map(
      Configuration.Keys.MATH_LINK_TCPIP -> mathLinkTcp,
      Configuration.Keys.QE_TOOL -> "mathematica")
    val interp = common.+(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")
    val uninterp = common.+(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "false")
    withTemporaryConfig(common) {
      val provider = mathematicaProvider()
      ToolProvider.setProvider(provider)
      val tool = provider.defaultTool() match {
        case Some(m: Mathematica) => m
        case _ => fail("Illegal Wolfram tool, please use one of 'Mathematica' or 'Wolfram Engine' in test setup")
      }
      if(initLibrary) {
        withTemporaryConfig(interp) {
          Ax.prepopulateDerivedLemmaDatabase()
        }
      }
      withTemporaryConfig(uninterp) {
        val to = if (timeout == -1) timeLimit else Span(timeout, Seconds)
        implicit val signaler: Signaler = (t: Thread) => {
          theInterpreter.kill()
          tool.cancel()
          tool.shutdown() // let testcode know it should stop (forEvery catches all exceptions)
          mathematicaProvider.synchronized {
            mathematicaProvider().doShutdown() //@note see [[afterAll]]
            provider.shutdown()
            mathematicaProvider = new Lazy(new DelayedShutdownToolProvider(new MathematicaToolProvider(configFileMathematicaConfig)))
          }
        }
        failAfter(to) {
          testcode(tool)
        }
      }
    }
  }

  /**
    * Creates and initializes Z3 for tests that want to use QE. Also necessary for tests that use derived
    * axioms that are proved by QE.
    * Note that Mathematica should also ne initialized in order to perform DiffSolution and CounterExample
    * @example {{{
    *    "My test" should "prove something with Z3" in withZ3 { qeTool =>
    *      // ... your test code here
    *    }
    * }}}
    * */
  def withZ3(testcode: Z3 => Any, timeout: Int = -1, initLibrary: Boolean = true) {
    val common = Map(Configuration.Keys.QE_TOOL -> "z3")
    val interp = common.+(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")
    val uninterp = common.+(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "false")
    withTemporaryConfig(common) {
      val provider = new Z3ToolProvider
      ToolProvider.setProvider(provider)
      provider.tool().setOperationTimeout(timeout)
      val tool = provider.tool()
      if(initLibrary) {
        withTemporaryConfig(interp) {
          Ax.prepopulateDerivedLemmaDatabase()
        }
      }
      withTemporaryConfig(uninterp) {
        val to = if (timeout == -1) timeLimit else Span(timeout, Seconds)
        implicit val signaler: Signaler = { t: Thread =>
          theInterpreter.kill()
          tool.cancel()
          t.interrupt()
          provider.shutdown()
        }
        failAfter(to) {
          testcode(tool)
        }
      }
    }
  }

  /** Tests with both Mathematica and Z3 as QE tools. */
  def withQE(testcode: Tool with QETacticTool => Any, timeout: Int = -1, initLibrary: Boolean = true): Unit = {
    withClue("Mathematica") { withMathematica(testcode, timeout, initLibrary) }
    afterEach()
    beforeEach()
    withClue("Z3") { withZ3(testcode, timeout, initLibrary) }
  }

  /** Creates and initializes Mathematica; checks that a Matlab bridge is configured. @see[[withMathematica]]. */
    //@todo skip if not matlink set up
  def withMathematicaMatlab(testcode: Mathematica => Any, timeout: Int = -1, initLibrary: Boolean = true) {
    if (System.getProperty("KILL_MATLAB") == "true") {
      var killExit = 0
      while (killExit == 0) {
        val p = Runtime.getRuntime.exec("pkill -9 MATLAB")
        p.waitFor()
        killExit = p.exitValue()
      }
    }
    withMathematica (initLibrary = initLibrary, timeout = timeout, testcode = { tool =>
      val getLink = PrivateMethod[JLinkMathematicaLink]('link)
      val link = tool invokePrivate getLink()
      link.runUnchecked("""Needs["MATLink`"]""", new M2KConverter[KExpr]() {
        override def k2m: K2MConverter[KExpr] = throw new Exception("Unexpected call to k2m")
        override def apply(e: MExpr): KExpr = {
          e shouldBe 'symbolQ
          if (e.asString() == "$Failed") fail("Test case requires Matlab, but MATLink bridge from Mathematica to Matlab not configured")
          True
        }
        override def convert(e: MExpr): KExpr = throw new Exception("Unexpected call to convert")
      })
      testcode(tool)
    })
  }

  /** Executes `testcode` with a temporary configuration that gets reset after execution. */
  def withTemporaryConfig(tempConfig: Map[String, String])(testcode: => Any) {
    val origConfig = tempConfig.keys.map(k => k -> Configuration.getOption(k))
    try {
      tempConfig.foreach({ case (k, v) => Configuration.set(k, v, saveToFile = false) })
      testcode
    } finally {
      origConfig.foreach({
        case (k, None) => Configuration.remove(k, saveToFile = false)
        case (k, Some(v)) => Configuration.set(k, v, saveToFile = false)
      })
    }
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
    DerivationInfoRegistry.init
    BelleInterpreter.setInterpreter(registerInterpreter(LazySequentialInterpreter(listeners)))
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
    val generator = new ConfigurableGenerator[GenProduct]()
    KeYmaeraXParser.setAnnotationListener((p: Program, inv: Formula) =>
      generator.products += (p->(generator.products.getOrElse(p, Nil) :+ (inv, Some(AnnotationProofHint(tryHard=true)))).distinct))
    TactixLibrary.invSupplier = generator
    // reinitialize with empty caches for test case separation
    TactixLibrary.differentialInvGenerator = InvariantGenerator.cached(InvariantGenerator.differentialInvariantGenerator)
    TactixLibrary.loopInvGenerator = InvariantGenerator.cached(InvariantGenerator.loopInvariantGenerator)
    //@note Mathematica is expected to shut down only in afterAll(), but setting provider shuts down the current provider
    if (!mathematicaProvider.isInitialized) ToolProvider.setProvider(new NoneToolProvider())
    LemmaDBFactory.lemmaDB.removeAll("user/tests")
    LemmaDBFactory.lemmaDB.removeAll("qecache")
  }

  /* Test teardown */
  override def afterEach(): Unit = {
    LemmaDBFactory.lemmaDB.removeAll("user/tests")
    LemmaDBFactory.lemmaDB.removeAll("qecache")
    try {
      interpreters.foreach(i => try { i.kill() } catch { case ex: Throwable => ex.printStackTrace() })
      interpreters = Nil
    } finally {
      PrettyPrinter.setPrinter(e => e.getClass.getName)
      ToolProvider.shutdown()
      ToolProvider.setProvider(new NoneToolProvider())
      if (dbTester.isInitialized) {
        dbTester().db.session.close()
        dbTester = null
      }
      TactixLibrary.invSupplier = FixedGenerator(Nil)
      TactixLibrary.differentialInvGenerator = FixedGenerator(Nil)
      TactixLibrary.loopInvGenerator = FixedGenerator(Nil)
    }
  }

  /** Test suite setup */
  override def beforeAll(): Unit = {
    mathematicaProvider =
      if (WOLFRAM.equalsIgnoreCase("Mathematica")) new Lazy(new DelayedShutdownToolProvider(new MathematicaToolProvider(configFileMathematicaConfig)))
      else if (WOLFRAM.equalsIgnoreCase("WolframEngine")) new Lazy(new DelayedShutdownToolProvider(new WolframEngineToolProvider(configFileWolframEngineConfig)))
      else if (WOLFRAM.equalsIgnoreCase("WolframScript")) new Lazy(new DelayedShutdownToolProvider(new WolframScriptToolProvider))
      else throw new IllegalArgumentException("Unknown Wolfram backend, please provide either 'Mathematica' or 'WolframEngine'")
  }

  /* Test suite tear down */
  override def afterAll(): Unit = {
    //@note reduce number of zombie MathKernels: init and tear down Mathematica once per test class
    if (mathematicaProvider.isInitialized) {
      mathematicaProvider().doShutdown()
    }
    ToolProvider.shutdown()
    ToolProvider.setProvider(new NoneToolProvider())
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
  def proveBy(fml: Formula, tactic: BelleExpr, labelCheck: Option[List[BelleLabel]] => Unit = _ => {}, defs: Declaration = Declaration(Map.empty)): ProvableSig = {
    val v = BelleProvable(ProvableSig.startProof(fml))
    theInterpreter(tactic, v) match {
      case dsp: BelleDelayedSubstProvable =>
        dsp.p.conclusion shouldBe Sequent(
          IndexedSeq(),
          IndexedSeq(fml.exhaustiveSubst(dsp.subst ++ USubst(defs.substs)).asInstanceOf[Formula])
        )
        labelCheck(dsp.label)
        dsp.p
      case BelleProvable(provable, labels) =>
        provable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(defs.exhaustiveSubst(fml)))
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

  /** Execute a task with tactic progress.
    * @example {{{
    *   withTacticProgress("implyR(1)".asTactic) { proveBy("x>0 -> x>=0".asFormula, _) }
    *   withTacticProgress("master".asTactic, "master"::"step"::"stepAt"::Nil) { proveBy("x>0 -> x>=0".asFormula, _) }
    * }}}
    */
  def withTacticProgress(tactic: BelleExpr, stepInto: List[String] = Nil)(task: BelleExpr => ProvableSig): ProvableSig = {
    val orig = theInterpreter
    val progressInterpreter = LazySequentialInterpreter(
      orig.listeners :+ new PrintProgressListener(tactic, stepInto), throwWithDebugInfo = false)
    registerInterpreter(progressInterpreter)
    BelleInterpreter.setInterpreter(progressInterpreter)
    try { task(tactic) } finally { BelleInterpreter.setInterpreter(orig) }
  }

  /** Filters the archive entries that should be provable with the `tool`. */
  def toolArchiveEntries(entries: List[ParsedArchiveEntry], tool: Tool): List[ParsedArchiveEntry] = {
    // finds all specific QE({`tool`}) entries, but ignores the generic QE that works with any tool
    val qeFinder = """QE\(\{`([^`]+)`\}\)""".r("toolName")
    entries.
      filter(e => e.tactics.nonEmpty &&
        qeFinder.findAllMatchIn(BellePrettyPrinter(e.tactics.head._3)).forall(p => p.group("toolName") == tool.name))
  }

  /** Checks a specific entry from a bundled archive. Uses the first tactic if tacticName is None. */
  def checkArchiveEntry(archive: String, entryName: String, tacticName: Option[String] = None): Unit = {
    val entry = KeYmaeraXArchiveParser.getEntry(entryName, io.Source.fromInputStream(
      getClass.getResourceAsStream(archive)).mkString).get

    val tactic = tacticName match {
      case Some(tn) => entry.tactics.find(_._1 == tn).get._3
      case None => entry.tactics.head._3
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
        "tactic" -> entry.tactics.head._2
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
      val tactic = entry.tactics.head._3

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
          "tactic" -> entry.tactics.head._2
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
    * @example {{{
    *     "My string with     whitespace" should equal ("Mystring   with whitespace") (after being whiteSpaceRemoved)
    * }}}
    */
  val whiteSpaceRemoved: Uniformity[String] =
    new AbstractStringUniformity {
      def normalized(s: String): String = s.replaceAll("\\s+", "")
      override def toString: String = "whiteSpaceRemoved"
    }
}