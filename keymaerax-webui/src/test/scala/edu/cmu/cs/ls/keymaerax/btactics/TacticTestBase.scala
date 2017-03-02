package edu.cmu.cs.ls.keymaerax.btactics

import java.io.File

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.hydra.SQLite.SQLiteDB
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, ExtractTacticFromTrace, ProofTree}
import edu.cmu.cs.ls.keymaerax.launcher.DefaultConfiguration
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXPrettyPrinter, KeYmaeraXProblemParser}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tacticsinterface.TraceRecordingListener
import edu.cmu.cs.ls.keymaerax.tools._
import org.scalactic.{AbstractStringUniformity, Uniformity}
import org.scalatest.{BeforeAndAfterEach, FlatSpec, Matchers}

import scala.collection.immutable._

/**
 * Base class for tactic tests.
 */
class TacticTestBase extends FlatSpec with Matchers with BeforeAndAfterEach {
  val theInterpreter = SequentialInterpreter()

  /** Tests that want to record proofs in a database. */
  class DbTacticTester {
    val db: SQLiteDB = {
      val testLocation = File.createTempFile("testdb", ".sqlite")
      val db = new SQLiteDB(testLocation.getAbsolutePath)
      db.cleanup(testLocation.getAbsolutePath)
      db
    }

    /** Creates a new proof entry in the database for a model parsed from `modelContent`. */
    def createProof(modelContent: String, modelName: String = ""): Int = {
      db.createModel("guest", modelName, modelContent, "", None, None, None, None) match {
        case Some(modelId) => db.createProofForModel(modelId, modelName + "Proof", "", "")
        case None => fail("Unable to create temporary model in DB")
      }
    }

    /** Prove sequent `s` using tactic  `t`. Record the proof in the database and check that the recorded tactic is
      * the provided tactic. */
    def proveBy(modelContent: String, t: BelleExpr, modelName: String = ""): ProvableSig = {
      val s: Sequent = KeYmaeraXProblemParser(modelContent) match {
        case fml: Formula => Sequent(IndexedSeq(), IndexedSeq(fml))
        case _ => fail("Model content " + modelContent + " cannot be parsed")
      }
      val proofId = createProof(modelContent, modelName)
      val trace = db.getExecutionTrace(proofId)
      val globalProvable = trace.lastProvable
      val listener = new TraceRecordingListener(db, proofId, trace.executionId.toInt, trace.lastStepId,
        globalProvable, trace.alternativeOrder, 0 /* start from single provable */, recursive = false, "custom")
      SequentialInterpreter(listener :: Nil)(t, BelleProvable(ProvableSig.startProof(s))) match {
        case BelleProvable(provable, _) =>
          provable.conclusion shouldBe s
          extractTactic(proofId) shouldBe t
          if (provable.isProved) {
            // check that database thinks so too
            val finalTree = ProofTree.ofTrace(db.getExecutionTrace(proofId))
            finalTree.theLeaves shouldBe empty
            finalTree.nodes.foreach(n => {
              n.endStep shouldBe 'defined
              val end = n.endStep.get
              end.output.get.subgoals should have length end.input.subgoals.length - 1
              for (i <- end.input.subgoals.indices) {
                if (i < end.branch) end.output.get.subgoals(i) shouldBe end.input.subgoals(i)
                if (i > end.branch) end.output.get.subgoals(i-1) shouldBe end.input.subgoals(i)
              }
            })
          }
          provable
        case r => fail("Unexpected tactic result " + r)
      }
    }

    /** Returns the tactic recorded for the proof `proofId`. */
    def extractTactic(proofId: Int): BelleExpr = new ExtractTacticFromTrace(db).apply(db.getExecutionTrace(proofId))
  }

  /** For tests that want to record proofs in the database. */
  def withDatabase(testcode: DbTacticTester => Any): Unit = testcode(new DbTacticTester())

  /**
   * Creates and initializes Mathematica for tests that want to use QE. Also necessary for tests that use derived
   * axioms that are proved by QE.
   * @example{{{
   *    "My test" should "prove something with Mathematica" in withMathematica { implicit qeTool =>
   *      // ... your test code here
   *    }
   * }}}
   * */
  def withMathematica(testcode: Mathematica => Any) {
    val provider = new MathematicaToolProvider(DefaultConfiguration.currentMathematicaConfig)
    ToolProvider.setProvider(provider)
    testcode(provider.tool())
  }

  /**
    * Creates and initializes Z3 for tests that want to use QE. Also necessary for tests that use derived
    * axioms that are proved by QE.
    * Note that Mathematica should also ne initialized in order to perform DiffSolution and CounterExample
    * @example{{{
    *    "My test" should "prove something with Mathematica" in withZ3 { implicit qeTool =>
    *      // ... your test code here
    *    }
    * }}}
    * */
  def withZ3(testcode: Z3 => Any) {
    val provider = new Z3ToolProvider
    ToolProvider.setProvider(provider)
    testcode(provider.tool())
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
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
    val generator = new ConfigurableGenerator[Formula]()
    KeYmaeraXParser.setAnnotationListener((p: Program, inv: Formula) => generator.products += (p->inv))
    TactixLibrary.invGenerator = generator
  }

  /* Test teardown */
  override def afterEach(): Unit = {
    PrettyPrinter.setPrinter(e => e.getClass.getName)
    ToolProvider.shutdown()
    TactixLibrary.invGenerator = FixedGenerator(Nil)
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

  //@deprecated("TactixLibrary.proveBy should probably be used instead of TacticTestBase")
  def proveBy(p: ProvableSig, tactic: BelleExpr): ProvableSig = {
    val v = BelleProvable(p)
    theInterpreter(tactic, v) match {
      case BelleProvable(provable, _) => provable
      case r => fail("Unexpected tactic result " + r)
    }
  }

  /** A listener that stores proof steps in the database `db` for proof `proofId`. */
  def listener(db: DBAbstraction)(proofId: Int)(tacticName: String, branch: Int): Seq[IOListener] = {
    val trace = db.getExecutionTrace(proofId)
    val globalProvable = trace.lastProvable
    new TraceRecordingListener(db, proofId, trace.executionId.toInt, trace.lastStepId,
      globalProvable, trace.alternativeOrder, branch, recursive = false, tacticName) :: Nil
  }

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