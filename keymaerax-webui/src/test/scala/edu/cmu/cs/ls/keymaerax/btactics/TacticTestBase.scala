package edu.cmu.cs.ls.keymaerax.btactics

import java.io.File

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.hydra.SQLite.SQLiteDB
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, DbProofTree, UserPOJO}
import edu.cmu.cs.ls.keymaerax.launcher.DefaultConfiguration
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXPrettyPrinter, KeYmaeraXProblemParser}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tacticsinterface.TraceRecordingListener
import edu.cmu.cs.ls.keymaerax.tools._
import org.scalactic.{AbstractStringUniformity, Uniformity}
import org.scalatest.{Assertions, BeforeAndAfterEach, FlatSpec, Matchers}

import scala.collection.immutable._

/**
 * Base class for tactic tests.
 */
class TacticTestBase extends FlatSpec with Matchers with BeforeAndAfterEach {
  protected var theInterpreter: Interpreter = _

  /** Tests that want to record proofs in a database. */
  class DbTacticTester {
    lazy val user: UserPOJO = db.getUser("guest").get

    val db: SQLiteDB = {
      val testLocation = File.createTempFile("testdb", ".sqlite")
      val db = new SQLiteDB(testLocation.getAbsolutePath)
      db.cleanup(testLocation.getAbsolutePath)
      db
    }

    /** Turns a formula into a model problem with mandatory declarations. */
    def makeModel(content: String): String = {
      def printDomain(d: Sort): String = d match {
        case Real => "R"
        case Bool => "B"
        case Unit => ""
        case Tuple(l, r) => printDomain(l) + "," + printDomain(r)
      }

      def augmentDeclarations(content: String, parsedContent: Formula): String =
        if (content.contains("Problem.")) content //@note determine by mandatory "Problem." block of KeYmaeraXProblemParser
        else {
          val symbols = StaticSemantics.symbols(parsedContent)
          val fnDecls = symbols.filter(_.isInstanceOf[Function]).map(_.asInstanceOf[Function]).map(fn =>
            if (fn.sort == Real) s"R ${fn.asString}(${printDomain(fn.domain)})."
            else if (fn.sort == Bool) s"B ${fn.asString}(${printDomain(fn.domain)})."
            else ???
          ).mkString("\n  ")
          val varDecls = symbols.filter(_.isInstanceOf[BaseVariable]).map(v => s"R ${v.prettyString}.").mkString("\n  ")
          s"""Functions.
             |  $fnDecls
             |End.
             |ProgramVariables.
             |  $varDecls
             |End.
             |Problem.
             |  $content
             |End.""".stripMargin
        }

      augmentDeclarations(content, KeYmaeraXProblemParser.parseAsProblemOrFormula(content))
    }

    /** Creates a new proof entry in the database for a model parsed from `modelContent`. */
    def createProof(modelContent: String, modelName: String = "", proofName: String = "Proof"): Int = {
      db.createModel(user.userName, modelName, makeModel(modelContent), "", None, None, None, None) match {
        case Some(modelId) => db.createProofForModel(modelId, modelName + proofName, "", "", None)
        case None => fail("Unable to create temporary model in DB")
      }
    }

    /** Prove model `modelContent` using tactic  `t`. Record the proof in the database and check that the recorded
      * tactic is the provided tactic. Returns the proof ID and resulting provable. */
    def proveByWithProofId(modelContent: String, t: BelleExpr, modelName: String = ""): (Int, ProvableSig) = {
      val s: Sequent = KeYmaeraXProblemParser.parseAsProblemOrFormula(modelContent) match {
        case fml: Formula => Sequent(IndexedSeq(), IndexedSeq(fml))
        case _ => fail("Model content " + modelContent + " cannot be parsed")
      }
      db.getModelList(user.userName).find(_.name == modelName) match {
        case Some(m) => db.deleteModel(m.modelId)
        case None => // nothing to do
      }
      val proofId = createProof(modelContent, modelName)
      val globalProvable = ProvableSig.startProof(s)
      val listener = new TraceRecordingListener(db, proofId, None,
        globalProvable, 0 /* start from single provable */, recursive = false, "custom")
      SequentialInterpreter(listener :: Nil)(t, BelleProvable(ProvableSig.startProof(s))) match {
        case BelleProvable(provable, _) =>
          provable.conclusion shouldBe s
          //extractTactic(proofId) shouldBe t //@todo trim trailing branching nil
          if (provable.isProved) {
            // check that database thinks so too
            val finalTree = DbProofTree(db, proofId.toString)
            finalTree.load()
            //finalTree.leaves shouldBe empty
            finalTree.nodes.foreach(n => n.parent match {
              case None => n.conclusion shouldBe s
              case Some(parent) => n.conclusion shouldBe parent.localProvable.subgoals(n.goalIdx)
            })
          }
          (proofId, provable)
        case r => fail("Unexpected tactic result " + r)
      }
    }

    /** Prove model `modelContent` using tactic  `t`. Record the proof in the database and check that the recorded
      * tactic is the provided tactic. Returns the resulting provable. */
    def proveBy(modelContent: String, t: BelleExpr, modelName: String = ""): ProvableSig = proveByWithProofId(modelContent, t, modelName)._2

    /** Returns the tactic recorded for the proof `proofId`. */
    def extractTactic(proofId: Int): BelleExpr = DbProofTree(db, proofId.toString).tactic

    /** Extracts the internal steps taken by proof step `stepId` at level `level` (0: original tactic, 1: direct internal steps, etc.)  */
    def extractStepDetails(proofId: Int, stepId: String, level: Int = 1): BelleExpr = {
      DbProofTree(db, proofId.toString).locate(stepId) match {
        case Some(node) => node.maker match {
          case Some(tactic) =>
            val localProofId = db.createProof(node.localProvable)
            val interpreter = SpoonFeedingInterpreter(localProofId, -1, db.createProof, listener(db), SequentialInterpreter, level, strict=false)
            interpreter(BelleParser(tactic), BelleProvable(ProvableSig.startProof(node.localProvable.conclusion)))
            extractTactic(localProofId)
        }
      }

    }
  }

  /** For tests that want to record proofs in the database. */
  def withDatabase(testcode: DbTacticTester => Any): Unit = testcode(new DbTacticTester())

  /**
   * Creates and initializes Mathematica for tests that want to use QE. Also necessary for tests that use derived
   * axioms that are proved by QE.
   * @example{{{
   *    "My test" should "prove something with Mathematica" in withMathematica { qeTool =>
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
    *    "My test" should "prove something with Z3" in withZ3 { qeTool =>
    *      // ... your test code here
    *    }
    * }}}
    * */
  def withZ3(testcode: Z3 => Any) {
    val provider = new Z3ToolProvider
    ToolProvider.setProvider(provider)
    testcode(provider.tool())
  }

  /** Tests with both Mathematica and Z3 as QE tools. */
  def withQE(testcode: QETool => Any): Unit = {
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
    theInterpreter = SequentialInterpreter()
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
    val generator = new ConfigurableGenerator[Formula]()
    KeYmaeraXParser.setAnnotationListener((p: Program, inv: Formula) => generator.products += (p->inv))
    TactixLibrary.invGenerator = generator
    ToolProvider.setProvider(new NoneToolProvider())
  }

  /* Test teardown */
  override def afterEach(): Unit = {
    theInterpreter = null
    PrettyPrinter.setPrinter(e => e.getClass.getName)
    ToolProvider.shutdown()
    ToolProvider.setProvider(new NoneToolProvider())
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
  def listener(db: DBAbstraction)(proofId: Int)(tacticName: String, parentInTrace: Int, branch: Int): Seq[IOListener] = {
    val trace = db.getExecutionSteps(proofId)
    assert(-1 <= parentInTrace && parentInTrace < trace.length, "Invalid trace index " + parentInTrace + ", expected -1<=i<trace.length")
    val parentStep: Option[Int] = if (parentInTrace < 0) None else trace(parentInTrace).stepId
    val globalProvable = parentStep match {
      case None => db.getProvable(db.getProofInfo(proofId).provableId.get).provable
      case Some(sId) => db.getExecutionStep(proofId, sId).map(_.local).get
    }
    new TraceRecordingListener(db, proofId, parentStep,
      globalProvable, branch, recursive = false, tacticName) :: Nil
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