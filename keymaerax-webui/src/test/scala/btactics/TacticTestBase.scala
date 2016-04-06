package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, BelleProvable, SequentialInterpreter}
import edu.cmu.cs.ls.keymaerax.btactics.{ConfigurableGenerate, DerivedAxioms, NoneGenerate, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.launcher.DefaultConfiguration
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXPrettyPrinter}
import edu.cmu.cs.ls.keymaerax.tools._
import org.scalatest.{BeforeAndAfterEach, FlatSpec, Matchers}

/**
 * Base class for tactic tests.
 */
class TacticTestBase extends FlatSpec with Matchers with BeforeAndAfterEach {
  val theInterpreter = SequentialInterpreter()

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
    val mathematica = new Mathematica()
    mathematica.init(DefaultConfiguration.defaultMathematicaConfig)
    withTool(mathematica)(testcode)
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
    val z3 = new Z3()
    z3.init(DefaultConfiguration.defaultMathematicaConfig)
    withTool(z3)(testcode)
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
    val polya = new Polya()
    polya.init(DefaultConfiguration.defaultMathematicaConfig)
    withTool(polya)(testcode)
  }

  /** Sets 'tool' as the tool used in DerivedAxioms and TactixLibrary. tool must be initialized already. */
  def withTool[T <: Tool with QETool with DiffSolutionTool with CounterExampleTool](tool: T)(testcode: T => Any): Unit = {
    tool shouldBe 'initialized
    DerivedAxioms.qeTool = tool
    TactixLibrary.tool = tool
    try {
      testcode(tool)
    } finally tool.shutdown()
  }

  /** Test setup */
  override def beforeEach() = {
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
    val generator = new ConfigurableGenerate[Formula]()
    KeYmaeraXParser.setAnnotationListener((p: Program, inv: Formula) => generator.products += (p->inv))
    TactixLibrary.invGenerator = generator
  }

  /* Test teardown */
  override def afterEach() = {
    if (DerivedAxioms.qeTool != null) {
      DerivedAxioms.qeTool match { case t: Tool => t.shutdown() }
      DerivedAxioms.qeTool = null
    }
    if (TactixLibrary.tool != null) {
      TactixLibrary.tool match { case t: Tool => t.shutdown() }
      TactixLibrary.tool = null
      TactixLibrary.invGenerator = new NoneGenerate()
    }
  }

  /** Proves a formula using the specified tactic. Fails the test when tactic fails. */
  def proveBy(fml: Formula, tactic: BelleExpr): Provable = {
    val v = BelleProvable(Provable.startProof(fml))
    theInterpreter(tactic, v) match {
      case BelleProvable(provable, _) => provable
      case r => fail("Unexpected tactic result " + r)
    }
  }

  /** Proves a sequent using the specified tactic. Fails the test when tactic fails. */
  def proveBy(s: Sequent, tactic: BelleExpr): Provable = {
    val v = BelleProvable(Provable.startProof(s))
    theInterpreter(tactic, v) match {
      case BelleProvable(provable, _) => provable
      case r => fail("Unexpected tactic result " + r)
    }
  }

}
