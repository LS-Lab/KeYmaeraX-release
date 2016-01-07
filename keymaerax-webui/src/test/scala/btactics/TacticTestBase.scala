package edu.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleProvable, BelleExpr, SequentialInterpreter}
import edu.cmu.cs.ls.keymaerax.btactics.{ConfigurableGenerate, NoneGenerate, DerivedAxioms, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.launcher.DefaultConfiguration
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXPrettyPrinter}
import edu.cmu.cs.ls.keymaerax.tools.Mathematica
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}

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
    mathematica shouldBe 'initialized
    DerivedAxioms.qeTool = mathematica
    TactixLibrary.tool = mathematica
    try {
      testcode(mathematica)
    } finally mathematica.shutdown()
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
      DerivedAxioms.qeTool match { case m: Mathematica => m.shutdown() }
      DerivedAxioms.qeTool = null
    }
    if (TactixLibrary.tool != null) {
      TactixLibrary.tool match { case m: Mathematica => m.shutdown() }
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
