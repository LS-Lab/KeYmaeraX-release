package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleProvable, BelleExpr, SequentialInterpreter}
import edu.cmu.cs.ls.keymaerax.core.{Sequent, Provable, Formula, PrettyPrinter}
import edu.cmu.cs.ls.keymaerax.launcher.DefaultConfiguration
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import edu.cmu.cs.ls.keymaerax.tools.Mathematica
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}

/**
 * Base class for tactic tests.
 */
class TacticTestBase extends FlatSpec with Matchers with BeforeAndAfterEach {
  val theInterpreter = SequentialInterpreter()

  /**
   * Creates and initializes Mathematica for tests that want to use QE.
   * @example{{{
   *    "My test" should "prove something with Mathematica" in new MathematicaBuilder {
   *      // ... your test code here
   *    }
   * }}}
   * */
  trait MathematicaBuilder {
    implicit val qeTool = new Mathematica()
    qeTool.init(DefaultConfiguration.defaultMathematicaConfig)
    qeTool shouldBe 'initialized
  }

  /** Test setup */
  override def beforeEach() = {
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
  }

  /** Proves a formula using the specified tactic. Fails the test when tactic fails. */
  def proveBy(fml: Formula, tactic: BelleExpr): Provable = {
    val v = BelleProvable(Provable.startProof(fml))
    theInterpreter(tactic, v) match {
      case BelleProvable(provable) => provable
      case r => fail("Unexpected tactic result " + r)
    }
  }

  /** Proves a sequent using the specified tactic. Fails the test when tactic fails. */
  def proveBy(s: Sequent, tactic: BelleExpr): Provable = {
    val v = BelleProvable(Provable.startProof(s))
    theInterpreter(tactic, v) match {
      case BelleProvable(provable) => provable
      case r => fail("Unexpected tactic result " + r)
    }
  }

}
