package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleProvable, BelleExpr, SequentialInterpreter}
import edu.cmu.cs.ls.keymaerax.core.{Sequent, Provable, Formula, PrettyPrinter}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}

/**
 * Base class for tactic tests.
 */
class TacticTestBase extends FlatSpec with Matchers with BeforeAndAfterEach {
  val theInterpreter = SequentialInterpreter()

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
