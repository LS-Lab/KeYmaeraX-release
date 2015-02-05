import edu.cmu.cs.ls.keymaera.core.{Formula, ProofNode, Mathematica}
import edu.cmu.cs.ls.keymaera.tactics.Tactics
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}

/**
 * Created by nfulton on 2/5/15.
 */
trait TacticTestSuite extends FlatSpec with Matchers with BeforeAndAfterEach {
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Boilerplate
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  val helper = new ProvabilityTestHelper(x=>println(x))

  var tool: Mathematica = null
  val mathematicaConfig = helper.mathematicaConfig

  override def beforeEach() = {
    tool = new Mathematica
    tool.init(mathematicaConfig)
    Tactics.KeYmaeraScheduler.init(Map())
    Tactics.MathematicaScheduler.init(mathematicaConfig)
  }

  override def afterEach() = {
    tool.shutdown()
    tool = null
    Tactics.KeYmaeraScheduler.shutdown()
    Tactics.MathematicaScheduler.shutdown()
  }

  protected def containsOpenGoal(node:ProofNode, f:Formula) =
    !node.openGoals().find(_.sequent.succ.contains(f)).isEmpty
}
