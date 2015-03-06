import edu.cmu.cs.ls.keymaera.core.{Mathematica, KeYmaera, RootNode}
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl.locateSucc
import edu.cmu.cs.ls.keymaera.tactics.{Interpreter, Tactics, Config}
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest.{FlatSpec, Matchers, BeforeAndAfterEach}
import testHelper.ProofFactory._
import testHelper.SequentFactory._
import testHelper.StringConverter._

import scala.collection.immutable.Map

/**
 * Created by smitsch on 2/20/15.
 * @author Stefan Mitsch
 */
class PropositionalTacticTests extends FlatSpec with Matchers with BeforeAndAfterEach {

  val helper = new ProvabilityTestHelper((x) => println(x))
  val mathematicaConfig : Map[String, String] = Map("linkName" -> "/Applications/Mathematica.app/Contents/MacOS/MathKernel")

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
    Tactics.MathematicaScheduler = new Interpreter(new Mathematica)
    Tactics.MathematicaScheduler.init(mathematicaConfig)
    Tactics.KeYmaeraScheduler.init(Map())
  }

  override def afterEach() = {
    Tactics.MathematicaScheduler.shutdown()
    Tactics.KeYmaeraScheduler.shutdown()
    Tactics.MathematicaScheduler = null
    Tactics.KeYmaeraScheduler = null
  }

  "K Modal Modus Ponens" should "be [x:=2;](x>1 -> x>0) on [x:=2;]x>1 -> [x:=2;]x>0" in {
    import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl.kModalModusPonensT
    val tactic = locateSucc(kModalModusPonensT)
    getProofSequent(tactic, new RootNode(sucSequent("[x:=2;]x>1 -> [x:=2;]x>0".asFormula))) should be (
      sucSequent("[x:=2;](x>1 -> x>0)".asFormula))
  }
}
