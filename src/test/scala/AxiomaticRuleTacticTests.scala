import edu.cmu.cs.ls.keymaera.core.{RootNode, Mathematica, KeYmaera}
import edu.cmu.cs.ls.keymaera.tactics.{AxiomaticRuleTactics, Interpreter, Tactics}
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}
import testHelper.StringConverter._
import testHelper.SequentFactory._

import scala.collection.immutable.Map

/**
 * Created by smitsch on 3/16/15.
 * @author Stefan Mitsch
 */
class AxiomaticRuleTacticTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  // TODO mathematica is only necessary because of ProofFactory -> make ProofFactory configurable

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

  "Box congruence" should "congruence rewrite with primes" in {
    val s = sucSequent("[x':=1;](x*y())'<=0 <-> [x':=1;]x'*y()<=0".asFormula)
    val tactic = AxiomaticRuleTactics.boxCongruenceT

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "(x*y())'<=0 <-> x'*y()<=0".asFormula
  }

}
