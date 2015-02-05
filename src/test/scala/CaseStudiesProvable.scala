import java.io.File

import edu.cmu.cs.ls.keymaera.core.{Formula, ProofNode, RootNode}
import edu.cmu.cs.ls.keymaera.tactics.{Generate, TacticLibrary, Tactics, Config}
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest.{PrivateMethodTester, BeforeAndAfterEach, Matchers, FlatSpec}
import scala.collection.immutable.Map
import testHelper.ParserFactory._
import testHelper.StringConverter._
import TacticLibrary._

/**
 * Created by ran on 2/4/15.
 * @author Ran Ji
 */
class CaseStudiesProvable extends FlatSpec with Matchers with BeforeAndAfterEach with PrivateMethodTester {

  Config.mathlicenses = 1
  Config.maxCPUs = 1

  val helper = new ProvabilityTestHelper((x) => println(x))
  val mathematicaConfig : Map[String, String] = Map("linkName" -> "/Applications/Mathematica.app/Contents/MacOS/MathKernel")

  override def beforeEach() = {
    Tactics.MathematicaScheduler.init(mathematicaConfig)
    Tactics.KeYmaeraScheduler.init(Map())
  }

  override def afterEach() = {
    Tactics.MathematicaScheduler.shutdown()
    Tactics.KeYmaeraScheduler.shutdown()
  }

  "AxiomClose" should "be provable" in {
    val file = new File("examples/dev/t/tactics/AxiomClose.key")
    val s = parseToSequent(file)

    helper.runTactic(default, new RootNode(s)).isClosed() should be (true)
  }

  "DecomposeQuant" should "be provable" in {
    val file = new File("examples/dev/t/tactics/DecomposeQuant.key")
    val s = parseToSequent(file)

    helper.runTactic(default, new RootNode(s)).isClosed() should be (true)
  }

  "EqualityRewriting" should "be provable" in {
    val file = new File("examples/dev/t/tactics/EqualityRewriting.key")
    val s = parseToSequent(file)

    helper.runTactic(default, new RootNode(s)).isClosed() should be (true)
  }

  "ETCS-essentials-noloop" should "be provable" in {
    val file = new File("examples/dev/t/tactics/ETCS-essentials-noloop.key")
    val s = parseToSequent(file)

    helper.runTactic(default, new RootNode(s)).isClosed() should be (true)
  }

  "ETCS-essentials" should "be provable" in {
    val file = new File("examples/dev/t/tactics/ETCS-essentials.key")
    val s = parseToSequent(file)

    helper.runTactic(master(new Generate("v^2<=2*b*(m-z)".asFormula), true), new RootNode(s)).isClosed() should be (true)
  }


  ignore should "prove ETCS-safety" in {
    val file = new File("examples/dev/t/tactics/ETCS-safety.key")
    val s = parseToSequent(file)

    helper.runTactic(master(new Generate("v^2 - d^2 <= 2*b*(m-z) & d >= 0".asFormula), true), new RootNode(s)).isClosed() should be (true)
  }

  "Saturable" should "be provable" in {
    val file = new File("examples/dev/t/tactics/Saturable.key")
    val s = parseToSequent(file)

    helper.runTactic(default, new RootNode(s)).isClosed() should be (true)
  }

  ignore should "prove SimpleDiff" in {
    val file = new File("examples/dev/t/tactics/SimpleDiff.key")
    val s = parseToSequent(file)

    helper.runTactic(default, new RootNode(s)).isClosed() should be (true)
  }
}
