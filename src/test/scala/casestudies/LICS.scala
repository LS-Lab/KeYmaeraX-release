package casestudies

import java.io.File

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.locateAnte
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.locateSucc
import edu.cmu.cs.ls.keymaera.tactics.Tactics.PositionTactic
import edu.cmu.cs.ls.keymaera.tactics.Interpreter
import edu.cmu.cs.ls.keymaera.tactics.BranchLabels
import edu.cmu.cs.ls.keymaera.tactics.Tactics
import edu.cmu.cs.ls.keymaera.tactics._
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, FlatSpec, Matchers}
import testHelper.ParserFactory._
import edu.cmu.cs.ls.keymaera.tactics.ODETactics.diffSolution
import edu.cmu.cs.ls.keymaera.tactics.HybridProgramTacticsImpl.wipeContextInductionT
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl._
import testHelper.StringConverter._
import BranchLabels._

/**
 * Created by ran on 3/24/15.
 */
class LICS extends FlatSpec with Matchers with BeforeAndAfterEach {
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

  def ls(t: PositionTactic) = locateSucc(t)
  def la(t: PositionTactic) = locateAnte(t)

  "LICS 4a" should "be provable" in {
    val file = new File("examples/tutorials/lics/lics-4a.key")
    val s = parseToSequent(file)

    val plant = debugT("plant") & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxSeqT) & ls(boxAssignT) &
      ls(diffSolution(None)) & ls(ImplyRightT)

    val tactic = ls(ImplyRightT) & (la(AndLeftT)*) &
      ls(wipeContextInductionT(Some("v^2<=2*b*(m-x)".asFormula))) & onBranch(
      (indInitLbl, debugT("Base Case") & AxiomCloseT),
      (indUseCaseLbl, debugT("Use Case") & ls(ImplyRightT) & arithmeticT),
      (indStepLbl, debugT("Step") & ls(ImplyRightT) & ls(boxSeqT) & ls(boxChoiceT) & ls(AndRightT) &&
        (debugT("Case 1") & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxAssignT),
         debugT("Case 2") & ls(boxAssignT)) &
       plant & (AxiomCloseT | arithmeticT))
    )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  it should "be provable automatically" in {
    val file = new File("examples/tutorials/lics/lics-4a.key")
    val s = parseToSequent(file)

    helper.runTactic(master(new Generate("v^2<=2*b*(m-x)".asFormula), true), new RootNode(s)) shouldBe 'closed
  }
}
