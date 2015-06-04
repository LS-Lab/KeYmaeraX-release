package casestudies

import java.io.File

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.locateAnte
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.locateSucc
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.PositionTactic
import edu.cmu.cs.ls.keymaerax.tactics.Interpreter
import edu.cmu.cs.ls.keymaerax.tactics.BranchLabels
import edu.cmu.cs.ls.keymaerax.tactics.Tactics
import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.tools.{Mathematica, Z3, KeYmaera}
import testHelper.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, FlatSpec, Matchers}
import testHelper.ParserFactory._
import edu.cmu.cs.ls.keymaerax.tactics.ODETactics.diffSolution
import edu.cmu.cs.ls.keymaerax.tactics.HybridProgramTacticsImpl.wipeContextInductionT
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl._
import testHelper.StringConverter._
import BranchLabels._

import scala.collection.immutable.Map
import scala.language.postfixOps

/**
 * Created by ran on 3/24/15.
 * @author Ran Ji
 */
class BouncingBall extends FlatSpec with Matchers with BeforeAndAfterEach {
  val helper = new ProvabilityTestHelper((x) => println(x))
  val mathematicaConfig: Map[String, String] = helper.mathematicaConfig

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
    Tactics.MathematicaScheduler = new Interpreter(new Mathematica)
    Tactics.MathematicaScheduler.init(mathematicaConfig)
    Tactics.KeYmaeraScheduler.init(Map())
    Tactics.Z3Scheduler = Some(new Interpreter(new Z3))
    Tactics.Z3Scheduler.get.init(Map())
  }

  override def afterEach() = {
    Tactics.Z3Scheduler.get.shutdown()
    Tactics.MathematicaScheduler.shutdown()
    Tactics.KeYmaeraScheduler.shutdown()
    Tactics.Z3Scheduler = null
    Tactics.MathematicaScheduler = null
    Tactics.KeYmaeraScheduler = null
  }

  def ls(t: PositionTactic) = locateSucc(t)
  def la(t: PositionTactic) = locateAnte(t)

  "bouncing ball tout" should "be provable" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/simple/bouncing-ball/bouncing-ball-tout.key"))

    val tactic = ls(ImplyRightT) & (la(AndLeftT)*) & ls(wipeContextInductionT(Some("v^2<=2*g()*(H-h) & h>=0".asFormula))) & onBranch(
      (indInitLbl, debugT("Base Case") & ls(AndRightT) &&
        (AxiomCloseT,
          AxiomCloseT)),
      (indUseCaseLbl, debugT("Use Case") & ls(ImplyRightT) & (la(AndLeftT)*) & ls(AndRightT) &&
        (AxiomCloseT,
          arithmeticT)),
      (indStepLbl, debugT("Step") & ls(ImplyRightT) & (la(AndLeftT)*) & ls(boxSeqT) &
        ls(diffSolution(None)) & debugT("open goal")
        & ls(ImplyRightT) & (la(AndLeftT)*) &
        ls(boxChoiceT) & ls(AndRightT) &&
        (ls(boxTestT) & ls(ImplyRightT) & ls(AndRightT) &&
          (arithmeticT,
            AxiomCloseT),
          ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxAssignT) & ls(AndRightT) &&
            (arithmeticT,
              AxiomCloseT)
          )
        )
    )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  it should "be provable automatically with Mathematica" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/simple/bouncing-ball/bouncing-ball-tout.key"))
    helper.runTactic(master(new Generate("v^2<=2*g()*(H-h) & h>=0".asFormula), true, "Mathematica"), new RootNode(s)) shouldBe 'closed
  }

  it should "be provable automatically with Z3" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/simple/bouncing-ball/bouncing-ball-tout.key"))
    helper.runTactic(master(new Generate("v^2<=2*g()*(H-h) & h>=0".asFormula), true, "Z3"), new RootNode(s)) shouldBe 'closed
  }

}
