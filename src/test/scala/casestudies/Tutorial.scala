package casestudies

import java.io.File

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.locateAnte
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.locateSucc
import edu.cmu.cs.ls.keymaera.tactics.Tactics.PositionTactic
import edu.cmu.cs.ls.keymaera.tactics.{Interpreter, BranchLabels, Tactics}
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, FlatSpec, Matchers}
import testHelper.ParserFactory._
import edu.cmu.cs.ls.keymaera.tactics.ODETactics.diffSolution
import edu.cmu.cs.ls.keymaera.tactics.HybridProgramTacticsImpl.wipeContextInductionT
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl._
import testHelper.StringConverter._
import BranchLabels._

import scala.language.postfixOps


import scala.collection.immutable.Map

/**
 * Created by smitschon 2/27/15.
 * @author Stefan Mitsch
 */
class Tutorial extends FlatSpec with Matchers with BeforeAndAfterEach {

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

  "Example 1" should "be provable" in {
    val file = new File("examples/dev/t/casestudies/tutorial/example1.key")
    val s = parseToSequent(file)

    val tactic = ls(ImplyRightT) & la(AndLeftT) & ls(diffSolution(None)) & ls(ImplyRightT) & arithmeticT

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  "Example 1a" should "be provable" in {
    val file = new File("examples/dev/t/casestudies/tutorial/example1a.key")
    val s = parseToSequent(file)

    val tactic = ls(ImplyRightT) & (la(AndLeftT)*) & ls(diffSolution(None)) & ls(ImplyRightT) & arithmeticT

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  "Example 2" should "be provable" in {
    val file = new File("examples/dev/t/casestudies/tutorial/example2.key")
    val s = parseToSequent(file)

    val tactic = ls(ImplyRightT) & la(AndLeftT) & ls(wipeContextInductionT(Some("v>=0".asFormula))) & onBranch(
      (indInitLbl, debugT("Base Case") & (la(AndLeftT)*) & AxiomCloseT),
      (indUseCaseLbl, debugT("Use Case") & ls(ImplyRightT) & AxiomCloseT),
      (indStepLbl, debugT("Step") & ls(ImplyRightT) & ls(boxSeqT) &
        ls(boxChoiceT) & ls(AndRightT) && (
        debugT("Case 1") & ls(boxAssignT),
        ls(boxChoiceT) & ls(AndRightT) && (
          debugT("Case 2") & ls(boxAssignT),
          debugT("Case 3") & ls(boxAssignT)
          )
        ) & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(diffSolution(None)) & ls(ImplyRightT) & arithmeticT)
    )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  // TODO not implemented yet: evolution domain must hold in the beginning
  ignore /*"Example 3a"*/ should "Example 3a be provable" in {
    val file = new File("examples/dev/t/casestudies/tutorial/example3a.key")
    val s = parseToSequent(file)

    val plant = debugT("plant") & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxChoiceT) & ls(AndRightT) &&
      (debugT("evolution domain <=") & ls(diffSolution(None)) & ls(ImplyRightT),
       debugT("evolution domain >=") & ls(diffSolution(None)) & ls(ImplyRightT))

    val tactic = ls(ImplyRightT) & (la(AndLeftT)*) &
      ls(wipeContextInductionT(Some("v>=0 & x+v^2/(2*B) <= S".asFormula))) & onBranch(
      (indInitLbl, debugT("Base Case") & (la(AndLeftT)*) & ls(AndRightT) & arithmeticT),
      (indUseCaseLbl, debugT("Use Case") & ls(ImplyRightT) & arithmeticT),
      (indStepLbl, debugT("Step") & ls(ImplyRightT) & la(AndLeftT) & ls(boxSeqT) & ls(boxChoiceT) & ls(AndRightT) && (
        debugT("Case 1") & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxAssignT),
        ls(boxChoiceT) & ls(AndRightT) && (
          debugT("Case 2") & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxAssignT),
          debugT("Case 3") & ls(boxAssignT)
          )
        ) & plant & (la(AndLeftT)*) & (ls(AndRightT)*) & (AxiomCloseT | arithmeticT)
      )
    )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  // TODO not implemented yet: evolution domain must hold in the beginning, IfThenElse
  ignore /*"Example 4a"*/ should "Example 4a be provable" in {
    val file = new File("examples/dev/t/casestudies/tutorial/example4a.key")
    val s = parseToSequent(file)

    val plant = debugT("plant") & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(diffSolution(None)) & ls(ImplyRightT)

    val tactic = ls(ImplyRightT) & (la(AndLeftT)*) &
      ls(wipeContextInductionT(Some("v <= V".asFormula))) & onBranch(
      (indInitLbl, debugT("Base Case") & arithmeticT),
      (indUseCaseLbl, debugT("Use Case") & ls(ImplyRightT) & arithmeticT),
      (indStepLbl, debugT("Step") & ls(ImplyRightT) & ls(boxSeqT) & plant & arithmeticT)
    )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  // TODO not implemented yet: evolution domain must hold in the beginning, IfThenElse
  ignore /*"Example 4b"*/ should "Example 4b be provable" in {
    val file = new File("examples/dev/t/casestudies/tutorial/example4b.key")
    val s = parseToSequent(file)

    val plant = debugT("plant") & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(diffSolution(None)) & ls(ImplyRightT)

    val tactic = ls(ImplyRightT) & (la(AndLeftT)*) &
      ls(wipeContextInductionT(Some("v <= V".asFormula))) & onBranch(
      (indInitLbl, debugT("Base Case") & arithmeticT),
      (indUseCaseLbl, debugT("Use Case") & ls(ImplyRightT) & arithmeticT),
      (indStepLbl, debugT("Step") & ls(ImplyRightT) & ls(boxSeqT) & ls(boxAssignT) & plant & arithmeticT)
    )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  // TODO not implemented yet: evolution domain must hold in the beginning, IfThenElse
  ignore /*"Example 4c"*/ should "Example 4c be provable" in {
    val file = new File("examples/dev/t/casestudies/tutorial/example4c.key")
    val s = parseToSequent(file)

    val plant = debugT("plant") & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxChoiceT) & ls(AndRightT) &
      ls(diffSolution(None)) & ls(ImplyRightT)

    val tactic = ls(ImplyRightT) & (la(AndLeftT)*) &
      ls(wipeContextInductionT(Some("v <= V".asFormula))) & onBranch(
      (indInitLbl, debugT("Base Case") & arithmeticT),
      (indUseCaseLbl, debugT("Use Case") & ls(ImplyRightT) & arithmeticT),
      (indStepLbl, debugT("Step") & ls(ImplyRightT) & ls(boxSeqT)
        )
    )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  "Example 5 with simple control" should "be provable" in {
    val file = new File("examples/dev/t/casestudies/tutorial/example5_simplectrl.key")
    val s = parseToSequent(file)

    val plant = debugT("plant") & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxSeqT) & ls(boxAssignT) &
      ls(diffSolution(None)) & ls(ImplyRightT)

    val tactic = ls(ImplyRightT) & (la(AndLeftT)*) &
      ls(wipeContextInductionT(Some("v >= 0 & x+v^2/(2*B) <= S".asFormula))) & onBranch(
      (indInitLbl, debugT("Base Case") & ls(AndRightT) & AxiomCloseT),
      (indUseCaseLbl, debugT("Use Case") & ls(ImplyRightT) & arithmeticT),
      (indStepLbl, debugT("Step") & ls(ImplyRightT) & la(AndLeftT) & ls(boxSeqT) & ls(boxAssignT) & plant &
        arithmeticT)
    )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  "Example 5" should "be provable" in {
    val file = new File("examples/dev/t/casestudies/tutorial/example5.key")
    val s = parseToSequent(file)

    val plant = debugT("plant") & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxSeqT) & ls(boxAssignT) &
      ls(diffSolution(None)) & ls(ImplyRightT)

    val tactic = ls(ImplyRightT) & (la(AndLeftT)*) &
      ls(wipeContextInductionT(Some("v >= 0 & x+v^2/(2*B) <= S".asFormula))) & onBranch(
      (indInitLbl, debugT("Base Case") & ls(AndRightT) & AxiomCloseT),
      (indUseCaseLbl, debugT("Use Case") & ls(ImplyRightT) & arithmeticT),
      (indStepLbl, debugT("Step") & ls(ImplyRightT) & la(AndLeftT) & ls(boxSeqT) & ls(boxChoiceT) & ls(AndRightT) && (
        debugT("Case 1") & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxAssignT),
        ls(boxChoiceT) & ls(AndRightT) && (
          debugT("Case 2") & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxAssignT),
          debugT("Case 3") & ls(boxAssignT)
          )
        ) & plant & ls(AndRightT) & (AxiomCloseT | arithmeticT)
      )
    )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  "Example 6" should "be provable" in {
    val file = new File("examples/dev/t/casestudies/tutorial/example6.key")
    val s = parseToSequent(file)

    val plant = debugT("plant") & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxSeqT) & ls(boxAssignT) &
      ls(diffSolution(None)) & ls(ImplyRightT)

    val tactic = ls(ImplyRightT) & (la(AndLeftT)*) &
      ls(wipeContextInductionT(Some("v >= 0 & x+v^2/(2*B) <= S".asFormula))) & onBranch(
      (indInitLbl, debugT("Base Case") & ls(AndRightT) & AxiomCloseT),
      (indUseCaseLbl, debugT("Use Case") & ls(ImplyRightT) & arithmeticT),
      (indStepLbl, debugT("Step") & ls(ImplyRightT) & la(AndLeftT) & ls(boxSeqT) & ls(boxChoiceT) & ls(AndRightT) && (
        debugT("Case 1") & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxSeqT) & ls(boxNDetAssign) &
          ls(boxTestT) & ls(ImplyRightT) & la(AndLeftT),
        ls(boxChoiceT) & ls(AndRightT) && (
          debugT("Case 2") & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxAssignT),
          debugT("Case 3") & ls(boxAssignT)
          )
        ) & plant & ls(AndRightT) & (AxiomCloseT | arithmeticT)
        )
    )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  "Example 7" should "be provable" in {
    val file = new File("examples/dev/t/casestudies/tutorial/example7.key")
    val s = parseToSequent(file)

    val plant = debugT("plant") & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxSeqT) & ls(boxAssignT) &
      ls(diffSolution(None)) & ls(ImplyRightT)

    val tactic = ls(ImplyRightT) & (la(AndLeftT)*) &
      ls(wipeContextInductionT(Some("v >= 0 & x+v^2/(2*b) <= S".asFormula))) & onBranch(
      (indInitLbl, debugT("Base Case") & ls(AndRightT) & AxiomCloseT),
      (indUseCaseLbl, debugT("Use Case") & ls(ImplyRightT) & arithmeticT),
      (indStepLbl, debugT("Step") & ls(ImplyRightT) & la(AndLeftT) & ls(boxSeqT) & ls(boxChoiceT) & ls(AndRightT) && (
        debugT("Case 1") & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxSeqT) & ls(boxNDetAssign) &
          ls(boxTestT) & ls(ImplyRightT) & la(AndLeftT),
        ls(boxChoiceT) & ls(AndRightT) && (
          debugT("Case 2") & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxAssignT),
          debugT("Case 3") & ls(boxSeqT) & ls(boxNDetAssign) & ls(boxTestT) & ls(ImplyRightT) & la(AndLeftT)
          )
        ) & plant & ls(AndRightT) & (AxiomCloseT | arithmeticT)
        )
    )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  // TODO not yet implemented: differential inequalities
  // Example 8

  "Example 9a" should "be provable" in {
    val file = new File("examples/dev/t/casestudies/tutorial/example9a.key")
    val s = parseToSequent(file)

    val tactic = ls(ImplyRightT) & (la(AndLeftT)*) & ls(diffInvariant)

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  "Example 9b" should "be provable" in {
    val file = new File("examples/dev/t/casestudies/tutorial/example9b.key")
    val s = parseToSequent(file)

    val plant = debugT("Plant") & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & la(AndLeftT) &
      ls(diffCutT("xm() <= x".asFormula)) & onBranch(
      (cutShowLbl, debugT("Show cut 1") & ls(diffInvariant)),
      (cutUseLbl, debugT("Use cut 1") & ls(diffCutT("5/4*(x-xr())^2 + (x-xr())*v/2 + v^2/4 < ((S() - xm())/2)^2".asFormula)) & onBranch(
        (cutShowLbl, debugT("Show cut 2") & ls(diffInvariant)),
        (cutUseLbl, debugT("Use cut 2") & ls(diffWeakenT) & ls(ImplyRightT) & debugT("Result Weaken"))
          )
        )
      )

    val tactic = ls(ImplyRightT) & (la(AndLeftT)*) &
      ls(wipeContextInductionT(Some("v >= 0 & xm() <= x & xr() = (xm() + S())/2 & 5/4*(x-xr())^2 + (x-xr())*v/2 + v^2/4 < ((S() - xm())/2)^2".asFormula))) & onBranch(
      (indInitLbl, debugT("Base case") & (ls(AndRightT)*) & AxiomCloseT),
      (indStepLbl, debugT("Step") & ls(ImplyRightT) & (la(AndLeftT)*) & ls(boxSeqT) & ls(boxChoiceT) & ls(AndRightT) &&
        (debugT("Case 1") & ls(boxSeqT) & ls(boxAssignT) & ls(boxSeqT) & ls(boxAssignT) & ls(boxTestT) &
          ls(ImplyRightT) & debugT("Result 1"),
         debugT("Case 2") & ls(boxSeqT) & ls(boxAssignT) & ls (boxAssignT) & debugT("Result 2")
        ) & plant & (la(AndLeftT)*) & (ls(AndRightT)*) & AxiomCloseT
        ),
      (indUseCaseLbl, debugT("Use case") & ls(ImplyRightT) & arithmeticT)
      )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  // TODO needs better assignment tactic (when ODE is not first statement in subsequent modality, like in [w:=0;][c:=0; v'=w, w'=5;]1>0)
  ignore /* "Example 10"*/ should "Example 10 be provable" in {
    val file = new File("examples/dev/t/casestudies/tutorial/example10.key")
    val s = parseToSequent(file)

    // TODO
    val tactic = ls(ImplyRightT) & (la(AndLeftT)*) &
      ls(wipeContextInductionT(Some("v >= 0 & dx^2+dy^2 = 1 & r() != 0 & ((y >= ly -> (y-ly) + v^2/(2*B) < lw) | (y <= ly -> (ly-y) + v^2/(2*B) < lw))".asFormula))) & onBranch(
      (indInitLbl, debugT("Base case") & (ls(AndRightT)*) & (AxiomCloseT | arithmeticT)),
      (indStepLbl, debugT("Step") & ls(ImplyRightT) & (la(AndLeftT)*) & ls(boxSeqT) & ls(boxChoiceT) & ls(AndRightT) &&
        (debugT("Case 1") & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxSeqT) & ls(boxNDetAssign) & debugT("Result 1"),
         ls(boxChoiceT) & ls(AndRightT) && (
           debugT("Case 2") & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxSeqT) & ls(boxAssignT) &
             ls(boxSeqT) & ls(boxAssignT) & ls(boxSeqT) & ls(boxAssignT) & debugT("Result 2"),
           debugT("Case 3") & ls(boxSeqT) & ls(boxNDetAssign) & ls(boxSeqT) & ls(boxAssignT) & ls(boxSeqT) &
             ls(boxAssignT) & ls(boxTestT) & ls(ImplyRightT) & la(AndLeftT) & debugT("Result 3")
           )
        )
      ),
      (indUseCaseLbl, debugT("Use case") & ls(ImplyRightT) & arithmeticT)
    )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }
}
