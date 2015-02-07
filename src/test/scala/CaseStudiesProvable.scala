import java.io.File

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.Tactics.Tactic
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
 * @author Stefan Mitsch
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

  "ETCS-safety-allwrites" should "be provable with explicit strategy" in {
    import edu.cmu.cs.ls.keymaera.tactics.BranchLabels.{indInitLbl,indStepLbl,indUseCaseLbl}
    import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl.onBranch
    import Tactics.NilT

    import scala.language.postfixOps
    val file = new File("examples/dev/t/tactics/ETCS-safety-allwrites.key")
    val s = parseToSequent(file)

    // sub strategies for SB cases
    def subsubtactic(testTactic: Tactic) = (locateSucc(boxSeqT) ~
      ((locateSucc(boxTestT) & locateSucc(ImplyRightT)) | locateSucc(boxAssignT) | locateSucc(boxNDetAssign))*) &
      (locateAnte(AndLeftT)*) & locateSucc(AndRightT) &&
      (List(19,18,17,16,15,13,9,8,7,4,3).foldLeft(NilT)((t, i) => t & eqLeft(exhaustive = true)(AntePosition(i)) & hideT(AntePosition(i))) &
        testTactic,
        NilT) & arithmeticT

    val subtactic = ((locateSucc(boxSeqT) ~
      ((locateSucc(boxTestT) & locateSucc(ImplyRightT)) | locateSucc(boxNDetAssign)))*) &
      locateAnte(AndLeftT) ~ locateSucc(boxAssignT) & locateSucc(boxSeqT) & locateSucc(boxChoiceT) &
      locateSucc(AndRightT) && (debugT("choice 2.2.*.1") & subsubtactic(locateAnte(OrLeftT)),
                                debugT("choice 2.2.*.2") & subsubtactic(locateAnte(NotLeftT) & locateSucc(OrRightT)))

    // main strategy
    val tactic = locateSucc(ImplyRightT) & (locateAnte(AndLeftT)*) &
      locateSucc(inductionT(Some("v^2-d^2 <= 2*b*(m-z) & d>=0".asFormula))) &
      onBranch(
        (indInitLbl, locateSucc(AndRightT) && (AxiomCloseT(AntePosition(4), SuccPosition(0)),
                                               AxiomCloseT(AntePosition(3), SuccPosition(0)))),
        (indStepLbl, debugT("step") & List(5,4,3).foldLeft(NilT)((t, i) => t & hideT(AntePosition(i))) ~ locateSucc(skolemizeT) &
          locateSucc(ImplyRightT) & locateAnte(AndLeftT) & locateSucc(boxChoiceT) & locateSucc(AndRightT) &&
          (debugT("choice 1") & ((locateSucc(boxSeqT) ~ (locateSucc(boxAssignT) | locateSucc(boxNDetAssign)))*) &
                                locateSucc(boxTestT) & locateSucc(ImplyRightT) & (locateAnte(AndLeftT)*) &
                                locateSucc(AndRightT) && (/* v,z not written without self-assignment */ arithmeticT,
                                                          AxiomCloseT(AntePosition(12), SuccPosition(0))),
            debugT("choice 2") & locateSucc(boxChoiceT) & locateSucc(AndRightT) &&
              /* {state:=brake} */
              (debugT("choice 2.1") & ((locateSucc(boxSeqT) ~ locateSucc(boxAssignT))*) &
                locateSucc(AndRightT) && /* v,z,d,m, etc. not written without self-assignment */
                  /* explicit equality rewriting, just for demo purposes -> see eqLeft above for alternative */
                  /* numbering in positions: 0 -> lhs, 1 -> rhs
                   * e.g. in v^2-d^2 <= 2*b*(m-z) 0::0 refers to v^2, 0::0::0 to v, 0::0::1 to 2, 0::1::0 to d
                   *                              1::1::0 to m, 1::1::1 to z, 1::0 to 2*b
                   */
                  (equalityRewriting(AntePosition(7), SuccPosition(0, PosInExpr(0::0::0::Nil))) & hideT(SuccPosition(0)) &
                    equalityRewriting(AntePosition(9), SuccPosition(0, PosInExpr(0::1::0::Nil))) & hideT(SuccPosition(0)) &
                    equalityRewriting(AntePosition(11), SuccPosition(0, PosInExpr(1::1::0::Nil))) & hideT(SuccPosition(0)) &
                    equalityRewriting(AntePosition(8), SuccPosition(0, PosInExpr(1::1::1::Nil))) & hideT(SuccPosition(0)) &
                    AxiomCloseT(AntePosition(5), SuccPosition(0)),
                   equalityRewriting(AntePosition(9), SuccPosition(0, PosInExpr(0::Nil))) & hideT(SuccPosition(0)) &
                     AxiomCloseT(AntePosition(6), SuccPosition(0))
                  ),
                debugT("choice 2.2") & ((locateSucc(boxSeqT) ~ locateSucc(boxAssignT))*) &
                  locateSucc(boxChoiceT) & locateSucc(AndRightT) &&
                  (debugT("choice 2.2.1") & subtactic,
                    debugT("choice 2.2.2") & subtactic
                  )
              )
            )),
        (indUseCaseLbl, List(5,4,3).foldLeft(NilT)((t, i) => t & hideT(AntePosition(i))) ~ locateSucc(skolemizeT) &
          locateSucc(ImplyRightT) & locateAnte(AndLeftT) & arithmeticT))

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  it should "be provable with master strategy" in {
    val file = new File("examples/dev/t/tactics/ETCS-safety-allwrites.key")
    val s = parseToSequent(file)
    helper.runTactic(master(new Generate("v^2-d^2 <= 2*b*(m-z) & d>=0".asFormula), true), new RootNode(s)) shouldBe 'closed
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
