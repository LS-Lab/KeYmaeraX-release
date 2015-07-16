/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
import edu.cmu.cs.ls.keymaerax.core.{AntePos, Expression, Sequent}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.{PositionTactic, Tactic}
import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.tools.{Z3, Mathematica, KeYmaera}
import testHelper.ProvabilityTestHelper
import org.scalatest.{PrivateMethodTester, BeforeAndAfterEach, Matchers, FlatSpec}
import scala.collection.immutable
import scala.collection.immutable.Map
import testHelper.ParserFactory._
import TacticLibrary._
import edu.cmu.cs.ls.keymaerax.tactics.BranchLabels.{indInitLbl,indStepLbl,indUseCaseLbl}
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl.onBranch
import edu.cmu.cs.ls.keymaerax.tactics.HybridProgramTacticsImpl.wipeContextInductionT
import Tactics.NilT

import scala.language.postfixOps

/**
 * Created by ran on 2/4/15.
 * @author Ran Ji
 * @author Stefan Mitsch
 */
class CaseStudiesProvable extends FlatSpec with Matchers with BeforeAndAfterEach with PrivateMethodTester {
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
    Tactics.MathematicaScheduler.shutdown()
    Tactics.KeYmaeraScheduler.shutdown()
    Tactics.Z3Scheduler.get.shutdown()
    Tactics.MathematicaScheduler = null
    Tactics.KeYmaeraScheduler = null
    Tactics.Z3Scheduler = null
  }

  def ls(t: PositionTactic) = locateSucc(t)
  def la(t: PositionTactic) = locateAnte(t)

  "AxiomClose" should "be provable with Mathematica" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/dev/t/tactics/AxiomClose.key"))
    helper.runTactic(default, new RootNode(s)) shouldBe 'closed
  }

  it should "be provable with Z3" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/dev/t/tactics/AxiomClose.key"))
    helper.runTactic(default("Z3"), new RootNode(s)) shouldBe 'closed
  }

  "DecomposeQuant" should "be provable with Mathematica" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/dev/t/tactics/DecomposeQuant.key"))
    helper.runTactic(default, new RootNode(s)) shouldBe 'closed
  }

  it should "be provable with Z3" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/dev/t/tactics/DecomposeQuant.key"))
    helper.runTactic(default("Z3"), new RootNode(s)) shouldBe 'closed
  }

  "EqualityRewriting" should "be provable with Mathematica" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/dev/t/tactics/EqualityRewriting.key"))
    helper.runTactic(default, new RootNode(s)) shouldBe 'closed
  }

  it should "be provable with Z3" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/dev/t/tactics/EqualityRewriting.key"))
    helper.runTactic(default("Z3"), new RootNode(s)) shouldBe 'closed
  }

  "ETCS-essentials-noloop" should "be provable with Mathematica" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/dev/t/tactics/ETCS-essentials-noloop.key"))
    helper.runTactic(default, new RootNode(s)) shouldBe 'closed
  }

  it should "be provable with Z3" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/dev/t/tactics/ETCS-essentials-noloop.key"))
    helper.runTactic(default("Z3"), new RootNode(s)) shouldBe 'closed
  }

  "ETCS-essentials" should "be provable with Mathematica" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/dev/t/tactics/ETCS-essentials.key"))
    helper.runTactic(master(new Generate("v^2<=2*b*(m-z)".asFormula), true, "Mathematica"), new RootNode(s)) shouldBe 'closed
  }

  it should "be provable with Z3" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/dev/t/tactics/ETCS-essentials.key"))
    helper.runTactic(master(new Generate("v^2<=2*b*(m-z)".asFormula), true, "Z3"), new RootNode(s)) shouldBe 'closed
  }

  "Stuttering" should "be provable with Mathematica" in {
    val tactic = ls(ImplyRightT) &
      ls(wipeContextInductionT(Some("x <= y".asFormula))) &
      onBranch(
        (indInitLbl, AxiomCloseT(AntePosition(0), SuccPosition(0))),
        (indStepLbl, debugT("step") & ls(ImplyRightT) &
          ls(boxChoiceT) & ls(AndRightT) &
          ((ls(boxSeqT) ~ ls(boxAssignT))*) & arithmeticT),
        (indUseCaseLbl, ls(ImplyRightT) & AxiomCloseT(AntePosition(0), SuccPosition(0)))
      )

    val s = parseToSequent(getClass.getResourceAsStream("/examples/dev/t/tactics/Stuttering-allwrites.key"))
    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
    // loops where not all branches write the same variables are not yet supported
//    helper.runTactic(tactic, new RootNode(parseToSequent(this.getClass.getResourceAsStream("/examples/dev/t/tactics/Stuttering.key")))) shouldBe 'closed
  }

  it should "be provable automatically with Mathematica" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/dev/t/tactics/Stuttering-allwrites.key"))
    helper.runTactic(master(new Generate("x <= y".asFormula), true, "Mathematica"), new RootNode(s)) shouldBe 'closed
  }

  it should "be provable automatically with Z3" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/dev/t/tactics/Stuttering-allwrites.key"))
    helper.runTactic(master(new Generate("x <= y".asFormula), true, "Z3"), new RootNode(s)) shouldBe 'closed
  }

  "ETCS safety all-writes" should "be provable automatically with Mathematica" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/dev/t/tactics/ETCS-safety-allwrites.key"))
    helper.runTactic(master(new Generate("v^2-d^2 <= 2*b*(m-z) & d>=0".asFormula), true, "Mathematica"), new RootNode(s)) shouldBe 'closed
  }

  it should "be provable automatically with Z3" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/dev/t/tactics/ETCS-safety-allwrites.key"))
    helper.runTactic(master(new Generate("v^2-d^2 <= 2*b*(m-z) & d>=0".asFormula), true, "Z3"), new RootNode(s)) shouldBe 'closed
  }

  it should "be provable with explicit strategy" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/dev/t/tactics/ETCS-safety-allwrites.key"))

    // sub strategies for SB cases
    def subsubtactic(testTactic: Tactic) = (ls(boxSeqT) ~
      ((ls(boxTestT) & ls(ImplyRightT)) | ls(boxAssignT) | (ls(boxNDetAssign) & ls(skolemizeT)))*) &
      (la(AndLeftT)*) & ls(AndRightT) &&
      (testTactic & arithmeticT & debugT("result 1"), /* d_2 */ eqLeft(exhaustive=true)(AntePosition(19)) & AxiomCloseT ~ debugT("result 2"))

    val subtactic = ((ls(boxSeqT) ~
      ((ls(boxTestT) & ls(ImplyRightT)) | (ls(boxNDetAssign) & ls(skolemizeT))))*) &
      la(AndLeftT) ~ ls(boxAssignT) & ls(boxSeqT) & ls(boxChoiceT) &
      ls(AndRightT) && (debugT("choice 2.2.*.1") & subsubtactic(la(OrLeftT)),
      debugT("choice 2.2.*.2") & subsubtactic(la(NotLeftT) & ls(OrRightT) & arithmeticT))

    // main strategy
    val tactic = ls(ImplyRightT) & (la(AndLeftT)*) &
      ls(inductionT(Some("v^2-d^2 <= 2*b*(m-z) & d>=0".asFormula))) &
      onBranch(
        (indInitLbl, debugT("base case") & ls(AndRightT) & AxiomCloseT),
        (indStepLbl, debugT("step") & ls(ImplyRightT) & la(AndLeftT) & ls(boxChoiceT) & ls(AndRightT) &&
          (debugT("choice 1") & ((ls(boxSeqT) ~ (ls(boxAssignT) | ls(boxNDetAssign)) ~ ls(skolemizeT))*) &
            ls(boxTestT) & ls(ImplyRightT) & (la(AndLeftT)*) &
            ls(AndRightT) && (/* v,z not written without self-assignment */ arithmeticT ~ debugT("choice 1 result (should not be displayed)"),
            AxiomCloseT ~ debugT("choice 1 result 2 (should not be displayed)")),
            debugT("choice 2") & ls(boxChoiceT) & ls(AndRightT) &&
              /* {state:=brake} */
              (debugT("choice 2.1") & ((ls(boxSeqT) ~ ls(boxAssignT))*) & la(AndLeftT) & debugT("After assign") &
                ls(AndRightT) && /* v,z,d,m, etc. not written without self-assignment */
                /* explicit equality rewriting, just for demo purposes -> see eqLeft above for alternative */
                /* numbering in positions: 0 -> lhs, 1 -> rhs
                 * e.g. in v^2-d^2 <= 2*b*(m-z) 0::0 refers to v^2, 0::0::0 to v, 0::0::1 to 2, 0::1::0 to d
                 *                              1::1::0 to m, 1::1::1 to z, 1::0 to 2*b
                 */
                (/* v_3 */eqLeft(exhaustive=true)(AntePosition(12)) &
                  /* d_2 */eqLeft(exhaustive=true)(AntePosition(19)) &
                  /* m_2 */eqLeft(exhaustive=true)(AntePosition(17)) &
                  /* z_3 */ eqLeft(exhaustive=true)(AntePosition(13)) & AxiomCloseT,
                  /* d_2 */ eqLeft(exhaustive=true)(AntePosition(19)) & AxiomCloseT
                  ),
                debugT("choice 2.2") & ((ls(boxSeqT) ~ ls(boxAssignT))*) &
                  ls(boxChoiceT) & ls(AndRightT) &&
                  (debugT("choice 2.2.1") & subtactic,
                    debugT("choice 2.2.2") & subtactic
                    )
                )
            )),
        (indUseCaseLbl, debugT("use case") & ls(ImplyRightT) & la(AndLeftT) & arithmeticT ~ debugT("use case result (should never be displayed)")))

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  "Saturable" should "be provable with Mathematica" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/dev/t/tactics/Saturable.key"))
    helper.runTactic(default("Mathematica"), new RootNode(s)) shouldBe 'closed
  }

  it should "be provable with Z3" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/dev/t/tactics/Saturable.key"))
    helper.runTactic(default("Z3"), new RootNode(s)) shouldBe 'closed
  }

  ignore should "prove SimpleDiff" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/dev/t/tactics/SimpleDiff.key"))
    helper.runTactic(default, new RootNode(s)) shouldBe 'closed
  }

  "simple car" should "not fail due to new ^' tactic" in {
//    val sequent = new Sequent(Nil, immutable.IndexedSeq(
//      "2!=0".asFormula, "(kxtime_1^2)'=2*kxtime_1^(2-1)*(kxtime_1)'".asFormula
//    ),immutable.IndexedSeq(
//
//    ))
    val node = helper.formulaToNode("[{x'=v,v'=(a()),kxtime_1'=(0*kxtime_1+1) & (true&kxtime_1>=kxtime_4()&v=v_2()+a()*kxtime_1)}][kxtime_1':=0*kxtime_1+1;][v':=a();][x':=v;](x)'=(0*2-1*0)/2^2*(2*x_2()+2*v_2()*kxtime_1+a()*kxtime_1^2)+1/2*(0*x_2()+2*0+((0*v_2()+2*0)*kxtime_1+2*v_2()*(kxtime_1)')+(0*kxtime_1^2+a()*(kxtime_1^2)'))".asFormula)

    val tactic = SearchTacticsImpl.locateTerm(SyntacticDerivationInContext.PowerDerivativeT, false)

    helper.runTactic(tactic, node)

    helper.report(node)
  }


  "Simple car" should "be provable" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/simplecar.key"))

    val plantTactic = debugT("plant") & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(diffSolutionT) & arithmeticT

    val tactic = ls(ImplyRightT) & la(AndLeftT) &
      ls(wipeContextInductionT(Some("v>=0".asFormula))) &
      onBranch(
        (indInitLbl, debugT("init") & AxiomCloseT),
        (indStepLbl, debugT("step") & ls(ImplyRightT) &
          ls(boxSeqT) & ls(boxChoiceT) & ls(AndRightT) && (
            ls(boxAssignT) & plantTactic,
            ls(boxAssignT) & plantTactic
          )
          ),
        (indUseCaseLbl, debugT("use") & ls(ImplyRightT) & AxiomCloseT)
      )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  it should "be provable automatically with Mathematica" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/simplecar.key"))
    helper.runTactic(master(new Generate("v>=0".asFormula), true, "Mathematica"), new RootNode(s)) shouldBe 'closed
  }

  it should "be provable automatically with Z3" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/simplecar.key"))
    helper.runTactic(master(new Generate("v>=0".asFormula), true, "Z3"), new RootNode(s)) shouldBe 'closed
  }

}
