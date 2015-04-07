package casestudies

import java.io.File

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.ODETactics._
import edu.cmu.cs.ls.keymaera.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaera.tactics.FOQuantifierTacticsImpl.{instantiateT,skolemizeT}
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.{debugT, arithmeticT, ImplyRightT, AndLeftT, hideT, AndRightT,
  ImplyLeftT, AxiomCloseT, OrRightT, OrLeftT, cutT, locate}
import edu.cmu.cs.ls.keymaera.tactics.Tactics.PositionTactic
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl.{Propositional,NonBranchingPropositionalT,cohideT}
import edu.cmu.cs.ls.keymaera.tactics.HybridProgramTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.{Interpreter, Tactics}
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}

import testHelper.ParserFactory._
import testHelper.StringConverter._

import scala.collection.immutable.Map

/**
 * Created by smitsch on 3/27/15.
 * @author Stefan Mitsch
 * @author Jean-Baptiste Jeannin
 */
class AcasX extends FlatSpec with Matchers with BeforeAndAfterEach {

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
  def l(t: PositionTactic) = locate(t)

  "No Delay" should "be provable" in {
    val file = new File("examples/casestudies/acasx/nodelay.key")
    val s = parseToSequent(file)

    val invariant = ("( (w=-1 | w=1) & " +
      "      (" +
      "        \\forall t. \\forall ro. \\forall ho." +
      "        ((0 <= t & t < w * (dhf - dhd) / a &" +
      "          ro = rv * t & ho = (w * a) / 2 * t^2 + dhd * t) |" +
      "         (t >=0 & t >= w * (dhf - dhd) / a &" +
      "          ro = rv * t &" +
      "      ( (w * (dhf - dhd) <=  0 & ho = dhf * t) |" +
      "        (w * (dhf - dhd) > 0 & ho = dhf * t - w * (w * (dhf - dhd))^2 / (2*a))))" +
      "         -> (r - ro < -rp | r - ro > rp | w * h < w * ho - hp))" +
      "      )) & ( hp>0&rp>0&rv>=0&a>0 )").asFormula
//    val invariant = "w=42".asFormula

    val arith = arithmeticT

    val tactic = ls(ImplyRightT) & la(AndLeftT) & ls(wipeContextInductionT(Some(invariant))) & onBranch(
      (indInitLbl, debugT("Base case") & arith),
      (indUseCaseLbl, debugT("Use case") & ls(ImplyRightT) & (la(AndLeftT)*) & ls(AndRightT) &&(
        la(instantiateT(Variable("t", None, Real), Number(0))) &
          la(instantiateT(Variable("ro", None, Real), Number(0))) &
          la(instantiateT(Variable("ho", None, Real), Number(0))) & la(ImplyLeftT) && (
            arith,
            arith
          ),
        arith
        )),
      (indStepLbl, debugT("Step") & ls(ImplyRightT) & ls(boxSeqGenT(invariant)) & onBranch(
        (cutShowLbl, debugT("Generalization Holds") &
          ls(boxSeqT) & ls(boxChoiceT) & ls(AndRightT) && (
          debugT("1.1") & ls(boxTestT) & ls(ImplyRightT) & ls(boxNDetAssign) /* & ls(skolemizeT) & ls(ImplyRightT) */ & AxiomCloseT,
          debugT("1.2") & ls(boxSeqT) & ls(boxNDetAssign) /* & ls(skolemizeT) & ls(ImplyRightT) */ & ls(boxSeqT) & ls(boxChoiceT) & hideT(AntePosition(1)) &
            ls(AndRightT) & /* both branches are the same */
            ls(substitutionBoxAssignT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxNDetAssign) /* & ls(skolemizeT) & ls(ImplyRightT) */ & arith
          )),
        (cutUseLbl, debugT("Generalization Strong Enough") &
          /* remove when HACK ?rv()=rv etc. is removed from model */ ((ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT))*) &
          debugT("Solving") & ls(diffSolution(None)) & ls(ImplyRightT) & (la(AndLeftT)*) & ls(AndRightT) && (
            ls(AndRightT) && (
              AxiomCloseT,
              debugT("Before skolemization") & (ls(skolemizeT)*) & debugT("After skolemization") & ls(ImplyRightT) & ls(OrRightT) &
              // here we'd want to access the previously introduced skolem symbol and the time introduced by diffSolution
              // goal 90
              la(instantiateT(Variable("t", None, Real),
                // t_22+t_23: k4_t_5 == t_22, t_0 == t_23
                Add(Real, Variable("k4_t", Some(5), Real), Variable("t", Some(0), Real)))) &
              la(instantiateT(Variable("ro", None, Real),
                // rv*(t_22+t_23)
                Multiply(Real,
                  Variable("rv", None, Real),
                  Add(Real, Variable("k4_t", Some(5), Real), Variable("t", Some(0), Real)))
                )) &
              // here we'd also want to access symbols created during the proof
              // CUT 1: (0 <= t_0+k4_t_5 & t_0+k4_t_5 < Max(0, w*(dhf-dhd))/a) | t_0+k4_t_5 >= Max(0, w*(dhf-dhd))/a
              cutT(Some("(0 <= t_0+k4_t_5 & t_0+k4_t_5 < w*(dhf-dhd)/a) | (0 <= t_0+k4_t_5 & t_0+k4_t_5 >= w*(dhf-dhd)/a)".asFormula)) & onBranch(
                (cutShowLbl, debugT("Show Cut") & lastAnte(hideT) & hideT(SuccPosition(1)) & hideT(SuccPosition(0)) &
                  ls(OrRightT) & lastAnte(OrLeftT) & (la(AndLeftT)*) & (ls(AndRightT)*) & (arith | debugT("Should be closed") & Tactics.stopT)),
                (cutUseLbl, debugT("Use Cut") & /* OrLeftT on formula of CUT 1 */ lastAnte(OrLeftT) && (
                    // goal 110
                    instantiateT(Variable("ho", None, Real), "w*a/2*(t_0+k4_t_5)^2 + dhd*(t_0+k4_t_5)".asTerm)(AntePosition(18)) & debugT("Did we instantiate?") &
                      // OrLeftT on ???
                      ((AxiomCloseT | l(NonBranchingPropositionalT))*) & debugT("Implication at same pos as instantiate?") & ImplyLeftT(AntePosition(18)) && (
                        (ls(OrRightT)*) & lastSucc(hideT) & (ls(AndRightT)*) & (AxiomCloseT | arith | debugT("Shouldn't get here")),
                        OrLeftT(AntePosition(17)) && (
                          debugT("Goal 124") & lastAnte(OrLeftT) && (
                            hideT(SuccPosition(0)) & (arith | debugT("This should close") & Tactics.stopT),
                            debugT("Goal 135") & lastSucc(hideT) & lastSucc(hideT) & (la(AndLeftT)*) & OrLeftT(AntePosition(15)) && (
                              debugT("Goal 146") & OrLeftT(AntePosition(8)) && (debugT("Goal 146-1") & arith, debugT("Goal 146-2") & arith),
                              debugT("Goal 148") & OrLeftT(AntePosition(8)) && (debugT("Goal 148-1") & arith, debugT("Goal 148-2") & arith)
                              )
                            ),
                          debugT("Goal 125") & lastAnte(OrLeftT) && (
                            debugT("Goal 280") & arith,
                            debugT("Goal 281") & (la(AndLeftT)*) & (la(OrLeftT)*) & arith/*OrLeftT(AntePosition(20)) && (
                              OrLeftT(AntePosition(8)) && (debugT("Goal 283") & arith, debugT("Goal 285") & arith),
                              OrLeftT(AntePosition(8)) && (debugT("Goal 283-1") & arith, debugT("Goal 285-1") & arith)
                              )*/
                            )
                          )
                      ),
                    // goal 111
                    // we don't have Max, so instead of instantiating ho with dhf*(t_0+k4_t_5) - w*(Max(0, w*(dhf-dhd))^2/(2*a) we first cut
                    cutT(Some("w*(dhf-dhd) > 0 | w*(dhf-dhd) <= 0".asFormula)) & onBranch(
                      (cutShowLbl, lastSucc(cohideT) & arith),
                      (cutUseLbl, lastAnte(OrLeftT) && (
                        /* w*(dhf-dhd_3) > 0 */ instantiateT(Variable("ho", None, Real), "dhf*(t_0+k4_t_5) - w*(w*(dhf-dhd))^2/(2*a)".asTerm)(AntePosition(18)) &
                        debugT("Goal 120-1") & lastAnte(ImplyLeftT) && (
                          debugT("Goal 122") & (la(AndLeftT)*) & (ls(OrRightT)*) & (ls(AndRightT)*) & (AxiomCloseT | arith),
                          debugT("Goal 123") & OrLeftT(AntePosition(17)) && (
                            OrLeftT(AntePosition(15)) && (
                              OrLeftT(AntePosition(8)) && (debugT("Goal 123-1") & arith, debugT("Goal 123-2") & arith),
                              debugT("Goal 153") & lastAnte(OrLeftT) && (
                                debugT("Goal 154") & arith,
                                debugT("Goal 155") & OrLeftT(AntePosition(8)) && (
                                  debugT("Goal 165") & arith,
                                  debugT("Goal 166") & arith
                                  )
                                )
                              ),
                            debugT("Goal 127") & lastAnte(OrLeftT) && (
                              debugT("Goal 194") & arith,
                              debugT("Goal 195") & hideT(SuccPosition(0)) & debugT("Goal 209") & (la(AndLeftT)*) & OrLeftT(AntePosition(19)) && (
                                debugT("Goal 214") & hideT(AntePosition(15)) & (la(AndLeftT)*) & debugT("Goal 217")/* TODO open goal with counterexamples */ /*& (la(OrLeftT)*) & (la(AndLeftT)*) & debugT("WTF?")*/ & arith,
                                debugT("Goal 215") & OrLeftT(AntePosition(15)) && (
                                  debugT("Goal 215-1") & OrLeftT(AntePosition(8)) && (debugT("Goal 215-11") & arith, debugT("Goal 215-12") & arith),
                                  debugT("Goal 215-2") & OrLeftT(AntePosition(8)) && (debugT("Goal 215-21") & arith, debugT("Goal 215-22") & arith))
                                )
                              )
                            )
                        ),
                        /* w*(dhf-dhd_3) <= 0 */ instantiateT(Variable("ho", None, Real), "dhf*(t_0+k4_t_5)".asTerm)(AntePosition(18)) &
                          debugT("Goal 120-2") /* TODO open goal */
                        ))
                    )
                  )
                  )
              )
            ),
            arith
          )
          )
        ))
    )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

}
