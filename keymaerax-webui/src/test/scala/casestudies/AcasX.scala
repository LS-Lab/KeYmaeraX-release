/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package casestudies

import java.io.File

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.ODETactics._
import edu.cmu.cs.ls.keymaerax.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaerax.tactics.FOQuantifierTacticsImpl.{instantiateT,skolemizeT}
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.{debugT, arithmeticT, ImplyRightT, AndLeftT, hideT, AndRightT,
  ImplyLeftT, AxiomCloseT, OrRightT, OrLeftT, cutT, locate}
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.PositionTactic
import edu.cmu.cs.ls.keymaerax.tactics.PropositionalTacticsImpl.{Propositional,NonBranchingPropositionalT,cohideT}
import edu.cmu.cs.ls.keymaerax.tactics.HybridProgramTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.tools.{Mathematica, KeYmaera}
import testHelper.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}

import testHelper.ParserFactory._

import scala.collection.immutable.Map

/**
 * Created by smitsch on 3/27/15.
 * @author Stefan Mitsch
 * @author Jean-Baptiste Jeannin
 */
class AcasX extends FlatSpec with Matchers with BeforeAndAfterEach {

  val helper = new ProvabilityTestHelper((x) => println(x))
  val mathematicaConfig: Map[String, String] = helper.mathematicaConfig

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

  def foo(f: String)(fml: Formula) = {
    fml == f.asFormula
  }

  def ls(tactic: PositionTactic, fml: String*) =
    if (fml.isEmpty) locateSucc(tactic)
    else fml.map(f => locateSucc(tactic, _ == f.asFormula)).reduce(_ & _)
  def la(tactic: PositionTactic, fml: String*) =
    if (fml.isEmpty) locateAnte(tactic)
    else fml.map(f => locateAnte(tactic, foo(f)/*_ == f.asFormula*/)).reduce(_ & _)
  def l(t: PositionTactic) = locate(t)

  "No Delay" should "be provable" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/acasx/nodelay.key"))

    val invariant = ("( (w=-1 | w=1) & " +
      "      (" +
      "        \\forall t \\forall ro \\forall ho" +
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

    val crushw = la(OrLeftT, "w()=-1|w()=1") && (
      debugT("Goal Crush Left") & arith,
      debugT("Goal Crush Right") & arith
      )

    val crushor = (la(OrLeftT)*) & arith

    val tactic = ls(ImplyRightT) & la(AndLeftT) & ls(wipeContextInductionT(Some(invariant))) & onBranch(
      (indInitLbl, debugT("Base case") & arith),
      (indUseCaseLbl, debugT("Use case") & ls(ImplyRightT) & (la(AndLeftT)*) & ls(AndRightT) &&(
        la(instantiateT(Variable("t"), Number(0))) &
          la(instantiateT(Variable("ro"), Number(0))) &
          la(instantiateT(Variable("ho"), Number(0))) & la(ImplyLeftT) && (
            arith,
            arith
          ),
        arith
        )),
      (indStepLbl, debugT("Step") & ls(ImplyRightT) & ls(boxSeqGenT(invariant)) & onBranch(
        (cutShowLbl, debugT("Generalization Holds") &
          ls(boxSeqT) & ls(boxChoiceT) & ls(AndRightT) && (
          debugT("1.1") & ls(boxTestT) & ls(ImplyRightT) & ls(boxNDetAssign) & ls(skolemizeT) & AxiomCloseT,
          debugT("1.2") & ls(boxSeqT) & ls(boxNDetAssign) & ls(skolemizeT) & ls(boxSeqT) & ls(boxChoiceT) & hideT(AntePosition(1)) &
            ls(AndRightT) & /* both branches are the same */
            ls(substitutionBoxAssignT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxNDetAssign) & ls(skolemizeT) & arith
          )),
        (cutUseLbl, debugT("Generalization Strong Enough") &
          debugT("Introducing constants") & ls(diffIntroduceConstantT) &
          debugT("Goal 69 (Solving)") & /*ls(LogicalODESolver.solveT) &*/ ls(diffSolution(None)) & debugT("Diff. Solution") &
          /* cutting in the side condition that we expect from diff. solution. Remove once diff. solution produces it */
          cutT(Some("\\forall tside (0<=tside & tside<=kxtime_5 -> (w()*(dhd_2()+ao()*tside)>=w()*dhf()|w()*ao()>=a()))".asFormula)) &
          onBranch(
            (cutShowLbl, debugT("Ignore this branch - cut cannot be shown") /* TODO Counts as open goal */),
            (cutUseLbl,
          ls(ImplyRightT) & (la(AndLeftT)*) & ls(AndRightT) && (
            ls(AndRightT) && (
              AxiomCloseT,
              debugT("Before skolemization") & (ls(skolemizeT)*) & debugT("After skolemization") & ls(ImplyRightT) & ls(OrRightT) &
              // here we'd want to access the previously introduced skolem symbol and the time introduced by diffSolution
              // goal 90
              la(instantiateT(Variable("t"),
                // t_22+t_23: kxtime_5 == t_22, t_0 == t_23
                Plus(Variable("kxtime", Some(5)), Variable("t", Some(0))))) &
              la(instantiateT(Variable("ro"),
                // rv*(t_22+t_23)
                Times(
                  FuncOf(Function("rv", None, Unit, Real), Nothing),
                  Plus(Variable("kxtime", Some(5)), Variable("t", Some(0))))
                )) &
              debugT("Before CUT") &
              // here we'd also want to access symbols created during the proof
              // CUT 1: (0 <= t_0+kxtime_5 & t_0+kxtime_5 < Max(0, w*(dhf-dhd))/a) | t_0+kxtime_5 >= Max(0, w*(dhf-dhd))/a
              cutT(Some("(0 <= t_0+kxtime_5 & t_0+kxtime_5 < w()*(dhf()-dhd)/a()) | (0 <= t_0+kxtime_5 & t_0+kxtime_5 >= w()*(dhf()-dhd)/a())".asFormula)) & onBranch(
                (cutShowLbl, debugT("Show Cut") & lastAnte(hideT) & hideT(SuccPosition(1)) & hideT(SuccPosition(0)) &
                  ls(OrRightT) & lastAnte(OrLeftT) & (la(AndLeftT)*) & (ls(AndRightT)*) & (arith | debugT("Should be closed") & Tactics.stopT)),
                (cutUseLbl, debugT("Use Cut") & /* OrLeftT on formula of CUT 1 */ lastAnte(OrLeftT) && (
                    // goal 110
                    debugT("Goal 110") & locateAnte(instantiateT(Variable("ho"), "w()*a()/2*(t_0+kxtime_5)^2 + dhd*(t_0+kxtime_5)".asTerm), { case Forall(Variable("ho", None, Real) :: Nil, _) => true case _ => false }) &
                      // OrLeftT on ???
                      ((AxiomCloseT | l(NonBranchingPropositionalT))*) & la(ImplyLeftT, "0<=kxtime_5+t_0&kxtime_5+t_0 < w()*(dhf()-dhd)/a()&rv()*(kxtime_5+t_0)=rv()*(kxtime_5+t_0)&w()*a()/2*(t_0+kxtime_5)^2+dhd*(t_0+kxtime_5)=w()*a()/2*(kxtime_5+t_0)^2+dhd*(kxtime_5+t_0)|kxtime_5+t_0>=0&kxtime_5+t_0>=w()*(dhf()-dhd)/a()&rv()*(kxtime_5+t_0)=rv()*(kxtime_5+t_0)&(w()*(dhf()-dhd)<=0&w()*a()/2*(t_0+kxtime_5)^2+dhd*(t_0+kxtime_5)=dhf()*(kxtime_5+t_0)|w()*(dhf()-dhd)>0&w()*a()/2*(t_0+kxtime_5)^2+dhd*(t_0+kxtime_5)=dhf()*(kxtime_5+t_0)-w()*(w()*(dhf()-dhd))^2/(2*a()))->r-rv()*(kxtime_5+t_0) < -rp|r-rv()*(kxtime_5+t_0)>rp|w()*h < w()*(w()*a()/2*(t_0+kxtime_5)^2+dhd*(t_0+kxtime_5))-hp") && (
                        (ls(OrRightT)*) & lastSucc(hideT) & (ls(AndRightT)*) & (AxiomCloseT | arith | debugT("Shouldn't get here")),
                        la(OrLeftT, "0<=t_0&t_0 < w()*(dhf()-dhd_3)/a()&ro_0=rv()*t_0&ho_0=w()*a()/2*t_0^2+dhd_3*t_0|t_0>=0&t_0>=w()*(dhf()-dhd_3)/a()&ro_0=rv()*t_0&(w()*(dhf()-dhd_3)<=0&ho_0=dhf()*t_0|w()*(dhf()-dhd_3)>0&ho_0=dhf()*t_0-w()*(w()*(dhf()-dhd_3))^2/(2*a()))") && (
                          debugT("Goal 124") & lastAnte(OrLeftT) && (
                            hideT(SuccPosition(0)) & (arith | debugT("This should close") & Tactics.stopT),
                            debugT("Goal 135") & lastSucc(hideT) & lastSucc(hideT) & (la(AndLeftT)*) & debugT("Goal 145") & la(OrLeftT, "w()*dhd_3>=w()*dhf()|w()*ao()>=a()") && (
                              debugT("Goal 146") & crushw,
                              debugT("Goal 148") & crushw
                              )
                            ),
                          debugT("Goal 125") & lastAnte(OrLeftT) && (
                            debugT("Goal 280") & arith,
                            debugT("Goal 281") & (la(AndLeftT)*) & (la(OrLeftT)*) & arith
                            )
                          )
                      ),
                    // goal 111
                    // we don't have Max, so instead of instantiating ho with dhf*(t_0+kxtime_5) - w*(Max(0, w*(dhf-dhd))^2/(2*a) we first cut
                    debugT("Goal 111") &
                    cutT(Some("w()*(dhf()-dhd) > 0 | w()*(dhf()-dhd) <= 0".asFormula)) & onBranch(
                      (cutShowLbl, lastSucc(cohideT) & arith),
                      (cutUseLbl, lastAnte(OrLeftT) && (
                        /* w*(dhf-dhd_3) > 0 */ locateAnte(instantiateT(Variable("ho"), "dhf()*(t_0+kxtime_5) - w()*(w()*(dhf()-dhd))^2/(2*a())".asTerm), { case Forall(Variable("ho", None, Real) :: Nil, _) => true case _ => false }) &
                        debugT("Goal 120-1") & lastAnte(ImplyLeftT) && (
                          debugT("Goal 122") & arith,
                          debugT("Goal 123") & la(OrLeftT, "0<=t_0&t_0 < w()*(dhf()-dhd_3)/a()&ro_0=rv()*t_0&ho_0=w()*a()/2*t_0^2+dhd_3*t_0|t_0>=0&t_0>=w()*(dhf()-dhd_3)/a()&ro_0=rv()*t_0&(w()*(dhf()-dhd_3)<=0&ho_0=dhf()*t_0|w()*(dhf()-dhd_3)>0&ho_0=dhf()*t_0-w()*(w()*(dhf()-dhd_3))^2/(2*a()))") && (
                            crushor,
                            debugT("Goal 127") &
                            la(TacticLibrary.eqLeft(exhaustive=true), "kxtime_1=0") &
                            la(TacticLibrary.eqLeft(exhaustive=true), "kxtime_4()=0") &
                            (la(AndLeftT)*) &
                            la(instantiateT(Variable("tside"), Variable("kxtime", Some(5))), "\\forall tside (0<=tside&tside<=kxtime_5->w()*(dhd_2()+ao()*tside)>=w()*dhf()|w()*ao()>=a())") &
                            la(ImplyLeftT, "0<=kxtime_5&kxtime_5<=kxtime_5->w()*(dhd_2()+ao()*kxtime_5)>=w()*dhf()|w()*ao()>=a()") && (
                              arith,
                              debugT("Goal 193") & la(OrLeftT, "r-rv()*(kxtime_5+t_0) < -rp|r-rv()*(kxtime_5+t_0)>rp|w()*h < w()*(dhf()*(t_0+kxtime_5)-w()*(w()*(dhf()-dhd))^2/(2*a()))-hp") && (
                                debugT("Goal 194") & crushor,
                                debugT("Goal 195") & ls(hideT, "r_3-ro_0 < -rp|r_3-ro_0>rp") &
                                la(OrLeftT, "w()*(dhf()-dhd_3)<=0&ho_0=dhf()*t_0|w()*(dhf()-dhd_3)>0&ho_0=dhf()*t_0-w()*(w()*(dhf()-dhd_3))^2/(2*a())") && (
                                  debugT("Goal 214") & cutT(Some("w()*ao()>=a()|!w()*ao()>=a()".asFormula)) & onBranch(
                                    (cutShowLbl, lastSucc(cohideT) & arith),
                                    (cutUseLbl, la(OrLeftT, "w()*ao()>=a()|!w()*ao()>=a()") && (
                                      arith,
                                      debugT("Goal 231") & la(OrLeftT, "w()*dhd_3>=w()*dhf()|w()*ao()>=a()") && (
                                        debugT("Goal 233") /* TODO instantiate tside with 0: call to instantiateT above did hide forall */ &
                                          cutT(Some("\\forall tside (0<=tside & tside<=kxtime_5 -> (w()*(dhd_2()+ao()*tside)>=w()*dhf()|w()*ao()>=a()))".asFormula)) &
                                          onBranch(
                                            (cutShowLbl, debugT("Ignore this branch - cut cannot be shown") /* TODO Counts as open goal */),
                                            (cutUseLbl, la(instantiateT(Variable("tside"), "0".asTerm), "\\forall tside (0<=tside&tside<=kxtime_5->w()*(dhd_2()+ao()*tside)>=w()*dhf()|w()*ao()>=a())") &
                                              la(ImplyLeftT, "0<=0&0<=kxtime_5->w()*(dhd_2()+ao()*0)>=w()*dhf()|w()*ao()>=a()") && (
                                                arith,
                                                la(OrLeftT, "w()*(dhd_2()+ao()*0)>=w()*dhf()|w()*ao()>=a()") && (
                                                  crushor,
                                                  la(PropositionalTacticsImpl.NotLeftT) & AxiomCloseT
                                                  )
                                              )
                                              )
                                          ),
                                        la(PropositionalTacticsImpl.NotLeftT) & AxiomCloseT
                                        )
                                      ))
                                  ),
                                  crushor
                                  )
                                )
                              )

//                            debugT("Goal 127") & /*lastAnte(OrLeftT) &&*/ (
//                              //debugT("Goal 194") & arith,
//                              debugT("Goal 195") & /*hideT(SuccPosition(0)) &*/ debugT("Goal 209") & (la(AndLeftT)*) & debugT("Goal 213") & la(OrLeftT, "w()*(dhf()-dhd_3)<=0&ho_0=dhf()*t_0|w()*(dhf()-dhd_3)>0&ho_0=dhf()*t_0-w()*(w()*(dhf()-dhd_3))^2/(2*a())") && (
//                                debugT("Goal 214") &
//                                  la(hideT, "w()*dhd_3>=w()*dhf()|w()*ao()>=a()") & (la(AndLeftT)*) & debugT("Goal 217/126") &
//                                  la(TacticLibrary.eqLeft(exhaustive=true), "kxtime_1=0") &
//                                  la(TacticLibrary.eqLeft(exhaustive=true), "kxtime_4()=0") &
//                                  la(instantiateT(Variable("tside"), Variable("kxtime", Some(5))), "\\forall tside (0<=tside&tside<=kxtime_5->w()*(dhd_2()+ao()*tside)>=w()*dhf()|w()*ao()>=a())") &
//                                  debugT("After Instantiate") & la(ImplyLeftT, "0<=kxtime_5&kxtime_5<=kxtime_5->w()*(dhd_2()+ao()*kxtime_5)>=w()*dhf()|w()*ao()>=a()") && (
//                                    debugT("Should be trivial") & arith,
//                                    debugT("Continue here") & la(OrLeftT, "w()*(dhd_2()+ao()*kxtime_5)>=w()*dhf()|w()*ao()>=a()") && (
//                                      debugT("Goal 152") &
//                                        la(OrLeftT, "r-rv()*(kxtime_5+t_0) < -rp|r-rv()*(kxtime_5+t_0)>rp|w()*h < w()*(dhf()*(t_0+kxtime_5)-w()*(w()*(dhf()-dhd))^2/(2*a()))-hp") && (
//                                          ls(hideT, "w()*h_3 < w()*ho_0-hp") & debugT("First") & crushw,
//                                          debugT("Second") & crushw
//                                        ),
//                                      debugT("Goal 153") & ls(hideT, "r_3-ro_0 < -rp|r_3-ro_0>rp") & crushw
//                                      )
//                                  ),
//                                debugT("Goal 215") & la(OrLeftT, "w()*dhd_3>=w()*dhf()|w()*ao()>=a()") && (
//                                  debugT("Goal 215-1") & crushw,
//                                  debugT("Goal 215-2") & crushw)
//                                )
//                              )
                            )
                        ),
                        /* w*(dhf-dhd_3) <= 0 */ locateAnte(instantiateT(Variable("ho"), "dhf()*(t_0+kxtime_5)".asTerm), { case Forall(Variable("ho", None, Real) :: Nil, _) => true case _ => false }) &
                          debugT("BGoal 120-2") /* TODO open goal: remainder of this tactic copied from above */ & Tactics.stopT & lastAnte(ImplyLeftT) && (
                          debugT("BGoal 122") & (la(AndLeftT)*) & (ls(OrRightT)*) & (ls(AndRightT)*) & (AxiomCloseT | arith),
                          debugT("BGoal 123") & la(OrLeftT, "0<=t_0&t_0 < w()*(dhf()-dhd_3)/a()&ro_0=rv()*t_0&ho_0=w()*a()/2*t_0^2+dhd_3*t_0|t_0>=0&t_0>=w()*(dhf()-dhd_3)/a()&ro_0=rv()*t_0&(w()*(dhf()-dhd_3)<=0&ho_0=dhf()*t_0|w()*(dhf()-dhd_3)>0&ho_0=dhf()*t_0-w()*(w()*(dhf()-dhd_3))^2/(2*a()))") && (
                            la(OrLeftT, "w()*dhd_3>=w()*dhf()|w()*ao()>=a()") && (
                              la(OrLeftT, "w()=-1|w()=1") && (debugT("BGoal 123-1") & arith, debugT("BGoal 123-2") & arith),
                              debugT("BGoal 153") & lastAnte(OrLeftT) && (
                                debugT("BGoal 154") & arith,
                                debugT("BGoal 155") & crushw
                                )
                              ),
                            debugT("BGoal 127") & /*lastAnte(OrLeftT) &&*/ (
                              //debugT("BGoal 194") & arith,
                              debugT("BGoal 195") & /*hideT(SuccPosition(0)) &*/ debugT("BGoal 209") & (la(AndLeftT)*) & debugT("BGoal 213") & la(OrLeftT, "w()*(dhf()-dhd_3)<=0&ho_0=dhf()*t_0|w()*(dhf()-dhd_3)>0&ho_0=dhf()*t_0-w()*(w()*(dhf()-dhd_3))^2/(2*a())") && (
                                debugT("BGoal 214") &
                                  la(hideT, "w()*dhd_3>=w()*dhf()|w()*ao()>=a()") & (la(AndLeftT)*) & debugT("BGoal 217/126") &
                                  la(TacticLibrary.eqLeft(exhaustive=true), "kxtime_1=0") &
                                  la(TacticLibrary.eqLeft(exhaustive=true), "kxtime_4()=0") &
                                  la(instantiateT(Variable("tside"), Variable("kxtime", Some(5))), "\\forall tside (0<=tside&tside<=kxtime_5->w()*(dhd_2()+ao()*tside)>=w()*dhf()|w()*ao()>=a())") &
                                  debugT("After Instantiate") & la(ImplyLeftT, "0<=kxtime_5&kxtime_5<=kxtime_5->w()*(dhd_2()+ao()*kxtime_5)>=w()*dhf()|w()*ao()>=a()") && (
                                  debugT("Should be trivial") & arith,
                                  debugT("Continue here") & la(OrLeftT, "w()*(dhd_2()+ao()*kxtime_5)>=w()*dhf()|w()*ao()>=a()") && (
                                    debugT("BGoal 152") &
                                      la(OrLeftT, "r-rv()*(kxtime_5+t_0) < -rp|r-rv()*(kxtime_5+t_0)>rp|w()*h < w()*(dhf()*(t_0+kxtime_5)-w()*(w()*(dhf()-dhd))^2/(2*a()))-hp") && (
                                      ls(hideT, "w()*h_3 < w()*ho_0-hp") & debugT("First") & crushw,
                                      debugT("Second") & crushw
                                      ),
                                    debugT("BGoal 153") & ls(hideT, "r_3-ro_0 < -rp|r_3-ro_0>rp") & crushw
                                    )
                                  ),
                                debugT("BGoal 215") & la(OrLeftT, "w()*dhd_3>=w()*dhf()|w()*ao()>=a()") && (
                                  debugT("BGoal 215-1") & crushw,
                                  debugT("BGoal 215-2") & crushw)
                                )
                              )
                            )
                          )


                        ))
                    )
                  )
                  )
              )
            ),
            arith
          ) /* End AndRight */
          ) /* End cutUseLbl of ODE cut */
          ) /* End onBranch of ODE cut */
          )
        ))
    )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  "No Delay explicit time" should "be provable" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/acasx/nodelay_explicittime.key"))

    val invariant = ("( (w=-1 | w=1) & " +
      "      (" +
      "        \\forall t \\forall ro \\forall ho" +
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

    val odePos = SuccPosition(0)

    val tactic = ls(ImplyRightT) & la(AndLeftT) & ls(wipeContextInductionT(Some(invariant))) & onBranch(
      (indInitLbl, debugT("Base case") & arith),
      (indUseCaseLbl, debugT("Use case") & ls(ImplyRightT) & (la(AndLeftT)*) & ls(AndRightT) &&(
        la(instantiateT(Variable("t"), Number(0))) &
          la(instantiateT(Variable("ro"), Number(0))) &
          la(instantiateT(Variable("ho"), Number(0))) & la(ImplyLeftT) && (
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
          ls(boxSeqT) & ls(boxAssignT) &
          debugT("Introducing constants") & ls(diffIntroduceConstantT) &
          debugT("Storing initial values") &
          discreteGhostT(Some(Variable("r0")), Variable("r"))(odePos) & boxAssignT(FOQuantifierTacticsImpl.skolemizeToFnT(_))(odePos) &
          discreteGhostT(Some(Variable("dhd0")), Variable("dhd"))(odePos) & boxAssignT(FOQuantifierTacticsImpl.skolemizeToFnT(_))(odePos) &
          discreteGhostT(Some(Variable("h0")), Variable("h"))(odePos) & boxAssignT(FOQuantifierTacticsImpl.skolemizeToFnT(_))(odePos) &
          debugT("Solving") & /* TODO have to use advanced ODE solver, this one uses diff. weaken */ ls(LogicalODESolver.solveT) & debugT("Diff. Solution") &
          Tactics.stopT &
          // TODO when ODESolver works, continue fixing the proof here (just copied from above)
          ls(ImplyRightT) & (la(AndLeftT)*) & ls(AndRightT) && (
          ls(AndRightT) && (
            AxiomCloseT,
            debugT("Before skolemization") & (ls(skolemizeT)*) & debugT("After skolemization") & ls(ImplyRightT) & ls(OrRightT) &
              // here we'd want to access the previously introduced skolem symbol and the time introduced by diffSolution
              // goal 90
              la(instantiateT(Variable("t"),
                // t_22+t_23: kxtime_5 == t_22, t_0 == t_23
                Plus(Variable("kxtime", Some(5)), Variable("t", Some(0))))) &
              la(instantiateT(Variable("ro"),
                // rv*(t_22+t_23)
                Times(
                  FuncOf(Function("rv", None, Unit, Real), Nothing),
                  Plus(Variable("kxtime", Some(5)), Variable("t", Some(0))))
              )) &
              debugT("Before CUT") &
              // here we'd also want to access symbols created during the proof
              // CUT 1: (0 <= t_0+kxtime_5 & t_0+kxtime_5 < Max(0, w*(dhf-dhd))/a) | t_0+kxtime_5 >= Max(0, w*(dhf-dhd))/a
              cutT(Some("(0 <= t_0+kxtime_5 & t_0+kxtime_5 < w()*(dhf()-dhd)/a()) | (0 <= t_0+kxtime_5 & t_0+kxtime_5 >= w()*(dhf()-dhd)/a())".asFormula)) & onBranch(
              (cutShowLbl, debugT("Show Cut") & lastAnte(hideT) & hideT(SuccPosition(1)) & hideT(SuccPosition(0)) &
                ls(OrRightT) & lastAnte(OrLeftT) & (la(AndLeftT)*) & (ls(AndRightT)*) & (arith | debugT("Should be closed") & Tactics.stopT)),
              (cutUseLbl, debugT("Use Cut") & /* OrLeftT on formula of CUT 1 */ lastAnte(OrLeftT) && (
                // goal 110
                debugT("Goal 110") & locateAnte(instantiateT(Variable("ho"), "w()*a()/2*(t_0+kxtime_5)^2 + dhd*(t_0+kxtime_5)".asTerm), { case Forall(Variable("ho", None, Real) :: Nil, _) => true case _ => false }) &
                  // OrLeftT on ???
                  ((AxiomCloseT | l(NonBranchingPropositionalT))*) & la(ImplyLeftT, "0<=kxtime_5+t_0&kxtime_5+t_0 < w()*(dhf()-dhd)/a()&rv()*(kxtime_5+t_0)=rv()*(kxtime_5+t_0)&w()*a()/2*(t_0+kxtime_5)^2+dhd*(t_0+kxtime_5)=w()*a()/2*(kxtime_5+t_0)^2+dhd*(kxtime_5+t_0)|kxtime_5+t_0>=0&kxtime_5+t_0>=w()*(dhf()-dhd)/a()&rv()*(kxtime_5+t_0)=rv()*(kxtime_5+t_0)&(w()*(dhf()-dhd)<=0&w()*a()/2*(t_0+kxtime_5)^2+dhd*(t_0+kxtime_5)=dhf()*(kxtime_5+t_0)|w()*(dhf()-dhd)>0&w()*a()/2*(t_0+kxtime_5)^2+dhd*(t_0+kxtime_5)=dhf()*(kxtime_5+t_0)-w()*(w()*(dhf()-dhd))^2/(2*a()))->r-rv()*(kxtime_5+t_0) < -rp|r-rv()*(kxtime_5+t_0)>rp|w()*h < w()*(w()*a()/2*(t_0+kxtime_5)^2+dhd*(t_0+kxtime_5))-hp") && (
                  (ls(OrRightT)*) & lastSucc(hideT) & (ls(AndRightT)*) & (AxiomCloseT | arith | debugT("Shouldn't get here")),
                  la(OrLeftT, "0<=t_0&t_0 < w()*(dhf()-dhd_3)/a()&ro_0=rv()*t_0&ho_0=w()*a()/2*t_0^2+dhd_3*t_0|t_0>=0&t_0>=w()*(dhf()-dhd_3)/a()&ro_0=rv()*t_0&(w()*(dhf()-dhd_3)<=0&ho_0=dhf()*t_0|w()*(dhf()-dhd_3)>0&ho_0=dhf()*t_0-w()*(w()*(dhf()-dhd_3))^2/(2*a()))") && (
                    debugT("Goal 124") & lastAnte(OrLeftT) && (
                      hideT(SuccPosition(0)) & (arith | debugT("This should close") & Tactics.stopT),
                      debugT("Goal 135") & lastSucc(hideT) & lastSucc(hideT) & (la(AndLeftT)*) & debugT("Goal 145") & la(OrLeftT, "w()*dhd_3>=w()*dhf()|w()*ao()>=a()") && (
                        debugT("Goal 146") & la(OrLeftT, "w()=-1|w()=1") && (debugT("Goal 146-1") & arith, debugT("Goal 146-2") & arith),
                        debugT("Goal 148") & la(OrLeftT, "w()=-1|w()=1") && (debugT("Goal 148-1") & arith, debugT("Goal 148-2") & arith)
                        )
                      ),
                    debugT("Goal 125") & lastAnte(OrLeftT) && (
                      debugT("Goal 280") & arith,
                      debugT("Goal 281") & (la(AndLeftT)*) & (la(OrLeftT)*) & arith
                      )
                    )
                  ),
                // goal 111
                // we don't have Max, so instead of instantiating ho with dhf*(t_0+kxtime_5) - w*(Max(0, w*(dhf-dhd))^2/(2*a) we first cut
                cutT(Some("w()*(dhf()-dhd) > 0 | w()*(dhf()-dhd) <= 0".asFormula)) & onBranch(
                  (cutShowLbl, lastSucc(cohideT) & arith),
                  (cutUseLbl, lastAnte(OrLeftT) && (
                    /* w*(dhf-dhd_3) > 0 */ locateAnte(instantiateT(Variable("ho"), "dhf()*(t_0+kxtime_5) - w()*(w()*(dhf()-dhd))^2/(2*a())".asTerm), { case Forall(Variable("ho", None, Real) :: Nil, _) => true case _ => false }) &
                    debugT("Goal 120-1") & lastAnte(ImplyLeftT) && (
                    debugT("Goal 122") & (la(AndLeftT)*) & (ls(OrRightT)*) & (ls(AndRightT)*) & (AxiomCloseT | arith),
                    debugT("Goal 123") & la(OrLeftT, "0<=t_0&t_0 < w()*(dhf()-dhd_3)/a()&ro_0=rv()*t_0&ho_0=w()*a()/2*t_0^2+dhd_3*t_0|t_0>=0&t_0>=w()*(dhf()-dhd_3)/a()&ro_0=rv()*t_0&(w()*(dhf()-dhd_3)<=0&ho_0=dhf()*t_0|w()*(dhf()-dhd_3)>0&ho_0=dhf()*t_0-w()*(w()*(dhf()-dhd_3))^2/(2*a()))") && (
                      la(OrLeftT, "w()*dhd_3>=w()*dhf()|w()*ao()>=a()") && (
                        la(OrLeftT, "w()=-1|w()=1") && (debugT("Goal 123-1") & arith, debugT("Goal 123-2") & arith),
                        debugT("Goal 153") & lastAnte(OrLeftT) && (
                          debugT("Goal 154") & arith,
                          debugT("Goal 155") & la(OrLeftT, "w()=-1|w()=1") && (
                            debugT("Goal 165") & arith,
                            debugT("Goal 166") & arith
                            )
                          )
                        ),
                      debugT("Goal 127") & lastAnte(OrLeftT) && (
                        debugT("Goal 194") & arith,
                        debugT("Goal 195") & hideT(SuccPosition(0)) & debugT("Goal 209") & (la(AndLeftT)*) & debugT("Goal 213") & la(OrLeftT, "w()*(dhf()-dhd_3)<=0&ho_0=dhf()*t_0|w()*(dhf()-dhd_3)>0&ho_0=dhf()*t_0-w()*(w()*(dhf()-dhd_3))^2/(2*a())") && (
                          debugT("Goal 214") & la(hideT, "w()*dhd_3>=w()*dhf()|w()*ao()>=a()") & (la(AndLeftT)*) & debugT("Goal 217")/* TODO open goal with counterexamples */ /*& (la(OrLeftT)*) & (la(AndLeftT)*) & debugT("WTF?")*/ & arith,
                          debugT("Goal 215") & la(OrLeftT, "w()*dhd_3>=w()*dhf()|w()*ao()>=a()") && (
                            debugT("Goal 215-1") & la(OrLeftT, "w()=-1|w()=1") && (debugT("Goal 215-11") & arith, debugT("Goal 215-12") & arith),
                            debugT("Goal 215-2") & la(OrLeftT, "w()=-1|w()=1") && (debugT("Goal 215-21") & arith, debugT("Goal 215-22") & arith))
                          )
                        )
                      )
                    ),
                    /* w*(dhf-dhd_3) <= 0 */ locateAnte(instantiateT(Variable("ho"), "dhf()*(t_0+kxtime_5)".asTerm), { case Forall(Variable("ho", None, Real) :: Nil, _) => true case _ => false }) &
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
