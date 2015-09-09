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
import edu.cmu.cs.ls.keymaerax.tactics.FOQuantifierTacticsImpl.{instantiateT,skolemizeT,instantiateExistentialQuanT}
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.{debugT, arithmeticT, ImplyRightT, AndLeftT, hideT, AndRightT,
  ImplyLeftT, AxiomCloseT, OrRightT, OrLeftT, cutT, locate, NotRightT, NotLeftT}
import edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary.{la,ls,l,QE,closeId,abs,min,max,andL,andR,orL,orR,implyR,implyL,
  hide,cohide,cut}
import edu.cmu.cs.ls.keymaerax.tactics.ArithmeticTacticsImpl.{AbsAxiomT,AbsT,MinMaxAxiomT,MinMaxT,EqualReflexiveT}
import edu.cmu.cs.ls.keymaerax.tactics.EqualityRewritingImpl.{abbrv,eqLeft}
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.PositionTactic
import edu.cmu.cs.ls.keymaerax.tactics.PropositionalTacticsImpl.{Propositional,NonBranchingPropositionalT,cohideT}
import edu.cmu.cs.ls.keymaerax.tactics.HybridProgramTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.tools.{Mathematica, KeYmaera}
import testHelper.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}

import testHelper.ParserFactory._
import testHelper.SequentFactory._

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
/*
  def ls(tactic: PositionTactic, fml: String*) =
    if (fml.isEmpty) locateSucc(tactic)
    else fml.map(f => locateSucc(tactic, _ == f.asFormula)).reduce(_ & _)
  def la(tactic: PositionTactic, fml: String*) =
    if (fml.isEmpty) locateAnte(tactic)
    else fml.map(f => locateAnte(tactic, foo(f)/*_ == f.asFormula*/)).reduce(_ & _)
  def l(t: PositionTactic) = locate(t)
*/
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

    val arith = arithmeticT

    val crushw = la(OrLeftT, "w=-1|w=1") && (
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
          debugT("Goal 69 (Solving)") & /*ls(LogicalODESolver.solveT) &*/ ls(diffSolution(None)) & debugT("Diff. Solution") &
          /* cutting in the side condition that we expect from diff. solution. Remove once diff. solution produces it */
          cutT(Some("\\forall tside (0<=tside & tside<=kxtime_5 -> (w*(dhd_2()+ao*tside)>=w*dhf|w*ao>=a))".asFormula)) &
          onBranch(
            (cutShowLbl, debugT("Ignore this branch - cut cannot be shown") /* TODO Counts as open goal */),
            (cutUseLbl,
              /* repeat cut so that we can instantiate twice */
              cutT(Some("\\forall tside (0<=tside & tside<=kxtime_5 -> (w*(dhd_2()+ao*tside)>=w*dhf|w*ao>=a))".asFormula)) & onBranch(
                (cutShowLbl, AxiomCloseT),
                (cutUseLbl,
          ls(ImplyRightT) & (la(AndLeftT)*) & ls(AndRightT) && (
            ls(AndRightT) && (
              AxiomCloseT,
              debugT("Before skolemization") & (ls(skolemizeT)*) & debugT("After skolemization") & ls(ImplyRightT) & ls(OrRightT) &
              // here we'd want to access the previously introduced skolem symbol and the time introduced by diffSolution
              // goal 90
              la(instantiateT(Variable("t"),
                // t_22+t_23: kxtime_5 == t_22, t_0 == t_23
                "kxtime_5 + t_0".asTerm)) &
              la(instantiateT(Variable("ro"),
                // rv*(t_22+t_23)
                "rv*(kxtime_5 + t_0)".asTerm)) &
              debugT("Before CUT") &
              // here we'd also want to access symbols created during the proof
              // CUT 1: (0 <= t_0+kxtime_5 & t_0+kxtime_5 < Max(0, w*(dhf-dhd))/a) | t_0+kxtime_5 >= Max(0, w*(dhf-dhd))/a
              // TODO: This cut should be done way later. We need a proper use of quantifiers
              cutT(Some("(0 <= t_0+kxtime_5 & t_0+kxtime_5 < w*(dhf-dhd)/a) | (0 <= t_0+kxtime_5 & t_0+kxtime_5 >= w*(dhf-dhd)/a)".asFormula)) & onBranch(
                (cutShowLbl, debugT("Show Cut") & lastAnte(hideT) & hideT(SuccPosition(1)) & hideT(SuccPosition(0)) &
                  ls(OrRightT) & lastAnte(OrLeftT) & (la(AndLeftT)*) & (ls(AndRightT)*) & (arith | debugT("Should be closed") & Tactics.stopT)),
                (cutUseLbl, debugT("Use Cut") & /* OrLeftT on formula of CUT 1 */ lastAnte(OrLeftT) && (
                    // goal 110
                    debugT("Goal 110") & locateAnte(instantiateT(Variable("ho"), "w*a/2*(t_0+kxtime_5)^2 + dhd*(t_0+kxtime_5)".asTerm), { case Forall(Variable("ho", None, Real) :: Nil, _) => true case _ => false }) &
                      // OrLeftT on ???
                      ((AxiomCloseT | l(NonBranchingPropositionalT))*) & la(ImplyLeftT, "0<=kxtime_5+t_0&kxtime_5+t_0 < w*(dhf-dhd)/a&rv*(kxtime_5+t_0)=rv*(kxtime_5+t_0)&w*a/2*(t_0+kxtime_5)^2+dhd*(t_0+kxtime_5)=w*a/2*(kxtime_5+t_0)^2+dhd*(kxtime_5+t_0)|kxtime_5+t_0>=0&kxtime_5+t_0>=w*(dhf-dhd)/a&rv*(kxtime_5+t_0)=rv*(kxtime_5+t_0)&(w*(dhf-dhd)<=0&w*a/2*(t_0+kxtime_5)^2+dhd*(t_0+kxtime_5)=dhf*(kxtime_5+t_0)|w*(dhf-dhd)>0&w*a/2*(t_0+kxtime_5)^2+dhd*(t_0+kxtime_5)=dhf*(kxtime_5+t_0)-w*(w*(dhf-dhd))^2/(2*a))->r-rv*(kxtime_5+t_0) < -rp|r-rv*(kxtime_5+t_0)>rp|w*h < w*(w*a/2*(t_0+kxtime_5)^2+dhd*(t_0+kxtime_5))-hp") && (
                        (ls(OrRightT)*) & debugT("lastSucc") & lastSucc(hideT) & (ls(AndRightT)*) & (AxiomCloseT | arith | debugT("Shouldn't get here")),
                        la(OrLeftT, "0<=t_0&t_0 < w*(dhf-dhd_3)/a&ro_0=rv*t_0&ho_0=w*a/2*t_0^2+dhd_3*t_0|t_0>=0&t_0>=w*(dhf-dhd_3)/a&ro_0=rv*t_0&(w*(dhf-dhd_3)<=0&ho_0=dhf*t_0|w*(dhf-dhd_3)>0&ho_0=dhf*t_0-w*(w*(dhf-dhd_3))^2/(2*a))") && (
                          debugT("Goal 124") & lastAnte(OrLeftT) && (
                            hideT(SuccPosition(0)) & (arith | debugT("This should close") & Tactics.stopT),
                            debugT("Goal 135") & lastSucc(hideT) & lastSucc(hideT) & (la(AndLeftT)*) & debugT("Goal 145") & la(OrLeftT, "w*dhd_3>=w*dhf|w*ao>=a") && (
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
                    cutT(Some("w*(dhf-dhd) > 0 | w*(dhf-dhd) <= 0".asFormula)) & onBranch(
                      (cutShowLbl, lastSucc(cohideT) & arith),
                      (cutUseLbl, lastAnte(OrLeftT) && (
                        /* w*(dhf-dhd_3) > 0 */ locateAnte(instantiateT(Variable("ho"), "dhf*(t_0+kxtime_5) - w*(w*(dhf-dhd))^2/(2*a)".asTerm), { case Forall(Variable("ho", None, Real) :: Nil, _) => true case _ => false }) &
                        debugT("Goal 120-1") & lastAnte(ImplyLeftT) && (
                          debugT("Goal 122") & arith,
                          debugT("Goal 123") & la(OrLeftT, "0<=t_0&t_0 < w*(dhf-dhd_3)/a&ro_0=rv*t_0&ho_0=w*a/2*t_0^2+dhd_3*t_0|t_0>=0&t_0>=w*(dhf-dhd_3)/a&ro_0=rv*t_0&(w*(dhf-dhd_3)<=0&ho_0=dhf*t_0|w*(dhf-dhd_3)>0&ho_0=dhf*t_0-w*(w*(dhf-dhd_3))^2/(2*a))") && (
                            crushor,
                            debugT("Goal 127") &
                            la(TacticLibrary.eqLeft(exhaustive=true), "kxtime_1=0") &
                            la(TacticLibrary.eqLeft(exhaustive=true), "kxtime_4()=0") &
                            (la(AndLeftT)*) &
                            la(instantiateT(Variable("tside"), Variable("kxtime", Some(5))), "\\forall tside (0<=tside&tside<=kxtime_5->w*(dhd_2()+ao*tside)>=w*dhf|w*ao>=a)") &
                            la(ImplyLeftT, "0<=kxtime_5&kxtime_5<=kxtime_5->w*(dhd_2()+ao*kxtime_5)>=w*dhf|w*ao>=a") && (
                              arith,
                              debugT("Goal 193") & la(OrLeftT, "r-rv*(kxtime_5+t_0) < -rp|r-rv*(kxtime_5+t_0)>rp|w*h < w*(dhf*(t_0+kxtime_5)-w*(w*(dhf-dhd))^2/(2*a))-hp") && (
                                debugT("Goal 194") & crushor,
                                debugT("Goal 195") & ls(hideT, "r_3-ro_0 < -rp|r_3-ro_0>rp") &
                                la(OrLeftT, "w*(dhf-dhd_3)<=0&ho_0=dhf*t_0|w*(dhf-dhd_3)>0&ho_0=dhf*t_0-w*(w*(dhf-dhd_3))^2/(2*a)") && (
                                  debugT("Goal 214") & cutT(Some("w*ao>=a|!w*ao>=a".asFormula)) & onBranch(
                                    (cutShowLbl, lastSucc(cohideT) & arith),
                                    (cutUseLbl, la(OrLeftT, "w*ao>=a|!w*ao>=a") && (
                                      arith,
                                      debugT("Goal 231") & la(OrLeftT, "w*dhd_3>=w*dhf|w*ao>=a") && (
                                        debugT("Goal 233") &
                                          la(instantiateT(Variable("tside"), "0".asTerm), "\\forall tside (0<=tside&tside<=kxtime_5->w*(dhd_2()+ao*tside)>=w*dhf|w*ao>=a)") &
                                          la(ImplyLeftT, "0<=0&0<=kxtime_5->w*(dhd_2()+ao*0)>=w*dhf|w*ao>=a") && (
                                            arith,
                                            la(OrLeftT, "w*(dhd_2()+ao*0)>=w*dhf|w*ao>=a") && (
                                              crushor,
                                              la(PropositionalTacticsImpl.NotLeftT) & AxiomCloseT
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
                            )
                        ),
                        /* w*(dhf-dhd_3) <= 0 */ locateAnte(instantiateT(Variable("ho"), "dhf*(t_0+kxtime_5)".asTerm), { case Forall(Variable("ho", None, Real) :: Nil, _) => true case _ => false }) &
                        debugT("BGoal 120-2") & lastAnte(ImplyLeftT) && (
                        debugT("BGoal 122") & arith,
                        debugT("BGoal 123") & la(OrLeftT, "0<=t_0&t_0 < w*(dhf-dhd_3)/a&ro_0=rv*t_0&ho_0=w*a/2*t_0^2+dhd_3*t_0|t_0>=0&t_0>=w*(dhf-dhd_3)/a&ro_0=rv*t_0&(w*(dhf-dhd_3)<=0&ho_0=dhf*t_0|w*(dhf-dhd_3)>0&ho_0=dhf*t_0-w*(w*(dhf-dhd_3))^2/(2*a))") && (
                          crushor,
                          debugT("BGoal 127") &
                            la(TacticLibrary.eqLeft(exhaustive=true), "kxtime_1=0") &
                            la(TacticLibrary.eqLeft(exhaustive=true), "kxtime_4()=0") &
                            (la(AndLeftT)*) &
                            la(instantiateT(Variable("tside"), Variable("kxtime", Some(5))), "\\forall tside (0<=tside&tside<=kxtime_5->w*(dhd_2()+ao*tside)>=w*dhf|w*ao>=a)") &
                            la(ImplyLeftT, "0<=kxtime_5&kxtime_5<=kxtime_5->w*(dhd_2()+ao*kxtime_5)>=w*dhf|w*ao>=a") && (
                            arith,
                            debugT("BGoal 193") & la(OrLeftT, "r-rv*(kxtime_5+t_0) < -rp|r-rv*(kxtime_5+t_0)>rp|w*h < w*(dhf*(t_0+kxtime_5))-hp") && (
                              debugT("BGoal 194") & crushor,
                              debugT("BGoal 195") & ls(hideT, "r_3-ro_0 < -rp|r_3-ro_0>rp") &
                                la(OrLeftT, "w*(dhf-dhd_3)<=0&ho_0=dhf*t_0|w*(dhf-dhd_3)>0&ho_0=dhf*t_0-w*(w*(dhf-dhd_3))^2/(2*a)") && (
                                crushor,
                                crushor
                                )
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
              ) /* End cutUseLbl of 1st ODE cut */
              ) /* End onBranch of ODE cut */
          ) /* End onBranch of 1st ODE cut */
          )
        ))
    )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  "No Delay using Max" should "be provable" in {
  // one goal left corresponding to ODESolve issue, with 7982464f7daa4afb29295d19528830f2eff56523, Stefan, Tue Sep 8 17:41:17 2015 +0200
  // 780 seconds on robin (about 13 min)
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/acasx/nodelay_max.key"))

    val invariant = ("( (w=-1 | w=1) & " +
      "      (" +
      "\\forall t \\forall ro \\forall ho" +
      "((0 <= t & t < max(0, w * (dhf - dhd)) / a &" +
      "  ro = rv * t & ho = (w * a) / 2 * t^2 + dhd * t) |" +
      "  (t >= max(0, w * (dhf - dhd)) / a &" +
      "    ro = rv * t & ho = dhf * t - w * max(0, w * (dhf - dhd))^2 / (2*a))" +
      "-> (abs(r - ro) > rp | w * h < w * ho - hp))" +
      "      )) & ( hp>0&rp>0&rv>=0&a>0 )").asFormula

    def dT(s : String) = debugT(s)

    val crushw = la(OrLeftT, "w=-1|w=1") && (QE, QE)
    // Q: Stefan, why did you change this from w() ?

    val crushor = (la(OrLeftT)*) & QE

    val absmax = abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxA"))) &
      la(MinMaxT, "", Some("max(0,w*(dhf-dhd))".asTerm)) &
      ls(AbsT, "", Some("abs(r)".asTerm)) &
      ls(AbsT, "", Some("abs(h)".asTerm)) &
      la(AbsT, "", Some("abs(r-0)".asTerm))

    val absmax2 = (ls(AbsT, "", Some("abs(r_3-ro_0)".asTerm)) | dT("abs(r_3-ro_0) not present")) &
      ( abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxI"))) &
        la(MinMaxT, "", Some("max((0,w*(dhf-dhd)))".asTerm)) | dT("max(0,w*(dhf-dhd)) not present")) &
      ( abbrv("max((0,w*(dhf-dhd_3)))".asTerm, Some(Variable("maxF"))) &
        la(MinMaxT, "", Some("max((0,w*(dhf-dhd_3)))".asTerm)) | dT("max(0,w*(dhf-dhd_3)) not present"))

    val crushabsmax = absmax & crushor

    val tactic = ls(implyR) & la(andL) & ls(wipeContextInductionT(Some(invariant))) & onBranch(
      (indInitLbl, dT("Base case") & ls(andR) & closeId),
      (indUseCaseLbl, dT("Use case") & ls(implyR) & (la(andL)*) & ls(andR) && (
        la(instantiateT(Variable("t"), Number(0))) &
          la(instantiateT(Variable("ro"), Number(0))) &
          la(instantiateT(Variable("ho"), Number(0))) & la(implyL) && (
          dT("Use case 1") & ls(hide, "abs(r)>rp|abs(h)>hp") &
            /*abbrv(Variable("max0"))(SuccPosition(0, PosInExpr(0::0::0::1::1::0::Nil))) // But more fragile */
            abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxI"))) & dT("abbrv") &
            la(MinMaxT, "", Some("max(0,w*(dhf-dhd))".asTerm)) & QE, //MinMaxT(AntePosition(9, PosInExpr(1 :: Nil)))
          dT("Absolute value") &
            ls(AbsT, "", Some("abs(r)".asTerm)) &   //AbsT(SuccPosition(0, PosInExpr(0 :: 0 :: Nil))) &
            ls(AbsT, "", Some("abs(h)".asTerm)) &   //AbsT(SuccPosition(0, PosInExpr(1 :: 0 :: Nil)))
            la(AbsT, "", Some("abs(r-0)".asTerm)) & //AbsT(AntePosition(9, PosInExpr(0 :: 0 :: Nil))) &
            dT("Use case 2") & QE
          ), AxiomCloseT
        )),
      (indStepLbl, dT("Step") & ls(implyR) & ls(boxSeqGenT(invariant)) & onBranch(
        (cutShowLbl, dT("Generalization Holds") &
          ls(boxSeqT) & ls(boxChoiceT) & ls(andR) && (
          dT("1.1") & ls(boxTestT) & ls(implyR) & ls(boxNDetAssign) & ls(skolemizeT) & AxiomCloseT, /* closed */
          dT("1.2") & ls(boxSeqT) & ls(boxNDetAssign) & ls(skolemizeT) & ls(boxSeqT) & ls(boxChoiceT) &
            dT("1.2.1") & hide(AntePosition(1)) & ls(andR) & /* almost identical branches */
            ls(substitutionBoxAssignT) & ls(boxTestT) & dT("1.2.2") & ls(implyR) & ls(boxNDetAssign) & ls(skolemizeT) &
            ls(andR) && (ls(andR) && (dT("cohide") & cohide(SuccPosition(0)) & QE, AxiomCloseT), AxiomCloseT)
            /* last line used to be handled by QE, but Max broke that */
            /* Would like to replace cohide by: ls(cohide, "-1=-1|-1=1") OR ls(cohide, "1=-1|1=1") (BUT two different branches)*/
          )),
        (cutUseLbl, dT("Generalization Strong Enough") &
          dT("Goal 69 (Solving)") &
          abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("max0"))) & dT("abbrv2") &
          /*abbrv(Variable("max0"))(AntePosition(0, PosInExpr(0::1::0::0::0::0::0::0::0::1::1::0::Nil)))*/
          ls(diffSolution(None, la(hide, "max0=max((0,w*(dhf-dhd)))"))) & dT("Diff. Solution") &
          /* cutting in the side condition that we expect from diff. solution. Remove once diff. solution produces it */
          cut("\\forall tside (0<=tside & tside<=kxtime_5 -> (w*(dhd_2()+ao*tside)>=w*dhf|w*ao>=a))".asFormula) &
          onBranch(
            (cutShowLbl,
              ls(cohide, "\\forall tside (0<=tside & tside<=kxtime_5 -> (w*(dhd_2()+ao*tside)>=w*dhf|w*ao>=a))") &
              dT("Ignore this branch - cut cannot be shown") /* TODO Counts as open goal */),
            (cutUseLbl, dT("bla") & /* repeat cut so that we can instantiate twice */
              cut("\\forall tside (0<=tside & tside<=kxtime_5 -> (w*(dhd_2()+ao*tside)>=w*dhf|w*ao>=a))".asFormula) & onBranch(
                (cutShowLbl, AxiomCloseT),
                (cutUseLbl,
                  ls(implyR) & (la(andL)*) & ls(andR) && (
                    ls(andR) && (
                      AxiomCloseT,
                      dT("Before skolemization") & (ls(skolemizeT)*) & dT("After skolemization") & ls(implyR) & ls(OrRightT) &
                        // here we'd want to access the previously introduced skolem symbol and the time introduced by diffSolution; goal 90
                        la(instantiateT(Variable("t"), "kxtime_5 + t_0".asTerm)) & // t_22+t_23: kxtime_5 == t_22, t_0 == t_23
                        la(instantiateT(Variable("ro"), "rv*(kxtime_5 + t_0)".asTerm)) & // rv*(t_22+t_23)
                        dT("Before CUT") &
                        // CUT: "(0 <= t_0+kxtime_5 & t_0+kxtime_5 < Max(0, w*(dhf-dhd))/a) | t_0+kxtime_5 >= Max(0, w*(dhf-dhd))/a"
                        cut("(0 <= t_0+kxtime_5 & t_0+kxtime_5 < max0/a) | t_0+kxtime_5 >= max0/a".asFormula) & onBranch(
                        (cutShowLbl, dT("Show Cut") & lastAnte(hide) & hide(AntePosition(0)) &
                          hide(SuccPosition(1)) & hide(SuccPosition(0)) & dT("Show Cut 2") &
                          ls(OrRightT) & lastAnte(OrLeftT) & (la(andL)*) & (ls(andR)*) & (QE | dT("Should be closed") & Tactics.stopT)),
                        (cutUseLbl, dT("Use Cut") & /*hide(AntePosition(0)) &*/ lastAnte(OrLeftT) && (
                          dT("Goal 110") & // All this closes fine; just trying to avoid recomputing it each time
                            locateAnte(instantiateT(Variable("ho"), "w*a/2*(t_0+kxtime_5)^2 + dhd*(t_0+kxtime_5)".asTerm), { case Forall(Variable("ho", None, Real) :: Nil, _) => true case _ => false }) &
                            dT("instantiate ho") & ((AxiomCloseT | l(NonBranchingPropositionalT))*) &
                            la(implyL, "0<=kxtime_5+t_0&kxtime_5+t_0 < max0/a&rv*(kxtime_5+t_0)=rv*(kxtime_5+t_0)&w*a/2*(t_0+kxtime_5)^2+dhd*(t_0+kxtime_5)=w*a/2*(kxtime_5+t_0)^2+dhd*(kxtime_5+t_0)|kxtime_5+t_0>=max0/a&rv*(kxtime_5+t_0)=rv*(kxtime_5+t_0)&w*a/2*(t_0+kxtime_5)^2+dhd*(t_0+kxtime_5)=dhf*(kxtime_5+t_0)-w*max0^2/(2*a)->abs(r-rv*(kxtime_5+t_0))>rp|w*h < w*(w*a/2*(t_0+kxtime_5)^2+dhd*(t_0+kxtime_5))-hp")
                            && ( (ls(OrRightT)*) & dT("lastSucc") & lastSucc(hide) & (ls(andR)*) & (AxiomCloseT | absmax2 & dT("before QE") & QE | dT("Shouldn't get here")) & dT("Shouldn't get here 2"),
                                 dT("cut 3") & la(OrLeftT, "0<=t_0&t_0 < max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=w*a/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=dhf*t_0-w*max((0,w*(dhf-dhd_3)))^2/(2*a)") && (
                              dT("Goal 124") & lastAnte(OrLeftT) && (
                                dT("lastSucc2") & lastSucc(hide) & (absmax2 & dT("Maybe here") & QE | dT("This should close") & Tactics.stopT), // closes
                                dT("Goal 135") & /*lastSucc(hide) & lastSucc(hide) &*/ (la(andL)*) & dT("Goal 145") & la(OrLeftT, "w*dhd_3>=w*dhf|w*ao>=a") && (
                                  dT("Goal 146") & absmax2 & crushw, // closes
                                  dT("Goal 148") & absmax2 & crushw  // closes
                                )
                              ),
                              dT("Goal 125") & lastAnte(OrLeftT) && (
                                dT("Goal 280") & absmax2 & QE, // closes
                                dT("Goal 281") & absmax2 & (la(hide, "\\forall tside (0<=tside&tside<=kxtime_5->w*(dhd_2()+ao*tside)>=w*dhf|w*ao>=a)")*)
                                  & (la(andL)*) & dT("Goal 282") & (la(OrLeftT)*) & QE // generates 12 subgoals
                              )
                            ) ),
                          // goal 111
                          dT("Goal 111") &
                              locateAnte(instantiateT(Variable("ho"), "dhf*(t_0+kxtime_5) - w*max0^2/(2*a)".asTerm), { case Forall(Variable("ho", None, Real) :: Nil, _) => true case _ => false }) &
                              dT("Goal 120-1") & lastAnte(implyL) && (
                              dT("Goal 122") & absmax2 & QE,
                              dT("Goal 123") & la(OrLeftT, "0<=t_0&t_0 < max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=w*a/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=dhf*t_0-w*max((0,w*(dhf-dhd_3)))^2/(2*a)")
                              && (
                                absmax2 & crushor, // takes a while (about 170 seconds)
                                dT("Goal 127") &
                                  la(TacticLibrary.eqLeft(exhaustive=true), "kxtime_1=0") &
                                  la(TacticLibrary.eqLeft(exhaustive=true), "kxtime_4()=0") &
                                  (la(andL)*) &
                                  la(instantiateT(Variable("tside"), Variable("kxtime", Some(5))), "\\forall tside (0<=tside&tside<=kxtime_5->w*(dhd_2()+ao*tside)>=w*dhf|w*ao>=a)") &
                                  la(implyL, "0<=kxtime_5&kxtime_5<=kxtime_5->w*(dhd_2()+ao*kxtime_5)>=w*dhf|w*ao>=a") && (
                                  absmax2 & QE,
                                  dT("Goal 193") & la(OrLeftT, "abs(r-rv*(kxtime_5+t_0))>rp|w*h < w*(dhf*(t_0+kxtime_5)-w*max0^2/(2*a))-hp") && (
                                    dT("Goal 194") & absmax2 & crushor, // takes a while (100 seconds or so)
                                    dT("Goal 195") & ls(hide, "abs(r_3-ro_0)>rp") & absmax2 &
                                      la(OrLeftT, "0>=w*(dhf-dhd_3)&max_1=0|0 < w*(dhf-dhd_3)&max_1=w*(dhf-dhd_3)") && (
                                      dT("Goal 214") & cut("w*ao>=a|!w*ao>=a".asFormula) & onBranch(
                                        (cutShowLbl, ls(cohide, "w*ao>=a|!w*ao>=a") & QE),
                                        (cutUseLbl, dT("Goal 214-2") & la(OrLeftT, "w*ao>=a|!w*ao>=a") && (
                                          QE,
                                          dT("Goal 231") & la(OrLeftT, "w*dhd_3>=w*dhf|w*ao>=a") && (
                                            dT("Goal 233") &
                                              la(instantiateT(Variable("tside"), Number(0)), "\\forall tside (0<=tside&tside<=kxtime_5->w*(dhd_2()+ao*tside)>=w*dhf|w*ao>=a)") &
                                              la(implyL, "0<=0&0<=kxtime_5->w*(dhd_2()+ao*0)>=w*dhf|w*ao>=a") && (
                                              QE,
                                              la(OrLeftT, "w*(dhd_2()+ao*0)>=w*dhf|w*ao>=a") && (
                                                crushor,
                                                la(PropositionalTacticsImpl.NotLeftT) & AxiomCloseT
                                                )
                                              ),
                                            la(PropositionalTacticsImpl.NotLeftT) & AxiomCloseT
                                            )
                                          ) )
                                      ),
                                      crushor
                                      )
                                    )
                                  )
                                )
                              )
                          )
                        )
                      )
                    ), QE /* End AndRight */
                  )
                ) /* End cutUseLbl of 2nd ODE cut */
              ) /* End onBranch 2nd ODE cut */
            ) /* End cutUseLbl of 1st ODE cut */
          ) /* End onBranch 1st ODE cut */
        ) /* End cutUseLbl "Generalization strong enough" */
      )) /* End indStepLbl */
    )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  "abs_test0" should "be provable" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/acasx/abs_test0.key"))

    val arith = arithmeticT

    val tactic = ls(ImplyRightT) & debugT("A simple goal with abs") &
      AbsT(AntePosition(0, PosInExpr(0 :: Nil))) & arith

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  "reflexivity" should "be provable 0" in {
    val arith = arithmeticT
    val s0 = new RootNode(sequent(Nil, Nil, "a=a".asFormula :: Nil))
    helper.runTactic(arith, s0) shouldBe 'closed
  }
  it should "be provable 1" in { //@todo why not?
    val arith = arithmeticT
    val s1 = new RootNode(sequent(Nil, Nil, "f(x)=f(x)".asFormula :: Nil))
    helper.runTactic(arith, s1) shouldBe 'closed
  }
  it should "NOT be provable 1b" in {
    val arith = arithmeticT
    val s1 = new RootNode(sequent(Nil, Nil, "f(x)=g(x)".asFormula :: Nil))
    helper.runTactic(arith, s1).openGoals() should have size 1
  }
  it should "NOT be provable 1c" in {
    val arith = arithmeticT
    val s1 = new RootNode(sequent(Nil, Nil, "f(x)=f(y)".asFormula :: Nil))
    helper.runTactic(arith, s1).openGoals() should have size 1
  }
  it should "NOT be provable 1d" in {
    val arith = arithmeticT
    val s1 = new RootNode(sequent(Nil, Nil, "f(x)=f(x_0)".asFormula :: Nil))
    helper.runTactic(arith, s1).openGoals() should have size 1
  }
  it should "NOT be provable 1e" in {
    val arith = arithmeticT
    val s1 = new RootNode(sequent(Nil, Nil, "f(x_0)=f(x_1)".asFormula :: Nil))
    helper.runTactic(arith, s1).openGoals() should have size 1
  }
  it should "be provable 2" in {
    val arith = arithmeticT
    val s2 = new RootNode(sequent(Nil, "f(x)=y".asFormula :: "1+y=0".asFormula :: Nil, "1+f(x)=0".asFormula :: Nil))
    helper.runTactic(arith, s2) shouldBe 'closed
  }
  it should "be provable 3" in {
    val arith = arithmeticT
    val s3 = new RootNode(sequent(Nil, "f(x)=y".asFormula :: Nil, "f(x)=f(x)".asFormula :: Nil))
    helper.runTactic(arith, s3) shouldBe 'closed
  }
  it should "be provable 4" in { //@todo why not?
    val arith = arithmeticT
    val s4 = new RootNode(sequent(Nil, Nil, "f(x)=y".asFormula  :: "f(x)=f(x)".asFormula :: Nil))
    helper.runTactic(arith, s4) shouldBe 'closed
  }
  it should "NOT be provable 4b" in {
    val arith = arithmeticT
    val s4 = new RootNode(sequent(Nil, Nil, "f(x)=y".asFormula  :: "f(x)=f(y)".asFormula :: Nil))
    helper.runTactic(arith, s4).openGoals() should have size 1
  }
  it should "be provable 5" in { //@todo why not?
    val arith = arithmeticT
    val s5 = new RootNode(sequent(Nil, "!(f(x)=f(x))".asFormula :: "!(f(x)=y)".asFormula :: Nil, Nil))
    helper.runTactic(arith, s5) shouldBe 'closed
  }
  it should "NOT be provable 5b" in {
  val arith = arithmeticT
    val s5 = new RootNode(sequent(Nil, "!(f(x)=f(y))".asFormula :: "!(f(x)=y)".asFormula :: Nil, Nil))
    helper.runTactic(arith, s5).openGoals() should have size 1
  }

  "min and max" should "be parseable" in {
    "min(0, x) <= max(x, 0)".asFormula shouldBe
      LessEqual(
        FuncOf(Function("min", None, Tuple(Real, Real), Real), Pair(Number(0), Variable("x"))),
        FuncOf(Function("max", None, Tuple(Real, Real), Real), Pair(Variable("x"), Number(0)))
      )
  }

}
