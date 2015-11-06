/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package casestudies

import java.io.File

import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory

import scala.collection.immutable
import scala.collection.immutable._

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.ODETactics._
import edu.cmu.cs.ls.keymaerax.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaerax.tactics.FOQuantifierTacticsImpl.{instantiateT,skolemizeT,instantiateExistentialQuanT}
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.{debugT, arithmeticT, ImplyRightT, AndLeftT, hideT, AndRightT,
  ImplyLeftT, AxiomCloseT, OrRightT, OrLeftT, cutT, locate, NotRightT, NotLeftT}
import edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.tactics.ArithmeticTacticsImpl.{AbsAxiomT,AbsT,MinMaxAxiomT,MinMaxT,EqualReflexiveT}
import edu.cmu.cs.ls.keymaerax.tactics.EqualityRewritingImpl.{abbrv,eqLeft}
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.{ApplyRule, Tactic, PositionTactic}
import edu.cmu.cs.ls.keymaerax.tactics.PropositionalTacticsImpl.{Propositional,NonBranchingPropositionalT,cohideT}
import edu.cmu.cs.ls.keymaerax.tactics.HybridProgramTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import edu.cmu.cs.ls.keymaerax.tools.{ToolEvidence, Mathematica, KeYmaera}
import testHelper.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}

import testHelper.ParserFactory._
import testHelper.SequentFactory._

import scala.collection.immutable.{Nil, Map}

/**
 * Created by smitsch on 3/27/15.
 * @author Stefan Mitsch
 * @author Jean-Baptiste Jeannin
 */
@SlowTest
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

    val evolutionDomain = "\\forall tside (0<=tside & tside<=kxtime_5 -> (w*(dhd_2()+ao*tside)>=w*dhf|w*ao>=a))"
    val initDomain = "w*dhd>=w*dhf|w*ao>=a"

    def dT(s : String) = debugT(s)

    val crushw = la(orL, "w=-1|w=1") && (QE, QE)
    // Q: Stefan, why did you change this from w() ?

    val crushor = (la(orL)*) & QE

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

    def cutEZ(c:Formula, t:Tactic) = cut(c) & onBranch(
      (cutShowLbl, t | dT("Cut didn't close") & Tactics.stopT)
    )

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
          ), closeId
        )),
      (indStepLbl, dT("Step") & ls(implyR) & ls(boxSeqGenT(invariant)) & onBranch(
        (cutShowLbl, dT("Generalization Holds") &
          ls(boxSeqT) & ls(boxChoiceT) & ls(andR) && (
          dT("1.1") & ls(boxTestT) & ls(implyR) & ls(boxNDetAssign) & ls(skolemizeT) & closeId, /* closed */
          dT("1.2") & ls(boxSeqT) & ls(boxNDetAssign) & ls(skolemizeT) & ls(boxSeqT) & ls(boxChoiceT) & dT("1.2.1") &
            la(hide, "((w=-1|w=1)&\\forall t \\forall ro \\forall ho (0<=t&t < max((0,w*(dhf-dhd)))/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=max((0,w*(dhf-dhd)))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-dhd)))^2/(2*a)->abs(r-ro)>rp|w*h < w*ho-hp))&(hp>0&rp>0&rv>=0&a>0)")
            & ls(andR) & /* almost identical branches */
            ls(substitutionBoxAssignT) & ls(boxTestT) & dT("1.2.2") & ls(implyR) & ls(boxNDetAssign) & ls(skolemizeT) &
            ls(andR) && (ls(andR) && (dT("cohide") & cohide(SuccPosition(0)) & QE, closeId), closeId)
          /* last line used to be handled by QE, but Max broke that */
          /* Would like to replace cohide by: ls(cohide, "-1=-1|-1=1") OR ls(cohide, "1=-1|1=1") (BUT
             two different branches)*/
          )),
        (cutUseLbl, dT("Generalization Strong Enough") &
          abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("max0"))) & dT("abbrv2") &
          /*abbrv(Variable("max0"))(AntePosition(0, PosInExpr(0::1::0::0::0::0::0::0::0::1::1::0::Nil)))*/
          cutEZ("!(w*dhd>=w*dhf|w*ao>=a) | (w*dhd>=w*dhf|w*ao>=a)".asFormula,
            ls(cohide, "!(w*dhd>=w*dhf|w*ao>=a) | (w*dhd>=w*dhf|w*ao>=a)") & QE) &
          la(orL, "!(w*dhd>=w*dhf|w*ao>=a) | (w*dhd>=w*dhf|w*ao>=a)") && (
          la(hide, "max0=max((0,w*(dhf-dhd)))") &
            la(hide, "((w=-1|w=1)&\\forall t \\forall ro \\forall ho (0<=t&t < max0/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=max0/a&ro=rv*t&ho=dhf*t-w*max0^2/(2*a)->abs(r-ro)>rp|w*h < w*ho-hp))&(hp>0&rp>0&rv>=0&a>0)") &
            dT("Before DI") &
            cutEZ("[{r'=-rv,dhd'=ao,h'=-dhd&w*dhd>=w*dhf|w*ao>=a}](0=1)".asFormula, // false as postcondition doesn't work
              ls(hide, "[{r'=-rv,dhd'=ao,h'=-dhd&w*dhd>=w*dhf|w*ao>=a}](((w=-1|w=1)&\\forall t \\forall ro \\forall ho (0<=t&t < max((0,w*(dhf-dhd)))/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=max((0,w*(dhf-dhd)))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-dhd)))^2/(2*a)->abs(r-ro)>rp|w*h < w*ho-hp))&(hp>0&rp>0&rv>=0&a>0))")
                & ls(DI)) &
            la(hide, "!(w*dhd>=w*dhf|w*ao>=a)") &
            dT("After DI") & ls(DC("0=1".asFormula)) & onBranch(
            (cutShowLbl, dT("After DC 1") & closeId),
            (cutUseLbl, dT("After DC 2") & ls(DW) & dT("after DW") &
              ls(implyR) & la(andL) & la(cohide, "0=1") & dT("before QE") & QE)
          ),
          ls(diffSolution(None, la(hide, "max0=max((0,w*(dhf-dhd)))"))) & dT("Diff. Solution") &
            /* cutting in the side condition that we expect from diff. solution. Remove once diff. sol. produces it */
            dT("bla") & ls(implyR) & (la(andL)*) & ls(andR) && (
            ls(andR) && (
              closeId,
              dT("Before skolemization") & (ls(skolemizeT)*) & dT("After skolemization") & ls(implyR) & ls(orR) &
                //here we'd want to access previously introduced skolem symbol and time introduced by diffSolution;goal 90
                la(instantiateT(Variable("t"), "kxtime_5 + t_0".asTerm)) & // t_22+t_23: kxtime_5 == t_22, t_0 == t_23
                la(instantiateT(Variable("ro"), "rv*(kxtime_5 + t_0)".asTerm)) & // rv*(t_22+t_23)
                dT("Before CUT") &
                cut("(0<=t_0+kxtime_5 & t_0+kxtime_5<max0/a) | t_0+kxtime_5 >= max0/a".asFormula) & onBranch(
                (cutShowLbl, dT("Show Cut") & la(hide, "max0=max((0,w*(dhf-dhd)))") &
                  la(hide, "\\forall ho (0<=kxtime_5+t_0&kxtime_5+t_0 < max0/a&rv*(kxtime_5+t_0)=rv*(kxtime_5+t_0)&ho=w*a/2*(kxtime_5+t_0)^2+dhd*(kxtime_5+t_0)|kxtime_5+t_0>=max0/a&rv*(kxtime_5+t_0)=rv*(kxtime_5+t_0)&ho=dhf*(kxtime_5+t_0)-w*max0^2/(2*a)->abs(r-rv*(kxtime_5+t_0))>rp|w*h < w*ho-hp)")
                  & ls(hide, "abs(r_3-ro_0)>rp") & ls(hide, "w*h_3 < w*ho_0-hp") & dT("Show Cut 2") & ls(orR) &
                  la(orL, "0<=t_0&t_0 < max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=w*a/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=dhf*t_0-w*max((0,w*(dhf-dhd_3)))^2/(2*a)")
                  & (la(andL)*) & (ls(andR)*) & (QE | dT("Should be closed") & Tactics.stopT)),
                (cutUseLbl, dT("Use Cut") &
                  la(orL, "0<=t_0+kxtime_5&t_0+kxtime_5 < max0/a|t_0+kxtime_5>=max0/a") && (
                  dT("Goal 110") & la(hide, initDomain) &
                    la(instantiateT(Variable("ho"), "w*a/2*(t_0+kxtime_5)^2 + dhd*(t_0+kxtime_5)".asTerm)) //, { case Forall(Variable("ho", None, Real) :: Nil, _) => true case _ => false })
                    & dT("instantiate ho") & ((closeId | l(NonBranchingPropositionalT))*) &
                    la(implyL, "0<=kxtime_5+t_0&kxtime_5+t_0 < max0/a&rv*(kxtime_5+t_0)=rv*(kxtime_5+t_0)&w*a/2*(t_0+kxtime_5)^2+dhd*(t_0+kxtime_5)=w*a/2*(kxtime_5+t_0)^2+dhd*(kxtime_5+t_0)|kxtime_5+t_0>=max0/a&rv*(kxtime_5+t_0)=rv*(kxtime_5+t_0)&w*a/2*(t_0+kxtime_5)^2+dhd*(t_0+kxtime_5)=dhf*(kxtime_5+t_0)-w*max0^2/(2*a)->abs(r-rv*(kxtime_5+t_0))>rp|w*h < w*(w*a/2*(t_0+kxtime_5)^2+dhd*(t_0+kxtime_5))-hp")
                    && (
                    (ls(orR)*) &
                      ls(hide, "kxtime_5+t_0>=max0/a&rv*(kxtime_5+t_0)=rv*(kxtime_5+t_0)&w*a/2*(t_0+kxtime_5)^2+dhd*(t_0+kxtime_5)=dhf*(kxtime_5+t_0)-w*max0^2/(2*a)")
                      & (ls(andR)*) & (closeId | absmax2 & dT("before QE") & QE | dT("Shouldn't get here")) & dT("Shouldn't get here 2"),
                    dT("cut 3") & la(orL, "0<=t_0&t_0 < max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=w*a/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=dhf*t_0-w*max((0,w*(dhf-dhd_3)))^2/(2*a)")
                      && (
                      dT("Goal 124") &
                        la(orL,"abs(r-rv*(kxtime_5+t_0))>rp|w*h < w*(w*a/2*(t_0+kxtime_5)^2+dhd*(t_0+kxtime_5))-hp")&& (
                        dT("lSucc2") & ls(hide, "w*h_3 < w*ho_0-hp") & absmax2 & QE,
                        dT("Goal 135") & ls(hide, "abs(r_3-ro_0)>rp") & (la(andL)*) &
                          la(orL, "w*dhd_3>=w*dhf|w*ao>=a") && (
                          dT("Goal 146") & absmax2 & crushw,
                          dT("Goal 148") & absmax2 & crushw
                          )
                        ),
                      dT("Goal 125") &
                        la(orL,"abs(r-rv*(kxtime_5+t_0))>rp|w*h < w*(w*a/2*(t_0+kxtime_5)^2+dhd*(t_0+kxtime_5))-hp")&& (
                        dT("Goal 280") & absmax2 & QE,
                        dT("Goal 281") & absmax2 & (la(andL)*) & (la(orL)*) & QE
                        )
                      ) ),
                  // goal 111
                  dT("Goal 111") &
                    la(instantiateT(Variable("ho"), "dhf*(t_0+kxtime_5) - w*max0^2/(2*a)".asTerm)) //, { case Forall(Variable("ho", None, Real) :: Nil, _) => true case _ => false })
                    & dT("Goal 120-1") &
                    la(implyL, "0<=kxtime_5+t_0&kxtime_5+t_0 < max0/a&rv*(kxtime_5+t_0)=rv*(kxtime_5+t_0)&dhf*(t_0+kxtime_5)-w*max0^2/(2*a)=w*a/2*(kxtime_5+t_0)^2+dhd*(kxtime_5+t_0)|kxtime_5+t_0>=max0/a&rv*(kxtime_5+t_0)=rv*(kxtime_5+t_0)&dhf*(t_0+kxtime_5)-w*max0^2/(2*a)=dhf*(kxtime_5+t_0)-w*max0^2/(2*a)->abs(r-rv*(kxtime_5+t_0))>rp|w*h < w*(dhf*(t_0+kxtime_5)-w*max0^2/(2*a))-hp")
                    && (
                    dT("Goal 122") & la(hide, initDomain) & absmax2 & QE,
                    dT("Goal 123") & la(orL, "0<=t_0&t_0 < max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=w*a/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=dhf*t_0-w*max((0,w*(dhf-dhd_3)))^2/(2*a)")
                      && (
                      la(hide, initDomain) & absmax2 & crushor, // takes a while (about 170 seconds)
                      dT("Goal 127") &
                        la(TacticLibrary.eqLeft(exhaustive=true), "kxtime_1=0") &
                        la(TacticLibrary.eqLeft(exhaustive=true), "kxtime_4()=0") &
                        (la(andL)*) & dT("Goal 193") &
                        la(orL, "abs(r-rv*(kxtime_5+t_0))>rp|w*h < w*(dhf*(t_0+kxtime_5)-w*max0^2/(2*a))-hp") && (
                        dT("Goal 194") & absmax2 & crushor, // takes a while (100 seconds or so)
                        dT("Goal 195") & ls(hide, "abs(r_3-ro_0)>rp") & absmax2 &
                          la(orL, "0>=w*(dhf-dhd_3)&max_1=0|0 < w*(dhf-dhd_3)&max_1=w*(dhf-dhd_3)") && (
                          dT("Goal 214") & cut("w*ao>=a|!w*ao>=a".asFormula) & onBranch(
                            (cutShowLbl, ls(cohide, "w*ao>=a|!w*ao>=a") & QE),
                            (cutUseLbl, dT("Goal 214-2") & la(orL, "w*ao>=a|!w*ao>=a") && (
                              dT("Goal 214-3") /*& la(hide, initDomain)*/ & QE,
                              dT("Goal 231") & la(orL, "w*dhd_3>=w*dhf|w*ao>=a") && (
                                dT("Goal 233") & la(orL, "w*dhd>=w*dhf|w*ao>=a") && (
                                  crushor,
                                  la(notL) & closeId
                                  ),
                                la(notL) & closeId
                                ) ) ) ),
                          la(hide, initDomain) & crushor
                          )
                        )

                      )
                    )
                  )
                  )
              )
              ), QE /* End AndRight */
            )
          /* ) End cutUseLbl of 2nd ODE cut */
          /* ) End onBranch 2nd ODE cut */
          /* ) End cutUseLbl of 1st ODE cut */
          /* ) End onBranch 1st ODE cut */
          ) /* end orL on cutEZ */
        ) /* End cutUseLbl "Generalization strong enough" */
      )) /* End indStepLbl */
    )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  "ACAS X 2-sided safe implicit with lemmas" should "be provable" in {

    /*** Helper tactics ***/
    def dT(s : String) = debugT(s)

    val crushw = la(orL, "w=-1|w=1") && (QE, QE)
    // Q: Stefan, why did you change this from w() ?

    val crushor = (la(orL)*) & QE

    val absmax = abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxA"))) &
      la(MinMaxT, "", Some("max(0,w*(dhf-dhd))".asTerm)) &
      ls(AbsT, "", Some("abs(r)".asTerm)) &
      ls(AbsT, "", Some("abs(h)".asTerm)) &
      la(AbsT, "", Some("abs(r-0)".asTerm))

    val absmax2 =
      (ls(AbsT, "", Some("abs(r_3-ro_0)".asTerm)) |
        dT("abs(r_3-ro_0) not present")) &
        ( abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxI"))) &
          la(MinMaxT, "", Some("max((0,w*(dhf-dhd)))".asTerm)) |
          dT("max(0,w*(dhf-dhd)) not present")) &
        ( abbrv("max((0,w*(dhf-dhd_3)))".asTerm, Some(Variable("maxF"))) &
          la(MinMaxT, "", Some("max((0,w*(dhf-dhd_3)))".asTerm)) |
          dT("max(0,w*(dhf-dhd_3)) not present"))

    val absmax3 =
      la(MinMaxT, "", Some("max(0,w*(dhfM-dhd))".asTerm)) &
        abbrv("max(0,w*(dhfM-dhd_3))".asTerm, Some(Variable("maxFM"))) &
        la(MinMaxT, "", Some("max(0,w*(dhfM-dhd_3))".asTerm))

    def cutEZ(c:Formula, t:Tactic) = cut(c) & onBranch(
      (cutShowLbl, t | dT("Cut didn't close") & Tactics.stopT)
    )

    def applyLemma(formula:String, apply:Tactic) =
      cut(formula.asFormula) & onBranch(
        (cutShowLbl, ls(cohideT, formula) &
          dT("apply Lemma " + formula) & apply),
        (cutUseLbl, dT("use Lemma " + formula) &
          la(implyL, formula) && (
          (ls(andR)*) & closeId, // checking hyps
          closeId // apply concl
          ))
      )

    val crushabsmax = absmax & crushor

    /*** Invariants etc. ***/
    val condImplLower = "    ("+
      "      \\forall t \\forall ro \\forall ho"+
      "        ((0 <= t & t < max(0, w * (dhf - dhd)) / a &"+
      "          ro = rv * t & ho = (w * a) / 2 * t^2 + dhd * t) |"+
      "          (t >= max(0, w * (dhf - dhd)) / a &"+
      "            ro = rv * t &"+
      "            ho = dhf * t - w * max(0, w * (dhf - dhd))^2 / (2*a))"+
      "            -> (abs(r - ro) > rp | w * h < w * ho - hp))"+
      "      )"
    val condImplUpper = "("+
      "        \\forall t \\forall ro \\forall ho"+
      "          ((0 <= t & t < max(0, w * (dhfM - dhd)) / aM &"+
      "            ro = rv * t & ho = (w * aM) / 2 * t^2 + dhd * t) |"+
      "            (t >= max(0, w * (dhfM - dhd)) / aM &"+
      "              ro = rv * t &"+
      "              ho = (dhd + w * max(0, w * (dhfM-dhd))) * t "+
      "                   - w * max(0, w * (dhfM - dhd))^2 / (2*aM))"+
      "              -> (abs(r - ro) > rp | w * h > w * ho + hp))"+
      "        )"
    val condImpl = "("+ condImplLower + "|"+ condImplUpper + ")"
    val invariantStr = "(( (w=-1 | w=1) &"+ condImpl +
      ") & (hp > 0 & rp >= 0 & rv >= 0 & a > 0 & aM > 0))"
    val invariant = invariantStr.asFormula

    val evolutionDomain =
      "(( w * dhd >= w * dhf  | w * ao >= a ) &" +
        " ((w * dhd <= w * dhfM & w * ao <= aM) | w * ao <= 0))"

    val initDomain = "w*dhd>=w*dhf|w*ao>=a"

    val ode = "r'=-rv,dhd'=ao,h'=-dhd"

    /*** Lower bound safe lemma and its tactic ***/

    val safeLemmaFormula =
      "maxI=max((0,w*(dhf-dhd))) &" +
        "(w*dhd>=w*dhf|w*ao>=a) &" +
        "(w=-1|w=1) &" +
        "(\\forall t \\forall ro \\forall ho (0<=t&t < maxI/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxI/a&ro=rv*t&ho=dhf*t-w*maxI^2/(2*a)->abs(r-ro)>rp|w*h < w*ho-hp)) &" +
        "hp>0 & rp>=0 & rv>=0 & a>0 &" +
        "(w*dhd_3>=w*dhf|w*ao>=a) &" +
        "kxtime_5>=0 &" +
        "r_3=r+-1*kxtime_5*rv &" +
        "dhd_3=dhd+ao*kxtime_5 &" +
        "h_3=1/2*(2*h+-2*dhd*kxtime_5+-1*ao*kxtime_5^2)" +
        "->" +
        "\\forall t \\forall ro \\forall ho (0<=t&t < max((0,w*(dhf-dhd_3)))/a&ro=rv*t&ho=w*a/2*t^2+dhd_3*t|t>=max((0,w*(dhf-dhd_3)))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-dhd_3)))^2/(2*a)->abs(r_3-ro)>rp|w*h_3 < w*ho-hp)"
    val safeUpLemmaFormula =
      "maxIM=max((0,w*(dhfM-dhd))) &"+
        "(w*dhd<=w*dhfM&w*ao<=aM|w*ao<=0) &" +
        "(w=-1|w=1) &" +
        "(\\forall t \\forall ro \\forall ho (0<=t&t < maxIM/aM&ro=rv*t&ho=w*aM/2*t^2+dhd*t|t>=maxIM/aM&ro=rv*t&ho=(dhd+w*maxIM)*t-w*maxIM^2/(2*aM)->abs(r-ro)>rp|w*h>w*ho+hp)) &" +
        "hp>0 & rp>=0 & rv>=0 & aM>0 &" +
        "(w*dhd_3<=w*dhfM&w*ao<=aM|w*ao<=0) &" +
        "kxtime_5>=0 &" +
        "r_3=r+-1*kxtime_5*rv &" +
        "dhd_3=dhd+ao*kxtime_5 &" +
        "h_3=1/2*(2*h+-2*dhd*kxtime_5+-1*ao*kxtime_5^2)" +
        "->" +
        "\\forall t \\forall ro \\forall ho (0<=t&t < max((0,w*(dhfM-dhd_3)))/aM&ro=rv*t&ho=w*aM/2*t^2+dhd_3*t|t>=max((0,w*(dhfM-dhd_3)))/aM&ro=rv*t&ho=(dhd_3+w*max((0,w*(dhfM-dhd_3))))*t-w*max((0,w*(dhfM-dhd_3)))^2/(2*aM)->abs(r_3-ro)>rp|w*h_3>w*ho+hp)"

    val safeLemmaSeq = sequent(Nil, Nil, safeLemmaFormula.asFormula :: Nil)
    val safeUpLemmaSeq = sequent(Nil, Nil, safeUpLemmaFormula.asFormula :: Nil)

    val safeLemmaTac = dT("lemma") & ls(implyR) & (la(andL)*) &
      dT("Before skolem") & (ls(skolemizeT)*) & dT("After skolem") &
      ls(implyR) & ls(orR) &
      //here we'd want to access previously introduced skolem symbol and
      // time introduced by diffSolution;goal 90
      la(instantiateT(Variable("t"), "kxtime_5 + t_0".asTerm)) & // t_22+t_23: kxtime_5 == t_22, t_0 == t_23
      la(instantiateT(Variable("ro"), "rv*(kxtime_5 + t_0)".asTerm)) & // rv*(t_22+t_23)
      dT("Before CUT") &
      cut("0<=t_0+kxtime_5&t_0+kxtime_5<maxI/a|t_0+kxtime_5>=maxI/a".asFormula) & onBranch(
      (cutShowLbl, dT("Show Cut") & la(hide, "maxI=max((0,w*(dhf-dhd)))") &
        la(hide, "\\forall ho (0<=kxtime_5+t_0&kxtime_5+t_0 < maxI/a&rv*(kxtime_5+t_0)=rv*(kxtime_5+t_0)&ho=w*a/2*(kxtime_5+t_0)^2+dhd*(kxtime_5+t_0)|kxtime_5+t_0>=maxI/a&rv*(kxtime_5+t_0)=rv*(kxtime_5+t_0)&ho=dhf*(kxtime_5+t_0)-w*maxI^2/(2*a)->abs(r-rv*(kxtime_5+t_0))>rp|w*h < w*ho-hp)")
        & ls(hide, "abs(r_3-ro_0)>rp") & ls(hide, "w*h_3<w*ho_0-hp") &
        dT("Show Cut 2") & ls(orR) &
        la(orL, "0<=t_0&t_0<max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=w*a/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=dhf*t_0-w*max((0,w*(dhf-dhd_3)))^2/(2*a)")
        & (la(andL)*) & (ls(andR)*) & dT("End CutShowLbl") & QE),
      (cutUseLbl, dT("Use Cut") &
        la(orL, "0<=t_0+kxtime_5&t_0+kxtime_5 < maxI/a|t_0+kxtime_5>=maxI/a") && (
        dT("Goal 110") & la(hide, initDomain) & // TODO remove this hide
          la(instantiateT(Variable("ho"), "w*a/2*(t_0+kxtime_5)^2 + dhd*(t_0+kxtime_5)".asTerm))
          & dT("instantiate ho 1 Lo") &
          la(implyL, "0<=kxtime_5+t_0&kxtime_5+t_0 < maxI/a&rv*(kxtime_5+t_0)=rv*(kxtime_5+t_0)&w*a/2*(t_0+kxtime_5)^2+dhd*(t_0+kxtime_5)=w*a/2*(kxtime_5+t_0)^2+dhd*(kxtime_5+t_0)|kxtime_5+t_0>=maxI/a&rv*(kxtime_5+t_0)=rv*(kxtime_5+t_0)&w*a/2*(t_0+kxtime_5)^2+dhd*(t_0+kxtime_5)=dhf*(kxtime_5+t_0)-w*maxI^2/(2*a)->abs(r-rv*(kxtime_5+t_0))>rp|w*h < w*(w*a/2*(t_0+kxtime_5)^2+dhd*(t_0+kxtime_5))-hp")
          && (
          dT("left of -> 1 Lo") & ls(orR) &
            ls(hide, "kxtime_5+t_0>=maxI/a&rv*(kxtime_5+t_0)=rv*(kxtime_5+t_0)&w*a/2*(t_0+kxtime_5)^2+dhd*(t_0+kxtime_5)=dhf*(kxtime_5+t_0)-w*maxI^2/(2*a)") &
            ls(hide, "abs(r_3-ro_0)>rp") & ls(hide, "w*h_3<w*ho_0-hp") &
            la(hide, "maxI=max((0,w*(dhf-dhd)))") & QE,
          dT("right of -> 1 Lo") &
            la(orL, "0<=t_0&t_0 < max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=w*a/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=dhf*t_0-w*max((0,w*(dhf-dhd_3)))^2/(2*a)")
            && (
            dT("1-early Lo") &
              la(orL,"abs(r-rv*(kxtime_5+t_0))>rp|w*h < w*(w*a/2*(t_0+kxtime_5)^2+dhd*(t_0+kxtime_5))-hp")
              && (QE, ls(hide, "abs(r_3-ro_0)>rp") & QE),
            dT("1-late Lo") &
              la(orL,"abs(r-rv*(kxtime_5+t_0))>rp|w*h < w*(w*a/2*(t_0+kxtime_5)^2+dhd*(t_0+kxtime_5))-hp")
              && (QE, ls(hide, "abs(r_3-ro_0)>rp") & absmax2 & crushw)
            )
          ),
        dT("final time in straight Lo") &
          la(instantiateT(Variable("ho"), "dhf*(t_0+kxtime_5) - w*maxI^2/(2*a)".asTerm)) &
          dT("instantiate ho 2 Lo") &
          la(implyL, "0<=kxtime_5+t_0&kxtime_5+t_0 < maxI/a&rv*(kxtime_5+t_0)=rv*(kxtime_5+t_0)&dhf*(t_0+kxtime_5)-w*maxI^2/(2*a)=w*a/2*(kxtime_5+t_0)^2+dhd*(kxtime_5+t_0)|kxtime_5+t_0>=maxI/a&rv*(kxtime_5+t_0)=rv*(kxtime_5+t_0)&dhf*(t_0+kxtime_5)-w*maxI^2/(2*a)=dhf*(kxtime_5+t_0)-w*maxI^2/(2*a)->abs(r-rv*(kxtime_5+t_0))>rp|w*h < w*(dhf*(t_0+kxtime_5)-w*maxI^2/(2*a))-hp")
          && (
          dT("left of -> 2 Lo") & ls(orR) &
            ls(hide, "0<=kxtime_5+t_0&kxtime_5+t_0 < maxI/a&rv*(kxtime_5+t_0)=rv*(kxtime_5+t_0)&dhf*(t_0+kxtime_5)-w*maxI^2/(2*a)=w*a/2*(kxtime_5+t_0)^2+dhd*(kxtime_5+t_0)") &
            ls(hide, "abs(r_3-ro_0)>rp") & ls(hide, "w*h_3<w*ho_0-hp") &
            la(hide, "maxI=max((0,w*(dhf-dhd)))") & QE,
          // also closes with: la(hide, initDomain) & absmax2 & QE
          dT("right of -> 2 Lo") & (la(andL)*) &
            la(orL, "0<=t_0&t_0 < max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=w*a/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=dhf*t_0-w*max((0,w*(dhf-dhd_3)))^2/(2*a)")
            && (
            dT("2-early Lo") &
              la(orL, "abs(r-rv*(kxtime_5+t_0))>rp|w*h<w*(dhf*(t_0+kxtime_5)-w*maxI^2/(2*a))-hp")
              && (QE, ls(hide, "abs(r_3-ro_0)>rp") & absmax2 & crushw),
            dT("2-late Up") &
              la(orL, "abs(r-rv*(kxtime_5+t_0))>rp|w*h<w*(dhf*(t_0+kxtime_5)-w*maxI^2/(2*a))-hp")
              && (QE, ls(hide, "abs(r_3-ro_0)>rp") & absmax2 & crushw)
            )
          )
        )
        )
    )

    val safeUpLemmaTac = dT("lemma Up") & ls(implyR) & (la(andL)*) &
      dT("Before skolem Up") & (ls(skolemizeT)*) & dT("After skolem Up") &
      ls(implyR) & ls(orR) &
      la(instantiateT(Variable("t"), "kxtime_5 + t_0".asTerm)) &
      la(instantiateT(Variable("ro"), "rv*(kxtime_5 + t_0)".asTerm)) &
      dT("Before CUT") &
      cut("0<=kxtime_5+t_0&kxtime_5+t_0<maxIM/aM|kxtime_5+t_0>=maxIM/aM".asFormula) & onBranch(
      (cutShowLbl, dT("Show Cut") & la(hide, "maxIM=max((0,w*(dhfM-dhd)))") &
        la(hide, "\\forall ho (0<=kxtime_5+t_0&kxtime_5+t_0 < maxIM/aM&rv*(kxtime_5+t_0)=rv*(kxtime_5+t_0)&ho=w*aM/2*(kxtime_5+t_0)^2+dhd*(kxtime_5+t_0)|kxtime_5+t_0>=maxIM/aM&rv*(kxtime_5+t_0)=rv*(kxtime_5+t_0)&ho=(dhd+w*maxIM)*(kxtime_5+t_0)-w*maxIM^2/(2*aM)->abs(r-rv*(kxtime_5+t_0))>rp|w*h>w*ho+hp)")
        & ls(hide, "abs(r_3-ro_0)>rp") & ls(hide, "w*h_3>w*ho_0+hp") &
        dT("Show Cut 2") & ls(orR) &
        la(orL, "0<=t_0&t_0<max((0,w*(dhfM-dhd_3)))/aM&ro_0=rv*t_0&ho_0=w*aM/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhfM-dhd_3)))/aM&ro_0=rv*t_0&ho_0=(dhd_3+w*max((0,w*(dhfM-dhd_3))))*t_0-w*max((0,w*(dhfM-dhd_3)))^2/(2*aM)")
        & (la(andL)*) & (ls(andR)*) & QE),
      (cutUseLbl, dT("Use Cut") &
        la(orL, "0<=kxtime_5+t_0&kxtime_5+t_0<maxIM/aM|kxtime_5+t_0>=maxIM/aM") && (
        dT("final time in parabola") & // add hide initDomain?
          la(instantiateT(Variable("ho"), "w*aM/2*(kxtime_5+t_0)^2+dhd*(kxtime_5+t_0)".asTerm)) &
          dT("instantiate ho 1 Up") &
          la(implyL, "0<=kxtime_5+t_0&kxtime_5+t_0 < maxIM/aM&rv*(kxtime_5+t_0)=rv*(kxtime_5+t_0)&w*aM/2*(kxtime_5+t_0)^2+dhd*(kxtime_5+t_0)=w*aM/2*(kxtime_5+t_0)^2+dhd*(kxtime_5+t_0)|kxtime_5+t_0>=maxIM/aM&rv*(kxtime_5+t_0)=rv*(kxtime_5+t_0)&w*aM/2*(kxtime_5+t_0)^2+dhd*(kxtime_5+t_0)=(dhd+w*maxIM)*(kxtime_5+t_0)-w*maxIM^2/(2*aM)->abs(r-rv*(kxtime_5+t_0))>rp|w*h>w*(w*aM/2*(kxtime_5+t_0)^2+dhd*(kxtime_5+t_0))+hp")
          && (
          dT("left of -> 1 Up") & ls(orR) &
            ls(hide, "kxtime_5+t_0>=maxIM/aM&rv*(kxtime_5+t_0)=rv*(kxtime_5+t_0)&w*aM/2*(kxtime_5+t_0)^2+dhd*(kxtime_5+t_0)=(dhd+w*maxIM)*(kxtime_5+t_0)-w*maxIM^2/(2*aM)") &
            ls(hide, "abs(r_3-ro_0)>rp") & ls(hide, "w*h_3>w*ho_0+hp") &
            la(hide, "maxIM=max((0,w*(dhfM-dhd)))") & QE,
          dT("right of -> 1 Up") & (la(andL)*) &
            la(orL, "0<=t_0&t_0 < max((0,w*(dhfM-dhd_3)))/aM&ro_0=rv*t_0&ho_0=w*aM/2*t_0^2+dhd_3*t_0|\nt_0>=max((0,w*(dhfM-dhd_3)))/aM&ro_0=rv*t_0&ho_0=(dhd_3+w*max((0,w*(dhfM-dhd_3))))*t_0-w*max((0,w*(dhfM-dhd_3)))^2/(2*aM)")
            && (
            dT("1-early Up") &
              la(orL, "abs(r-rv*(kxtime_5+t_0))>rp|w*h>w*(w*aM/2*(kxtime_5+t_0)^2+dhd*(kxtime_5+t_0))+hp")
              && (QE, QE),
            dT("1-late Up") &
              la(orL, "abs(r-rv*(kxtime_5+t_0))>rp|w*h>w*(w*aM/2*(kxtime_5+t_0)^2+dhd*(kxtime_5+t_0))+hp")
              && (QE, ls(hide, "abs(r_3-ro_0)>rp") & absmax3 & crushw)
            )
          ),
        dT("final time in straight Up") &
          la(instantiateT(Variable("ho"), "(dhd+w*maxIM)*(kxtime_5+t_0)-w*maxIM^2/(2*aM)".asTerm)) &
          dT("instantiate ho 2 Lo") &
          la(implyL, "0<=kxtime_5+t_0&kxtime_5+t_0 < maxIM/aM&rv*(kxtime_5+t_0)=rv*(kxtime_5+t_0)&(dhd+w*maxIM)*(kxtime_5+t_0)-w*maxIM^2/(2*aM)=w*aM/2*(kxtime_5+t_0)^2+dhd*(kxtime_5+t_0)|kxtime_5+t_0>=maxIM/aM&rv*(kxtime_5+t_0)=rv*(kxtime_5+t_0)&(dhd+w*maxIM)*(kxtime_5+t_0)-w*maxIM^2/(2*aM)=(dhd+w*maxIM)*(kxtime_5+t_0)-w*maxIM^2/(2*aM)->abs(r-rv*(kxtime_5+t_0))>rp|w*h>w*((dhd+w*maxIM)*(kxtime_5+t_0)-w*maxIM^2/(2*aM))+hp")
          && (
          dT("left of -> 2 Up") & ls(orR) &
            ls(hide, "0<=kxtime_5+t_0&kxtime_5+t_0 < maxIM/aM&rv*(kxtime_5+t_0)=rv*(kxtime_5+t_0)&(dhd+w*maxIM)*(kxtime_5+t_0)-w*maxIM^2/(2*aM)=w*aM/2*(kxtime_5+t_0)^2+dhd*(kxtime_5+t_0)") &
            ls(hide, "abs(r_3-ro_0)>rp") & ls(hide, "w*h_3>w*ho_0+hp") &
            la(hide, "maxIM=max((0,w*(dhfM-dhd)))") & QE,
          dT("right of -> 2 Up") & (la(andL)*) &
            la(orL, "0<=t_0&t_0 < max((0,w*(dhfM-dhd_3)))/aM&ro_0=rv*t_0&ho_0=w*aM/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhfM-dhd_3)))/aM&ro_0=rv*t_0&ho_0=(dhd_3+w*max((0,w*(dhfM-dhd_3))))*t_0-w*max((0,w*(dhfM-dhd_3)))^2/(2*aM)")
            && (
            dT("2-early Up") &
              la(orL, "abs(r-rv*(kxtime_5+t_0))>rp|w*h>w*((dhd+w*maxIM)*(kxtime_5+t_0)-w*maxIM^2/(2*aM))+hp")
              && (QE, ls(hide, "abs(r_3-ro_0)>rp") & absmax3 & crushw),
            dT("2-late Up") &
              la(orL, "abs(r-rv*(kxtime_5+t_0))>rp|w*h>w*((dhd+w*maxIM)*(kxtime_5+t_0)-w*maxIM^2/(2*aM))+hp")
              && (QE, ls(hide, "abs(r_3-ro_0)>rp") & absmax3 & crushw)
            )
          )
        )
        )
    )

    val safeLemma = helper.runTactic(safeLemmaTac, new RootNode(safeLemmaSeq))
    safeLemma shouldBe 'closed

    /*** Lemma machinery, TODO clean up ***/
    val lemmaDB = LemmaDBFactory.lemmaDB
    // create evidence (traces input into tool and output from tool)
    val evidence = new ToolEvidence(
      immutable.Map("input" -> safeLemmaFormula, "output" -> "true")) :: Nil
    // add lemma into DB, which creates an ID for it. use ID to apply the lemma
    val lemmaID = lemmaDB.add(Lemma(safeLemma.provableWitness, evidence))
    val safeLemmaApply = new ApplyRule(LookupLemma(lemmaDB, lemmaID)) {
      override def applicable(node: ProofNode): Boolean =
        node.sequent.sameSequentAs(safeLemmaSeq)
    }

    val safeUpLemma =
      helper.runTactic(safeUpLemmaTac, new RootNode(safeUpLemmaSeq))
    safeUpLemma shouldBe 'closed

    /*** Lemma machinery, TODO clean up ***/
    // create evidence (traces input into tool and output from tool)
    val evidenceUp = new ToolEvidence(
      immutable.Map("input" -> safeUpLemmaFormula, "output" -> "true")) :: Nil
    // add lemma into DB, which creates an ID for it. use ID to apply the lemma
    val lemmaUpID = lemmaDB.add(Lemma(safeUpLemma.provableWitness, evidenceUp))
    val safeUpLemmaApply = new ApplyRule(LookupLemma(lemmaDB, lemmaUpID)) {
      override def applicable(node: ProofNode): Boolean =
        node.sequent.sameSequentAs(safeUpLemmaSeq)
    }

    /*** Main safe theorem and its tactic ***/
    val safeSeq = new Sequent(Nil, immutable.IndexedSeq(), immutable.IndexedSeq(
      KeYmaeraXProblemParser(io.Source.fromInputStream(
        getClass.getResourceAsStream("/examples/casestudies/acasx/nodelay_2sided.key")).mkString)))
    val safeTac = ls(implyR) & la(andL) &
      ls(wipeContextInductionT(Some(invariant))) & onBranch(
      (indInitLbl, dT("Base case") & ls(andR) & closeId),
      (indUseCaseLbl, dT("Use case") & ls(implyR) & (la(andL)*) &
        dT("andL*") & ls(andR) && (
        dT("before orL") & la(orL, condImpl) && (
          dT("before inst 0 lower") &
            la(instantiateT(Variable("t"), Number(0))) &
            la(instantiateT(Variable("ro"), Number(0))) &
            la(instantiateT(Variable("ho"), Number(0))) & la(implyL) && (
            dT("Use case 1") & ls(hide, "abs(r)>rp|abs(h)>hp") &
              abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxI"))) &
              la(MinMaxT, "", Some("max(0,w*(dhf-dhd))".asTerm)) &
              dT("MinMax Lower") &
              /*(abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxI"))) |
                dT("max((0,w*(dhf-dhd))) not present")) &
              (la(MinMaxT, "", Some("max(0,w*(dhf-dhd))".asTerm)) |
                dT("max((0,w*(dhf-dhd))) not present")) &
              (abbrv("max((0,w*(dhfM-dhd)))".asTerm, Some(Variable("maxIM"))) |
                dT("max((0,w*(dhfM-dhd))) not present")) &
              (la(MinMaxT, "", Some("max(0,w*(dhfM-dhd))".asTerm)) |
                dT("max((0,w*(dhfM-dhd))) not present")) & */
              QE,
            dT("Absolute value") &
              ls(AbsT, "", Some("abs(r)".asTerm)) &
              ls(AbsT, "", Some("abs(h)".asTerm)) &
              la(AbsT, "", Some("abs(r-0)".asTerm)) &
              dT("Use case 2") & QE
            ),
          dT("before inst 0 upper") &
            la(instantiateT(Variable("t"), Number(0))) &
            la(instantiateT(Variable("ro"), Number(0))) &
            la(instantiateT(Variable("ho"), Number(0))) & la(implyL) && (
            dT("Use case 1") & ls(hide, "abs(r)>rp|abs(h)>hp") &
              abbrv("max((0,w*(dhfM-dhd)))".asTerm, Some(Variable("maxIM"))) &
              la(MinMaxT, "", Some("max(0,w*(dhfM-dhd))".asTerm)) &
              dT("MinMax Upper") & QE,
            dT("Absolute value") &
              ls(AbsT, "", Some("abs(r)".asTerm)) &
              ls(AbsT, "", Some("abs(h)".asTerm)) &
              la(AbsT, "", Some("abs(r-0)".asTerm)) &
              dT("Use case 2 upper") & QE
            )), closeId
        )),
      (indStepLbl, dT("Step") & ls(implyR) &
        ls(boxSeqGenT(invariant)) & onBranch(
        (cutShowLbl, dT("Generalization Holds") &
          ls(boxSeqT) & ls(boxChoiceT) & ls(andR) && (
          dT("1.1") & ls(boxTestT) & ls(implyR) & ls(boxNDetAssign) &
            ls(skolemizeT) & closeId, /* closed */
          dT("1.2") & ls(boxSeqT) & ls(boxNDetAssign) & ls(skolemizeT) &
            ls(boxSeqT) & ls(boxChoiceT) & dT("1.2.1") &
            la(hide, invariantStr) & ls(andR) & /* almost identical branches */
            dT("AAA") &
            ls(substitutionBoxAssignT) & dT("BBB") & ls(boxTestT) & dT("1.2.2") &
            ls(implyR) & ls(boxNDetAssign) & ls(skolemizeT) & ls(andR) &&
            (ls(andR) &&
              (dT("cohide") & cohide(SuccPosition(0)) & QE, closeId),
              closeId)
          /* last line used to be handled by QE, but Max broke that
             Would like to replace cohide by (BUT different branches):
             ls(cohide, "-1=-1|-1=1") OR ls(cohide, "1=-1|1=1") */
          )),
        (cutUseLbl, dT("Generalization Strong Enough") &
          cutEZ(("!" + evolutionDomain + " | " + evolutionDomain).asFormula,
            ls(cohide, "!" + evolutionDomain + " | " + evolutionDomain) & QE) &
          la(orL, "!" + evolutionDomain + " | " + evolutionDomain) && (
          la(hide, invariantStr) &
            dT("Before DI") &
            cutEZ(("[{"+ode+"&" + evolutionDomain + "}]" + "(0=1)").asFormula,
              // false as postcondition doesn't work
              ls(hide, "[{"+ode+"&" + evolutionDomain + "}]" + invariantStr)
                & ls(DI)) &
            la(hide, "!" + evolutionDomain) &
            dT("After DI") & ls(DC("0=1".asFormula)) & onBranch(
            (cutShowLbl, dT("After DC 1") & closeId),
            (cutUseLbl, dT("After DC 2") & ls(DW) & dT("after DW") &
              ls(implyR) & la(andL) & la(cohide, "0=1") & dT("before QE") & QE)
          ),
          dT("Before diff. solution") &
            abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxI"))) &
            abbrv("max((0,w*(dhfM-dhd)))".asTerm, Some(Variable("maxIM"))) &
            ls(diffSolution(None,
              la(hide, "maxI=max((0,w*(dhf-dhd)))") &
                la(hide, "maxIM=max((0,w*(dhfM-dhd)))"))) &
            dT("Diff. Solution") & ls(implyR) & (la(andL)*) &
            la(TacticLibrary.eqLeft(exhaustive=true), "kxtime_1=0") &
            la(hideT, "kxtime_1=0") &
            la(TacticLibrary.eqLeft(exhaustive=true), "kxtime_4()=0") &
            la(hideT, "kxtime_4()=0") &
            la(TacticLibrary.eqLeft(exhaustive=true), "r_2()=r") &
            la(hideT, "r_2()=r") &
            la(TacticLibrary.eqLeft(exhaustive=true), "dhd_2()=dhd") &
            la(hideT, "dhd_2()=dhd") &
            la(TacticLibrary.eqLeft(exhaustive=true), "h_2()=h") &
            la(hideT, "h_2()=h") & dT("bla") & ls(andR) && (
            ls(andR) && (
              closeId,
              dT("bla2") & ls(orR) &
                la(orL, "\\forall t \\forall ro \\forall ho (0<=t&t < maxI/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxI/a&ro=rv*t&ho=dhf*t-w*maxI^2/(2*a)->abs(r-ro)>rp|w*h < w*ho-hp)|\\forall t \\forall ro \\forall ho (0<=t&t < maxIM/aM&ro=rv*t&ho=w*aM/2*t^2+dhd*t|t>=maxIM/aM&ro=rv*t&ho=(dhd+w*maxIM)*t-w*maxIM^2/(2*aM)->abs(r-ro)>rp|w*h>w*ho+hp)")
                && (
                la(hide, "maxIM=max((0,w*(dhfM-dhd)))") & la(hide, "aM>0") &
                  la(hide, "w*dhd<=w*dhfM&w*ao<=aM|w*ao<=0") &
                  la(hide, "w*dhd_3<=w*dhfM&w*ao<=aM|w*ao<=0") &
                  ls(hide, "\\forall t \\forall ro \\forall ho (0<=t&t < max((0,w*(dhfM-dhd_3)))/aM&ro=rv*t&ho=w*aM/2*t^2+dhd_3*t|t>=max((0,w*(dhfM-dhd_3)))/aM&ro=rv*t&ho=(dhd_3+w*max((0,w*(dhfM-dhd_3))))*t-w*max((0,w*(dhfM-dhd_3)))^2/(2*aM)->abs(r_3-ro)>rp|w*h_3>w*ho+hp)") &
                  dT("lower lemma") &
                  applyLemma(safeLemmaFormula,safeLemmaApply),
                la(hide, "maxI=max((0,w*(dhf-dhd)))") & la(hide, "a>0") &
                  la(hide, "w*dhd>=w*dhf|w*ao>=a") &
                  la(hide, "w*dhd_3>=w*dhf|w*ao>=a") &
                  ls(hide, "\\forall t \\forall ro \\forall ho (0<=t&t < max((0,w*(dhf-dhd_3)))/a&ro=rv*t&ho=w*a/2*t^2+dhd_3*t|t>=max((0,w*(dhf-dhd_3)))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-dhd_3)))^2/(2*a)->abs(r_3-ro)>rp|w*h_3 < w*ho-hp)") &
                  dT("upper lemma") &
                  applyLemma(safeUpLemmaFormula,safeUpLemmaApply)
                )
              ),
            QE
            )
          ) /* end orL on cutEZ */
          ) /* End cutUseLbl "Generalization strong enough" */
      )) /* End indStepLbl */
    )

    val safeTheorem = helper.runTactic(safeTac, new RootNode(safeSeq))
    safeTheorem shouldBe 'closed
  }

  "ACAS X limited time safe implicit" should "be provable" in {

    /*** Helper tactics ***/
    def dT(s : String) = debugT(s)

    val crushw = la(orL, "w=-1|w=1") && (QE, QE)
    // Q: Stefan, why did you change this from w() ?

    val crushor = (la(orL)*) & QE

    val absmax = abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxA"))) &
      la(MinMaxT, "", Some("max(0,w*(dhf-dhd))".asTerm)) &
      ls(AbsT, "", Some("abs(r)".asTerm)) &
      ls(AbsT, "", Some("abs(h)".asTerm)) &
      la(AbsT, "", Some("abs(r-0)".asTerm))

    val absmax2 = la(MinMaxT, "", Some("max((0,w*(dhf-dhd)))".asTerm)) &
      abbrv("max((0,w*(dhf-dhd_3)))".asTerm, Some(Variable("maxF"))) &
      la(MinMaxT, "", Some("max((0,w*(dhf-dhd_3)))".asTerm))

    val absmax3 = la(MinMaxT, "", Some("max(0,w*(dhfM-dhd))".asTerm)) &
      abbrv("max(0,w*(dhfM-dhd_3))".asTerm, Some(Variable("maxFM"))) &
      la(MinMaxT, "", Some("max(0,w*(dhfM-dhd_3))".asTerm))

    def cutEZ(c:Formula, t:Tactic) = cut(c) & onBranch(
      (cutShowLbl, t | dT("Cut didn't close") & Tactics.stopT)
    )

    def applyLemma(formula:String, apply:Tactic) =
      cut(formula.asFormula) & onBranch(
        (cutShowLbl, ls(cohideT, formula) &
          dT("apply Lemma " + formula) & apply),
        (cutUseLbl, dT("use Lemma " + formula) &
          la(implyL, formula) && (
          (ls(andR)*) & closeId, // checking hyps
          closeId // apply concl
          ))
      )

    def applyLemma2(formula:String, apply:Tactic) =
    // when the conclusion doesn't match exactly, but close enough for QE to close
      cut(formula.asFormula) & onBranch(
        (cutShowLbl, ls(cohideT, formula) &
          dT("apply Lemma " + formula) & apply),
        (cutUseLbl, dT("use Lemma " + formula) &
          la(implyL, formula) && (
          (ls(andR)*) & closeId, // checking hyps
          QE // apply concl
          ))
      )

    val crushabsmax = absmax & crushor

    /*** Invariants etc. ***/
    val condImplLower = "("+"\n"+
      "\\forall t \\forall ro \\forall ho"+"\n"+
      " ((t<=tl-to | tl<0) &"+"\n"+
      "  ((0 <= t & t < max(0, w * (dhf - dhd)) / a &"+"\n"+
      "    ro = rv * t & ho = (w * a) / 2 * t^2 + dhd * t) |"+"\n"+
      "   (t >= max(0, w * (dhf - dhd)) / a &"+"\n"+
      "    ro = rv * t &"+"\n"+
      "    ho = dhf * t - w * max(0, w * (dhf - dhd))^2 / (2*a)))"+"\n"+
      "  -> (abs(r - ro) > rp | w * h < w * ho - hp))"+"\n"+
      ")"+"\n"
    val condImplUpper = "("+"\n"+
      "\\forall t \\forall ro \\forall ho"+"\n"+
      " ((t<=tl-to | tl<0) &"+"\n"+
      "  ((0 <= t & t < max(0, w * (dhfM - dhd)) / aM &"+"\n"+
      "    ro = rv * t &"+"\n"+
      "    ho = (w * aM) / 2 * t^2 + dhd * t) |"+"\n"+
      "   (t >= max(0, w * (dhfM - dhd)) / aM &"+"\n"+
      "    ro = rv * t &"+"\n"+
      "    ho = (dhd + w * max(0, w * (dhfM-dhd))) * t "+"\n"+
      "         - w * max(0, w * (dhfM - dhd))^2 / (2*aM)))"+"\n"+
      "  -> (abs(r - ro) > rp | w * h > w * ho + hp))"+"\n"+
      ")"+"\n"
    val condImpl = "("+ condImplLower + "|"+ condImplUpper + ")"
    val invariantStr = "(( ((w=-1 | w=1) & (to<=tl | tl<0)) & "+ condImpl +
      ") & (hp > 0 & rp >= 0 & rv >= 0 & a > 0 & aM > 0))"
    val invariant = invariantStr.asFormula

    val evolutionDomain = "((to<=tl | tl<0) &"+
      "(( w * dhd >= w * dhf  | w * ao >= a ) &" +
      " ((w * dhd <= w * dhfM & w * ao <= aM) | w * ao <= 0)))"

    val initDomain = "w*dhd>=w*dhf|w*ao>=a" // used?

    val ode = "r'=-rv,dhd'=ao,h'=-dhd,to'=1"

    /*** Lower bound safe lemma and its tactic ***/

    val safeLemmaFormula =
      "maxI=max((0,w*(dhf-dhd))) &" +
        "(w*dhd>=w*dhf|w*ao>=a) &" +
        "(w=-1|w=1) &" +
        "\\forall t \\forall ro \\forall ho ((t<=tl-to|tl < 0)&(0<=t&t < maxI/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxI/a&ro=rv*t&ho=dhf*t-w*maxI^2/(2*a))->abs(r-ro)>rp|w*h < w*ho-hp) &"+
        "hp>0 & rp>=0 & rv>=0 & a>0 &" +
        "(w*dhd_3>=w*dhf|w*ao>=a) &" +
        "to_3>=to &" +
        "r_3=r+-1*rv*(to_3-to) &" +
        "dhd_3=dhd+ao*(to_3-to) &" +
        "h_3=1/2*(2*h+-2*dhd*(to_3-to)+-1*ao*(to_3-to)^2)" +
        "->" +
        "\\forall t \\forall ro \\forall ho ((t<=tl-to_3|tl < 0)&(0<=t&t < max((0,w*(dhf-dhd_3)))/a&ro=rv*t&ho=w*a/2*t^2+dhd_3*t|t>=max((0,w*(dhf-dhd_3)))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-dhd_3)))^2/(2*a))->abs(r_3-ro)>rp|w*h_3 < w*ho-hp)"
    val safeUpLemmaFormula =
      "maxIM=max((0,w*(dhfM-dhd))) &"+
        "(w*dhd<=w*dhfM&w*ao<=aM|w*ao<=0) &" +
        "(w=-1|w=1) &" +
        "(\\forall t \\forall ro \\forall ho ((t<=tl-to|tl < 0)&(0<=t&t < maxIM/aM&ro=rv*t&ho=w*aM/2*t^2+dhd*t|t>=maxIM/aM&ro=rv*t&ho=(dhd+w*maxIM)*t-w*maxIM^2/(2*aM))->abs(r-ro)>rp|w*h>w*ho+hp)) &" +
        "hp>0 & rp>=0 & rv>=0 & aM>0 &" +
        "(w*dhd_3<=w*dhfM&w*ao<=aM|w*ao<=0) &" +
        "to_3>=to &" +
        "r_3=r+-1*rv*(to_3-to) &" +
        "dhd_3=dhd+ao*(to_3-to) &" +
        "h_3=1/2*(2*h+-2*dhd*(to_3-to)+-1*ao*(to_3-to)^2)" +
        "->" +
        "\\forall t \\forall ro \\forall ho ((t<=tl-to_3|tl < 0)&(0<=t&t < max((0,w*(dhfM-dhd_3)))/aM&ro=rv*t&ho=w*aM/2*t^2+dhd_3*t|t>=max((0,w*(dhfM-dhd_3)))/aM&ro=rv*t&ho=(dhd_3+w*max((0,w*(dhfM-dhd_3))))*t-w*max((0,w*(dhfM-dhd_3)))^2/(2*aM))->abs(r_3-ro)>rp|w*h_3>w*ho+hp)"

    val safeLemmaSeq = sequent(Nil, Nil, safeLemmaFormula.asFormula :: Nil)
    val safeUpLemmaSeq = sequent(Nil, Nil, safeUpLemmaFormula.asFormula :: Nil)

    val safeLemmaTac = dT("lemma") & ls(implyR) & (la(andL)*) &
      dT("Before skolem") & (ls(skolemizeT)*) & dT("After skolem") &
      ls(implyR) & ls(orR) &
      la(instantiateT(Variable("t"), "((to_3-to)+t_0)".asTerm)) &
      la(instantiateT(Variable("ro"), "rv*((to_3-to)+t_0)".asTerm)) &
      dT("Before CUT") &
      cut("0<=((to_3-to)+t_0)&((to_3-to)+t_0)<maxI/a|((to_3-to)+t_0)>=maxI/a".asFormula) & onBranch(
      (cutShowLbl, dT("Show Cut") & la(hide, "maxI=max((0,w*(dhf-dhd)))") &
        la(hide, "\\forall ho ((((to_3-to)+t_0)<=tl-to|tl < 0)&(0<=((to_3-to)+t_0)&((to_3-to)+t_0) < maxI/a&rv*((to_3-to)+t_0)=rv*((to_3-to)+t_0)&ho=w*a/2*((to_3-to)+t_0)^2+dhd*((to_3-to)+t_0)|((to_3-to)+t_0)>=maxI/a&rv*((to_3-to)+t_0)=rv*((to_3-to)+t_0)&ho=dhf*((to_3-to)+t_0)-w*maxI^2/(2*a))->abs(r-rv*((to_3-to)+t_0))>rp|w*h < w*ho-hp)")
        & ls(hide, "abs(r_3-ro_0)>rp") & ls(hide, "w*h_3<w*ho_0-hp") &
        dT("Show Cut 2") & ls(orR) & la(andL) &
        la(hide, "t_0<=tl-to_3|tl < 0") &
        la(orL, "0<=t_0&t_0<max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=w*a/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=dhf*t_0-w*max((0,w*(dhf-dhd_3)))^2/(2*a)")
        & (la(andL)*) & (ls(andR)*) &dT("End CutShowLbl") & QE),
      (cutUseLbl, dT("Use Cut") &
        la(orL, "0<=((to_3-to)+t_0)&((to_3-to)+t_0) < maxI/a|((to_3-to)+t_0)>=maxI/a") && (
        dT("Goal 110") & la(hide, initDomain) & // TODO remove this hide
          la(instantiateT(Variable("ho"), "w*a/2*((to_3-to)+t_0)^2 + dhd*((to_3-to)+t_0)".asTerm))
          & dT("instantiate ho 1 Lo") &
          la(implyL, "((((to_3-to)+t_0)<=tl-to|tl < 0)&(0<=((to_3-to)+t_0)&((to_3-to)+t_0) < maxI/a&rv*((to_3-to)+t_0)=rv*((to_3-to)+t_0)&w*a/2*((to_3-to)+t_0)^2+dhd*((to_3-to)+t_0)=w*a/2*((to_3-to)+t_0)^2+dhd*((to_3-to)+t_0)|((to_3-to)+t_0)>=maxI/a&rv*((to_3-to)+t_0)=rv*((to_3-to)+t_0)&w*a/2*((to_3-to)+t_0)^2+dhd*((to_3-to)+t_0)=dhf*((to_3-to)+t_0)-w*maxI^2/(2*a)))->abs(r-rv*((to_3-to)+t_0))>rp|w*h < w*(w*a/2*((to_3-to)+t_0)^2+dhd*((to_3-to)+t_0))-hp")
          && (
          dT("left of -> 1 Lo") & la(andL) &
            ls(hide, "abs(r_3-ro_0)>rp") & ls(hide, "w*h_3<w*ho_0-hp") &
            la(hide, "maxI=max((0,w*(dhf-dhd)))") &
            ls(andR) && (
            ls(orR) & dT("tl 1") & QE,
            ls(orR) &
              ls(hide, "((to_3-to)+t_0)>=maxI/a&rv*((to_3-to)+t_0)=rv*((to_3-to)+t_0)&w*a/2*((to_3-to)+t_0)^2+dhd*((to_3-to)+t_0)=dhf*((to_3-to)+t_0)-w*maxI^2/(2*a)") &
              dT("End L1") & QE
            ),
          dT("right of -> 1 Lo") &
            la(andL, "(t_0<=tl-to_3|tl < 0)&(0<=t_0&t_0 < max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=w*a/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=dhf*t_0-w*max((0,w*(dhf-dhd_3)))^2/(2*a))") &
            la(hide, "t_0<=tl-to_3|tl < 0") &
            la(orL, "0<=t_0&t_0 < max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=w*a/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=dhf*t_0-w*max((0,w*(dhf-dhd_3)))^2/(2*a)")
            && (
            dT("1-early Lo") &
              la(orL,"abs(r-rv*((to_3-to)+t_0))>rp|w*h < w*(w*a/2*((to_3-to)+t_0)^2+dhd*((to_3-to)+t_0))-hp")
              && (QE, ls(hide, "abs(r_3-ro_0)>rp") & dT("End R1E") & QE),
            dT("1-late Lo") &
              la(orL,"abs(r-rv*((to_3-to)+t_0))>rp|w*h < w*(w*a/2*((to_3-to)+t_0)^2+dhd*((to_3-to)+t_0))-hp")
              && (QE, ls(hide, "abs(r_3-ro_0)>rp") & absmax2 & dT("End R1L") & crushw)
            )
          ),
        dT("final time in straight Lo") &
          la(instantiateT(Variable("ho"), "dhf*((to_3-to)+t_0) - w*maxI^2/(2*a)".asTerm)) &
          dT("instantiate ho 2 Lo") &
          la(implyL, "((((to_3-to)+t_0)<=tl-to|tl < 0)&(0<=((to_3-to)+t_0)&((to_3-to)+t_0) < maxI/a&rv*((to_3-to)+t_0)=rv*((to_3-to)+t_0)&dhf*((to_3-to)+t_0)-w*maxI^2/(2*a)=w*a/2*((to_3-to)+t_0)^2+dhd*((to_3-to)+t_0)|((to_3-to)+t_0)>=maxI/a&rv*((to_3-to)+t_0)=rv*((to_3-to)+t_0)&dhf*((to_3-to)+t_0)-w*maxI^2/(2*a)=dhf*((to_3-to)+t_0)-w*maxI^2/(2*a)))->abs(r-rv*((to_3-to)+t_0))>rp|w*h < w*(dhf*((to_3-to)+t_0)-w*maxI^2/(2*a))-hp")
          && (
          dT("left of -> 2 Lo") & la(andL) &
            ls(hide, "abs(r_3-ro_0)>rp") & ls(hide, "w*h_3<w*ho_0-hp") &
            la(hide, "maxI=max((0,w*(dhf-dhd)))") &
            ls(andR) && (
            ls(orR) & dT("tl 2") & QE,
            ls(orR) &
              ls(hide, "0<=to_3-to+t_0&to_3-to+t_0 < maxI/a&rv*(to_3-to+t_0)=rv*(to_3-to+t_0)&dhf*(to_3-to+t_0)-w*maxI^2/(2*a)=w*a/2*(to_3-to+t_0)^2+dhd*(to_3-to+t_0)") &
              dT("End L2") & QE
            ),
          dT("right of -> 2 Lo") &
            la(andL, "(t_0<=tl-to_3|tl < 0)&(0<=t_0&t_0 < max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=w*a/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=dhf*t_0-w*max((0,w*(dhf-dhd_3)))^2/(2*a))") &
            la(hide, "t_0<=tl-to_3|tl < 0") &
            la(orL, "0<=t_0&t_0 < max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=w*a/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=dhf*t_0-w*max((0,w*(dhf-dhd_3)))^2/(2*a)")
            && (
            dT("2-early Lo") &
              la(orL, "abs(r-rv*((to_3-to)+t_0))>rp|w*h<w*(dhf*((to_3-to)+t_0)-w*maxI^2/(2*a))-hp")
              && (QE, ls(hide, "abs(r_3-ro_0)>rp") & absmax2 & dT("End L2E") & crushw),
            dT("2-late Lo") &
              la(orL, "abs(r-rv*((to_3-to)+t_0))>rp|w*h<w*(dhf*((to_3-to)+t_0)-w*maxI^2/(2*a))-hp")
              && (QE, ls(hide, "abs(r_3-ro_0)>rp") & absmax2 & dT("End L2L") & crushw)
            )
          )
        )
        )
    )

    val safeUpLemmaTac = dT("lemma Up") & ls(implyR) & (la(andL)*) &
      dT("Before skolem Up") & (ls(skolemizeT)*) & dT("After skolem Up") &
      ls(implyR) & ls(orR) &
      la(instantiateT(Variable("t"), "((to_3-to)+t_0)".asTerm)) &
      la(instantiateT(Variable("ro"), "rv*((to_3-to)+t_0)".asTerm)) &
      dT("Before CUT") &
      cut("0<=((to_3-to)+t_0)&((to_3-to)+t_0)<maxIM/aM|((to_3-to)+t_0)>=maxIM/aM".asFormula) & onBranch(
      (cutShowLbl, dT("Show Cut") & la(hide, "maxIM=max((0,w*(dhfM-dhd)))") &
        la(hide, "\\forall ho ((to_3-to+t_0<=tl-to|tl < 0)&(0<=to_3-to+t_0&to_3-to+t_0 < maxIM/aM&rv*(to_3-to+t_0)=rv*(to_3-to+t_0)&ho=w*aM/2*(to_3-to+t_0)^2+dhd*(to_3-to+t_0)|to_3-to+t_0>=maxIM/aM&rv*(to_3-to+t_0)=rv*(to_3-to+t_0)&ho=(dhd+w*maxIM)*(to_3-to+t_0)-w*maxIM^2/(2*aM))->abs(r-rv*(to_3-to+t_0))>rp|w*h>w*ho+hp)")
        & ls(hide, "abs(r_3-ro_0)>rp") & ls(hide, "w*h_3>w*ho_0+hp") &
        dT("Show Cut 2") & ls(orR) & la(andL) &
        la(hide, "t_0<=tl-to_3|tl < 0") &
        la(orL, "0<=t_0&t_0<max((0,w*(dhfM-dhd_3)))/aM&ro_0=rv*t_0&ho_0=w*aM/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhfM-dhd_3)))/aM&ro_0=rv*t_0&ho_0=(dhd_3+w*max((0,w*(dhfM-dhd_3))))*t_0-w*max((0,w*(dhfM-dhd_3)))^2/(2*aM)")
        & (la(andL)*) & (ls(andR)*) & dT("End CutShowLbl") & QE),
      (cutUseLbl, dT("Use Cut") &
        la(orL, "0<=((to_3-to)+t_0)&((to_3-to)+t_0)<maxIM/aM|((to_3-to)+t_0)>=maxIM/aM") && (
        dT("final time in parabola") & // add hide initDomain?
          la(instantiateT(Variable("ho"), "w*aM/2*((to_3-to)+t_0)^2+dhd*((to_3-to)+t_0)".asTerm)) &
          dT("instantiate ho 1 Up") &
          la(implyL, "(to_3-to+t_0<=tl-to|tl < 0)&(0<=to_3-to+t_0&to_3-to+t_0 < maxIM/aM&rv*(to_3-to+t_0)=rv*(to_3-to+t_0)&w*aM/2*(to_3-to+t_0)^2+dhd*(to_3-to+t_0)=w*aM/2*(to_3-to+t_0)^2+dhd*(to_3-to+t_0)|to_3-to+t_0>=maxIM/aM&rv*(to_3-to+t_0)=rv*(to_3-to+t_0)&w*aM/2*(to_3-to+t_0)^2+dhd*(to_3-to+t_0)=(dhd+w*maxIM)*(to_3-to+t_0)-w*maxIM^2/(2*aM))->abs(r-rv*(to_3-to+t_0))>rp|w*h>w*(w*aM/2*(to_3-to+t_0)^2+dhd*(to_3-to+t_0))+hp")
          && (
          dT("left of -> 1 Up") &
            ls(hide, "abs(r_3-ro_0)>rp") & ls(hide, "w*h_3>w*ho_0+hp") &
            la(hide, "maxIM=max((0,w*(dhfM-dhd)))") &
            ls(andR) && (
            ls(orR) & dT("tl 1") & QE,
            ls(orR) &
              ls(hide, "((to_3-to)+t_0)>=maxIM/aM&rv*((to_3-to)+t_0)=rv*((to_3-to)+t_0)&w*aM/2*((to_3-to)+t_0)^2+dhd*((to_3-to)+t_0)=(dhd+w*maxIM)*((to_3-to)+t_0)-w*maxIM^2/(2*aM)") &
              dT("End L1") & QE
            ),
          dT("right of -> 1 Up") &
            la(andL, "(t_0<=tl-to_3|tl < 0)&(0<=t_0&t_0 < max((0,w*(dhfM-dhd_3)))/aM&ro_0=rv*t_0&ho_0=w*aM/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhfM-dhd_3)))/aM&ro_0=rv*t_0&ho_0=(dhd_3+w*max((0,w*(dhfM-dhd_3))))*t_0-w*max((0,w*(dhfM-dhd_3)))^2/(2*aM))") &
            la(hide, "t_0<=tl-to_3|tl < 0") &
            la(orL, "0<=t_0&t_0 < max((0,w*(dhfM-dhd_3)))/aM&ro_0=rv*t_0&ho_0=w*aM/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhfM-dhd_3)))/aM&ro_0=rv*t_0&ho_0=(dhd_3+w*max((0,w*(dhfM-dhd_3))))*t_0-w*max((0,w*(dhfM-dhd_3)))^2/(2*aM)")
            && (
            dT("1-early Up") &
              la(orL, "abs(r-rv*((to_3-to)+t_0))>rp|w*h>w*(w*aM/2*((to_3-to)+t_0)^2+dhd*((to_3-to)+t_0))+hp")
              && (QE, QE),
            dT("1-late Up") &
              la(orL, "abs(r-rv*((to_3-to)+t_0))>rp|w*h>w*(w*aM/2*((to_3-to)+t_0)^2+dhd*((to_3-to)+t_0))+hp")
              && (QE, ls(hide, "abs(r_3-ro_0)>rp") & absmax3 & crushw)
            )
          ),
        dT("final time in straight Up") &
          la(instantiateT(Variable("ho"), "(dhd+w*maxIM)*((to_3-to)+t_0)-w*maxIM^2/(2*aM)".asTerm)) &
          dT("instantiate ho 2 Lo") &
          la(implyL, "(to_3-to+t_0<=tl-to|tl < 0)&(0<=to_3-to+t_0&to_3-to+t_0 < maxIM/aM&rv*(to_3-to+t_0)=rv*(to_3-to+t_0)&(dhd+w*maxIM)*(to_3-to+t_0)-w*maxIM^2/(2*aM)=w*aM/2*(to_3-to+t_0)^2+dhd*(to_3-to+t_0)|to_3-to+t_0>=maxIM/aM&rv*(to_3-to+t_0)=rv*(to_3-to+t_0)&(dhd+w*maxIM)*(to_3-to+t_0)-w*maxIM^2/(2*aM)=(dhd+w*maxIM)*(to_3-to+t_0)-w*maxIM^2/(2*aM))->abs(r-rv*(to_3-to+t_0))>rp|w*h>w*((dhd+w*maxIM)*(to_3-to+t_0)-w*maxIM^2/(2*aM))+hp")
          && (
          dT("left of -> 2 Up") &
            ls(hide, "abs(r_3-ro_0)>rp") & ls(hide, "w*h_3>w*ho_0+hp") &
            la(hide, "maxIM=max((0,w*(dhfM-dhd)))") &
            ls(andR) && (
            ls(orR) & dT("tl 2b") & QE,
            ls(orR) &
              ls(hide, "0<=((to_3-to)+t_0)&((to_3-to)+t_0) < maxIM/aM&rv*((to_3-to)+t_0)=rv*((to_3-to)+t_0)&(dhd+w*maxIM)*((to_3-to)+t_0)-w*maxIM^2/(2*aM)=w*aM/2*((to_3-to)+t_0)^2+dhd*((to_3-to)+t_0)") &
              QE
            ),
          dT("right of -> 2 Up") &
            la(andL, "(t_0<=tl-to_3|tl < 0)&(0<=t_0&t_0 < max((0,w*(dhfM-dhd_3)))/aM&ro_0=rv*t_0&ho_0=w*aM/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhfM-dhd_3)))/aM&ro_0=rv*t_0&ho_0=(dhd_3+w*max((0,w*(dhfM-dhd_3))))*t_0-w*max((0,w*(dhfM-dhd_3)))^2/(2*aM))") &
            la(hide, "t_0<=tl-to_3|tl < 0") &
            la(orL, "0<=t_0&t_0 < max((0,w*(dhfM-dhd_3)))/aM&ro_0=rv*t_0&ho_0=w*aM/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhfM-dhd_3)))/aM&ro_0=rv*t_0&ho_0=(dhd_3+w*max((0,w*(dhfM-dhd_3))))*t_0-w*max((0,w*(dhfM-dhd_3)))^2/(2*aM)")
            && (
            dT("2-early Up") &
              la(orL, "abs(r-rv*((to_3-to)+t_0))>rp|w*h>w*((dhd+w*maxIM)*((to_3-to)+t_0)-w*maxIM^2/(2*aM))+hp")
              && (QE, ls(hide, "abs(r_3-ro_0)>rp") & absmax3 & crushw),
            dT("2-late Up") &
              la(orL, "abs(r-rv*((to_3-to)+t_0))>rp|w*h>w*((dhd+w*maxIM)*((to_3-to)+t_0)-w*maxIM^2/(2*aM))+hp")
              && (QE, ls(hide, "abs(r_3-ro_0)>rp") & absmax3 & crushw)
            )
          )
        )
        )
    )

    val safeLemma = helper.runTactic(safeLemmaTac, new RootNode(safeLemmaSeq))
    safeLemma shouldBe 'closed

    /*** Lemma machinery, TODO clean up ***/
    val lemmaDB = LemmaDBFactory.lemmaDB
    // create evidence (traces input into tool and output from tool)
    val evidence = new ToolEvidence(
      immutable.Map("input" -> safeLemmaFormula, "output" -> "true")) :: Nil
    // add lemma into DB, which creates an ID for it. use ID to apply the lemma
    val lemmaID = lemmaDB.add(Lemma(safeLemma.provableWitness, evidence))
    val safeLemmaApply = new ApplyRule(LookupLemma(lemmaDB, lemmaID)) {
      override def applicable(node: ProofNode): Boolean =
        node.sequent.sameSequentAs(safeLemmaSeq)
    }

    val safeUpLemma =
      helper.runTactic(safeUpLemmaTac, new RootNode(safeUpLemmaSeq))
    safeUpLemma shouldBe 'closed

    /*** Lemma machinery, TODO clean up ***/
    // create evidence (traces input into tool and output from tool)
    val evidenceUp = new ToolEvidence(
      immutable.Map("input" -> safeUpLemmaFormula, "output" -> "true")) :: Nil
    // add lemma into DB, which creates an ID for it. use ID to apply the lemma
    val lemmaUpID = lemmaDB.add(Lemma(safeUpLemma.provableWitness, evidenceUp))
    val safeUpLemmaApply = new ApplyRule(LookupLemma(lemmaDB, lemmaUpID)) {
      override def applicable(node: ProofNode): Boolean =
        node.sequent.sameSequentAs(safeUpLemmaSeq)
    }

    /*** Main safe theorem and its tactic ***/
    val safeSeq = new Sequent(Nil, immutable.IndexedSeq(), immutable.IndexedSeq(
      KeYmaeraXProblemParser(io.Source.fromInputStream(
        getClass.getResourceAsStream("/examples/casestudies/acasx/nodelay_2sided_tl.key")).mkString)))
    val safeTac = ls(implyR) & la(andL) &
      ls(wipeContextInductionT(Some(invariant))) & onBranch(
      (indInitLbl, dT("Base case") & ls(andR) & closeId),
      (indUseCaseLbl, dT("Use case") & ls(implyR) &
        la(hide, "hp>0&rp>=0&rv>=0&a>0&aM>0") & // appears twice??
        dT("andL*") & la(andL) & ls(andR) && (
        (la(andL)*) & dT("before orL") & la(orL, condImpl) && (
          dT("before inst 0 lower") &
            la(instantiateT(Variable("t"), Number(0))) &
            la(instantiateT(Variable("ro"), Number(0))) &
            la(instantiateT(Variable("ho"), Number(0))) & la(implyL) && (
            dT("Use case 1") & ls(hide, "abs(r)>rp|abs(h)>hp") &
              abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxI"))) &
              la(MinMaxT, "", Some("max(0,w*(dhf-dhd))".asTerm)) & ls(andR)&&(
              QE,
              dT("MinMax Lower") & QE
              ),
            dT("Absolute value") &
              ls(AbsT, "", Some("abs(r)".asTerm)) &
              ls(AbsT, "", Some("abs(h)".asTerm)) &
              la(AbsT, "", Some("abs(r-0)".asTerm)) &
              dT("Use case 2") & QE
            ),
          dT("before inst 0 upper") &
            la(instantiateT(Variable("t"), Number(0))) &
            la(instantiateT(Variable("ro"), Number(0))) &
            la(instantiateT(Variable("ho"), Number(0))) & la(implyL) && (
            dT("Use case 1") & ls(hide, "abs(r)>rp|abs(h)>hp") &
              abbrv("max((0,w*(dhfM-dhd)))".asTerm, Some(Variable("maxIM"))) &
              la(MinMaxT, "", Some("max(0,w*(dhfM-dhd))".asTerm)) & ls(andR)&&(
              QE,
              dT("MinMax Upper") & QE
              ),
            dT("Absolute value") &
              ls(AbsT, "", Some("abs(r)".asTerm)) &
              ls(AbsT, "", Some("abs(h)".asTerm)) &
              la(AbsT, "", Some("abs(r-0)".asTerm)) &
              dT("Use case 2 upper") & QE
            )), closeId
        ) ),
      (indStepLbl, dT("Step") & ls(implyR) &
        ls(boxSeqGenT(invariant)) & onBranch(
        (cutShowLbl, dT("Generalization Holds") &
          dT("1.21") & (ls(boxSeqT)*) & ls(boxChoiceT) & ls(andR) && (
          ls(boxTestT) & ls(implyR) & ls(boxNDetAssign) &
            ls(skolemizeT) & closeId,
          dT("1.2a") & (ls(boxSeqT)*) & ls(substitutionBoxAssignT) & // to:=0
            dT("1.2b") & (ls(boxSeqT)*) & ls(boxNDetAssign) & ls(skolemizeT) & // dhf:=*
            dT("1.2u") & (ls(boxSeqT)*) & ls(boxNDetAssign) & ls(skolemizeT) & // dhfu:=*
            dT("1.2c") & (ls(boxSeqT)*) & ls(boxChoiceT) & // w:=-1; ++ w:=1;
            la(hide, invariantStr) & ls(andR) & /* almost identical branches */
            ls(substitutionBoxAssignT) & // w:=1 or w:=-1
            dT("1.2d") & (ls(boxSeqT)*) & ls(boxTestT) & ls(implyR) & // ?Cimpl
            dT("1.2e") & (ls(boxSeqT)*) & ls(boxNDetAssign) & ls(skolemizeT) & // ao:=*
            dT("1.2f") & ls(andR) && (
            ls(andR) && (
              dT("cohide") & cohide(SuccPosition(0)) & QE, QE),
            closeId
            )
          )
          ),
        (cutUseLbl, dT("Generalization Strong Enough") &
          cutEZ(("!" + evolutionDomain + " | " + evolutionDomain).asFormula,
            ls(cohide, "!" + evolutionDomain + " | " + evolutionDomain) & QE) &
          la(orL, "!" + evolutionDomain + " | " + evolutionDomain) && (
          la(hide, invariantStr) &
            dT("Before DI") &
            cutEZ(("[{"+ode+"&" + evolutionDomain + "}]" + "(0=1)").asFormula,
              // false as postcondition doesn't work
              ls(hide, "[{"+ode+"&" + evolutionDomain + "}]" + invariantStr)
                & ls(DI)) &
            la(hide, "!" + evolutionDomain) &
            dT("After DI") & ls(DC("0=1".asFormula)) & onBranch(
            (cutShowLbl, dT("After DC 1") & closeId),
            (cutUseLbl, dT("After DC 2") & ls(DW) & dT("after DW") &
              ls(implyR) & la(andL) & la(cohide, "0=1") & dT("before QE") & QE)
          ),
          dT("Before diff. solution") &
            abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxI"))) &
            abbrv("max((0,w*(dhfM-dhd)))".asTerm, Some(Variable("maxIM"))) &
            ls(diffSolution(None,
              la(hide, "maxI=max((0,w*(dhf-dhd)))") &
                la(hide, "maxIM=max((0,w*(dhfM-dhd)))"))) &
            dT("Diff. Solution") & ls(implyR) & (la(andL)*) & dT("eqLeft's") &
            la(TacticLibrary.eqLeft(exhaustive=true), "r_2()=r") &
            la(hideT, "r_2()=r") &
            la(TacticLibrary.eqLeft(exhaustive=true), "dhd_2()=dhd") &
            la(hideT, "dhd_2()=dhd") &
            la(TacticLibrary.eqLeft(exhaustive=true), "h_2()=h") &
            la(hideT, "h_2()=h") &
            la(TacticLibrary.eqLeft(exhaustive=true), "to_2()=to") &
            la(hideT, "to_2()=to") & dT("bla") & ls(andR) && (
            ls(andR) && (
              ls(andR) && (closeId, closeId),
              dT("bla2") & ls(orR) &
                la(hide, "to<=tl|tl < 0") & la(hide, "to_3<=tl|tl < 0") &
                la(orL, "\\forall t \\forall ro \\forall ho ((t<=tl-to|tl < 0)&(0<=t&t < maxI/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxI/a&ro=rv*t&ho=dhf*t-w*maxI^2/(2*a))->abs(r-ro)>rp|w*h < w*ho-hp)|\\forall t \\forall ro \\forall ho ((t<=tl-to|tl < 0)&(0<=t&t < maxIM/aM&ro=rv*t&ho=w*aM/2*t^2+dhd*t|t>=maxIM/aM&ro=rv*t&ho=(dhd+w*maxIM)*t-w*maxIM^2/(2*aM))->abs(r-ro)>rp|w*h>w*ho+hp)")
                && (
                dT("Before hide lower") &
                  la(hide, "maxIM=max((0,w*(dhfM-dhd)))") & la(hide, "aM>0") &
                  la(hide, "w*dhd<=w*dhfM&w*ao<=aM|w*ao<=0") &
                  la(hide, "w*dhd_3<=w*dhfM&w*ao<=aM|w*ao<=0") &
                  ls(hide, "\\forall t \\forall ro \\forall ho ((t<=tl-to_3|tl < 0)&(0<=t&t < max((0,w*(dhfM-dhd_3)))/aM&ro=rv*t&ho=w*aM/2*t^2+dhd_3*t|t>=max((0,w*(dhfM-dhd_3)))/aM&ro=rv*t&ho=(dhd_3+w*max((0,w*(dhfM-dhd_3))))*t-w*max((0,w*(dhfM-dhd_3)))^2/(2*aM))->abs(r_3-ro)>rp|w*h_3>w*ho+hp)") &
                  dT("lower lemma") &
                  applyLemma2(safeLemmaFormula,safeLemmaApply),
                dT("Before hide upper") &
                  la(hide, "maxI=max((0,w*(dhf-dhd)))") & la(hide, "a>0") &
                  la(hide, "w*dhd>=w*dhf|w*ao>=a") &
                  la(hide, "w*dhd_3>=w*dhf|w*ao>=a") &
                  ls(hide, "\\forall t \\forall ro \\forall ho ((t<=tl-to_3|tl < 0)&(0<=t&t < max((0,w*(dhf-dhd_3)))/a&ro=rv*t&ho=w*a/2*t^2+dhd_3*t|t>=max((0,w*(dhf-dhd_3)))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-dhd_3)))^2/(2*a))->abs(r_3-ro)>rp|w*h_3 < w*ho-hp)") &
                  dT("upper lemma") &
                  applyLemma2(safeUpLemmaFormula,safeUpLemmaApply)
                )
              ), QE
            )
          ) /* end orL on cutEZ */
          ) /* End cutUseLbl "Generalization strong enough" */
      )) /* End indStepLbl */
    )

    val safeTheorem = helper.runTactic(safeTac, new RootNode(safeSeq))
    safeTheorem shouldBe 'closed
  }

  "ACAS X safeable implicit" should "be provable" in {

    /*** Helper tactics ***/
    def dT(s : String) = Tactics.SubLabelBranch(s) & debugT(s)
    def lbl(s : String) = Tactics.SubLabelBranch(s) & debugT(s)

    val crushw = la(orL, "w=-1|w=1") && (dT("w=-1") & QE, dT("w=1") & QE)
    // Q: Stefan, why did you change this from w() ?

    val crushor = (la(orL)*) & QE

    val abs3 = ls(AbsT, "", Some("abs(r)".asTerm)) &
      ls(AbsT, "", Some("abs(h)".asTerm)) &
      la(AbsT, "", Some("abs(r-0)".asTerm))

    val abs3tl = ls(AbsT, "", Some("abs(r)".asTerm)) &
      ls(AbsT, "", Some("abs(h)".asTerm)) &
      la(AbsT, "", Some("abs(r-rv*(tl-tl)-0)".asTerm))

    val absmax = abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxA"))) &
      la(MinMaxT, "", Some("max(0,w*(dhf-dhd))".asTerm)) & abs3

    val absmax2 = la(MinMaxT, "", Some("max((0,w*(dhf-dhd)))".asTerm)) &
      abbrv("max((0,w*(dhf-dhd_3)))".asTerm, Some(Variable("maxF"))) &
      la(MinMaxT, "", Some("max((0,w*(dhf-dhd_3)))".asTerm))

    val absmax3 = la(MinMaxT, "", Some("max(0,w*(dhfUp-dhd))".asTerm)) &
      abbrv("max(0,w*(dhfUp-dhd_3))".asTerm, Some(Variable("maxFM"))) &
      la(MinMaxT, "", Some("max(0,w*(dhfUp-dhd_3))".asTerm))

    def cutEZ(c:Formula, t:Tactic) = cut(c) & onBranch(
      (cutShowLbl, t | dT("Cut didn't close") & Tactics.stopT)
    )

    /*** Lemma machinery, TODO clean up ***/
    val lemmaDB = LemmaDBFactory.lemmaDB

    /*def saveLemma(formula:String, proof:proofNode):ApplyRule = {
      val evidence = new ToolEvidence(
        immutable.Map("input" -> formula, "output" -> "true")) :: Nil
      // add lemma into DB, which creates an ID for it. use ID to apply the lemma
      val lemmaID = lemmaDB.add(Lemma(proof.provableWitness, evidence))
      val sequent = sequent(Nil, Nil, formula.asFormula :: Nil)
      return new ApplyRule(LookupLemma(lemmaDB, lemmaID)) {
        override def applicable(node: ProofNode): Boolean =
          node.sequent.sameSequentAs(sequent)
      }
    }*/ // TODO: can't make typing go through; no idea how Scala works
    // create evidence (traces input into tool and output from tool)


    def applyLemma(formula:String, apply:Tactic) =
      cut(formula.asFormula) & onBranch(
        (cutShowLbl, ls(cohideT, formula) &
          dT("apply Lemma " + formula) & apply),
        (cutUseLbl, dT("use Lemma " + formula) &
          la(implyL, formula) && (
          (ls(andR)*) & closeId, // checking hyps
          closeId // apply concl
          ))
      )

    def insertLemma(formula:String, apply:Tactic) = // when no hyp in lemma
      cut(formula.asFormula) & onBranch(
        (cutShowLbl, ls(cohideT, formula) &
          dT("apply Lemma " + formula) & apply)
      )

    def applyLemma2(formula:String, apply:Tactic) =
    // when the conclusion doesn't match exactly, but close enough for QE to close
      cut(formula.asFormula) & onBranch(
        (cutShowLbl, ls(cohideT, formula) &
          dT("apply Lemma " + formula) & apply),
        (cutUseLbl, dT("use Lemma " + formula) &
          la(implyL, formula) && ( // implyL might not be present
          (ls(andR)*) & closeId, // checking hyps
          QE // apply concl
          ))
      )

    def eqHide(f:String) = la(eqLeft(exhaustive=true), f) & la(hideT, f)

    def inst(variable:String, value:String) =
      la(instantiateT(Variable(variable), value.asTerm))

    /*** Invariants etc. ***/
    /* TODO make accelerations a parameter and changing throughout time
    * now it's the same all the time (presumably g/3) */
    def condImplLo(r:String, h:String, dhd:String,
                   w:String, dhf:String, tl:String) =
      "("+"\n"+
        "\\forall t \\forall ro \\forall ho"+"\n"+
        " ((t <= "+tl+"-to | "+tl+"<0) &"+"\n"+ // strict < for t so no overlap with post-tl (cleaner)
        "  ((0 <= t & t < max(0, ("+w+") * (("+dhf+") - ("+dhd+"))) / a &"+"\n"+
        "    ro = rv * t &"+"\n"+
        "    ho = (("+w+") * a) / 2 * t^2 + ("+dhd+") * t) |"+"\n"+
        "   (t >= max(0, ("+w+") * (("+dhf+") - ("+dhd+"))) / a &"+"\n"+
        "    ro = rv * t &"+"\n"+
        "    ho = ("+dhf+") * t - ("+w+") * max(0, ("+w+") * (("+dhf+") - ("+dhd+")))^2 / (2*a)))"+"\n"+
        "  -> (abs(("+r+") - ro) > rp | ("+w+") * ("+h+") < ("+w+") * ho - hp))"+"\n"+
        ")"+"\n"
    val condImplLoStr = condImplLo("r","h","dhd","w","dhf","tl")
    def condImplUp(r:String, h:String, dhd:String,
                   w:String, dhfUp:String, tl:String) =
      "("+"\n"+
        "\\forall t \\forall ro \\forall ho"+"\n"+
        " ((t <= "+tl+"-to | "+tl+"<0) &"+"\n"+
        "  ((0 <= t & t < max(0, ("+w+") * (("+dhfUp+") - ("+dhd+"))) / aM &"+"\n"+
        "    ro = rv * t &"+"\n"+
        "    ho = (("+w+") * aM) / 2 * t^2 + ("+dhd+") * t) |"+"\n"+
        "   (t >= max(0, ("+w+") * (("+dhfUp+") - ("+dhd+"))) / aM &"+"\n"+
        "    ro = rv * t &"+"\n"+
        "    ho = (("+dhd+") + ("+w+") * max(0, ("+w+") * (("+dhfUp+")-("+dhd+")))) * t "+"\n"+
        "         - ("+w+") * max(0, ("+w+") * (("+dhfUp+") - ("+dhd+")))^2 / (2*aM)))"+"\n"+
        "  -> (abs(("+r+") - ro) > rp | ("+w+") * ("+h+") > ("+w+") * ho + hp))"+"\n"+
        ")"+"\n"
    val condImplUpStr = condImplUp("r","h","dhd","w","dhfUp","tl")

    val tlmto = "(tl-to)"
    def condImplSafeableLo(r:String, h:String, dhd:String,
                           w:String, dhf:String, dhfExtr:String, tl:String) =
      "(" + condImplLo(r,h,dhd,w,dhf,tl) + "& (\n" +
        "\\forall hNew \\forall dhdNew (\n"+
        "((0 <= "+tlmto+" & "+tlmto+" < max(0, ("+w+") * (("+dhf+") - ("+dhd+"))) / a &\n"+
        "  hNew=("+w+")*a/2*"+tlmto+"^2 + ("+dhd+")*"+tlmto+" &\n"+
        "  dhdNew=("+w+")*a*"+tlmto+" + ("+dhd+")) |\n"+
        " ("+tlmto+" >= max(0, ("+w+") * (("+dhf+") - ("+dhd+"))) / a &\n"+
        "  hNew=("+dhf+")*"+tlmto+" - ("+w+")*max(0, ("+w+")*(("+dhf+") - ("+dhd+")))^2/(2*a) &\n"+
        "  dhdNew=("+dhf+"))) -> \n"+
        condImplLo("("+r+")-rv*"+tlmto+"",
          "("+h+"-hNew"+")", "dhdNew",
          "("+w+")", dhfExtr, "-1")+
        ")))\n"
    val condImplSafeableLoStr = condImplSafeableLo("r","h","dhd","w","dhf","dhfExtr","tl")
    //print(condImplSafeableLo("r","h","dhd","w","dhf","dhfExtr","tl"))
    //print(condImplSafeableLo("r","h","dhd","w","dhf","dhfExtr","tl").asFormula+"\n")

    def condImplSafeableUp(r:String, h:String, dhd:String,
                           w:String, dhfUp:String, dhfUpExtr:String, tl:String) =
      "(" + condImplUp(r,h,dhd,w,dhfUp,tl) + "& (\n" +
        "\\forall hNew \\forall dhdNew (\n"+
        "((0 <= "+tlmto+" & "+tlmto+" < max(0, ("+w+") * (("+dhfUp+") - ("+dhd+"))) / aM &\n"+
        "  hNew=("+w+")*aM/2*"+tlmto+"^2 + ("+dhd+")*"+tlmto+" &\n"+
        "  dhdNew=("+w+")*aM*"+tlmto+" + ("+dhd+")) |\n"+
        " ("+tlmto+" >= max(0, ("+w+") * (("+dhfUp+") - ("+dhd+"))) / aM &\n"+
        "  hNew=("+dhd+"+("+w+")*"+"max(0, ("+w+")*(("+dhfUp+") - ("+dhd+")))"+")*"+tlmto+
        "       - ("+w+")*max(0, ("+w+")*(("+dhfUp+") - ("+dhd+")))^2/(2*aM) &\n"+
        "  dhdNew=("+dhd+"+("+w+")*"+"max(0, ("+w+")*(("+dhfUp+") - ("+dhd+")))"+"))) -> \n"+
        condImplLo("("+r+")-rv*"+tlmto+"",
          "("+h+"-hNew"+")", "dhdNew",
          "-("+w+")", dhfUpExtr, "-1")+
        ")))\n"
    val condImplSafeableUpStr = condImplSafeableUp("r","h","dhd","w","dhfUp", "dhfUpExtr", "tl")
    //print(condImplSafeableUp("r","h","dhd","w","dhf","dhfExtr","tl"))
    //print(condImplSafeableUp("r","h","dhd","w","dhf","dhfExtr","tl").asFormula)

    def condImplSafeable(r:String, h:String, dhd:String, w:String,
                         dhf:String, dhfExtr:String, dhfUp:String, dhfUpExtr:String, tl:String) =
      "(\n"+ condImplSafeableLo(r,h,dhd,w,dhf,dhfExtr,tl) + "|\n" +
        condImplSafeableUp(r,h,dhd,w,dhfUp,dhfUpExtr,tl) + ")\n"
    //print(condImplSafeable("r","h","dhd","w","dhf","dhfExtr","dhfUp", "dhfUpExtr", "tl"))
    //print(condImplSafeable("r","h","dhd","w","dhf","dhfExtr","dhfUp", "dhfUpExtr", "tl").asFormula+"\n")
    val condImplSafeableStr = condImplSafeable("r","h","dhd","w","dhf","dhfExtr","dhfUp", "dhfUpExtr", "tl")

    val constants = "(hp > 0 & rp >= 0 & rv >= 0 & a > 0 & aM >= a & tl>=0)"
    // adding tl>=0 because tl=-1 really meands 2-sided safe, so this is inadapted
    val invariantStr =
      "(( ((w=-1 | w=1) & (to<=tl | tl<0)) & " +
        condImplSafeableStr +
        ") & " + constants + ")"
    val invariant = invariantStr.asFormula
    //print(invariantStr)
    //print(invariant)

    val evolutionDomain = "((to<=tl | tl<0) &"+
      "(( w * dhd >= w * dhf  | w * ao >= a ) &" +
      " ((w * dhd <= w * dhfUp & w * ao <= aM) | w * ao <= 0)))"

    val initDomain = "w*dhd>=w*dhf|w*ao>=a" // used?

    val ode = "r'=-rv,dhd'=ao,h'=-dhd,to'=1"

    val model = (
      constants + " &\n"+
        "( ((w=-1 | w=1) & (to<=tl | tl<0)) &\n"+
        condImplSafeableStr+
        ")\n"+
        "-> [\n"+
        "  {   {\n"+
        "  { ?true; ++\n"+ // keep it or not?
        "  { to:=0; dhf :=*; dhfUp :=*; {w:=-1; ++ w:=1;}\n"+
        "    ?"+
        condImplSafeableStr+
        "    ;\n"+
        "  } }\n"+
        "    ao :=*;\n"+
        "  }\n"+
        "  {r' = -rv, dhd' = ao, h' = -dhd, to'=1 &\n"+
        "    (to<=tl | tl<0) &\n"+
        "    (( w * dhd >= w * dhf  | w * ao >= a ) &\n"+
        "    ((w * dhd <= w * dhfUp & w * ao <= aM) | w * ao <= 0)) }\n"+
        "  }*\n"+
        "  ] ( (abs(r) > rp | abs(h) > hp) &\n"+
        "  ( ((w=-1 | w=1) & (to<=tl | tl<0)) &\n"+
        condImplSafeableStr+
        ")\n"+
        ")\n")
    print(model)

    /*** Lower bound safe lemma and its tactic ***/

    val safeLemmaFormula =
      "maxI=max((0,w*(dhf-dhd))) &" +
        "(w*dhd>=w*dhf|w*ao>=a) &" +
        "(w=-1|w=1) &" +
        "\\forall t \\forall ro \\forall ho ((t<=tl-to|tl < 0)&(0<=t&t < maxI/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxI/a&ro=rv*t&ho=dhf*t-w*maxI^2/(2*a))->abs(r-ro)>rp|w*h < w*ho-hp) &"+
        "hp>0 & rp>=0 & rv>=0 & a>0 &" +
        "(w*dhd_3>=w*dhf|w*ao>=a) &" +
        "to_3>=to &" +
        "r_3=r+-1*rv*(to_3-to) &" +
        "dhd_3=dhd+ao*(to_3-to) &" +
        "h_3=1/2*(2*h+-2*dhd*(to_3-to)+-1*ao*(to_3-to)^2)" +
        "->" +
        "\\forall t \\forall ro \\forall ho ((t<=tl-to_3|tl < 0)&(0<=t&t < max((0,w*(dhf-dhd_3)))/a&ro=rv*t&ho=w*a/2*t^2+dhd_3*t|t>=max((0,w*(dhf-dhd_3)))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-dhd_3)))^2/(2*a))->abs(r_3-ro)>rp|w*h_3 < w*ho-hp)"
    val safeUpLemmaFormula =
      "maxUpI=max((0,w*(dhfUp-dhd))) &"+
        "(w*dhd<=w*dhfUp&w*ao<=aM|w*ao<=0) &" +
        "(w=-1|w=1) &" +
        "(\\forall t \\forall ro \\forall ho ((t<=tl-to|tl < 0)&(0<=t&t < maxUpI/aM&ro=rv*t&ho=w*aM/2*t^2+dhd*t|t>=maxUpI/aM&ro=rv*t&ho=(dhd+w*maxUpI)*t-w*maxUpI^2/(2*aM))->abs(r-ro)>rp|w*h>w*ho+hp)) &" +
        "hp>0 & rp>=0 & rv>=0 & aM>0 &" +
        "(w*dhd_3<=w*dhfUp&w*ao<=aM|w*ao<=0) &" +
        "to_3>=to &" +
        "r_3=r+-1*rv*(to_3-to) &" +
        "dhd_3=dhd+ao*(to_3-to) &" +
        "h_3=1/2*(2*h+-2*dhd*(to_3-to)+-1*ao*(to_3-to)^2)" +
        "->" +
        "\\forall t \\forall ro \\forall ho ((t<=tl-to_3|tl < 0)&(0<=t&t < max((0,w*(dhfUp-dhd_3)))/aM&ro=rv*t&ho=w*aM/2*t^2+dhd_3*t|t>=max((0,w*(dhfUp-dhd_3)))/aM&ro=rv*t&ho=(dhd_3+w*max((0,w*(dhfUp-dhd_3))))*t-w*max((0,w*(dhfUp-dhd_3)))^2/(2*aM))->abs(r_3-ro)>rp|w*h_3>w*ho+hp)"

    val safeLemmaSeq = sequent(Nil, Nil, safeLemmaFormula.asFormula :: Nil)
    val safeUpLemmaSeq = sequent(Nil, Nil, safeUpLemmaFormula.asFormula :: Nil)

    val safeLemmaTac = dT("lemma") & ls(implyR) & (la(andL)*) &
      dT("Before skolem") & (ls(skolemizeT)*) & dT("After skolem") &
      ls(implyR) & ls(orR) &
      la(instantiateT(Variable("t"), "((to_3-to)+t_0)".asTerm)) &
      la(instantiateT(Variable("ro"), "rv*((to_3-to)+t_0)".asTerm)) &
      dT("Before CUT") &
      cut("0<=((to_3-to)+t_0)&((to_3-to)+t_0)<maxI/a|((to_3-to)+t_0)>=maxI/a".asFormula) & onBranch(
      (cutShowLbl, dT("Show Cut") & la(hide, "maxI=max((0,w*(dhf-dhd)))") &
        la(hide, "\\forall ho ((((to_3-to)+t_0)<=tl-to|tl < 0)&(0<=((to_3-to)+t_0)&((to_3-to)+t_0) < maxI/a&rv*((to_3-to)+t_0)=rv*((to_3-to)+t_0)&ho=w*a/2*((to_3-to)+t_0)^2+dhd*((to_3-to)+t_0)|((to_3-to)+t_0)>=maxI/a&rv*((to_3-to)+t_0)=rv*((to_3-to)+t_0)&ho=dhf*((to_3-to)+t_0)-w*maxI^2/(2*a))->abs(r-rv*((to_3-to)+t_0))>rp|w*h < w*ho-hp)")
        & ls(hide, "abs(r_3-ro_0)>rp") & ls(hide, "w*h_3<w*ho_0-hp") &
        dT("Show Cut 2") & ls(orR) & la(andL) &
        la(hide, "t_0<=tl-to_3|tl < 0") &
        la(orL, "0<=t_0&t_0<max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=w*a/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=dhf*t_0-w*max((0,w*(dhf-dhd_3)))^2/(2*a)")
        & (la(andL)*) & (ls(andR)*) &dT("End CutShowLbl") & QE),
      (cutUseLbl, dT("Use Cut") &
        la(orL, "0<=((to_3-to)+t_0)&((to_3-to)+t_0) < maxI/a|((to_3-to)+t_0)>=maxI/a") && (
        dT("Goal 110") & la(hide, initDomain) & // TODO remove this hide
          la(instantiateT(Variable("ho"), "w*a/2*((to_3-to)+t_0)^2 + dhd*((to_3-to)+t_0)".asTerm))
          & dT("instantiate ho 1 Lo") &
          la(implyL, "((((to_3-to)+t_0)<=tl-to|tl < 0)&(0<=((to_3-to)+t_0)&((to_3-to)+t_0) < maxI/a&rv*((to_3-to)+t_0)=rv*((to_3-to)+t_0)&w*a/2*((to_3-to)+t_0)^2+dhd*((to_3-to)+t_0)=w*a/2*((to_3-to)+t_0)^2+dhd*((to_3-to)+t_0)|((to_3-to)+t_0)>=maxI/a&rv*((to_3-to)+t_0)=rv*((to_3-to)+t_0)&w*a/2*((to_3-to)+t_0)^2+dhd*((to_3-to)+t_0)=dhf*((to_3-to)+t_0)-w*maxI^2/(2*a)))->abs(r-rv*((to_3-to)+t_0))>rp|w*h < w*(w*a/2*((to_3-to)+t_0)^2+dhd*((to_3-to)+t_0))-hp")
          && (
          dT("left of -> 1 Lo") & la(andL) &
            ls(hide, "abs(r_3-ro_0)>rp") & ls(hide, "w*h_3<w*ho_0-hp") &
            la(hide, "maxI=max((0,w*(dhf-dhd)))") &
            ls(andR) && (
            ls(orR) & dT("tl 1") & QE,
            ls(orR) &
              ls(hide, "((to_3-to)+t_0)>=maxI/a&rv*((to_3-to)+t_0)=rv*((to_3-to)+t_0)&w*a/2*((to_3-to)+t_0)^2+dhd*((to_3-to)+t_0)=dhf*((to_3-to)+t_0)-w*maxI^2/(2*a)") &
              dT("End L1") & QE
            ),
          dT("right of -> 1 Lo") &
            la(andL, "(t_0<=tl-to_3|tl < 0)&(0<=t_0&t_0 < max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=w*a/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=dhf*t_0-w*max((0,w*(dhf-dhd_3)))^2/(2*a))") &
            la(hide, "t_0<=tl-to_3|tl < 0") &
            la(orL, "0<=t_0&t_0 < max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=w*a/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=dhf*t_0-w*max((0,w*(dhf-dhd_3)))^2/(2*a)")
            && (
            dT("1-early Lo") &
              la(orL,"abs(r-rv*((to_3-to)+t_0))>rp|w*h < w*(w*a/2*((to_3-to)+t_0)^2+dhd*((to_3-to)+t_0))-hp")
              && (QE, ls(hide, "abs(r_3-ro_0)>rp") & dT("End R1E") & QE),
            dT("1-late Lo") &
              la(orL,"abs(r-rv*((to_3-to)+t_0))>rp|w*h < w*(w*a/2*((to_3-to)+t_0)^2+dhd*((to_3-to)+t_0))-hp")
              && (QE, ls(hide, "abs(r_3-ro_0)>rp") & absmax2 & dT("End R1L") & crushw)
            )
          ),
        dT("final time in straight Lo") &
          la(instantiateT(Variable("ho"), "dhf*((to_3-to)+t_0) - w*maxI^2/(2*a)".asTerm)) &
          dT("instantiate ho 2 Lo") &
          la(implyL, "((((to_3-to)+t_0)<=tl-to|tl < 0)&(0<=((to_3-to)+t_0)&((to_3-to)+t_0) < maxI/a&rv*((to_3-to)+t_0)=rv*((to_3-to)+t_0)&dhf*((to_3-to)+t_0)-w*maxI^2/(2*a)=w*a/2*((to_3-to)+t_0)^2+dhd*((to_3-to)+t_0)|((to_3-to)+t_0)>=maxI/a&rv*((to_3-to)+t_0)=rv*((to_3-to)+t_0)&dhf*((to_3-to)+t_0)-w*maxI^2/(2*a)=dhf*((to_3-to)+t_0)-w*maxI^2/(2*a)))->abs(r-rv*((to_3-to)+t_0))>rp|w*h < w*(dhf*((to_3-to)+t_0)-w*maxI^2/(2*a))-hp")
          && (
          dT("left of -> 2 Lo") & la(andL) &
            ls(hide, "abs(r_3-ro_0)>rp") & ls(hide, "w*h_3<w*ho_0-hp") &
            la(hide, "maxI=max((0,w*(dhf-dhd)))") &
            ls(andR) && (
            ls(orR) & dT("tl 2") & QE,
            ls(orR) &
              ls(hide, "0<=to_3-to+t_0&to_3-to+t_0 < maxI/a&rv*(to_3-to+t_0)=rv*(to_3-to+t_0)&dhf*(to_3-to+t_0)-w*maxI^2/(2*a)=w*a/2*(to_3-to+t_0)^2+dhd*(to_3-to+t_0)") &
              dT("End L2") & QE
            ),
          dT("right of -> 2 Lo") &
            la(andL, "(t_0<=tl-to_3|tl < 0)&(0<=t_0&t_0 < max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=w*a/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=dhf*t_0-w*max((0,w*(dhf-dhd_3)))^2/(2*a))") &
            la(hide, "t_0<=tl-to_3|tl < 0") &
            la(orL, "0<=t_0&t_0 < max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=w*a/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhf-dhd_3)))/a&ro_0=rv*t_0&ho_0=dhf*t_0-w*max((0,w*(dhf-dhd_3)))^2/(2*a)")
            && (
            dT("2-early Lo") &
              la(orL, "abs(r-rv*((to_3-to)+t_0))>rp|w*h<w*(dhf*((to_3-to)+t_0)-w*maxI^2/(2*a))-hp")
              && (QE, ls(hide, "abs(r_3-ro_0)>rp") & absmax2 & dT("End L2E") & crushw),
            dT("2-late Lo") &
              la(orL, "abs(r-rv*((to_3-to)+t_0))>rp|w*h<w*(dhf*((to_3-to)+t_0)-w*maxI^2/(2*a))-hp")
              && (QE, ls(hide, "abs(r_3-ro_0)>rp") & absmax2 & dT("End L2L") & crushw)
            )
          )
        )
        )
    )

    val safeUpLemmaTac = dT("lemma Up") & ls(implyR) & (la(andL)*) &
      dT("Before skolem Up") & (ls(skolemizeT)*) & dT("After skolem Up") &
      ls(implyR) & ls(orR) &
      la(instantiateT(Variable("t"), "((to_3-to)+t_0)".asTerm)) &
      la(instantiateT(Variable("ro"), "rv*((to_3-to)+t_0)".asTerm)) &
      dT("Before CUT") &
      cut("0<=((to_3-to)+t_0)&((to_3-to)+t_0)<maxUpI/aM|((to_3-to)+t_0)>=maxUpI/aM".asFormula) & onBranch(
      (cutShowLbl, dT("Show Cut") & la(hide, "maxUpI=max((0,w*(dhfUp-dhd)))") &
        la(hide, "\\forall ho ((to_3-to+t_0<=tl-to|tl < 0)&(0<=to_3-to+t_0&to_3-to+t_0 < maxUpI/aM&rv*(to_3-to+t_0)=rv*(to_3-to+t_0)&ho=w*aM/2*(to_3-to+t_0)^2+dhd*(to_3-to+t_0)|to_3-to+t_0>=maxUpI/aM&rv*(to_3-to+t_0)=rv*(to_3-to+t_0)&ho=(dhd+w*maxUpI)*(to_3-to+t_0)-w*maxUpI^2/(2*aM))->abs(r-rv*(to_3-to+t_0))>rp|w*h>w*ho+hp)")
        & ls(hide, "abs(r_3-ro_0)>rp") & ls(hide, "w*h_3>w*ho_0+hp") &
        dT("Show Cut 2") & ls(orR) & la(andL) &
        la(hide, "t_0<=tl-to_3|tl < 0") &
        la(orL, "0<=t_0&t_0<max((0,w*(dhfUp-dhd_3)))/aM&ro_0=rv*t_0&ho_0=w*aM/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhfUp-dhd_3)))/aM&ro_0=rv*t_0&ho_0=(dhd_3+w*max((0,w*(dhfUp-dhd_3))))*t_0-w*max((0,w*(dhfUp-dhd_3)))^2/(2*aM)")
        & (la(andL)*) & (ls(andR)*) & dT("End CutShowLbl") & QE),
      (cutUseLbl, dT("Use Cut") &
        la(orL, "0<=((to_3-to)+t_0)&((to_3-to)+t_0)<maxUpI/aM|((to_3-to)+t_0)>=maxUpI/aM") && (
        dT("final time in parabola") & // add hide initDomain?
          la(instantiateT(Variable("ho"), "w*aM/2*((to_3-to)+t_0)^2+dhd*((to_3-to)+t_0)".asTerm)) &
          dT("instantiate ho 1 Up") &
          la(implyL, "(to_3-to+t_0<=tl-to|tl < 0)&(0<=to_3-to+t_0&to_3-to+t_0 < maxUpI/aM&rv*(to_3-to+t_0)=rv*(to_3-to+t_0)&w*aM/2*(to_3-to+t_0)^2+dhd*(to_3-to+t_0)=w*aM/2*(to_3-to+t_0)^2+dhd*(to_3-to+t_0)|to_3-to+t_0>=maxUpI/aM&rv*(to_3-to+t_0)=rv*(to_3-to+t_0)&w*aM/2*(to_3-to+t_0)^2+dhd*(to_3-to+t_0)=(dhd+w*maxUpI)*(to_3-to+t_0)-w*maxUpI^2/(2*aM))->abs(r-rv*(to_3-to+t_0))>rp|w*h>w*(w*aM/2*(to_3-to+t_0)^2+dhd*(to_3-to+t_0))+hp")
          && (
          dT("left of -> 1 Up") &
            ls(hide, "abs(r_3-ro_0)>rp") & ls(hide, "w*h_3>w*ho_0+hp") &
            la(hide, "maxUpI=max((0,w*(dhfUp-dhd)))") &
            ls(andR) && (
            ls(orR) & dT("tl 1") & QE,
            ls(orR) &
              ls(hide, "((to_3-to)+t_0)>=maxUpI/aM&rv*((to_3-to)+t_0)=rv*((to_3-to)+t_0)&w*aM/2*((to_3-to)+t_0)^2+dhd*((to_3-to)+t_0)=(dhd+w*maxUpI)*((to_3-to)+t_0)-w*maxUpI^2/(2*aM)") &
              dT("End L1") & QE
            ),
          dT("right of -> 1 Up") &
            la(andL, "(t_0<=tl-to_3|tl < 0)&(0<=t_0&t_0 < max((0,w*(dhfUp-dhd_3)))/aM&ro_0=rv*t_0&ho_0=w*aM/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhfUp-dhd_3)))/aM&ro_0=rv*t_0&ho_0=(dhd_3+w*max((0,w*(dhfUp-dhd_3))))*t_0-w*max((0,w*(dhfUp-dhd_3)))^2/(2*aM))") &
            la(hide, "t_0<=tl-to_3|tl < 0") &
            la(orL, "0<=t_0&t_0 < max((0,w*(dhfUp-dhd_3)))/aM&ro_0=rv*t_0&ho_0=w*aM/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhfUp-dhd_3)))/aM&ro_0=rv*t_0&ho_0=(dhd_3+w*max((0,w*(dhfUp-dhd_3))))*t_0-w*max((0,w*(dhfUp-dhd_3)))^2/(2*aM)")
            && (
            dT("1-early Up") &
              la(orL, "abs(r-rv*((to_3-to)+t_0))>rp|w*h>w*(w*aM/2*((to_3-to)+t_0)^2+dhd*((to_3-to)+t_0))+hp")
              && (QE, QE),
            dT("1-late Up") &
              la(orL, "abs(r-rv*((to_3-to)+t_0))>rp|w*h>w*(w*aM/2*((to_3-to)+t_0)^2+dhd*((to_3-to)+t_0))+hp")
              && (QE, ls(hide, "abs(r_3-ro_0)>rp") & absmax3 & crushw)
            )
          ),
        dT("final time in straight Up") &
          la(instantiateT(Variable("ho"), "(dhd+w*maxUpI)*((to_3-to)+t_0)-w*maxUpI^2/(2*aM)".asTerm)) &
          dT("instantiate ho 2 Lo") &
          la(implyL, "(to_3-to+t_0<=tl-to|tl < 0)&(0<=to_3-to+t_0&to_3-to+t_0 < maxUpI/aM&rv*(to_3-to+t_0)=rv*(to_3-to+t_0)&(dhd+w*maxUpI)*(to_3-to+t_0)-w*maxUpI^2/(2*aM)=w*aM/2*(to_3-to+t_0)^2+dhd*(to_3-to+t_0)|to_3-to+t_0>=maxUpI/aM&rv*(to_3-to+t_0)=rv*(to_3-to+t_0)&(dhd+w*maxUpI)*(to_3-to+t_0)-w*maxUpI^2/(2*aM)=(dhd+w*maxUpI)*(to_3-to+t_0)-w*maxUpI^2/(2*aM))->abs(r-rv*(to_3-to+t_0))>rp|w*h>w*((dhd+w*maxUpI)*(to_3-to+t_0)-w*maxUpI^2/(2*aM))+hp")
          && (
          dT("left of -> 2 Up") &
            ls(hide, "abs(r_3-ro_0)>rp") & ls(hide, "w*h_3>w*ho_0+hp") &
            la(hide, "maxUpI=max((0,w*(dhfUp-dhd)))") &
            ls(andR) && (
            ls(orR) & dT("tl 2b") & QE,
            ls(orR) &
              ls(hide, "0<=((to_3-to)+t_0)&((to_3-to)+t_0) < maxUpI/aM&rv*((to_3-to)+t_0)=rv*((to_3-to)+t_0)&(dhd+w*maxUpI)*((to_3-to)+t_0)-w*maxUpI^2/(2*aM)=w*aM/2*((to_3-to)+t_0)^2+dhd*((to_3-to)+t_0)") &
              QE
            ),
          dT("right of -> 2 Up") &
            la(andL, "(t_0<=tl-to_3|tl < 0)&(0<=t_0&t_0 < max((0,w*(dhfUp-dhd_3)))/aM&ro_0=rv*t_0&ho_0=w*aM/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhfUp-dhd_3)))/aM&ro_0=rv*t_0&ho_0=(dhd_3+w*max((0,w*(dhfUp-dhd_3))))*t_0-w*max((0,w*(dhfUp-dhd_3)))^2/(2*aM))") &
            la(hide, "t_0<=tl-to_3|tl < 0") &
            la(orL, "0<=t_0&t_0 < max((0,w*(dhfUp-dhd_3)))/aM&ro_0=rv*t_0&ho_0=w*aM/2*t_0^2+dhd_3*t_0|t_0>=max((0,w*(dhfUp-dhd_3)))/aM&ro_0=rv*t_0&ho_0=(dhd_3+w*max((0,w*(dhfUp-dhd_3))))*t_0-w*max((0,w*(dhfUp-dhd_3)))^2/(2*aM)")
            && (
            dT("2-early Up") &
              la(orL, "abs(r-rv*((to_3-to)+t_0))>rp|w*h>w*((dhd+w*maxUpI)*((to_3-to)+t_0)-w*maxUpI^2/(2*aM))+hp")
              && (QE, ls(hide, "abs(r_3-ro_0)>rp") & absmax3 & crushw),
            dT("2-late Up") &
              la(orL, "abs(r-rv*((to_3-to)+t_0))>rp|w*h>w*((dhd+w*maxUpI)*((to_3-to)+t_0)-w*maxUpI^2/(2*aM))+hp")
              && (QE, ls(hide, "abs(r_3-ro_0)>rp") & absmax3 & crushw)
            )
          )
        )
        )
    )

    val safeLemma = helper.runTactic(safeLemmaTac, new RootNode(safeLemmaSeq))
    safeLemma shouldBe 'closed

    /*** Lemma machinery, TODO clean up ***/
    // create evidence (traces input into tool and output from tool)
    val evidence = new ToolEvidence(
      immutable.Map("input" -> safeLemmaFormula, "output" -> "true")) :: Nil
    // add lemma into DB, which creates an ID for it. use ID to apply the lemma
    val lemmaID = lemmaDB.add(Lemma(safeLemma.provableWitness, evidence))
    val safeLemmaApply = new ApplyRule(LookupLemma(lemmaDB, lemmaID)) {
      override def applicable(node: ProofNode): Boolean =
        node.sequent.sameSequentAs(safeLemmaSeq)
    }

    val safeUpLemma =
      helper.runTactic(safeUpLemmaTac, new RootNode(safeUpLemmaSeq))
    safeUpLemma shouldBe 'closed

    /*** Lemma machinery, TODO clean up ***/
    // create evidence (traces input into tool and output from tool)
    val evidenceUp = new ToolEvidence(
      immutable.Map("input" -> safeUpLemmaFormula, "output" -> "true")) :: Nil
    // add lemma into DB, which creates an ID for it. use ID to apply the lemma
    val lemmaUpID = lemmaDB.add(Lemma(safeUpLemma.provableWitness, evidenceUp))
    val safeUpLemmaApply = new ApplyRule(LookupLemma(lemmaDB, lemmaUpID)) {
      override def applicable(node: ProofNode): Boolean =
        node.sequent.sameSequentAs(safeUpLemmaSeq)
    }


    // NOT USED BUT KEEPING IT FOR NOW; can be used to refactor proofs
    val parabolaLineFormula =
      "\\forall h0 \\forall v0 \\forall a0 \\forall vt0"+
        "\\forall h1 \\forall v1 \\forall a1 \\forall vt1"+
        "\\forall w \\forall tl \\forall to "+
        "\\forall t \\forall ro \\forall ho \\forall ro \\forall ho "+
        "t >= 0 & "+
        "a0 > 0 & a1 > 0 &"+
        "w*h0  <= w*h1  & "+
        "w*v0  <= w*v1  & "+
        "a0  <= a1  & "+
        "w*vt0 <= w*vt1 & "+
        "(w = -1 | w = 1) &"+
        "((t <= tl-to | tl<0) &"+
        " (( 0 <= t & t < max(0, w*(vt0-v0)) / a0 &"+
        "   ro = rv * t &"+
        "   ho = w * a0 / 2 * t^2 + v0 * t) |"+
        "  (t >= max(0, w*(vt0-v0)) / a0 &"+
        "   ro = rv * t &"+
        "   ho = vt0 * t - w*max(0, w*(vt0-v0))^2 / (2*a0)))) &"+
        "((t <= tl-to | tl<0) &"+
        " (( 0 <= t & t < max(0, w*(vt1-v1)) / a1 &"+
        "   ro = rv * t &"+
        "   ho = w * a1 / 2 * t^2 + v1 * t) |"+
        "  (t >= max(0, w*(vt1-v1)) / a1 &"+
        "   ro = rv * t &"+
        "   ho = vt1 * t - w*max(0, w*(vt1-v1))^2 / (2*a1))))"+
        "->"+
        "ro = ro & w*ho <= w*ho"
    val parabolaLineSeq = sequent(Nil, Nil, parabolaLineFormula.asFormula :: Nil)
    val max0 = "max(0, w*(vt0-v0))"
    val max1 = "max(0, w*(vt1-v1))"
    val cut0 = "0 <= t & t < max(0, w*(vt0-v0)) / a0 | t >= max(0, w*(vt0-v0)) / a0"
    val cut1 = "0 <= t & t < max(0, w*(vt1-v1)) / a1 | t >= max(0, w*(vt1-v1)) / a1"
    val parabolaLineTac = (ls(skolemizeT)*) & ls(implyR) & (la(andL)*) &
      cutEZ(cut0.asFormula, QE) & cutEZ(cut1.asFormula, QE) &
      abbrv(max0.asTerm, Some(Variable("max0"))) &
      la(MinMaxT, "", Some(max0.asTerm)) &
      abbrv(max1.asTerm, Some(Variable("max1"))) &
      la(MinMaxT, "", Some(max1.asTerm)) & dT("GO") &
      la(orL, "0<=t&t < max0/a0|t>=max0/a0") && (
      la(orL, "0<=t&t < max1/a1|t>=max1/a1") && (crushw, crushw),
      la(orL, "0<=t&t < max1/a1|t>=max1/a1") && (crushw, crushw)
      )
    /*val parabolaLine = helper.runTactic(parabolaLineTac, new RootNode(parabolaLineSeq))
    parabolaLine shouldBe 'closed*/

    // NOT USED BUT KEEPING IT FOR NOW; can be used to refactor proofs
    val parabolaLine2Formula =
      "\\forall h0 \\forall v0 \\forall a0 \\forall vt0"+
        "\\forall h1 \\forall v1 \\forall a1 \\forall vt1"+
        "\\forall w \\forall tl \\forall to "+
        "\\forall t \\forall ho \\forall vf0 \\forall ho \\forall vf1 "+
        "t >= 0 & "+
        "a0 > 0 & a1 > 0 &"+
        "w*h0  <= w*h1  & "+
        "w*v0  <= w*v1  & "+
        "a0  <= a1  & "+
        "w*vt0 <= w*vt1 & "+
        "(w = -1 | w = 1) &"+
        "((t <= tl-to | tl<0) &"+
        " (( 0 <= t & t < max(0, w*(vt0-v0)) / a0 &"+
        "   vf0 = w*a0*t + v0 &"+
        "   ho = w * a0 / 2 * t^2 + v0 * t) |"+
        "  (t >= max(0, w*(vt0-v0)) / a0 &"+
        "   vf0 = vt0 &"+
        "   ho = vt0 * t - w*max(0, w*(vt0-v0))^2 / (2*a0)))) &"+
        "((t <= tl-to | tl<0) &"+
        " (( 0 <= t & t < max(0, w*(vt1-v1)) / a1 &"+
        "   vf1 = w*a1*t + v1 &"+
        "   ho = w * a1 / 2 * t^2 + v1 * t) |"+
        "  (t >= max(0, w*(vt1-v1)) / a1 &"+
        "   vf1 = vt1 &"+
        "   ho = vt1 * t - w*max(0, w*(vt1-v1))^2 / (2*a1))))"+
        "->"+
        "w*ho <= w*ho & w*vf0 <= w*vf1"
    val parabolaLine2Seq = sequent(Nil, Nil, parabolaLine2Formula.asFormula :: Nil)
    val parabolaLine2Tac = parabolaLineTac
    /*val parabolaLine2 = helper.runTactic(parabolaLine2Tac, new RootNode(parabolaLine2Seq))
    parabolaLine2 shouldBe 'closed*/


    val propagateLoFormula =
      "\\forall h0 \\forall v0 \\forall a0 \\forall vt0 \\forall to0"+
        "\\forall h1 \\forall v1 \\forall a1 \\forall vt1 \\forall to1"+
        "\\forall tl \\forall r \\forall w ("+
        "(\\forall t \\forall ro \\forall ho "+
        " (((t <= tl-to0 | tl<0) &"+
        "  (( 0 <= t & t < max(0, w*(vt0-v0)) / a0 &"+
        "    ro = rv * t &"+
        "    ho = w * a0 / 2 * t^2 + v0 * t) |"+
        "   (t >= max(0, w*(vt0-v0)) / a0 &"+
        "    ro = rv * t &"+
        "    ho = vt0 * t - w*max(0, w*(vt0-v0))^2 / (2*a0))))"+
        "-> abs(r-ro)>rp | w*h0 < w*ho-hp)) &"+ //w*h > w*ho+hp
        "a0 > 0 & a1 > 0 &"+
        "w*h0 >= w*h1  & "+
        "w*v0 <= w*v1  & "+
        "a0   <= a1  & "+
        "to0  <= to1 & "+
        "w*vt0 <= w*vt1 & "+
        "(w = -1 | w = 1)"+
        "->"+
        "\\forall t \\forall ro \\forall ho "+
        "(((t <= tl-to1 | tl<0) &"+
        " (( 0 <= t & t < max(0, w*(vt1-v1)) / a1 &"+
        "   ro = rv * t &"+
        "   ho = w * a1 / 2 * t^2 + v1 * t) |"+
        "  (t >= max(0, w*(vt1-v1)) / a1 &"+
        "   ro = rv * t &"+
        "   ho = vt1 * t - w*max(0, w*(vt1-v1))^2 / (2*a1))))"+
        "-> abs(r-ro)>rp | w*h1 < w*ho-hp))" //w*h > w*ho+hp
    val max_0 = "max(0, w*(vt0-v0))"
    val max_1 = "max(0, w*(vt1-v1))"
    val cut_0 = "0 <= t_0 & t_0 < max(0, w*(vt0-v0)) / a0 | t_0 >= max(0, w*(vt0-v0)) / a0"
    val propagateLoTac = (ls(skolemizeT)*) & ls(implyR) & (la(andL)*) &
      (ls(skolemizeT)*) & ls(implyR) & la(andL) &
      inst("t", "t_0") & inst("ro", "rv*t_0") &
      cutEZ(cut_0.asFormula, dT("cut_0") &
        la(hide, "\\forall ho ((t_0 <= tl-to0|tl < 0)&(0<=t_0&t_0 < max((0,w*(vt0-v0)))/a0&rv*t_0=rv*t_0&ho=w*a0/2*t_0^2+v0*t_0|t_0>=max((0,w*(vt0-v0)))/a0&rv*t_0=rv*t_0&ho=vt0*t_0-w*max((0,w*(vt0-v0)))^2/(2*a0))->abs(r-rv*t_0)>rp|w*h0 < w*ho-hp)") &
        la(MinMaxT, "", Some(max_1.asTerm)) & // duplicated to keep names straight
        ls(hide, "abs(r-ro_0)>rp|w*h1 < w*ho_0-hp") & QE) &
      dT("before MinMax") &
      la(MinMaxT, "", Some(max_0.asTerm)) &
      la(MinMaxT, "", Some(max_1.asTerm)) &
      dT("after MinMax") &
      la(orL, "0<=t_0 & t_0 < max_0/a0 | t_0 >= max_0/a0") && (
      dT("para max0") & inst("ho", "w*a0/2*t_0^2+v0*t_0") & la(implyL) && (
        ls(andR) && (QE,
          ls(hide, "abs(r-ro_0)>rp|w*h1 < w*ho_0-hp") & ls(orR) & QE),
        la(hide, "t_0 <= tl-to1|tl < 0") & dT("post para") &
          la(orL, "0<=t_0&t_0 < max_1/a1&ro_0=rv*t_0&ho_0=w*a1/2*t_0^2+v1*t_0|t_0>=max_1/a1&ro_0=rv*t_0&ho_0=vt1*t_0-w*max_1^2/(2*a1)") && (
          (la(andL)*) & ls(orR) &
            eqHide("ro_0=rv*t_0") & eqHide("ho_0=w*a1/2*t_0^2+v1*t_0") &
            la(orL, "abs(r-rv*t_0)>rp|w*h0 < w*(w*a0/2*t_0^2+v0*t_0)-hp") && (
            closeId,
            dT("height") & ls(hide, "abs(r-rv*t_0)>rp") & QE
            ),
          (la(andL)*) & ls(orR) &
            eqHide("ro_0=rv*t_0") & eqHide("ho_0=vt1*t_0-w*max_1^2/(2*a1)") &
            la(orL, "abs(r-rv*t_0)>rp|w*h0 < w*(w*a0/2*t_0^2+v0*t_0)-hp") && (
            closeId,
            dT("height") & ls(hide, "abs(r-rv*t_0)>rp") & QE
            )
          )
        ),
      dT("line max0") & inst("ho", "vt0*t_0-w*max_0^2/(2*a0)") & la(implyL) && (
        ls(andR) && (QE,
          ls(hide, "abs(r-ro_0)>rp|w*h1 < w*ho_0-hp") & ls(orR) & QE),
        la(hide, "t_0 <= tl-to1|tl < 0") & dT("post line") &
          la(orL, "0<=t_0&t_0 < max_1/a1&ro_0=rv*t_0&ho_0=w*a1/2*t_0^2+v1*t_0|t_0>=max_1/a1&ro_0=rv*t_0&ho_0=vt1*t_0-w*max_1^2/(2*a1)") && (
          (la(andL)*) & ls(orR) &
            eqHide("ro_0=rv*t_0") & eqHide("ho_0=w*a1/2*t_0^2+v1*t_0") &
            la(orL, "abs(r-rv*t_0)>rp|w*h0 < w*(vt0*t_0-w*max_0^2/(2*a0))-hp") && (
            closeId,
            dT("height") & ls(hide, "abs(r-rv*t_0)>rp") & QE
            ),
          (la(andL)*) & ls(orR) &
            eqHide("ro_0=rv*t_0") & eqHide("ho_0=vt1*t_0-w*max_1^2/(2*a1)") &
            la(orL, "abs(r-rv*t_0)>rp|w*h0 < w*(vt0*t_0-w*max_0^2/(2*a0))-hp") && (
            closeId,
            dT("height") & ls(hide, "abs(r-rv*t_0)>rp") & QE
            )
          )
        )
      )
    val propagateLo = helper.runTactic(propagateLoTac,
      new RootNode(sequent(Nil, Nil, propagateLoFormula.asFormula :: Nil)))
    propagateLo shouldBe 'closed

    val propagateLoApply = new ApplyRule(LookupLemma(
      lemmaDB,
      lemmaDB.add(
        Lemma(propagateLo.provableWitness,
          new ToolEvidence(
            immutable.Map("input" -> propagateLoFormula, "output" -> "true")) :: Nil)))) {
      override def applicable(node: ProofNode): Boolean =
        node.sequent.sameSequentAs(
          sequent(Nil, Nil, propagateLoFormula.asFormula :: Nil)
        )
    }

    // NOT USED BUT KEEPING IT FOR NOW ; will be useful for delay
    val propagateUpFormula =
      "\\forall h0 \\forall v0 \\forall a0 \\forall vt0 \\forall to0"+
        "\\forall h1 \\forall v1 \\forall a1 \\forall vt1 \\forall to1"+
        "\\forall tl \\forall r \\forall w ("+
        "(\\forall t \\forall ro \\forall ho "+
        "(((t <= tl-to0 | tl<0) &"+
        " (( 0 <= t & t < max(0, w*(vt0-v0)) / a0 &"+
        "   ro = rv * t &"+
        "   ho = w * a0 / 2 * t^2 + v0 * t) |"+
        "  (t >= max(0, w*(vt0-v0)) / a0 &"+
        "   ro = rv * t &"+
        "   ho = vt0 * t - w*max(0, w*(vt0-v0))^2 / (2*a0))))"+
        "-> abs(r-ro)>rp | w*h0 > w*ho+hp)) &"+ //difference 1: w*h > w*ho+hp
        "a0 > 0 & a1 > 0 &"+
        "w*h0 <= w*h1  & "+ //switching sign
        "w*v0 >= w*v1  & "+ //switching sign
        "a0   >= a1  & "+ //switching sign
        "to0  <= to1 & "+
        "w*vt0 >= w*vt1 & "+ //switching sign
        "(w = -1 | w = 1)"+
        "->"+
        "\\forall t \\forall ro \\forall ho "+
        "(((t <= tl-to1 | tl<0) &"+
        " (( 0 <= t & t < max(0, w*(vt1-v1)) / a1 &"+
        "   ro = rv * t &"+
        "   ho = w * a1 / 2 * t^2 + v1 * t) |"+
        "  (t >= max(0, w*(vt1-v1)) / a1 &"+
        "   ro = rv * t &"+
        "   ho = vt1 * t - w*max(0, w*(vt1-v1))^2 / (2*a1))))"+
        "-> abs(r-ro)>rp | w*h1 > w*ho+hp))" //difference 2: w*h > w*ho+hp
    val propagateUpTac = (ls(skolemizeT)*) & ls(implyR) & (la(andL)*) &
        (ls(skolemizeT)*) & ls(implyR) & la(andL) &
        inst("t", "t_0") & inst("ro", "rv*t_0") &
        cutEZ(cut_0.asFormula, dT("cut_0") &
          la(hide, "\\forall ho ((t_0 <= tl-to0|tl < 0)&(0<=t_0&t_0 < max((0,w*(vt0-v0)))/a0&rv*t_0=rv*t_0&ho=w*a0/2*t_0^2+v0*t_0|t_0>=max((0,w*(vt0-v0)))/a0&rv*t_0=rv*t_0&ho=vt0*t_0-w*max((0,w*(vt0-v0)))^2/(2*a0))->abs(r-rv*t_0)>rp|w*h0 > w*ho+hp)") &
          la(MinMaxT, "", Some(max_1.asTerm)) & // duplicated to keep names straight
          ls(hide, "abs(r-ro_0)>rp|w*h1 > w*ho_0+hp") & QE) &
        dT("before MinMax") &
        la(MinMaxT, "", Some(max_0.asTerm)) &
        la(MinMaxT, "", Some(max_1.asTerm)) &
        dT("after MinMax") &
        la(orL, "0<=t_0 & t_0 < max_0/a0 | t_0 >= max_0/a0") && (
        dT("para max0") & inst("ho", "w*a0/2*t_0^2+v0*t_0") & la(implyL) && (
          ls(andR) && (QE, // closeId?
            ls(hide, "abs(r-ro_0)>rp|w*h1 > w*ho_0+hp") & ls(orR) & QE),
          la(hide, "t_0 <= tl-to1|tl < 0") & dT("post para") &
            la(orL, "0<=t_0&t_0 < max_1/a1&ro_0=rv*t_0&ho_0=w*a1/2*t_0^2+v1*t_0|t_0>=max_1/a1&ro_0=rv*t_0&ho_0=vt1*t_0-w*max_1^2/(2*a1)") && (
            (la(andL)*) & ls(orR) &
              eqHide("ro_0=rv*t_0") & eqHide("ho_0=w*a1/2*t_0^2+v1*t_0") &
              la(orL, "abs(r-rv*t_0)>rp|w*h0 > w*(w*a0/2*t_0^2+v0*t_0)+hp") && (
              closeId,
              dT("height") & ls(hide, "abs(r-rv*t_0)>rp") & QE
              ),
            (la(andL)*) & ls(orR) &
              eqHide("ro_0=rv*t_0") & eqHide("ho_0=vt1*t_0-w*max_1^2/(2*a1)") &
              la(orL, "abs(r-rv*t_0)>rp|w*h0 > w*(w*a0/2*t_0^2+v0*t_0)+hp") && (
              closeId,
              dT("height") & ls(hide, "abs(r-rv*t_0)>rp") & QE
              )
            )
          ),
        dT("line max0") & inst("ho", "vt0*t_0-w*max_0^2/(2*a0)") & la(implyL) && (
          ls(andR) && (QE, // closeId?
            ls(hide, "abs(r-ro_0)>rp|w*h1 > w*ho_0+hp") & ls(orR) & QE),
          la(hide, "t_0 <= tl-to1|tl < 0") & dT("post line") &
            la(orL, "0<=t_0&t_0 < max_1/a1&ro_0=rv*t_0&ho_0=w*a1/2*t_0^2+v1*t_0|t_0>=max_1/a1&ro_0=rv*t_0&ho_0=vt1*t_0-w*max_1^2/(2*a1)") && (
            (la(andL)*) & ls(orR) &
              eqHide("ro_0=rv*t_0") & eqHide("ho_0=w*a1/2*t_0^2+v1*t_0") &
              la(orL, "abs(r-rv*t_0)>rp|w*h0 > w*(vt0*t_0-w*max_0^2/(2*a0))+hp") && (
              closeId,
              dT("height1") & ls(hide, "abs(r-rv*t_0)>rp") & QE
              ),
            (la(andL)*) & ls(orR) &
              eqHide("ro_0=rv*t_0") & eqHide("ho_0=vt1*t_0-w*max_1^2/(2*a1)") &
              la(orL, "abs(r-rv*t_0)>rp|w*h0 > w*(vt0*t_0-w*max_0^2/(2*a0))+hp") && (
              closeId,
              dT("height2") & ls(hide, "abs(r-rv*t_0)>rp") & QE
              )
            )
          )
        )
    /*val propagateUp = helper.runTactic(propagateUpTac,
      new RootNode(sequent(Nil, Nil, propagateUpFormula.asFormula :: Nil)))
    propagateUp shouldBe 'closed

    val propagateUpApply = new ApplyRule(LookupLemma(
      lemmaDB,
      lemmaDB.add(
        Lemma(propagateUp.provableWitness,
          new ToolEvidence(
            immutable.Map("input" -> propagateUpFormula, "output" -> "true")) :: Nil)))) {
      override def applicable(node: ProofNode): Boolean =
        node.sequent.sameSequentAs(
          sequent(Nil, Nil, propagateUpFormula.asFormula :: Nil)
        )
      }*/


    /*** Main safe theorem and its tactic ***/
    val safeSeq = new Sequent(Nil, immutable.IndexedSeq(), immutable.IndexedSeq(model.asFormula))
    val safeTac = ls(implyR) & la(andL) &
      ls(wipeContextInductionT(Some(invariant))) & onBranch(
      (indInitLbl, dT("DONE Base case") & ls(andR) & closeId), // done
      (indUseCaseLbl, dT("DONE Use case") & ls(implyR) &
        la(hide, constants) & // TODO appears twice??
        dT("andL*") & la(andL) & ls(andR) && (
        (la(andL)*) & dT("before orL") &
          la(orL, condImplSafeableStr) && (
          dT("before inst 0 lower") & la(andL, condImplSafeableLoStr) &
            la(hide, "\\forall hNew \\forall dhdNew (0<=tl-to&tl-to < max((0,w*(dhf-dhd)))/a&hNew=w*a/2*(tl-to)^2+dhd*(tl-to)&dhdNew=w*a*(tl-to)+dhd|tl-to>=max((0,w*(dhf-dhd)))/a&hNew=dhf*(tl-to)-w*max((0,w*(dhf-dhd)))^2/(2*a)&dhdNew=dhf->\\forall t \\forall ro \\forall ho ((t<=-1-to|-1 < 0)&(0<=t&t < max((0,w*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=w*a/2*t^2+dhdNew*t|t>=max((0,w*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=dhfExtr*t-w*max((0,w*(dhfExtr-dhdNew)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|w*(h-hNew) < w*ho-hp))") &
            // replace by second part of condition
            inst("t","0") & inst("ro","0") & inst("ho","0") & la(implyL) && (
            dT("Use case 1 Lo") & ls(hide, "abs(r)>rp|abs(h)>hp") &
              abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxI"))) &
              la(MinMaxT, "", Some("max(0,w*(dhf-dhd))".asTerm)) &
              dT("MinMax Lower") & ls(andR) && (QE, QE),
            dT("Absolute value Lo") & abs3 & dT("Use case 2 Lo") & QE
            ),
          dT("before inst 0 upper") & la(andL, condImplSafeableUpStr) &
            la(hide, "\\forall hNew \\forall dhdNew (0<=tl-to&tl-to < max((0,w*(dhfUp-dhd)))/aM&hNew=w*aM/2*(tl-to)^2+dhd*(tl-to)&dhdNew=w*aM*(tl-to)+dhd|tl-to>=max((0,w*(dhfUp-dhd)))/aM&hNew=(dhd+w*max((0,w*(dhfUp-dhd))))*(tl-to)-w*max((0,w*(dhfUp-dhd)))^2/(2*aM)&dhdNew=dhd+w*max((0,w*(dhfUp-dhd)))->\\forall t \\forall ro \\forall ho ((t<=-1-to|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(-w)*(h-hNew) < (-w)*ho-hp))") &
            inst("t","0") & inst("ro","0") & inst("ho","0") & la(implyL) && (
            dT("Use case 1 Up") & ls(hide, "abs(r)>rp|abs(h)>hp") &
              abbrv("max((0,w*(dhfUp-dhd)))".asTerm, Some(Variable("maxUpI"))) &
              la(MinMaxT, "", Some("max(0,w*(dhfUp-dhd))".asTerm)) &
              dT("MinMax Upper") & ls(andR) && (QE, QE),
            dT("Absolute value Up") & abs3 & dT("Use case 2 Up") & QE
            )
          ), closeId
        ) ), // TODO DONE
      (indStepLbl, dT("Step") & ls(implyR) &
        ls(boxSeqGenT(invariant)) & onBranch(
        (cutShowLbl, dT("DONE Generalization Holds") & // from here
          dT("1.21") & (ls(boxSeqT)*) & ls(boxChoiceT) & ls(andR) && (
          ls(boxTestT) & ls(implyR) & ls(boxNDetAssign) &
            ls(skolemizeT) & dT("closeId 1") & closeId,
          dT("1.2a") & (ls(boxSeqT)*) & ls(substitutionBoxAssignT) & // to:=0
            dT("1.2b") & (ls(boxSeqT)*) & ls(boxNDetAssign) & ls(skolemizeT) & // dhf:=*
            dT("1.2u") & (ls(boxSeqT)*) & ls(boxNDetAssign) & ls(skolemizeT) & // dhfUp:=*
            dT("1.2c") & (ls(boxSeqT)*) & ls(boxChoiceT) & // w:=-1; ++ w:=1;
            la(hide, invariantStr) & ls(andR) & /* almost identical branches */
            ls(substitutionBoxAssignT) & // w:=1 or w:=-1 // creates an error unless function apply's ensures is commented out in KeYmaeraXPrettyPrinter.scala
            dT("1.2d") & (ls(boxSeqT)*) & ls(boxTestT) & ls(implyR) & // ?Cimpl
            dT("1.2e") & (ls(boxSeqT)*) & ls(boxNDetAssign) & ls(skolemizeT) & // ao:=*
            dT("1.2f") & ls(andR) && (
            ls(andR) && (
              dT("hide cond") & hideT(AntePosition(1)) & QE, // hide depends on branch
              closeId),
            dT("closeId 2") & closeId
            )
          )
          ),
        (cutUseLbl, dT("Generalization Strong Enough") &
          cutEZ(("!" + evolutionDomain + " | " + evolutionDomain).asFormula,
            ls(cohide, "!" + evolutionDomain + " | " + evolutionDomain) & QE) &
          la(orL, "!" + evolutionDomain + " | " + evolutionDomain) && (
          la(hide, invariantStr) &
            dT("Before DI") &
            cutEZ(("[{"+ode+"&" + evolutionDomain + "}]" + "(0=1)").asFormula,
              // false as postcondition doesn't work: false doesn't parse
              ls(hide, "[{"+ode+"&" + evolutionDomain + "}]" + invariantStr)
                & ls(DI)) &
            la(hide, "!" + evolutionDomain) &
            dT("After DI") & ls(DC("0=1".asFormula)) & onBranch(
            (cutShowLbl, dT("After DC 1") & closeId),
            (cutUseLbl, dT("After DC 2") & ls(DW) & dT("after DW") &
              ls(implyR) & la(andL) & la(cohide, "0=1") & dT("before QE") & QE)),
          dT("Before diff. solution") &
            abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxI"))) &
            abbrv("max((0,w*(dhfUp-dhd)))".asTerm, Some(Variable("maxUpI"))) &
            ls(diffSolution(None,
              la(hide, "maxI=max((0,w*(dhf-dhd)))") &
                la(hide, "maxUpI=max((0,w*(dhfUp-dhd)))"))) &
            dT("Diff. Solution") & ls(implyR) & (la(andL)*) & dT("eqHide's") &
            eqHide("r_2()=r") & eqHide("dhd_2()=dhd") & eqHide("h_2()=h") &
            eqHide("to_2()=to") & dT("bla") & ls(andR) && (
            ls(andR) && (
              ls(andR) && (closeId, closeId),
              dT("bla2") & ls(orR) &
                la(hide, "to<=tl|tl < 0") & la(hide, "to_3<=tl|tl < 0") & // first present twice, eliminating just one??
                la(orL, "\\forall t \\forall ro \\forall ho ((t <= tl-to|tl < 0)&(0<=t&t < maxI/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxI/a&ro=rv*t&ho=dhf*t-w*maxI^2/(2*a))->abs(r-ro)>rp|w*h < w*ho-hp)&\\forall hNew \\forall dhdNew (0<=tl-to&tl-to < maxI/a&hNew=w*a/2*(tl-to)^2+dhd*(tl-to)&dhdNew=w*a*(tl-to)+dhd|tl-to>=maxI/a&hNew=dhf*(tl-to)-w*maxI^2/(2*a)&dhdNew=dhf->\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(w)*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=(w)*a/2*t^2+dhdNew*t|t>=max((0,(w)*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=dhfExtr*t-(w)*max((0,(w)*(dhfExtr-dhdNew)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(w)*(h-hNew) < (w)*ho-hp))|\\forall t \\forall ro \\forall ho ((t <= tl-to|tl < 0)&(0<=t&t < maxUpI/aM&ro=rv*t&ho=w*aM/2*t^2+dhd*t|t>=maxUpI/aM&ro=rv*t&ho=(dhd+w*maxUpI)*t-w*maxUpI^2/(2*aM))->abs(r-ro)>rp|w*h>w*ho+hp)&\\forall hNew \\forall dhdNew (0<=tl-to&tl-to < maxUpI/aM&hNew=w*aM/2*(tl-to)^2+dhd*(tl-to)&dhdNew=w*aM*(tl-to)+dhd|tl-to>=maxUpI/aM&hNew=(dhd+w*maxUpI)*(tl-to)-w*maxUpI^2/(2*aM)&dhdNew=dhd+w*maxUpI->\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(-w)*(h-hNew) < (-w)*ho-hp))")
                && (
                dT("TODO Before hide lower") &
                  ls(hide, "\\forall t \\forall ro \\forall ho ((t <= tl-to_3|tl < 0)&(0<=t&t < max((0,w*(dhfUp-dhd_3)))/aM&ro=rv*t&ho=w*aM/2*t^2+dhd_3*t|t>=max((0,w*(dhfUp-dhd_3)))/aM&ro=rv*t&ho=(dhd_3+w*max((0,w*(dhfUp-dhd_3))))*t-w*max((0,w*(dhfUp-dhd_3)))^2/(2*aM))->abs(r_3-ro)>rp|w*h_3>w*ho+hp)&\\forall hNew \\forall dhdNew (0<=tl-to_3&tl-to_3 < max((0,w*(dhfUp-dhd_3)))/aM&hNew=w*aM/2*(tl-to_3)^2+dhd_3*(tl-to_3)&dhdNew=w*aM*(tl-to_3)+dhd_3|tl-to_3>=max((0,w*(dhfUp-dhd_3)))/aM&hNew=(dhd_3+w*max((0,w*(dhfUp-dhd_3))))*(tl-to_3)-w*max((0,w*(dhfUp-dhd_3)))^2/(2*aM)&dhdNew=dhd_3+w*max((0,w*(dhfUp-dhd_3)))->\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|(-w)*(h_3-hNew) < (-w)*ho-hp))") &
                  la(hide, "aM>=a") & la(hide, "maxUpI=max((0,w*(dhfUp-dhd)))") &
                  la(hide, "w*dhd<=w*dhfUp&w*ao<=aM|w*ao<=0") &
                  la(hide, "w*dhd_3<=w*dhfUp&w*ao<=aM|w*ao<=0") &
                  dT("lower separation") &
                  la(andL) & //, "\\forall t \\forall ro \\forall ho ((t <= tl-to|tl < 0)&(0<=t&t < maxUpI/aM&ro=rv*t&ho=w*aM/2*t^2+dhd*t|t>=maxUpI/aM&ro=rv*t&ho=(dhd+w*maxUpI)*t-w*maxUpI^2/(2*aM))->abs(r-ro)>rp|w*h>w*ho+hp)&\\forall hNew \\forall dhdNew ((0<=tl-to&tl-to < maxUpI/aM&hNew=w*aM/2*(tl-to)^2+dhd*(tl-to)&dhdNew=w*aM*(tl-to)+dhd|tl-to>=maxUpI/aM&hNew=(dhd+w*maxUpI)*(tl-to)-w*maxUpI^2/(2*aM)&dhdNew=dhd+w*maxUpI)->\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(-w)*(h-hNew) < (-w)*ho-hp))") &
                  ls(andR) && (
                  dT("TODO APPLY LEMMA LOWER") &
                    la(hide, "\\forall hNew \\forall dhdNew (0<=tl-to&tl-to < maxI/a&hNew=w*a/2*(tl-to)^2+dhd*(tl-to)&dhdNew=w*a*(tl-to)+dhd|tl-to>=maxI/a&hNew=dhf*(tl-to)-w*maxI^2/(2*a)&dhdNew=dhf->\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(w)*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=(w)*a/2*t^2+dhdNew*t|t>=max((0,(w)*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=dhfExtr*t-(w)*max((0,(w)*(dhfExtr-dhdNew)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(w)*(h-hNew) < (w)*ho-hp))") &
                    dT("lower lemma") &
                    applyLemma2(safeLemmaFormula,safeLemmaApply),
                  dT("DONE after tl") &
                    la(hide, "\\forall t \\forall ro \\forall ho ((t <= tl-to|tl < 0)&(0<=t&t < maxI/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxI/a&ro=rv*t&ho=dhf*t-w*maxI^2/(2*a))->abs(r-ro)>rp|w*h < w*ho-hp)") &
                    cutEZ("(0<=tl-to&tl-to < maxI/a) | tl-to >= maxI/a".asFormula, QE) & dT("cutEZ on tl-to") &
                    (ls(skolemizeT)*) & ls(implyR) & dT("skolemize hnew") &
                    la(orL, "(0<=tl-to&tl-to < maxI/a) | tl-to >= maxI/a") && (
                    dT("DONE tlmto case 1") &
                      abbrv("w*a/2*(tl-to)^2+dhd*(tl-to)".asTerm, Some(Variable("hNew1"))) &
                      abbrv("w*a*(tl-to)+dhd".asTerm, Some(Variable("dhdNew1"))) &
                      inst("hNew", "hNew1") & inst("dhdNew", "dhdNew1") &
                      la(implyL) && (
                      dT("DONE") &
                        ls(hide, "\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,(w)*(dhfExtr-dhdNew_0)))/a&ro=rv*t&ho=(w)*a/2*t^2+dhdNew_0*t|t>=max((0,(w)*(dhfExtr-dhdNew_0)))/a&ro=rv*t&ho=dhfExtr*t-(w)*max((0,(w)*(dhfExtr-dhdNew_0)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|(w)*(h_3-hNew_0) < (w)*ho-hp)") &
                        QE,
                      dT("DONE tlmto 1") &
                        cut("w*(h-hNew1)>=w*(h_3-hNew_0) & w*dhdNew_0>=w*dhdNew1".asFormula) & onBranch(
                        (cutShowLbl, dT("DONE proof cut") &
                          la(hide, "\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(w)*(dhfExtr-dhdNew1)))/a&ro=rv*t&ho=(w)*a/2*t^2+dhdNew1*t|t>=max((0,(w)*(dhfExtr-dhdNew1)))/a&ro=rv*t&ho=dhfExtr*t-(w)*max((0,(w)*(dhfExtr-dhdNew1)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(w)*(h-hNew1) < (w)*ho-hp)") &
                          ls(hide, "\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,(w)*(dhfExtr-dhdNew_0)))/a&ro=rv*t&ho=(w)*a/2*t^2+dhdNew_0*t|t>=max((0,(w)*(dhfExtr-dhdNew_0)))/a&ro=rv*t&ho=dhfExtr*t-(w)*max((0,(w)*(dhfExtr-dhdNew_0)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|(w)*(h_3-hNew_0) < (w)*ho-hp)") &
                          la(MinMaxT, "", Some("max(0,w*(dhf-dhd))".asTerm)) &
                          la(MinMaxT, "", Some("max((0,w*(dhf-dhd_3)))".asTerm)) &
                          dT("show cut hNew QE") &
                          la(orL, "0<=tl-to_3&tl-to_3 < max_1/a&hNew_0=w*a/2*(tl-to_3)^2+dhd_3*(tl-to_3)&dhdNew_0=w*a*(tl-to_3)+dhd_3|tl-to_3>=max_1/a&hNew_0=dhf*(tl-to_3)-w*max_1^2/(2*a)&dhdNew_0=dhf") &
                          (dT("case 1") & crushw, dT("case 2") & crushw ) ),
                        (cutUseLbl, dT("DONE tlmto 1.2") &
                          la(hide, "0<=tl-to_3&tl-to_3 < max((0,w*(dhf-dhd_3)))/a&hNew_0=w*a/2*(tl-to_3)^2+dhd_3*(tl-to_3)&dhdNew_0=w*a*(tl-to_3)+dhd_3|tl-to_3>=max((0,w*(dhf-dhd_3)))/a&hNew_0=dhf*(tl-to_3)-w*max((0,w*(dhf-dhd_3)))^2/(2*a)&dhdNew_0=dhf") &
                          la(hide, "hNew1=w*a/2*(tl-to)^2+dhd*(tl-to)") & la(hide, "dhdNew1=w*a*(tl-to)+dhd") &
                          la(hide, "0<=tl-to&tl-to < maxI/a") & la(hide, "maxI=max((0,w*(dhf-dhd)))") &
                          la(hide, "w*dhd>=w*dhf|w*ao>=a") & la(hide, "w*dhd_3>=w*dhf|w*ao>=a") &
                          dT("inserting lemma") & insertLemma(propagateLoFormula, propagateLoApply) &
                          dT("instantiating") &
                          inst("h0", "h-hNew1") & inst("v0", "dhdNew1") &
                          inst("a0", "a") & inst("vt0", "dhfExtr") & inst("to0", "to") &
                          inst("h1", "h_3-hNew_0") & inst("v1", "dhdNew_0") &
                          inst("a1", "a") & inst("vt1", "dhfExtr") & inst("to1", "to_3") &
                          inst("tl", "-1") & inst("r", "r-rv*(tl-to)") & inst("w", "w") &
                          dT("end inst") & la(implyL) && ( // ok to end inst
                          ls(andR) && (dT("cid") & closeId,
                            la(hide, "\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(w)*(dhfExtr-dhdNew1)))/a&ro=rv*t&ho=(w)*a/2*t^2+dhdNew1*t|t>=max((0,(w)*(dhfExtr-dhdNew1)))/a&ro=rv*t&ho=dhfExtr*t-(w)*max((0,(w)*(dhfExtr-dhdNew1)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(w)*(h-hNew1) < (w)*ho-hp)") &
                              ls(hide, "\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,(w)*(dhfExtr-dhdNew_0)))/a&ro=rv*t&ho=(w)*a/2*t^2+dhdNew_0*t|t>=max((0,(w)*(dhfExtr-dhdNew_0)))/a&ro=rv*t&ho=dhfExtr*t-(w)*max((0,(w)*(dhfExtr-dhdNew_0)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|(w)*(h_3-hNew_0) < (w)*ho-hp)") &
                              dT("qe") & QE
                            ),
                          dT("concl") &
                            la(hide, "\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(w)*(dhfExtr-dhdNew1)))/a&ro=rv*t&ho=(w)*a/2*t^2+dhdNew1*t|t>=max((0,(w)*(dhfExtr-dhdNew1)))/a&ro=rv*t&ho=dhfExtr*t-(w)*max((0,(w)*(dhfExtr-dhdNew1)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(w)*(h-hNew1) < (w)*ho-hp)") &
                            (ls(skolemizeT)*) &
                            inst("t", "t_0") & inst("ro", "ro_0") & inst("ho", "ho_0") &
                            ls(AbsT, "", Some("abs(r_3-rv*(tl-to_3)-ro_0)".asTerm)) &
                            la(AbsT, "", Some("abs(r-rv*(tl-to)-ro_0)".asTerm)) & dT("qe") & QE
                          )
                          )
                      )
                      ),
                    dT("TODO tlmto case 2") &
                      abbrv("dhf*(tl-to)-w*maxI^2/(2*a)".asTerm, Some(Variable("hNew1"))) &
                      //abbrv("dhf".asTerm, Some(Variable("dhdNew1"))) & // doesn't seem to work
                      inst("hNew", "hNew1") & inst("dhdNew", "dhf") &
                      la(implyL) && (
                      dT("DONE") &
                        ls(hide, "\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,(w)*(dhfExtr-dhdNew_0)))/a&ro=rv*t&ho=(w)*a/2*t^2+dhdNew_0*t|t>=max((0,(w)*(dhfExtr-dhdNew_0)))/a&ro=rv*t&ho=dhfExtr*t-(w)*max((0,(w)*(dhfExtr-dhdNew_0)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|(w)*(h_3-hNew_0) < (w)*ho-hp)") &
                        QE,
                      dT("TODO tlmto 1") &
                        cut("w*(h-hNew1)>=w*(h_3-hNew_0) & w*dhdNew_0>=w*dhf".asFormula) & onBranch(
                        (cutShowLbl, dT("TODO proof cut") &
                          la(hide, "\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(w)*(dhfExtr-dhf)))/a&ro=rv*t&ho=(w)*a/2*t^2+dhf*t|t>=max((0,(w)*(dhfExtr-dhf)))/a&ro=rv*t&ho=dhfExtr*t-(w)*max((0,(w)*(dhfExtr-dhf)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(w)*(h-hNew1) < (w)*ho-hp)") &
                          ls(hide, "\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,(w)*(dhfExtr-dhdNew_0)))/a&ro=rv*t&ho=(w)*a/2*t^2+dhdNew_0*t|t>=max((0,(w)*(dhfExtr-dhdNew_0)))/a&ro=rv*t&ho=dhfExtr*t-(w)*max((0,(w)*(dhfExtr-dhdNew_0)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|(w)*(h_3-hNew_0) < (w)*ho-hp)") &
                          la(MinMaxT, "", Some("max(0,w*(dhf-dhd))".asTerm)) &
                          la(MinMaxT, "", Some("max((0,w*(dhf-dhd_3)))".asTerm)) &
                          dT("show cut hNew QE") &
                          la(orL, "0<=tl-to_3&tl-to_3 < max_1/a&hNew_0=w*a/2*(tl-to_3)^2+dhd_3*(tl-to_3)&dhdNew_0=w*a*(tl-to_3)+dhd_3|tl-to_3>=max_1/a&hNew_0=dhf*(tl-to_3)-w*max_1^2/(2*a)&dhdNew_0=dhf") &
                          (dT("case 1") & crushw, dT("case 2") & crushw ) ),
                        (cutUseLbl, dT("TODO tlmto 1.2") &
                          la(hide, "0<=tl-to_3&tl-to_3 < max((0,w*(dhf-dhd_3)))/a&hNew_0=w*a/2*(tl-to_3)^2+dhd_3*(tl-to_3)&dhdNew_0=w*a*(tl-to_3)+dhd_3|tl-to_3>=max((0,w*(dhf-dhd_3)))/a&hNew_0=dhf*(tl-to_3)-w*max((0,w*(dhf-dhd_3)))^2/(2*a)&dhdNew_0=dhf") &
                          la(hide, "hNew1=dhf*(tl-to)-w*maxI^2/(2*a)") &
                          la(hide, "tl-to>=maxI/a") & la(hide, "maxI=max((0,w*(dhf-dhd)))") &
                          la(hide, "w*dhd>=w*dhf|w*ao>=a") & la(hide, "w*dhd_3>=w*dhf|w*ao>=a") &
                          dT("inserting lemma") & insertLemma(propagateLoFormula, propagateLoApply) &
                          dT("instantiating") &
                          inst("h0", "h-hNew1") & inst("v0", "dhf") &
                          inst("a0", "a") & inst("vt0", "dhfExtr") & inst("to0", "to") &
                          inst("h1", "h_3-hNew_0") & inst("v1", "dhdNew_0") &
                          inst("a1", "a") & inst("vt1", "dhfExtr") & inst("to1", "to_3") &
                          inst("tl", "-1") & inst("r", "r-rv*(tl-to)") & inst("w", "w") &
                          dT("end inst") & la(implyL) && ( // ok to end inst
                          ls(andR) && (dT("cid") & closeId,
                            la(hide, "\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(w)*(dhfExtr-dhf)))/a&ro=rv*t&ho=(w)*a/2*t^2+dhf*t|t>=max((0,(w)*(dhfExtr-dhf)))/a&ro=rv*t&ho=dhfExtr*t-(w)*max((0,(w)*(dhfExtr-dhf)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(w)*(h-hNew1) < (w)*ho-hp)") &
                              ls(hide, "\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,(w)*(dhfExtr-dhdNew_0)))/a&ro=rv*t&ho=(w)*a/2*t^2+dhdNew_0*t|t>=max((0,(w)*(dhfExtr-dhdNew_0)))/a&ro=rv*t&ho=dhfExtr*t-(w)*max((0,(w)*(dhfExtr-dhdNew_0)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|(w)*(h_3-hNew_0) < (w)*ho-hp)") &
                              dT("qe") & QE
                            ),
                          dT("concl") &
                            la(hide, "\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(w)*(dhfExtr-dhf)))/a&ro=rv*t&ho=(w)*a/2*t^2+dhf*t|t>=max((0,(w)*(dhfExtr-dhf)))/a&ro=rv*t&ho=dhfExtr*t-(w)*max((0,(w)*(dhfExtr-dhf)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(w)*(h-hNew1) < (w)*ho-hp)") &
                            (ls(skolemizeT)*) &
                            inst("t", "t_0") & inst("ro", "ro_0") & inst("ho", "ho_0") &
                            ls(AbsT, "", Some("abs(r_3-rv*(tl-to_3)-ro_0)".asTerm)) &
                            la(AbsT, "", Some("abs(r-rv*(tl-to)-ro_0)".asTerm)) & dT("qe") & QE
                          )
                          )
                      )
                      )
                    )
                  ),
                dT("Before hide upper") & // very similar proof as "Before hide lower". TODO refactor
                  ls(hide, "\\forall t \\forall ro \\forall ho ((t <= tl-to_3|tl < 0)&(0<=t&t < max((0,w*(dhf-dhd_3)))/a&ro=rv*t&ho=w*a/2*t^2+dhd_3*t|t>=max((0,w*(dhf-dhd_3)))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-dhd_3)))^2/(2*a))->abs(r_3-ro)>rp|w*h_3 < w*ho-hp)&\\forall hNew \\forall dhdNew (0<=tl-to_3&tl-to_3 < max((0,w*(dhf-dhd_3)))/a&hNew=w*a/2*(tl-to_3)^2+dhd_3*(tl-to_3)&dhdNew=w*a*(tl-to_3)+dhd_3|tl-to_3>=max((0,w*(dhf-dhd_3)))/a&hNew=dhf*(tl-to_3)-w*max((0,w*(dhf-dhd_3)))^2/(2*a)&dhdNew=dhf->\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,w*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=w*a/2*t^2+dhdNew*t|t>=max((0,w*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=dhfExtr*t-w*max((0,w*(dhfExtr-dhdNew)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|w*(h_3-hNew) < w*ho-hp))") &
                  cutEZ("aM>0".asFormula,
                    la(hide, "\\forall t \\forall ro \\forall ho ((t <= tl-to|tl < 0)&(0<=t&t < maxUpI/aM&ro=rv*t&ho=w*aM/2*t^2+dhd*t|t>=maxUpI/aM&ro=rv*t&ho=(dhd+w*maxUpI)*t-w*maxUpI^2/(2*aM))->abs(r-ro)>rp|w*h>w*ho+hp)&\\forall hNew \\forall dhdNew (0<=tl-to&tl-to < maxUpI/aM&hNew=w*aM/2*(tl-to)^2+dhd*(tl-to)&dhdNew=w*aM*(tl-to)+dhd|tl-to>=maxUpI/aM&hNew=(dhd+w*maxUpI)*(tl-to)-w*maxUpI^2/(2*aM)&dhdNew=dhd+w*maxUpI->\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(-w)*(h-hNew) < (-w)*ho-hp))")
                      & ls(hide, "\\forall t \\forall ro \\forall ho ((t <= tl-to_3|tl < 0)&(0<=t&t < max((0,w*(dhfUp-dhd_3)))/aM&ro=rv*t&ho=w*aM/2*t^2+dhd_3*t|t>=max((0,w*(dhfUp-dhd_3)))/aM&ro=rv*t&ho=(dhd_3+w*max((0,w*(dhfUp-dhd_3))))*t-w*max((0,w*(dhfUp-dhd_3)))^2/(2*aM))->abs(r_3-ro)>rp|w*h_3>w*ho+hp)&\\forall hNew \\forall dhdNew (0<=tl-to_3&tl-to_3 < max((0,w*(dhfUp-dhd_3)))/aM&hNew=w*aM/2*(tl-to_3)^2+dhd_3*(tl-to_3)&dhdNew=w*aM*(tl-to_3)+dhd_3|tl-to_3>=max((0,w*(dhfUp-dhd_3)))/aM&hNew=(dhd_3+w*max((0,w*(dhfUp-dhd_3))))*(tl-to_3)-w*max((0,w*(dhfUp-dhd_3)))^2/(2*aM)&dhdNew=dhd_3+w*max((0,w*(dhfUp-dhd_3)))->\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|(-w)*(h_3-hNew) < (-w)*ho-hp))")
                      & QE) &
                  la(hide, "aM>=a") &
                  //la(hide, "a>0") & // TODO: only keep aexup
                  la(hide, "maxI=max((0,w*(dhf-dhd)))") &
                  la(hide, "w*dhd>=w*dhf|w*ao>=a") &
                  la(hide, "w*dhd_3>=w*dhf|w*ao>=a") &
                  dT("upper separation") &
                  la(andL) &
                  ls(andR) && (
                  dT("TODO APPLY LEMMA UPPER") &
                    la(hide, "\\forall hNew \\forall dhdNew (0<=tl-to&tl-to < maxUpI/aM&hNew=w*aM/2*(tl-to)^2+dhd*(tl-to)&dhdNew=w*aM*(tl-to)+dhd|tl-to>=maxUpI/aM&hNew=(dhd+w*maxUpI)*(tl-to)-w*maxUpI^2/(2*aM)&dhdNew=dhd+w*maxUpI->\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(-w)*(h-hNew) < (-w)*ho-hp))") &
                    dT("upper lemma") &
                    applyLemma2(safeUpLemmaFormula,safeUpLemmaApply),
                  dT("DONE!! after tl") &
                    la(hide, "\\forall t \\forall ro \\forall ho ((t <= tl-to|tl < 0)&(0<=t&t < maxUpI/aM&ro=rv*t&ho=w*aM/2*t^2+dhd*t|t>=maxUpI/aM&ro=rv*t&ho=(dhd+w*maxUpI)*t-w*maxUpI^2/(2*aM))->abs(r-ro)>rp|w*h>w*ho+hp)") &
                    cutEZ("(0<=tl-to&tl-to < maxUpI/aM) | tl-to >= maxUpI/aM".asFormula, QE) & dT("cutEZ on tl-to") &
                    (ls(skolemizeT)*) & ls(implyR) & dT("skolemize hnew") &
                    la(orL, "(0<=tl-to&tl-to < maxUpI/aM) | tl-to >= maxUpI/aM") && (
                    dT("DONE tlmto case 1") &
                      abbrv("w*aM/2*(tl-to)^2+dhd*(tl-to)".asTerm, Some(Variable("hNew1"))) &
                      abbrv("w*aM*(tl-to)+dhd".asTerm, Some(Variable("dhdNew1"))) &
                      inst("hNew", "hNew1") & inst("dhdNew", "dhdNew1") &
                      la(implyL) && (
                      dT("DONE") &
                        ls(hide, "\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew_0)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew_0*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew_0)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew_0)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|(-w)*(h_3-hNew_0) < (-w)*ho-hp)") &
                        QE,
                      dT("DONE tlmto 1") &
                        cut("w*(h-hNew1)<=w*(h_3-hNew_0) & w*dhdNew_0<=w*dhdNew1".asFormula) & onBranch(
                        (cutShowLbl, dT("REVIEW, used to be done with old cut show cut hNew") &
                          la(hide, "\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew1)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew1*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew1)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew1)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(-w)*(h-hNew1) < (-w)*ho-hp)") &
                          ls(hide, "\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew_0)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew_0*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew_0)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew_0)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|(-w)*(h_3-hNew_0) < (-w)*ho-hp)") &
                          la(MinMaxT, "", Some("max(0,w*(dhfUp-dhd))".asTerm)) &
                          la(MinMaxT, "", Some("max((0,w*(dhfUp-dhd_3)))".asTerm)) &
                          dT("show cut hNew QE") &
                          la(orL, "0<=tl-to_3&tl-to_3 < max_1/aM&hNew_0=w*aM/2*(tl-to_3)^2+dhd_3*(tl-to_3)&dhdNew_0=w*aM*(tl-to_3)+dhd_3|tl-to_3>=max_1/aM&hNew_0=(dhd_3+w*max_1)*(tl-to_3)-w*max_1^2/(2*aM)&dhdNew_0=dhd_3+w*max_1") &&
                          (dT("case 1") & crushw, dT("case 2") & crushw ) ),
                        (cutUseLbl, dT("DONE tlmto 1.2") & la(hide, "aM>0") &
                          la(hide, "0<=tl-to_3&tl-to_3 < max((0,w*(dhfUp-dhd_3)))/aM&hNew_0=w*aM/2*(tl-to_3)^2+dhd_3*(tl-to_3)&dhdNew_0=w*aM*(tl-to_3)+dhd_3|tl-to_3>=max((0,w*(dhfUp-dhd_3)))/aM&hNew_0=(dhd_3+w*max((0,w*(dhfUp-dhd_3))))*(tl-to_3)-w*max((0,w*(dhfUp-dhd_3)))^2/(2*aM)&dhdNew_0=dhd_3+w*max((0,w*(dhfUp-dhd_3)))") &
                          la(hide, "hNew1=w*aM/2*(tl-to)^2+dhd*(tl-to)") & la(hide, "dhdNew1=w*aM*(tl-to)+dhd") &
                          la(hide, "0<=tl-to&tl-to < maxUpI/aM") & la(hide, "maxUpI=max((0,w*(dhfUp-dhd)))") &
                          la(hide, "w*dhd<=w*dhfUp&w*ao<=aM|w*ao<=0") & la(hide, "w*dhd_3<=w*dhfUp&w*ao<=aM|w*ao<=0") &
                          dT("inserting lemma") & insertLemma(propagateLoFormula, propagateLoApply) &
                          dT("instantiating") &
                          inst("h0", "h-hNew1") & inst("v0", "dhdNew1") &
                          inst("a0", "a") & inst("vt0", "dhfUpExtr") & inst("to0", "to") &
                          inst("h1", "h_3-hNew_0") & inst("v1", "dhdNew_0") &
                          inst("a1", "a") & inst("vt1", "dhfUpExtr") & inst("to1", "to_3") &
                          inst("tl", "-1") & inst("r", "r-rv*(tl-to)") & inst("w", "-w") &
                          dT("end inst") & la(implyL) && (
                          ls(andR) && (closeId,
                            la(hide, "\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew1)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew1*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew1)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew1)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(-w)*(h-hNew1) < (-w)*ho-hp)") &
                              ls(hide, "\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew_0)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew_0*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew_0)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew_0)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|(-w)*(h_3-hNew_0) < (-w)*ho-hp)") &
                              QE
                            ),
                          dT("concl") &
                            la(hide, "\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew1)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew1*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew1)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew1)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(-w)*(h-hNew1) < (-w)*ho-hp)") &
                            (ls(skolemizeT)*) &
                            inst("t", "t_0") & inst("ro", "ro_0") & inst("ho", "ho_0") &
                            //cutEZ("r_3-rv*(tl-to_3)=r-rv*(tl-to)".asFormula, QE) &
                            // eqHide("r_3-rv*(tl-to_3)=r-rv*(tl-to)") & closeId // ??? DOES NOW WORK EVEN AFTER INSTANTIATION
                            ls(AbsT, "", Some("abs(r_3-rv*(tl-to_3)-ro_0)".asTerm)) &
                            la(AbsT, "", Some("abs(r-rv*(tl-to)-ro_0)".asTerm)) & QE
                          )
                          )
                      )
                      ),
                    dT("DONE tlmto case 2") &
                      abbrv("(dhd+w*maxUpI)*(tl-to)-w*maxUpI^2/(2*aM)".asTerm, Some(Variable("hNew1"))) &
                      abbrv("dhd+w*maxUpI".asTerm, Some(Variable("dhdNew1"))) &
                      inst("hNew", "hNew1") & inst("dhdNew", "dhdNew1") &
                      la(implyL) && (
                      dT("DONE") &
                        ls(hide, "\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew_0)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew_0*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew_0)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew_0)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|(-w)*(h_3-hNew_0) < (-w)*ho-hp)") &
                        QE,
                      dT("DONE tlmto 2") &
                        cut("w*(h-hNew1)<=w*(h_3-hNew_0) & w*dhdNew_0<=w*dhdNew1".asFormula) & onBranch(
                        (cutShowLbl, dT("TODO cut") &
                          la(hide, "\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew1)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew1*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew1)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew1)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(-w)*(h-hNew1) < (-w)*ho-hp)") &
                          ls(hide, "\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew_0)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew_0*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew_0)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew_0)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|(-w)*(h_3-hNew_0) < (-w)*ho-hp)") &
                          la(MinMaxT, "", Some("max(0,w*(dhfUp-dhd))".asTerm)) &
                          la(MinMaxT, "", Some("max((0,w*(dhfUp-dhd_3)))".asTerm)) &
                          dT("show cut hNew QE") &
                          la(orL, "0<=tl-to_3&tl-to_3 < max_1/aM&hNew_0=w*aM/2*(tl-to_3)^2+dhd_3*(tl-to_3)&dhdNew_0=w*aM*(tl-to_3)+dhd_3|tl-to_3>=max_1/aM&hNew_0=(dhd_3+w*max_1)*(tl-to_3)-w*max_1^2/(2*aM)&dhdNew_0=dhd_3+w*max_1") &&
                          (dT("case 1") & crushw, dT("case 2") & crushw ) ),
                        (cutUseLbl, dT("DONE tlmto 2.2") & la(hide, "aM>0") &
                          // For future refactoring: This proof is exactly identical as TODO tlmto 1.2, except the hide on dhdNew1
                          la(hide, "0<=tl-to_3&tl-to_3 < max((0,w*(dhfUp-dhd_3)))/aM&hNew_0=w*aM/2*(tl-to_3)^2+dhd_3*(tl-to_3)&dhdNew_0=w*aM*(tl-to_3)+dhd_3|tl-to_3>=max((0,w*(dhfUp-dhd_3)))/aM&hNew_0=(dhd_3+w*max((0,w*(dhfUp-dhd_3))))*(tl-to_3)-w*max((0,w*(dhfUp-dhd_3)))^2/(2*aM)&dhdNew_0=dhd_3+w*max((0,w*(dhfUp-dhd_3)))") &
                          la(hide, "hNew1=dhdNew1*(tl-to)-w*maxUpI^2/(2*aM)") & la(hide, "dhdNew1=dhd+w*maxUpI") &
                          la(hide, "tl-to >= maxUpI/aM") & la(hide, "maxUpI=max((0,w*(dhfUp-dhd)))") &
                          la(hide, "w*dhd<=w*dhfUp&w*ao<=aM|w*ao<=0") & la(hide, "w*dhd_3<=w*dhfUp&w*ao<=aM|w*ao<=0") &
                          dT("inserting lemma") & insertLemma(propagateLoFormula, propagateLoApply) &
                          dT("instantiating") &
                          inst("h0", "h-hNew1") & inst("v0", "dhdNew1") &
                          inst("a0", "a") & inst("vt0", "dhfUpExtr") & inst("to0", "to") &
                          inst("h1", "h_3-hNew_0") & inst("v1", "dhdNew_0") &
                          inst("a1", "a") & inst("vt1", "dhfUpExtr") & inst("to1", "to_3") &
                          inst("tl", "-1") & inst("r", "r-rv*(tl-to)") & inst("w", "-w") &
                          dT("end inst") & la(implyL) && (
                          ls(andR) && (closeId,
                            la(hide, "\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew1)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew1*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew1)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew1)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(-w)*(h-hNew1) < (-w)*ho-hp)") &
                              ls(hide, "\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew_0)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew_0*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew_0)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew_0)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|(-w)*(h_3-hNew_0) < (-w)*ho-hp)") &
                              QE
                            ),
                          dT("concl") &
                            la(hide, "\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew1)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew1*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew1)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew1)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(-w)*(h-hNew1) < (-w)*ho-hp)") &
                            (ls(skolemizeT)*) &
                            inst("t", "t_0") & inst("ro", "ro_0") & inst("ho", "ho_0") &
                            ls(AbsT, "", Some("abs(r_3-rv*(tl-to_3)-ro_0)".asTerm)) &
                            la(AbsT, "", Some("abs(r-rv*(tl-to)-ro_0)".asTerm)) & QE
                          )
                          )
                      )
                      )
                    )
                  )
                )
              ), QE
            )
          )
          ) /* End cutUseLbl "Generalization strong enough" */
      ) ) /* End indStepLbl */
    )

    val safeTheorem = helper.runTactic(safeTac, new RootNode(safeSeq))
    safeTheorem shouldBe 'closed
  }


  "ACAS X" should "directly prove explicit region safety from implicit region safety and direct equivalence" in {
    val acasximplicit = KeYmaeraXProblemParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/acasx/nodelay.key")).mkString)
    val acasxexplicit = KeYmaeraXProblemParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/acasx/nodelay-explicit.key")).mkString)
    val equivalence = KeYmaeraXProblemParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/acasx/nodelay-equivalence-direct.key")).mkString)
    val shape = Context(
      """  (hp > 0 & rp > 0 & rv >= 0 & a > 0) &
  ( (w=-1 | w=1) &
      (
        ⎵
      ) /* C(w,dhf) */
  )
  -> [
  {   {
      { ?true; ++
        {dhf :=*; {w:=-1; ++ w:=1;}
         ?(
            ⎵
          ); /* C(w,dhf) */
        }}
        ao :=*;
      }
      {r' = -rv, dhd' = ao, h' = -dhd & (w * dhd >= w * dhf | w * ao >= a)}
   }*
  ] ((h < -hp | h > hp | r < -rp | r> rp) & ⎵)
      """.asFormula)

    import TactixLibrary._

    TactixLibrary.proveBy(acasxexplicit,
      HilbertCalculus.CE(Provable.startProof(equivalence) /*(CommuteEquivRight(SuccPos(0)), 0)*/, shape)(SuccPosition(0))).
      subgoals should contain only (
      new Sequent(Nil, immutable.IndexedSeq(), immutable.IndexedSeq(acasximplicit)),
      new Sequent(Nil, immutable.IndexedSeq(), immutable.IndexedSeq(equivalence))
      )
  }

  it should "derive distributive version of conditional equivalence" in {
    val equivalence = KeYmaeraXProblemParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/acasx/nodelay_equivalence.key")).mkString)
    val Imply(And(a, w), Equiv(e, i)) = equivalence
    import TactixLibrary._
    val distEquivalence = TactixLibrary.proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq(Equiv(Imply(And(a,w), e), Imply(And(a,w),i)))),
      useAt("-> distributes over <->", PosInExpr(1::Nil))(1))
    distEquivalence.subgoals should contain only Sequent(Nil, IndexedSeq(), IndexedSeq(equivalence))
  }


  it should "derive sequent version of conditional equivalence" in {
    val equivalence = KeYmaeraXProblemParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/acasx/nodelay_equivalence.key")).mkString)
    val Imply(And(a,w), Equiv(e,i)) = equivalence
    val seqEquivalence = (Provable.startProof(Sequent(Nil, IndexedSeq(a, w), IndexedSeq(Equiv(e,i))))
    (Cut(equivalence), 0)
    // right branch reduces to the proof of "equivalence"
    (CoHideRight(SuccPos(1)), 1)
      // left branch follows from "equivalence"
      (ImplyLeft(AntePos(2)), 0)
      // third branch e<->i |- e<->i
      (Close(AntePos(2), SuccPos(0)), 2)
      // second branch a,w |- e<->i, a&w
      (AndRight(SuccPos(1)), 0)
      // second-right branch a,w |- e<->i, w
      (Close(AntePos(1), SuccPos(1)), 2)
      // second-left branch a,w |- e<->i, a
      (Close(AntePos(0), SuccPos(1)), 0)
      )
    seqEquivalence.subgoals should contain only Sequent(Nil, IndexedSeq(), IndexedSeq(equivalence))
  }


  it should "nearly prove stylized generic region Ce safety from region Ci safety and conditional equivalence" in {
    val implicitExplicit = Provable.startProof(Sequent(Nil, IndexedSeq(), IndexedSeq("A()&W(w) -> (Ce(w,dhf/*r,dhd,h,dhf,w,ao*/)<->Ci(w,dhf/*r,dhd,h,dhf,w,ao*/))".asFormula)))
    val shape = Context(
      """  (A()) &
  ( (W(w)) &
        ⎵
  )
  -> [
  {   {
      { ?true; ++
        {dhf :=*; {w:=-1; ++ w:=1;}
         ?⎵;
        }}
        ao :=*;
      }
      {r' = -rv, dhd' = ao, h' = -dhd & (w * dhd >= w * dhf | w * ao >= a)}
   }*
  ] ((abs(r)>rp|abs(h)>hp) & ⎵)
      """.asFormula)

    val equivalence = implicitExplicit.conclusion.succ.head

    val Imply(And(a,w), Equiv(e,i)) = equivalence
    val acasximplicit = shape(i)
    val acasxexplicit = shape(e)
    acasXcongruence(implicitExplicit, Provable.startProof(acasximplicit), acasxexplicit).subgoals should have length 2
  }

  it should "prove explicit region safety from implicit region safety and conditional equivalence" in {
    val acasximplicit = KeYmaeraXProblemParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/acasx/nodelay_max.key")).mkString)
    val acasxexplicit = KeYmaeraXProblemParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/acasx/nodelay-explicit.key")).mkString)
    val implicitExplicit = KeYmaeraXProblemParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/acasx/nodelay_equivalence.key")).mkString)
    val lem = true
    val lemmaDB = LemmaDBFactory.lemmaDB
    val acasximplicitP = if (lem && lemmaDB.contains("nodelay_max")) LookupLemma(lemmaDB, "nodelay_max").lemma.fact else Provable.startProof(acasximplicit)
    val implicitExplicitP = if (lem && lemmaDB.contains("nodelay_equivalence")) LookupLemma(lemmaDB, "nodelay_equivalence").lemma.fact else Provable.startProof(implicitExplicit)
    if (!acasximplicitP.isProved || !implicitExplicitP.isProved) println("Proof will be partial. Prove other lemmas first")
    val proof = acasXcongruence(implicitExplicitP, acasximplicitP, acasxexplicit, QE)
    /*proof.subgoals should contain only (
      new Sequent(Nil, immutable.IndexedSeq(), immutable.IndexedSeq(acasximplicitP.subgoals)),
      new Sequent(Nil, immutable.IndexedSeq(), immutable.IndexedSeq(implicitExplicitP.subgoals))
      )*/
    println("Proof has " + proof.subgoals.size + " open goals")
    proof shouldBe 'proved
    proof.proved shouldBe Sequent(Nil, IndexedSeq(), IndexedSeq(acasxexplicit))
    lemmaDB.add(Lemma(proof, ToolEvidence(immutable.Map("input" -> acasxexplicit.toString, "output" -> "true")) :: Nil, Some("nodelay-explicit")))
  }


  /**
   * ACAS X proof embedding conditional equivalence of implicit and explicit into safety proof of implicit regions
   * to form a safety proof of explicit regions.
   * @param implicitExplicit conditional equivalence result for implicit, explicit regions
   * @param acasximplicitP safe hybrid systems model with implicit regions
   * @param acasxexplicit conjectured hybrid systems model with explicit regions
   * @param done what to call at arithmetic leaves
   * @return a proof of acasxexplicit as constructed out of the other ingredients.
   * @author Andre Platzer
   */
  private def acasXcongruence(implicitExplicit: Provable, acasximplicitP: Provable, acasxexplicit: Formula, done: Tactic = close): Provable = {
    println("implicit-explicit lemma subgoals: " + implicitExplicit.subgoals)
    implicitExplicit.conclusion.ante shouldBe 'empty
    implicitExplicit.conclusion.succ.length shouldBe 1
    val equivalence = implicitExplicit.conclusion.succ.head
    // extract subformulas A()&W(w) -> (Ce(...)<->Ci(...))
    val Imply(And(a,w), Equiv(e,i)) = equivalence

    acasximplicitP.conclusion.ante shouldBe 'empty
    acasximplicitP.conclusion.succ.length shouldBe 1
    val acasximplicit = acasximplicitP.conclusion.succ.head
    acasximplicit match {
      case Imply(And(aa, And(ww, c)), Box(Loop(_), And(_, c2))) if aa == a && ww == w && c == i && c2 == i =>
      case _ => throw new IllegalArgumentException("Unexpected input shape of implicit file\nFound:    " + acasximplicit
        + "\nExpected: " + Imply(And(a, And(w, i)), Context(Box(
        """
          |{   {
          |      { ?true; ++
          |        {dhf :=*; {w:=-1; ++ w:=1;}
          |         ?⎵;
          |        }}
          |        ao :=*;
          |      }
          |      {r' = -rv, dhd' = ao, h' = -dhd & (w * dhd >= w * dhf | w * ao >= a)}
          |   }*
        """.stripMargin.asProgram, And("abs(r)>rp|abs(h)>hp".asFormula, i))) (i)))

    }
    val Imply(And(_, And(_, _)), Box(Loop(body), And(u, _))) = acasximplicit

    acasxexplicit match {
      case Imply(And(aa, And(ww, c)), Box(Loop(_), And(_, c2))) if aa == a && ww == w && c == e && c2 == e =>
      case _ => throw new IllegalArgumentException("Unexpected input shape of explicit file\nFound:    " + acasxexplicit
        + "\nExpected: " + Imply(And(a, And(w, e)), Context(Box(
        """
          |{   {
          |      { ?true; ++
          |        {dhf :=*; {w:=-1; ++ w:=1;}
          |         ?⎵;
          |        }}
          |        ao :=*;
          |      }
          |      {r' = -rv, dhd' = ao, h' = -dhd & (w * dhd >= w * dhf | w * ao >= a)}
          |   }*
        """.stripMargin.asProgram, And("abs(r)>rp|abs(h)>hp".asFormula, e))) (e))
      )
    }

    // read off more lemmas from equivalence

    //@note same proof of seqEquivalence as in "derive sequent version of conditional equivalence"
    val seqEquivalence = (Provable.startProof(Sequent(Nil, IndexedSeq(a, w), IndexedSeq(Equiv(e,i))))
    (Cut(equivalence), 0)
    // right branch reduces to the proof of "equivalence"
    (CoHideRight(SuccPos(1)), 1)
    // left branch follows from "equivalence"
    (ImplyLeft(AntePos(2)), 0)
    // third branch e<->i |- e<->i
    (Close(AntePos(2), SuccPos(0)), 2)
    // second branch a,w |- e<->i, a&w
    (AndRight(SuccPos(1)), 0)
    // second-right branch a,w |- e<->i, w
    (Close(AntePos(1), SuccPos(1)), 2)
    // second-left branch a,w |- e<->i, a
    (Close(AntePos(0), SuccPos(1)), 0)
    // drag&drop proof
    (implicitExplicit, 0) )
    seqEquivalence.subgoals shouldBe implicitExplicit.subgoals
    val shuffle = TactixLibrary.proveBy("(A()&W()->(Ce()<->Ci())) -> ((W()->A()->u()&Ci()) <-> (W()->A()->u()&Ce()))".asFormula, prop)
    shuffle shouldBe 'proved
    // (W(w)->A->u&Ci(w,dhf)) <-> (W(w)->A->u&Ce(w,dhf))
    val postEquivalence = TactixLibrary.proveBy(
      Equiv(Imply(w,Imply(a, And(u, i))),
            Imply(w,Imply(a, And(u, e))))
      , useAt(shuffle, PosInExpr(1::Nil))(1)
        & by(implicitExplicit))
    postEquivalence.subgoals shouldBe implicitExplicit.subgoals

    //@note _0 variations in induction :-/
    val w0 = w // "W(w_0)".asFormula
    val i0 = i // "Ci(w_0,dhf_0)".asFormula
    val e0 = e // "Ce(w_0,dhf_0)".asFormula
    val u0 = u // "(h_0 < -hp | h_0 > hp | r_0 < -rp | r_0> rp)".asFormula

    // (A()&W(w) -> Ce(w,dhf))  <->  (A()&W(w) -> Ci(w,dhf))
    val distEquivalence = TactixLibrary.proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq(Equiv(Imply(And(a,w), e), Imply(And(a,w),i)))),
      useAt("-> distributes over <->", PosInExpr(1::Nil))(1)
      & by(implicitExplicit))
    distEquivalence.subgoals shouldBe implicitExplicit.subgoals
    val shuffle2 = TactixLibrary.proveBy("(A()&W()->(Ce()<->Ci())) -> ((A()&W() -> Ce() -> q()) <-> (A()&W() -> Ci() -> q()))".asFormula, prop)
    shuffle2 shouldBe 'proved
    // (A()&W(w_0) -> Ce(w_0,dhf_0) -> q())  <->  (A()&W(w_0) -> Ci(w_0,dhf_0) -> q())
    val distEquivImpl = (TactixLibrary.proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq(Equiv(
      Imply(And(a,w0), Imply(e0, "q()".asFormula)),
      Imply(And(a,w0), Imply(i0, "q()".asFormula))))),
      // //useAt("-> distributes over <->", PosInExpr(1::Nil))(1))
      useAt(shuffle2, PosInExpr(1::Nil))(1)
        & byUS(implicitExplicit)))
    distEquivImpl.subgoals shouldBe implicitExplicit.subgoals
    println("distEquivImpl " + distEquivImpl)

    val lemmaDB = LemmaDBFactory.lemmaDB
    val ucLoFact = if (lemmaDB.contains("nodelay_ucLoLemma")) LookupLemma(lemmaDB, "nodelay_ucLoLemma").lemma.fact
    else Provable.startProof(Imply(And(w,And(i,a)), u))
    val ucLoLemma = TactixLibrary.proveBy(Sequent(Nil, IndexedSeq(a, w, i), IndexedSeq(u)),
      cut(ucLoFact.conclusion.succ.head) & onBranch(
        (BranchLabels.cutShowLbl, cohide(2) & by(ucLoFact)),
        (BranchLabels.cutUseLbl, implyL(-4) & (andR(2) & (andR(2) & (closeId , closeId), closeId), closeId) )
      )
    )
    ucLoLemma.subgoals shouldBe ucLoFact.subgoals
    if (!ucLoLemma.isProved) println("Proof will be partial. Prove other lemmas first")

    // begin actual proof


    val invariantWT =
      // could also just always generalize(w0)
      // this is a more efficient version
      //@note could have handled 2*composeb(1) at once
      //@note useing W(w_0) instead of W(w) or use post-postcondition
      composeb(1) & generalize(w0)(1) & onBranch(
        (BranchLabels.genShow, debugT("W gen V 1") & V(1) & closeId),
        (BranchLabels.genUse, composeb(1) & useAt("V[:*] vacuous assign nondet")(SuccPosition(0, 1::Nil)) &
          choiceb(1) & andR(1) & (
          sublabel("& left") & testb(1) & implyR(1) & closeId
          ,
          sublabel("& right") &
            composeb(1) & composeb(SuccPosition(0, 1::Nil)) & generalize(w0)(1) & onBranch(
            (BranchLabels.genUse, useAt("V[:*] vacuous assign nondet")(1) & closeId),
            (BranchLabels.genShow, generalize(w0)(1) & onBranch(
              (BranchLabels.genShow, debugT("W gen V 2") & V(1) & closeId),
              (BranchLabels.genUse, sublabel("W arith") & debug("W arith") & cohide(1) & choiceb(1) & useAt("[:=] assign")(1, 0::Nil) & useAt("[:=] assign")(1, 1::Nil) & QE)
            ))
          )
          )
          )
      )

    // W is invariant proof for both implicit and explicit models. Same tactic above.
//    val invariantWi = TactixLibrary.proveBy(
//      Sequent(Nil, IndexedSeq(w), IndexedSeq(Box(body, w)))
//      ,
//      invariantWT)
    val invariantWe = TactixLibrary.proveBy(
      Sequent(Nil, IndexedSeq(w), IndexedSeq(Box(
        acasxexplicit match {case Imply(And(_, And(_, _)), Box(Loop(body), And(_, _))) => body}, w)))
      ,
      invariantWT)

    val proof = TactixLibrary.proveBy(acasxexplicit,
      implyR(1) & andL(-1) &
        postCut(a)(1) & onBranch(
        (BranchLabels.cutShowLbl, sublabel("A() vacuous") & debug("vacuous global assumptions") & V(1) & close(-1, 1)),

        (BranchLabels.cutUseLbl, label("") & debug("true induction need") &

          postCut(w)(1) & onBranch(
          (BranchLabels.cutShowLbl, label("") & debug("w=-1 | w=1") & assertT(And(w,e), "W&Ce")(-2) & andL(-2) &
            //loop(w)(1)
            ind(w)(1) & onBranch(
            (BranchLabels.indInitLbl, sublabel("W(w) init") & closeId),

            (BranchLabels.indStepLbl, sublabel("W(w) step") & //hide(w)(-4) & hide(w)(-2) &
              /*implyR(1) &*/ debug("step w=-1 | w=1") &
              by(invariantWe)
              ),

            (BranchLabels.indUseCaseLbl, sublabel("W(w) loop use") & /*implyR(1) &*/ closeId)
          )
            // end postCut(w)
            ),

          (BranchLabels.cutUseLbl, sublabel("A()&W(w) augmented") & assertT(And(w,e), "W&Ce")(-2) & andL(-2) & debug("inductive use of A&W") &
            cutL(i)(-3) & onBranch(
            (BranchLabels.cutShowLbl, hide(1) & label("by seq-equiv") & equivifyR(1) & by(seqEquivalence)),

            (BranchLabels.cutUseLbl, sublabel("Ce~>Ci reduction") & label("Ce~>Ci reduction") & debug("Ce~>Ci reduction") &
              CE(postEquivalence)(1, 1::Nil)
              & debug("Ce~>Ci reduced in postcondition")
              & debug("unpack and repack to replace test") &
              /*loop(And(w,And(u, i)))(1)*/
              ind(And(a,And(w,And(u, i))))(1)
              & sublabel("loop induction")
              & onBranch(
              (BranchLabels.indInitLbl, sublabel("W&u&Ci init") & debug("W&u&Ci init") & andR(1) & (closeId , andR(1) & (close(-2,1) , andR(1) & (
                label("arith") /*& done*/
                & debug("A&W(w)&Ci->u")
                & by(ucLoLemma)
                , close(-3,1))))),

              (BranchLabels.indStepLbl, sublabel("W&u&Ci step") & // hide(And(w,And(u,i)))(-4) & hide(i)(-3) & hide(w)(-2) &
                andL(-1) & assertE(a, "A()")(-1) &
                splitb(1) & andR(1) & (
                // A() invariant
                V(1) & closeId
                ,
                // implyR(1) &
                splitb(1) & andR(1) & (
                  // W(w) invariant
                  debug("W invariant again") &
                  andL(-2) & andL(-3)
                    & hide(i)(-4) & hide(u)(-3) & hide(a)(-1) &
                  by(invariantWe)
                  ,
                  // u&Ce invariant
                  composeb(1) & composeb(1) & choiceb(1)  // unpack
                    //& useAt("[;] compose", PosInExpr(1::Nil))(SuccPosition(0, 1::Nil))  // gather
                    & composeb(SuccPosition(0, 1::Nil)) & composeb(SuccPosition(0, 1::1::Nil))
                    & debug("cutting explicit dynamics away")
                    & cutAt(i0)(SuccPosition(0, 1::1::1::0::0::Nil)) & debug("cuttedAt") & onBranch(
                    (BranchLabels.cutShowLbl, sublabel("show patch") & debug("showing patch")
                      & useAt("-> distributes over &", PosInExpr(0::Nil))(1)
                      & andR(1) & (
                      // left branch is unchanged
                      sublabel("cutAt no change on left") & implyR(1) & andL(-3) & closeId
                      ,
                      // right branch replaced implicit with explicit conditionally
                      sublabel("CMon++")
                        & debug("CMon++")
                        & useAt("& commute")(SuccPosition(0, 0::Nil))
                        & debug("& commuted")
                        & useAt("-> weaken", PosInExpr(1::Nil))(1)
                        & debug("-> weakened")
                        & label("CMon") & debug("CMon")
                        & sublabel("-> weakened")
                        // the following is like CMon(PosInExpr(1::1::1::0::0::Nil)) except with context kept around
                        & implyR(1)
                        & debug("->R ed")
                        /*
                        & (choiceb(1, 1::Nil) & choiceb(-3, 1::Nil))
                        & (useAt("[:=] assign")(1, 1::0::Nil) & useAt("[:=] assign")(-3, 1::0::Nil))
                        & (useAt("[:=] assign")(1, 1::1::Nil) & useAt("[:=] assign")(-3, 1::1::Nil))
                        & (randomb(1) & randomb(-3))
                        */
                        // gather outer [dhf:=*;][w:=-1;++w:=1;] boxes to single [;]
                        & sublabel("gathering") & debug("gathering")
                        // A(), W(w)&u&Ci((w,dhf)), [dhf:=*;][w:=-1;++w:=1;][?Ci((w,dhf));][ao:=*;][{r'=-rv,dhd'=ao,h'=-dhd&w*dhd>=w*dhf|w*ao>=a}](u&Ci((w,dhf)))  ==>  [dhf:=*;][w:=-1;++w:=1;][?Ce((w,dhf));][ao:=*;][{r'=-rv,dhd'=ao,h'=-dhd&w*dhd>=w*dhf|w*ao>=a}](u&Ci((w,dhf)))
                        & useAt("[;] compose", PosInExpr(1::Nil))(1)
                        & useAt("[;] compose", PosInExpr(1::Nil))(-3)
                        & debug("gathered")
                        // A(), W(w)&u&Ci((w,dhf)), [dhf:=*;{w:=-1;++w:=1;}][?Ci((w,dhf));][ao:=*;][{r'=-rv,dhd'=ao,h'=-dhd&w*dhd>=w*dhf|w*ao>=a}](u&Ci((w,dhf)))  ==>  [dhf:=*;{w:=-1;++w:=1;}][?Ce((w,dhf));][ao:=*;][{r'=-rv,dhd'=ao,h'=-dhd&w*dhd>=w*dhf|w*ao>=a}](u&Ci((w,dhf)))
                        & sublabel("postCut A()&W(w0)") & debug("postCut A()&W(w0)")
                        & postCut(And(a,w0))(1) & onBranch(
                        (BranchLabels.cutShowLbl, sublabel("generalize post A()&W(w0)")
                          & hide(-3) & hide(And(w0,And(u0,i0)))(-2) & sublabel("chasing") & chase(1)
                          & allR(1) // equivalent:  HilbertCalculus.vacuousAll(1)
                          & sublabel("gen by arith") & debug("gen by arith")
                          & andR(1) & (
                          andR(1) & (
                            closeId
                            ,
                            done // QE
                            )
                          ,
                          andR(1) & (
                            closeId
                            ,
                            done //QE
                            )
                          )
                          ), // generalize post A()&W(w0)

                        (BranchLabels.cutUseLbl, sublabel("generalized A()&W(w0)->post")
                          & HilbertCalculus.testb(1, 1::1::Nil)
                          & debug("do use dist equiv impl")
                          & assertE(And(a,w0), "do use dist equiv form")(1, 1::0::Nil)
                          & assertE(e0, "do use dist equiv form")(1, 1::1::0::Nil)
                          & assertE("dhf:=*;{w:=-1;++w:=1;}".asProgram, "do use dist equiv form")(1, 0::Nil)
                          & assertE("ao:=*;".asProgram, "do use dist equiv form")(1, 1::1::1::0::Nil)
                          // [dhf:=*;{w:=-1;++w:=1;}]__(A()&W(w)->Ce(w,dhf) -> [ao:=*;][{r'=-rv,dhd'=ao,h'=-dhd&w*dhd>=w*dhf|w*ao>=a}](u&Ci))__
                          //@todo why will this guy keep around an extra premise??
                          // __(A()&W(w_0) -> Ce(w_0,dhf_0) -> q())__  <->  (A()&W(w_0) -> Ci(w_0,dhf_0) -> q())
                          & (if(distEquivImpl.isProved) useAt(distEquivImpl, PosInExpr(0::Nil))(1, 1::Nil)
                          else useAt(distEquivImpl.conclusion.succ.head, PosInExpr(0::Nil))(1, 1::Nil))
                          & sublabel("dist equiv impl")
                          & debug("used dist equiv impl")
                          & assertE(And(a,w0), "used dist equiv form")(1, 1::0::Nil)
                          & assertE(i0, "used dist equiv form")(1, 1::1::0::Nil)
                          & assertE("dhf:=*;{w:=-1;++w:=1;}".asProgram, "used dist equiv form")(1, 0::Nil)
                          & assertE("ao:=*;".asProgram, "used dist equiv form")(1, 1::1::1::0::Nil)
                          //                      & (if (distEquivImpl.isProved) {
                          //                      assertE("dhf_0:=*;{w_0:=-1;++w_0:=1;}".asProgram, "used dist equiv form")(1, 0 :: Nil) &
                          //                        assertE ("ao:=*;".asProgram, "used dist equiv form")(1, 1::1::1::0::Nil)
                          //                    } else {
                          //                    //  println("WARN: unproved distEquivImpl, so proof goals will remain around");
                          //                      skip
                          //                    })
                          // repacking
                          & useAt("[?] test", PosInExpr(1::Nil))(1, 1::1::Nil)
                          & debug("repacked test")
                          // drop a&w implication from postcondition again
                          //& useAt("K modal modus ponens", PosInExpr(0::Nil))(1) & implyR(1) & hide(-4)
                          & sublabel("[] post weaken")
                          & debug("do [] post weaken")
                          & assertE(And(a,w0), "post weaken form")(1, 1::0::Nil)
                          & assertE(Test(i0), "post weaken form")(1, 1::1::0::Nil)
                          & useAt("[] post weaken", PosInExpr(1::Nil))(1) //& useAt("[] post weaken")(1, /*Nil*/1::1::1::Nil)
                          & debug("did [] post weaken")
                          & close(-3, 1)
                          // successfully closes
                          ) // generalized A()&W(w0)->post
                      )  // postCut(And(a,w0))
                      )  // andR within show patch
                      )  // show patch
                    ,

                    (BranchLabels.cutUseLbl, sublabel("use patch") & debug("use patch")
                      // repacking
                      & useAt("[;] compose", PosInExpr(1::Nil))(SuccPosition(0, 1::1::Nil)) & useAt("[;] compose", PosInExpr(1::Nil))(SuccPosition(0, 1::Nil))
                      //& useAt("[;] compose", PosInExpr(0::Nil))(SuccPosition(0, 1::Nil))// ungather
                      // repack
                      & useAt("[++] choice", PosInExpr(1::Nil))(1) & useAt("[;] compose", PosInExpr(1::Nil))(1) & useAt("[;] compose", PosInExpr(1::Nil))(1)
                      & label("use patch") & debug("used patch")
                      // by unrolling implicit once
                      //@todo rename acasximplicit to w_0 names or vice versa ....
                      & cut(acasximplicit.asInstanceOf[Imply].right) & onBranch(
                      (BranchLabels.cutShowLbl,
                        sublabel("show implicit applicable") &
                          hide(1) &
                          cut(acasximplicit) & onBranch(
                          (BranchLabels.cutShowLbl, cohide(2) & sublabel("lookup lemma") & label("") & by(acasximplicitP)),
                          (BranchLabels.cutUseLbl,
                            sublabel("show lemma assumptions") & label("") & debug("show lemma assumptions") &
                              implyL(-3) & (
                              hide(1) &
                                label("step 1") &
                                // prove A()&(W(w)&Ci(w,dhf))
                                andR(1) & (
                                label("A id") & close(-1,1)
                                ,
                                // split W(w)&u&Ci finally
                                label("step W(w)&Ci") & debug("step W(w)&Ci") &
                                  andL(-2) & andL(-3) &
                                  andR(1) & (
                                  label("W(w) id") & closeId // (-2,1)
                                  ,
                                  label("Ci id") & closeId //(-4,1)
                                  /*andR(1) & (
                                    label("arithmetic")
                                    ,
                                    label("Ci id") & closeId //(-4,1)
                                    )
                                    */
                                  )
                                )
                              ,
                              label("looked up") & closeId)
                            )
                        )
                        ),  // show implicit applicable

                      (BranchLabels.cutUseLbl, sublabel("by implicit") & useAt("[*] approx")(-3) & close(-3,1))
                    )
                      )  // use patch
                  )  // cutAt(i0)
                  )  // u&Ce invariant
                )
                ),  // W(w)&Ci step

              (BranchLabels.indUseCaseLbl, sublabel("final use") & debug("final use") & andL(-1) & andL(-2) & andL(-3)
                & implyR(1) & implyR(1)
                & andR(1)
                & closeId)
            ) // ind(And(a,And(w,And(u, i))))
              )
          ) // cutL(i)(-3)
            )
        )
          )
      ) // postCut(a)
    )

    proof
  }

    /*  "abs_test0" should "be provable" in {
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
*/

  "min and max" should "be parseable" in {
    "min(0, x) <= max(x, 0)".asFormula shouldBe
      LessEqual(
        FuncOf(Function("min", None, Tuple(Real, Real), Real), Pair(Number(0), Variable("x"))),
        FuncOf(Function("max", None, Tuple(Real, Real), Real), Pair(Variable("x"), Number(0)))
      )
  }

  /*
  "true at beginning" should "be provable" in {
    def cutEZ(c:Formula, t:Tactic) = cut(c) & onBranch(
      (cutShowLbl, t | debugT("Cut didn't close") & Tactics.stopT)
    )
    val tactic = debugT("") & cutEZ("!(x>=0) | x>=0".asFormula, ls(cohide, "!(x>=0) | x>=0") & QE) &
      la(orL, "!(x>=0) | x>=0") && (ls(DI), ls(diffSolution(None)) & QE)
    // could be done with DI only if it wasn't for a DI bug (faster: 11 seconds vs. 18 seconds here)
    val s2 = new RootNode(sequent(Nil, "x=y".asFormula :: Nil, "[{x'=2 & (x>=0)}](y>=0)".asFormula :: Nil))
    helper.runTactic(tactic, s2) shouldBe 'closed
  }

  "Bug in DI" should "be provable" in {
    val tactic = ls(DI) & debugT("DW")
    val s2 = new RootNode(sequent(Nil, "x=y".asFormula :: Nil, "[{x'=2 & (x>=0)}](y>=0)".asFormula :: Nil))
    // closes fine if we add y'=0 explicitly
    helper.runTactic(tactic, s2) shouldBe 'closed
  }*/
}
