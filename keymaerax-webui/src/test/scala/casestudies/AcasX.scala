/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package casestudies

import java.io.File

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.ODETactics._
import edu.cmu.cs.ls.keymaerax.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaerax.tactics.FOQuantifierTacticsImpl.{instantiateT,skolemizeT,instantiateExistentialQuanT}
//import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl.onBranch
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.{debugT, arithmeticT, ImplyRightT, AndLeftT, hideT, AndRightT,
  ImplyLeftT, AxiomCloseT, OrRightT, OrLeftT, cutT, locate, NotRightT, NotLeftT}
import edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.tactics.ArithmeticTacticsImpl.{AbsAxiomT,AbsT,MinMaxAxiomT,MinMaxT,EqualReflexiveT}
import edu.cmu.cs.ls.keymaerax.tactics.EqualityRewritingImpl.{abbrv,eqLeft}
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.{ApplyRule, Tactic, PositionTactic}
import edu.cmu.cs.ls.keymaerax.tactics.PropositionalTacticsImpl.{Propositional,NonBranchingPropositionalT,cohideT}
import edu.cmu.cs.ls.keymaerax.tactics.HybridProgramTacticsImpl._
//import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import edu.cmu.cs.ls.keymaerax.tools.{ToolEvidence, Mathematica, KeYmaera}
import testHelper.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}

import testHelper.ParserFactory._
import testHelper.SequentFactory._

import scala.collection.immutable
import scala.collection.immutable.Map

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

  "ACAS X safe implicit" should "be provable" in {
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

  "ACAS X safe implicit with lemma" should "be provable" in {
    // one goal left corresponding to ODESolve issue, with 7982464f7daa4afb29295d19528830f2eff56523, Stefan, Tue Sep 8 17:41:17 2015 +0200
    // 780 seconds on robin (about 13 min)

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

    val absmax2 = (ls(AbsT, "", Some("abs(r_3-ro_0)".asTerm)) | dT("abs(r_3-ro_0) not present")) &
      ( abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxI"))) &
        la(MinMaxT, "", Some("max((0,w*(dhf-dhd)))".asTerm)) | dT("max(0,w*(dhf-dhd)) not present")) &
      ( abbrv("max((0,w*(dhf-dhd_3)))".asTerm, Some(Variable("maxF"))) &
        la(MinMaxT, "", Some("max((0,w*(dhf-dhd_3)))".asTerm)) | dT("max(0,w*(dhf-dhd_3)) not present"))

    def cutEZ(c:Formula, t:Tactic) = cut(c) & onBranch(
      (cutShowLbl, t | dT("Cut didn't close") & Tactics.stopT)
    )

    val crushabsmax = absmax & crushor

    /*** Invariants etc. ***/
    val invariant = ("( (w=-1 | w=1) & " +
      "      (" +
      "\\forall t \\forall ro \\forall ho" +
      "((0 <= t & t < max(0, w * (dhf - dhd)) / a &" +
      "  ro = rv * t & ho = (w * a) / 2 * t^2 + dhd * t) |" +
      "  (t >= max(0, w * (dhf - dhd)) / a &" +
      "    ro = rv * t & ho = dhf * t - w * max(0, w * (dhf - dhd))^2 / (2*a))" +
      "-> (abs(r - ro) > rp | w * h < w * ho - hp))" +
      "      )) & ( hp>0&rp>0&rv>=0&a>0 )").asFormula

    val initDomain = "w*dhd>=w*dhf|w*ao>=a"

    /*** Lower bound safe lemma and its tactic ***/

    val safeLemmaFormula =
      "max0=max((0,w*(dhf-dhd))) & " +
      "(w*dhd>=w*dhf|w*ao>=a) & " +
      "h_3=1/2*(2*h+-2*dhd*kxtime_5+-1*ao*kxtime_5^2) & " +
      "(w=-1|w=1) & " +
      "(\\forall t \\forall ro \\forall ho (0<=t&t < max0/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=max0/a&ro=rv*t&ho=dhf*t-w*max0^2/(2*a)->abs(r-ro)>rp|w*h < w*ho-hp)) & " +
      "hp>0 & " +
      "dhd_3=dhd+ao*kxtime_5 & " +
      "rp>0 & " +
      "r_3=r+-1*kxtime_5*rv & " +
      "rv>=0 & " +
      "a>0 & " +
      "(w*dhd_3>=w*dhf|w*ao>=a) & " +
      "kxtime_5>=0" +
      "->" +
      "((w=-1|w=1)&\\forall t \\forall ro \\forall ho (0<=t&t < max((0,w*(dhf-dhd_3)))/a&ro=rv*t&ho=w*a/2*t^2+dhd_3*t|t>=max((0,w*(dhf-dhd_3)))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-dhd_3)))^2/(2*a)->abs(r_3-ro)>rp|w*h_3 < w*ho-hp))&hp>0&rp>0&rv>=0&a>0"
    val safeLemmaSeq = sequent(Nil, Nil, safeLemmaFormula.asFormula :: Nil)
    val safeLemmaTac = dT("lemma") & ls(implyR) & (la(andL)*) && ls(andR) && (
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

    val safeLemma = helper.runTactic(safeLemmaTac, new RootNode(safeLemmaSeq))
    safeLemma shouldBe 'closed

    /*** Lemma machinery, TODO clean up ***/
    // create evidence (traces input into tool and output from tool)
    val evidence = new ToolEvidence(immutable.Map("input" -> safeLemmaFormula, "output" -> "true")) :: Nil
    // add lemma into DB, which creates an ID for it. use the ID to apply the lemma
    val lemmaDB = LemmaDBFactory.lemmaDB
    val lemmaID = lemmaDB.add(Lemma(safeLemma.provableWitness, evidence))
    val applyLemma = new ApplyRule(LookupLemma(lemmaDB, lemmaID)) {
      override def applicable(node: ProofNode): Boolean = node.sequent.sameSequentAs(safeLemmaSeq)
    }

    /*** Main safe theorem and its tactic ***/
    val safeSeq = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/acasx/nodelay_max.key"))
    val safeTac = ls(implyR) & la(andL) & ls(wipeContextInductionT(Some(invariant))) & onBranch(
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
          /* Would like to replace cohide by: ls(cohide, "-1=-1|-1=1") OR ls(cohide, "1=-1|1=1") (BUT different branches)*/
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
          dT("Before diff. solution") & ls(diffSolution(None, la(hide, "max0=max((0,w*(dhf-dhd)))"))) &
            dT("Diff. Solution") & ls(implyR) & (la(andL)*) &
            la(TacticLibrary.eqLeft(exhaustive=true), "kxtime_1=0") & la(hideT, "kxtime_1=0") &
            la(TacticLibrary.eqLeft(exhaustive=true), "kxtime_4()=0") & la(hideT, "kxtime_4()=0") &
            la(TacticLibrary.eqLeft(exhaustive=true), "r_2()=r") & la(hideT, "r_2()=r") &
            la(TacticLibrary.eqLeft(exhaustive=true), "dhd_2()=dhd") & la(hideT, "dhd_2()=dhd") &
            la(TacticLibrary.eqLeft(exhaustive=true), "h_2()=h") & la(hideT, "h_2()=h") &
            dT("bla") & cut(safeLemmaFormula.asFormula) & onBranch(
            (cutShowLbl, ls(cohideT, safeLemmaFormula) & dT("apply Lemma") & applyLemma),
            (cutUseLbl, dT("use lemma") & QE)
          )
          ) /* end orL on cutEZ */
          ) /* End cutUseLbl "Generalization strong enough" */
      )) /* End indStepLbl */
    )

    val safeTheorem = helper.runTactic(safeTac, new RootNode(safeSeq))
    safeTheorem shouldBe 'closed
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
      ") & (hp > 0 & rp > 0 & rv >= 0 & a > 0 & aM > 0))"
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
        "hp>0 & rp>0 & rv>=0 & a>0 &" +
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
        "hp>0 & rp>0 & rv>=0 & aM>0 &" +
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
        & (la(andL)*) & (ls(andR)*) & (QE | dT("Should be closed") & Tactics.stopT)),
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
    val safeSeq = parseToSequent(getClass.getResourceAsStream(
      "/examples/casestudies/acasx/nodelay_2sided.key"))
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
            ls(substitutionBoxAssignT) & ls(boxTestT) & dT("1.2.2") &
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

/*******************/
/**** Playground ***/
/*******************/
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
