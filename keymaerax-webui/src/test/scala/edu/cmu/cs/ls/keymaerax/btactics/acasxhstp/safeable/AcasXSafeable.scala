/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics.acasxhstp.safeable

import edu.cmu.cs.ls.keymaerax.btactics.acasxhstp.safeable.SharedTactics._
import edu.cmu.cs.ls.keymaerax.btactics.BelleLabels._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.arithmetic.speculative.ArithmeticSpeculativeSimplification
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.SlowTest

import scala.language.postfixOps

/**
 * Proves Sect. 5.3: Safe Region for Subsequent Advisories - Safeable Regions
 *
 * Theorem 5: Correctness of bounded-time implicit safe regions
 * @todo formalize Lemma 5: Simplification of cases 15 and 16
 * @todo formalize Lemma 6: Equivalence of implicit and explicit safeable regions

 * @see Jean-Baptiste Jeannin et al.: A Formally Verified Hybrid System for Safe Advisories in the Next-Generation
 *      Airborne Collision Avoidance System, STTT.
 *
 * @author Khalil Ghorbal
 * @author Jean-Baptiste Jeannin
 * @author Yanni A. Kouskoulas
 * @author Stefan Mitsch
 * @author Andre Platzer
 */
@SlowTest
class AcasXSafeable extends AcasXBase {

  private def eqHide(f: String) = exhaustiveEqL2R('L, f.asFormula)

  "ACAS X safeable" should "prove Theorem 5: lemma safe implicit" in withMathematica { tool =>
    val initDomain = "w*dhd>=w*dhf|w*ao>=a".asFormula

    val safeLemmaFormula =
      "maxI=max((0,w*(dhf-dhd))) &" +
      "t_>=0 &" +
      "(w*dhd>=w*dhf|w*ao>=a) &" +
      "(w=-1|w=1) &" +
      "\\forall t \\forall ro \\forall ho ((t<=tl-to|tl < 0)&(0<=t&t < maxI/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxI/a&ro=rv*t&ho=dhf*t-w*maxI^2/(2*a))->abs(r-ro)>rp|w*h < w*ho-hp) &"+
      "hp>0 & rp>=0 & rv>=0 & a>0 &" +
      "(w*dhd_3>=w*dhf|w*ao>=a) &" +
      "to_3=t_+to &" +
      "dhd_3=ao*t_+dhd &" +
      "r_3=(-rv)*t_+r &" +
      "h_3=-(ao/2*t_^2+dhd*t_)+h" +
      "->" +
      "\\forall t \\forall ro \\forall ho ((t<=tl-to_3|tl < 0)&(0<=t&t < max((0,w*(dhf-dhd_3)))/a&ro=rv*t&ho=w*a/2*t^2+dhd_3*t|t>=max((0,w*(dhf-dhd_3)))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-dhd_3)))^2/(2*a))->abs(r_3-ro)>rp|w*h_3 < w*ho-hp)"

    val safeLemmaTac = dT("lemma") & implyR('R) & (andL('L)*) &
      dT("Before skolem") & (allR('R)*) & dT("After skolem") &
      implyR('R) & orR('R) &
      allL("t".asVariable, "(t_+t)".asTerm)('L) &
      allL("ro".asVariable, "rv*(t_+t)".asTerm)('L) &
      dT("Before CUT") &
      Idioms.cases(
          //@todo try plain QE or atomicQE
          hideL('L, "\\forall ho (((t_+t)<=tl-to|tl < 0)&(0<=(t_+t)&(t_+t) < maxI/a&rv*(t_+t)=rv*(t_+t)&ho=w*a/2*(t_+t)^2+dhd*(t_+t)|(t_+t)>=maxI/a&rv*(t_+t)=rv*(t_+t)&ho=dhf*(t_+t)-w*maxI^2/(2*a))->abs(r-rv*(t_+t))>rp|w*h < w*ho-hp)".asFormula) &
          hideR('R, "abs(r_3-ro)>rp".asFormula) & hideR('R, "w*h_3<w*ho-hp".asFormula) &
          dT("Show Cut 2") & orR('R) & andL('L) & hideL('L, "t<=tl-to_3|tl < 0".asFormula) &
          orL('L, "0<=t&t<max((0,w*(dhf-dhd_3)))/a&ro=rv*t&ho=w*a/2*t^2+dhd_3*t|t>=max((0,w*(dhf-dhd_3)))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-dhd_3)))^2/(2*a)".asFormula) &
          (andL('L)*) & atomicQE(onAll(andR)*, dT("End CutShowLbl"))
      )(
        (Case("0<=(t_+t)&(t_+t)<maxI/a".asFormula),
          dT("Goal 110") & hideL('L, initDomain) & // TODO remove this hide
            allL("ho".asVariable, "w*a/2*(t_+t)^2 + dhd*(t_+t)".asTerm)('L) &
            dT("instantiate ho 1 Lo") &
            implyL('L, "(t_+t<=tl-to|tl < 0)&(0<=t_+t&t_+t < maxI/a&w*a/2*(t_+t)^2+dhd*(t_+t)=w*a/2*(t_+t)^2+dhd*(t_+t)|t_+t>=maxI/a&w*a/2*(t_+t)^2+dhd*(t_+t)=dhf*(t_+t)-w*maxI^2/(2*a))->abs(r-rv*(t_+t))>rp|w*h < w*(w*a/2*(t_+t)^2+dhd*(t_+t))-hp".asFormula) & Idioms.<(
              dT("left of -> 1 Lo") & andL('L) &
              hideR('R, "abs(r_3-ro)>rp".asFormula) & hideR('R, "w*h_3<w*ho-hp".asFormula) &
              hideL('L, "maxI=max((0,w*(dhf-dhd)))".asFormula) &
              andR('R) & Idioms.<(
                orR('R) & dT("tl 1") & QE,
                orR('R) &
                hideR('R, "t_+t>=maxI/a&w*a/2*(t_+t)^2+dhd*(t_+t)=dhf*(t_+t)-w*maxI^2/(2*a)".asFormula) &
                dT("End L1") & QE
            ),
            dT("right of -> 1 Lo") &
              andL('L, "(t<=tl-to_3|tl < 0)&(0<=t&t < max((0,w*(dhf-dhd_3)))/a&ro=rv*t&ho=w*a/2*t^2+dhd_3*t|t>=max((0,w*(dhf-dhd_3)))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-dhd_3)))^2/(2*a))".asFormula) &
              hideL('L, "t<=tl-to_3|tl < 0".asFormula) &
              orL('L, "0<=t&t < max((0,w*(dhf-dhd_3)))/a&ro=rv*t&ho=w*a/2*t^2+dhd_3*t|t>=max((0,w*(dhf-dhd_3)))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-dhd_3)))^2/(2*a)".asFormula)
              & onAll(
              dT("1-Lo") &
                orL('L,"abs(r-rv*(t_+t))>rp|w*h < w*(w*a/2*(t_+t)^2+dhd*(t_+t))-hp".asFormula)
                & Idioms.<(QE, hideR('R, "abs(r_3-ro)>rp".asFormula) & atomicQE(ArithmeticLibrary.varEliminationLeft("w".asVariable), dT("End 1L")))
            )
          )
        ),
        (Case("(t_+t)>=maxI/a".asFormula),
          dT("final time in straight Lo") &
            allL("ho".asVariable, "dhf*(t_+t) - w*maxI^2/(2*a)".asTerm)('L) &
            dT("instantiate ho 2 Lo") &
            implyL('L, "(t_+t<=tl-to|tl < 0)&dhf*(t_+t)-w*maxI^2/(2*a)=dhf*(t_+t)-w*maxI^2/(2*a)->abs(r-rv*(t_+t))>rp|w*h < w*(dhf*(t_+t)-w*maxI^2/(2*a))-hp".asFormula)
            & Idioms.<(
              dT("left of -> 2 Lo") & andL('L) &
              hideR('R, "abs(r_3-ro)>rp".asFormula) & hideR('R, "w*h_3<w*ho-hp".asFormula) &
              hideL('L, "maxI=max((0,w*(dhf-dhd)))".asFormula) & atomicQE(onAll(andR('R))*, dT("TL 2"))
            ,
            dT("right of -> 2 Lo") &
              andL('L, "(t<=tl-to_3|tl < 0)&(0<=t&t < max((0,w*(dhf-dhd_3)))/a&ro=rv*t&ho=w*a/2*t^2+dhd_3*t|t>=max((0,w*(dhf-dhd_3)))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-dhd_3)))^2/(2*a))".asFormula) &
              hideL('L, "t<=tl-to_3|tl < 0".asFormula) &
              orL('L, "0<=t&t < max((0,w*(dhf-dhd_3)))/a&ro=rv*t&ho=w*a/2*t^2+dhd_3*t|t>=max((0,w*(dhf-dhd_3)))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-dhd_3)))^2/(2*a)".asFormula)
              & onAll(
                dT("2-Lo") &
                orL('L, "abs(r-rv*(t_+t))>rp|w*h<w*(dhf*(t_+t)-w*maxI^2/(2*a))-hp".asFormula)
                & Idioms.<(QE, hideR('R, "abs(r_3-ro)>rp".asFormula) & atomicQE(ArithmeticLibrary.varEliminationLeft("w".asVariable), dT("End L2")))
            )
          )
        )
      )

    val safeLemma = proveBy(safeLemmaFormula.asFormula, safeLemmaTac)
    safeLemma shouldBe 'proved
    storeLemma(safeLemma, Some("safeable_safe_implicit"))
  }

  it should "prove Theorem 5: lemma safe upper implicit" in withMathematica { tool =>
    val safeUpLemmaFormula =
      "maxUpI=max((0,w*(dhfUp-dhd))) &"+
      "t_>=0 & "+
      "(w*dhd<=w*dhfUp&w*ao<=aM|w*ao<=0) &" +
      "(w=-1|w=1) &" +
      "(\\forall t \\forall ro \\forall ho ((t<=tl-to|tl < 0)&(0<=t&t < maxUpI/aM&ro=rv*t&ho=w*aM/2*t^2+dhd*t|t>=maxUpI/aM&ro=rv*t&ho=(dhd+w*maxUpI)*t-w*maxUpI^2/(2*aM))->abs(r-ro)>rp|w*h>w*ho+hp)) &" +
      "hp>0 & rp>=0 & rv>=0 & aM>0 &" +
      "(w*dhd_3<=w*dhfUp&w*ao<=aM|w*ao<=0) &" +
      "to_3=t_+to &" +
      "r_3=(-rv)*t_+r &" +
      "dhd_3=ao*t_+dhd &" +
      "h_3=-(ao/2*t_^2+dhd*t_)+h" +
      "->" +
      "\\forall t \\forall ro \\forall ho ((t<=tl-to_3|tl < 0)&(0<=t&t < max((0,w*(dhfUp-dhd_3)))/aM&ro=rv*t&ho=w*aM/2*t^2+dhd_3*t|t>=max((0,w*(dhfUp-dhd_3)))/aM&ro=rv*t&ho=(dhd_3+w*max((0,w*(dhfUp-dhd_3))))*t-w*max((0,w*(dhfUp-dhd_3)))^2/(2*aM))->abs(r_3-ro)>rp|w*h_3>w*ho+hp)"

    val safeUpLemmaTac = dT("lemma Up") & implyR('R) & (andL('L)*) &
      dT("Before skolem Up") & (allR('R)*) & dT("After skolem Up") &
      implyR('R) & orR('R) &
      allL(Variable("t"), "t_+t".asTerm)('L) &
      allL(Variable("ro"), "rv*(t_+t)".asTerm)('L) &
      dT("Before CUT") &
      cut("0<=(t_+t)&(t_+t)<maxUpI/aM|(t_+t)>=maxUpI/aM".asFormula) & Idioms.<(
      (cutShow, dT("Show Cut") & hideL('L, "maxUpI=max((0,w*(dhfUp-dhd)))".asFormula) &
        hideL('L, "\\forall ho ((t_+t<=tl-to|tl < 0)&(0<=t_+t&t_+t < maxUpI/aM&rv*(t_+t)=rv*(t_+t)&ho=w*aM/2*(t_+t)^2+dhd*(t_+t)|t_+t>=maxUpI/aM&rv*(t_+t)=rv*(t_+t)&ho=(dhd+w*maxUpI)*(t_+t)-w*maxUpI^2/(2*aM))->abs(r-rv*(t_+t))>rp|w*h>w*ho+hp)".asFormula)
        & hideR('R, "abs(r_3-ro)>rp".asFormula) & hideR('R, "w*h_3>w*ho+hp".asFormula) &
        dT("Show Cut 2") & orR('R) & andL('L) &
        hideL('L, "t<=tl-to_3|tl < 0".asFormula) &
        orL('L, "0<=t&t < max((0,w*(dhfUp-dhd_3)))/aM&ro=rv*t&ho=w*aM/2*t^2+dhd_3*t|t>=max((0,w*(dhfUp-dhd_3)))/aM&ro=rv*t&ho=(dhd_3+w*max((0,w*(dhfUp-dhd_3))))*t-w*max((0,w*(dhfUp-dhd_3)))^2/(2*aM)".asFormula)
        & atomicQE(onAll(andR('R))*, dT("End CutShowLbl"))),
      (cutUse, dT("Use Cut") &
        orL('L, "0<=(t_+t)&(t_+t)<maxUpI/aM|(t_+t)>=maxUpI/aM".asFormula) & Idioms.<(
        dT("final time in parabola") & // add hide initDomain?
          allL(Variable("ho"), "w*aM/2*(t_+t)^2+dhd*(t_+t)".asTerm)('L) &
          dT("instantiate ho 1 Up") &
          implyL('L, "(t_+t<=tl-to|tl < 0)&(0<=t_+t&t_+t < maxUpI/aM&rv*(t_+t)=rv*(t_+t)&w*aM/2*(t_+t)^2+dhd*(t_+t)=w*aM/2*(t_+t)^2+dhd*(t_+t)|t_+t>=maxUpI/aM&rv*(t_+t)=rv*(t_+t)&w*aM/2*(t_+t)^2+dhd*(t_+t)=(dhd+w*maxUpI)*(t_+t)-w*maxUpI^2/(2*aM))->abs(r-rv*(t_+t))>rp|w*h>w*(w*aM/2*(t_+t)^2+dhd*(t_+t))+hp".asFormula)
          & Idioms.<(
          dT("left of -> 1 Up") &
            hideR('R, "abs(r_3-ro)>rp".asFormula) & hideR('R, "w*h_3>w*ho+hp".asFormula) &
            hideL('L, "maxUpI=max((0,w*(dhfUp-dhd)))".asFormula) &
            andR('R) & Idioms.<(
            orR('R) & dT("tl 1") & QE,
            orR('R) &
              hideR('R, "(t_+t)>=maxUpI/aM&rv*(t_+t)=rv*(t_+t)&w*aM/2*(t_+t)^2+dhd*(t_+t)=(dhd+w*maxUpI)*(t_+t)-w*maxUpI^2/(2*aM)".asFormula) &
              dT("End L1") & QE
            ),
          dT("right of -> 1 Up") &
            andL('L, "(t<=tl-to_3|tl < 0)&(0<=t&t < max((0,w*(dhfUp-dhd_3)))/aM&ro=rv*t&ho=w*aM/2*t^2+dhd_3*t|t>=max((0,w*(dhfUp-dhd_3)))/aM&ro=rv*t&ho=(dhd_3+w*max((0,w*(dhfUp-dhd_3))))*t-w*max((0,w*(dhfUp-dhd_3)))^2/(2*aM))".asFormula) &
            hideL('L, "t<=tl-to_3|tl < 0".asFormula) &
            orL('L, "0<=t&t < max((0,w*(dhfUp-dhd_3)))/aM&ro=rv*t&ho=w*aM/2*t^2+dhd_3*t|t>=max((0,w*(dhfUp-dhd_3)))/aM&ro=rv*t&ho=(dhd_3+w*max((0,w*(dhfUp-dhd_3))))*t-w*max((0,w*(dhfUp-dhd_3)))^2/(2*aM)".asFormula)
            & onAll(
              dT("1-Up") &
              orL('L, "abs(r-rv*(t_+t))>rp|w*h>w*(w*aM/2*(t_+t)^2+dhd*(t_+t))+hp".asFormula) & Idioms.<(
                QE
                ,
                hideR('R, "abs(r_3-ro)>rp".asFormula) &
                atomicQE(ArithmeticLibrary.varEliminationLeft("w".asVariable), dT("crushw"))
              )
            )
          )
          ,
          dT("final time in straight Up") &
          allL(Variable("ho"), "(dhd+w*maxUpI)*(t_+t)-w*maxUpI^2/(2*aM)".asTerm)('L) &
          dT("instantiate ho 2 Lo") &
          implyL('L, "(t_+t<=tl-to|tl < 0)&(0<=t_+t&t_+t < maxUpI/aM&rv*(t_+t)=rv*(t_+t)&(dhd+w*maxUpI)*(t_+t)-w*maxUpI^2/(2*aM)=w*aM/2*(t_+t)^2+dhd*(t_+t)|t_+t>=maxUpI/aM&rv*(t_+t)=rv*(t_+t)&(dhd+w*maxUpI)*(t_+t)-w*maxUpI^2/(2*aM)=(dhd+w*maxUpI)*(t_+t)-w*maxUpI^2/(2*aM))->abs(r-rv*(t_+t))>rp|w*h>w*((dhd+w*maxUpI)*(t_+t)-w*maxUpI^2/(2*aM))+hp".asFormula)
          & Idioms.<(
            dT("left of -> 2 Up") &
            hideR('R, "abs(r_3-ro)>rp".asFormula) & hideR('R, "w*h_3>w*ho+hp".asFormula) &
            hideL('L, "maxUpI=max((0,w*(dhfUp-dhd)))".asFormula) &
            andR('R) & Idioms.<(
              dT("tl 2b") & QE
              ,
              orR('R) &
              hideR('R, "0<=(t_+t)&(t_+t) < maxUpI/aM&rv*(t_+t)=rv*(t_+t)&(dhd+w*maxUpI)*(t_+t)-w*maxUpI^2/(2*aM)=w*aM/2*(t_+t)^2+dhd*(t_+t)".asFormula) &
              QE
            )
            ,
          dT("right of -> 2 Up") &
            andL('L, "(t<=tl-to_3|tl < 0)&(0<=t&t < max((0,w*(dhfUp-dhd_3)))/aM&ro=rv*t&ho=w*aM/2*t^2+dhd_3*t|t>=max((0,w*(dhfUp-dhd_3)))/aM&ro=rv*t&ho=(dhd_3+w*max((0,w*(dhfUp-dhd_3))))*t-w*max((0,w*(dhfUp-dhd_3)))^2/(2*aM))".asFormula) &
            hideL('L, "t<=tl-to_3|tl < 0".asFormula) &
            orL('L, "0<=t&t < max((0,w*(dhfUp-dhd_3)))/aM&ro=rv*t&ho=w*aM/2*t^2+dhd_3*t|t>=max((0,w*(dhfUp-dhd_3)))/aM&ro=rv*t&ho=(dhd_3+w*max((0,w*(dhfUp-dhd_3))))*t-w*max((0,w*(dhfUp-dhd_3)))^2/(2*aM)".asFormula)
            & onAll(
              dT("2-Up") &
              orL('L, "abs(r-rv*(t_+t))>rp|w*h>w*((dhd+w*maxUpI)*(t_+t)-w*maxUpI^2/(2*aM))+hp".asFormula) & Idioms.<(
                QE
                ,
                hideR('R, "abs(r_3-ro)>rp".asFormula) &
                atomicQE(ArithmeticLibrary.varEliminationLeft("w".asVariable), dT("crushw"))
              )
            )
          )
        )
      )
    )

    val safeUpLemma = proveBy(safeUpLemmaFormula.asFormula , safeUpLemmaTac)
    safeUpLemma shouldBe 'proved
    storeLemma(safeUpLemma, Some("safeable_safe_upimplicit"))
  }

  it should "prove Theorem 5: propagate Lo" in withMathematica { tool =>
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
    val cut_0 = "0 <= t & t < max(0, w*(vt0-v0)) / a0 | t >= max(0, w*(vt0-v0)) / a0"

    val propagateLoTac = (allR('R)*) & implyR('R) & (andL('L)*) &
      (allR('R)*) & implyR('R) & andL('L) &
      allL("t".asVariable, "t".asTerm)('L) & allL("ro".asVariable, "rv*t".asTerm)('L) &
      cutEZ(cut_0.asFormula, dT("cut_0") &
        hideL('L, "\\forall ho ((t <= tl-to0|tl < 0)&(0<=t&t < max((0,w*(vt0-v0)))/a0&rv*t=rv*t&ho=w*a0/2*t^2+v0*t|t>=max((0,w*(vt0-v0)))/a0&rv*t=rv*t&ho=vt0*t-w*max((0,w*(vt0-v0)))^2/(2*a0))->abs(r-rv*t)>rp|w*h0 < w*ho-hp)".asFormula) &
        max('L, max_1.asTerm) & // duplicated to keep names straight
        hideR('R, "abs(r-ro)>rp|w*h1 < w*ho-hp".asFormula) & QE) &
      dT("before MinMax") &
      max('L, max_0.asTerm) &
      max('L, max_1.asTerm) &
      dT("after MinMax") &
      orL('L, "0<=t & t < max_0/a0 | t >= max_0/a0".asFormula) & Idioms.<(
      dT("para max0") & allL("ho".asVariable, "w*a0/2*t^2+v0*t".asTerm)('L) & implyL('L) & Idioms.<(
        andR('R) & Idioms.<(
          QE
          ,
          hideR('R, "abs(r-ro)>rp|w*h1 < w*ho-hp".asFormula) & QE)
          ,
          hideL('L, "t <= tl-to1|tl < 0".asFormula) & dT("post para") &
          orL('L, "0<=t&t < max_1/a1&ro=rv*t&ho=w*a1/2*t^2+v1*t|t>=max_1/a1&ro=rv*t&ho=vt1*t-w*max_1^2/(2*a1)".asFormula) & Idioms.<(
          (andL('L)*) & orR('R) &
            eqHide("ro=rv*t") & eqHide("ho=w*a1/2*t^2+v1*t") &
            orL('L, "abs(r-rv*t)>rp|w*h0 < w*(w*a0/2*t^2+v0*t)-hp".asFormula) & Idioms.<(
            closeId,
            dT("height") & hideR('R, "abs(r-rv*t)>rp".asFormula) & QE
            ),
          (andL('L)*) & orR('R) &
            eqHide("ro=rv*t") & eqHide("ho=vt1*t-w*max_1^2/(2*a1)") &
            orL('L, "abs(r-rv*t)>rp|w*h0 < w*(w*a0/2*t^2+v0*t)-hp".asFormula) & Idioms.<(
            closeId,
            dT("height") & hideR('R, "abs(r-rv*t)>rp".asFormula) & QE
            )
          )
        ),
      dT("line max0") & allL("ho".asVariable, "vt0*t-w*max_0^2/(2*a0)".asTerm)('L) & implyL('L) & Idioms.<(
        andR('R) & Idioms.<(
          QE
          ,
          hideR('R, "abs(r-ro)>rp|w*h1 < w*ho-hp".asFormula) & QE)
          ,
          hideL('L, "t <= tl-to1|tl < 0".asFormula) & dT("post line") &
          orL('L, "0<=t&t < max_1/a1&ro=rv*t&ho=w*a1/2*t^2+v1*t|t>=max_1/a1&ro=rv*t&ho=vt1*t-w*max_1^2/(2*a1)".asFormula) & Idioms.<(
          (andL('L)*) & orR('R) &
            eqHide("ro=rv*t") & eqHide("ho=w*a1/2*t^2+v1*t") &
            orL('L, "abs(r-rv*t)>rp|w*h0 < w*(vt0*t-w*max_0^2/(2*a0))-hp".asFormula) & Idioms.<(
            closeId,
            dT("height") & hideR('R, "abs(r-rv*t)>rp".asFormula) & QE
            ),
          (andL('L)*) & orR('R) &
            eqHide("ro=rv*t") & eqHide("ho=vt1*t-w*max_1^2/(2*a1)") &
            orL('L, "abs(r-rv*t)>rp|w*h0 < w*(vt0*t-w*max_0^2/(2*a0))-hp".asFormula) & Idioms.<(
            closeId,
            dT("height") & hideR('R, "abs(r-rv*t)>rp".asFormula) & QE
            )
          )
        )
      )

    val propagateLo = proveBy(propagateLoFormula.asFormula , propagateLoTac)
    propagateLo shouldBe 'proved
    storeLemma(propagateLo, Some("safeable_propagateLo"))
  }

  it should "prove Theorem 5: correctness of implicit safeable region" in withMathematica { tool =>
    // large lemma evidence, needs stack size -Xss256M

    /*** Invariants etc. ***/
    /* TODO make accelerations a parameter and changing throughout time
    * now it's the same all the time (presumably g/3) */
    def condImplLo(r:String, h:String, dhd:String,
                   w:String, dhf:String, tl:String) =
    s"""(
       # \\forall t \\forall ro \\forall ho
       #   ((t <= $tl-to | $tl<0) &
       #    ((0 <= t & t < max(0, ($w) * (($dhf) - ($dhd))) / a &
       #      ro = rv * t &
       #      ho = (($w) * a) / 2 * t^2 + ($dhd) * t) |
       #     (t >= max(0, ($w) * (($dhf) - ($dhd))) / a &
       #      ro = rv * t &
       #      ho = ($dhf) * t - ($w) * max(0, ($w) * (($dhf) - ($dhd)))^2 / (2*a)))
       #    -> (abs(($r) - ro) > rp | ($w) * ($h) < ($w) * ho - hp))
       # )
     """.stripMargin('#')

    def condImplUp(r:String, h:String, dhd:String,
                   w:String, dhfUp:String, tl:String) =
      s""" (
         # \\forall t \\forall ro \\forall ho
         # ((t <= $tl-to | $tl<0) &
         #  ((0 <= t & t < max(0, ($w) * (($dhfUp) - ($dhd))) / aM &
         #    ro = rv * t &
         #    ho = (($w) * aM) / 2 * t^2 + ($dhd) * t) |
         #   (t >= max(0, ($w) * (($dhfUp) - ($dhd))) / aM &
         #    ro = rv * t &
         #    ho = (($dhd) + ($w) * max(0, ($w) * (($dhfUp)-($dhd)))) * t
         #         - ($w) * max(0, ($w) * (($dhfUp) - ($dhd)))^2 / (2*aM)))
         # -> (abs(($r) - ro) > rp | ($w) * ($h) > ($w) * ho + hp))
         # )
       """.stripMargin('#')

    val tlmto = "(tl-to)"

    def condImplSafeableLo(r:String, h:String, dhd:String,
                           w:String, dhf:String, dhfExtr:String, tl:String) =
      s"""
       # (${condImplLo(r,h,dhd,w,dhf,tl)} & (
       # \\forall hNew \\forall dhdNew (
       # ((0 <= $tlmto & $tlmto < max(0, ($w) * (($dhf) - ($dhd))) / a &
       #   hNew=($w)*a/2*$tlmto^2 + ($dhd)*$tlmto &
       #   dhdNew=($w)*a*$tlmto + ($dhd)) |
       # ($tlmto >= max(0, ($w) * (($dhf) - ($dhd))) / a &
       #   hNew=($dhf)*$tlmto - ($w)*max(0, ($w)*(($dhf) - ($dhd)))^2/(2*a) &
       #   dhdNew=($dhf))) ->
       # ${condImplLo(s"($r)-rv*$tlmto", s"($h-hNew)", "dhdNew", s"($w)", dhfExtr, "-1")}
       # )))
     """.stripMargin('#')

    val condImplSafeableLoStr = condImplSafeableLo("r","h","dhd","w","dhf","dhfExtr","tl")
    //print(condImplSafeableLo("r","h","dhd","w","dhf","dhfExtr","tl"))
    //print(condImplSafeableLo("r","h","dhd","w","dhf","dhfExtr","tl").asFormula+"\n")

    def condImplSafeableUp(r:String, h:String, dhd:String,
                           w:String, dhfUp:String, dhfUpExtr:String, tl:String) =
      s""" ( ${condImplUp(r,h,dhd,w,dhfUp,tl)} & (
         #  \\forall hNew \\forall dhdNew (
         #    ((0 <= $tlmto & $tlmto < max(0, ($w) * (($dhfUp) - ($dhd))) / aM &
         #      hNew=($w)*aM/2*$tlmto^2 + ($dhd)*$tlmto &
         #      dhdNew=($w)*aM*$tlmto + ($dhd)) |
         #     ($tlmto >= max(0, ($w) * (($dhfUp) - ($dhd))) / aM &
         #      hNew=($dhd+($w)*max(0, ($w)*(($dhfUp) - ($dhd))))*$tlmto
         #           - ($w)*max(0, ($w)*(($dhfUp) - ($dhd)))^2/(2*aM) &
         #      dhdNew=($dhd+($w)*max(0, ($w)*(($dhfUp) - ($dhd)))))) ->
         #  ${condImplLo(s"($r)-rv*$tlmto", s"($h-hNew)", "dhdNew", s"-($w)", dhfUpExtr, "-1")}
         # )))
       """.stripMargin('#')

    val condImplSafeableUpStr = condImplSafeableUp("r","h","dhd","w","dhfUp", "dhfUpExtr", "tl")
    //print(condImplSafeableUp("r","h","dhd","w","dhf","dhfExtr","tl"))
    //print(condImplSafeableUp("r","h","dhd","w","dhf","dhfExtr","tl").asFormula)

    def condImplSafeable(r:String, h:String, dhd:String, w:String,
                         dhf:String, dhfExtr:String, dhfUp:String, dhfUpExtr:String, tl:String) =
      s"""( ${condImplSafeableLo(r,h,dhd,w,dhf,dhfExtr,tl)} |
         #  ${condImplSafeableUp(r,h,dhd,w,dhfUp,dhfUpExtr,tl)} )
       """.stripMargin('#')
    //print(condImplSafeable("r","h","dhd","w","dhf","dhfExtr","dhfUp", "dhfUpExtr", "tl"))
    //print(condImplSafeable("r","h","dhd","w","dhf","dhfExtr","dhfUp", "dhfUpExtr", "tl").asFormula+"\n")
    val condImplSafeableStr = condImplSafeable("r","h","dhd","w","dhf","dhfExtr","dhfUp", "dhfUpExtr", "tl")

    // tl>=0 because tl=-1 really means 2-sided safe, so this is inadapted
    val constants = "(hp > 0 & rp >= 0 & rv >= 0 & a > 0 & aM >= a & tl>=0)".asFormula

    val invariant = And(And("((w=-1 | w=1) & (to<=tl | tl<0))".asFormula, condImplSafeableStr.asFormula), constants)

    //print(invariantStr)
    //print(invariant)

    val evolutionDomain = ("((to<=tl | tl<0) &"+
      "(( w * dhd >= w * dhf  | w * ao >= a ) &" +
      " ((w * dhd <= w * dhfUp & w * ao <= aM) | w * ao <= 0)))").asFormula

    val model =
      s""" $constants &
         # ( ((w=-1 | w=1) & (to<=tl | tl<0)) & $condImplSafeableStr )
         # -> [
         #   {   {
         #   { ?true; ++
         #   { to:=0; dhf :=*; dhfUp :=*; {w:=-1; ++ w:=1;}
         #     ?$condImplSafeableStr;
         #   }  }
         #      ao :=*;
         #   }
         #   {r' = -rv, h' = -dhd, dhd' = ao, to'=1 &
         #      (to<=tl | tl<0) &
         #      (( w * dhd >= w * dhf  | w * ao >= a ) &
         #      ((w * dhd <= w * dhfUp & w * ao <= aM) | w * ao <= 0)) }
         #   }*
         #   ] ( (abs(r) > rp | abs(h) > hp) &
         #       ( ((w=-1 | w=1) & (to<=tl | tl<0)) & $condImplSafeableStr )
         #     )
       """.stripMargin('#')

    print(model)

    /*** Main safe theorem and its tactic ***/
    val safeTac = implyR('R) & andL('L) &
      loop(invariant)('R) & Idioms.<(
      (initCase, Idioms.rememberAs("Safeable_BaseCase", dT("Base case") & prop & done)),
      (useCase, Idioms.rememberAs("Safeable_UseCase", dT("Use case") & andR('R) & Idioms.<(
          SimplifierV2.fullSimpTac & dT("andL*") & (andL('L)*) &
          dT("before orL") &
          orL('L, condImplSafeableStr.asFormula) & Idioms.<(
          dT("before inst 0 lower") & andL('L, condImplSafeableLoStr.asFormula) &
            hideL('L, "\\forall hNew \\forall dhdNew (0<=tl-to&tl-to < max((0,w*(dhf-dhd)))/a&hNew=w*a/2*(tl-to)^2+dhd*(tl-to)&dhdNew=w*a*(tl-to)+dhd|tl-to>=max((0,w*(dhf-dhd)))/a&hNew=dhf*(tl-to)-w*max((0,w*(dhf-dhd)))^2/(2*a)&dhdNew=dhf->\\forall t \\forall ro \\forall ho ((t<=-1-to|-1 < 0)&(0<=t&t < max((0,w*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=w*a/2*t^2+dhdNew*t|t>=max((0,w*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=dhfExtr*t-w*max((0,w*(dhfExtr-dhdNew)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|w*(h-hNew) < w*ho-hp))".asFormula) &
            // replace by second part of condition
            allTRoHoL("", "0", "0", "0") & implyL('L) & Idioms.<(
              dT("Use case 1 Lo") & hideR('R, "abs(r)>rp|abs(h)>hp".asFormula) &
              EqualityTactics.abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxI"))) &
              max('L, "max(0,w*(dhf-dhd))".asTerm) &
              dT("MinMax Lower") & atomicQE(onAll(andR('R))*, dT("MinMax Lower QE")) & done
              ,
              dT("Absolute value Lo") & ArithmeticSpeculativeSimplification.speculativeQE & done
            ),
          dT("before inst 0 upper") & andL('L, condImplSafeableUpStr.asFormula) &
            hideL('L, "\\forall hNew \\forall dhdNew (0<=tl-to&tl-to < max((0,w*(dhfUp-dhd)))/aM&hNew=w*aM/2*(tl-to)^2+dhd*(tl-to)&dhdNew=w*aM*(tl-to)+dhd|tl-to>=max((0,w*(dhfUp-dhd)))/aM&hNew=(dhd+w*max((0,w*(dhfUp-dhd))))*(tl-to)-w*max((0,w*(dhfUp-dhd)))^2/(2*aM)&dhdNew=dhd+w*max((0,w*(dhfUp-dhd)))->\\forall t \\forall ro \\forall ho ((t<=-1-to|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(-w)*(h-hNew) < (-w)*ho-hp))".asFormula) &
            allTRoHoL("", "0", "0", "0") & implyL('L) & Idioms.<(
              dT("Use case 1 Up") & hideR('R, "abs(r)>rp|abs(h)>hp".asFormula) &
              EqualityTactics.abbrv("max((0,w*(dhfUp-dhd)))".asTerm, Some(Variable("maxUpI"))) &
              max('L, "max(0,w*(dhfUp-dhd))".asTerm) &
              dT("MinMax Upper") & atomicQE(onAll(andR('R))*, dT("MinMax Upper QE")) & done
              ,
              dT("Absolute value Up") & ArithmeticSpeculativeSimplification.speculativeQE & done
            )
          )
          ,
          andL('L) & close & done
        ) & done)
      ) // end use case
      ,
      (indStep, dT("Step") & composeb('R) & generalize(invariant)('R) & Idioms.<(
        /*show*/ dT("Generalization Holds") & Idioms.rememberAs("Safeable_StepGenHolds",
          dT("1.21") & chase('R) & dT("After chase") & andR('R) & Idioms.<(
            implyR('R) & allR('R) & close & done
            ,
            (andL('L)*) & hideL('L, "\\forall t \\forall ro \\forall ho ((t<=tl-to|tl < 0)&(0<=t&t < max((0,w*(dhf-dhd)))/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=max((0,w*(dhf-dhd)))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-dhd)))^2/(2*a))->abs(r-ro)>rp|w*h < w*ho-hp)&\\forall hNew \\forall dhdNew (0<=tl-to&tl-to < max((0,w*(dhf-dhd)))/a&hNew=w*a/2*(tl-to)^2+dhd*(tl-to)&dhdNew=w*a*(tl-to)+dhd|tl-to>=max((0,w*(dhf-dhd)))/a&hNew=dhf*(tl-to)-w*max((0,w*(dhf-dhd)))^2/(2*a)&dhdNew=dhf->\\forall t \\forall ro \\forall ho ((t<=-1-to|-1 < 0)&(0<=t&t < max((0,w*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=w*a/2*t^2+dhdNew*t|t>=max((0,w*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=dhfExtr*t-w*max((0,w*(dhfExtr-dhdNew)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|w*(h-hNew) < w*ho-hp))|\\forall t \\forall ro \\forall ho ((t<=tl-to|tl < 0)&(0<=t&t < max((0,w*(dhfUp-dhd)))/aM&ro=rv*t&ho=w*aM/2*t^2+dhd*t|t>=max((0,w*(dhfUp-dhd)))/aM&ro=rv*t&ho=(dhd+w*max((0,w*(dhfUp-dhd))))*t-w*max((0,w*(dhfUp-dhd)))^2/(2*aM))->abs(r-ro)>rp|w*h>w*ho+hp)&\\forall hNew \\forall dhdNew (0<=tl-to&tl-to < max((0,w*(dhfUp-dhd)))/aM&hNew=w*aM/2*(tl-to)^2+dhd*(tl-to)&dhdNew=w*aM*(tl-to)+dhd|tl-to>=max((0,w*(dhfUp-dhd)))/aM&hNew=(dhd+w*max((0,w*(dhfUp-dhd))))*(tl-to)-w*max((0,w*(dhfUp-dhd)))^2/(2*aM)&dhdNew=dhd+w*max((0,w*(dhfUp-dhd)))->\\forall t \\forall ro \\forall ho ((t<=-1-to|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(-w)*(h-hNew) < (-w)*ho-hp))".asFormula) &
              SimplifierV2.simpTac(1) & atomicQE(ArithmeticLibrary.exhaustiveBeta, dT("Gen Holds QE"))
          )) & done
          ,
        /*use*/ dT("Generalization Strong Enough") & Idioms.cases(prop)(
          (Case(Not(evolutionDomain)),
            hideL('L, invariant) & dT("Before DI") &
            DifferentialTactics.diffUnpackEvolutionDomainInitially('R) & (hideR('R)*) & notL('L) & close & done
          ),
          (Case(evolutionDomain),
            dT("Before diff. solution") &
              EqualityTactics.abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxI"))) &
              EqualityTactics.abbrv("max((0,w*(dhfUp-dhd)))".asTerm, Some(Variable("maxUpI"))) &
              diffSolveEnd('R) &
              dT("Diff. Solution") & allR('R) & implyR('R)*2 &
              andR('R) & Idioms.<(
                (andL('L)*) & andR('R) & Idioms.<(
                  dT("Showing w=-1|w=1") & close & done
                  ,
                  dT("bla2") & orR('R) &
                  // proof adaptation to vars to_3, dhd_3, r_3, and h_3 of original proof
                  EqualityTactics.abbrv("t_+to".asTerm, Some(Variable("to", Some(3)))) &
                  EqualityTactics.abbrv("ao*t_+dhd".asTerm, Some(Variable("dhd", Some(3)))) &
                  EqualityTactics.abbrv("(-rv)*t_+r".asTerm, Some(Variable("r", Some(3)))) &
                  EqualityTactics.abbrv("(-(ao/2*t_^2+dhd*t_)+h)".asTerm, Some(Variable("h", Some(3)))) &
                  hideL('L, "to<=tl|tl < 0".asFormula) & // present twice, eliminating one
                  hideL('L, "to_3<=tl|tl < 0".asFormula) &
                  orL('L, "\\forall t \\forall ro \\forall ho ((t <= tl-to|tl < 0)&(0<=t&t < maxI/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxI/a&ro=rv*t&ho=dhf*t-w*maxI^2/(2*a))->abs(r-ro)>rp|w*h < w*ho-hp)&\\forall hNew \\forall dhdNew (0<=tl-to&tl-to < maxI/a&hNew=w*a/2*(tl-to)^2+dhd*(tl-to)&dhdNew=w*a*(tl-to)+dhd|tl-to>=maxI/a&hNew=dhf*(tl-to)-w*maxI^2/(2*a)&dhdNew=dhf->\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(w)*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=(w)*a/2*t^2+dhdNew*t|t>=max((0,(w)*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=dhfExtr*t-(w)*max((0,(w)*(dhfExtr-dhdNew)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(w)*(h-hNew) < (w)*ho-hp))|\\forall t \\forall ro \\forall ho ((t <= tl-to|tl < 0)&(0<=t&t < maxUpI/aM&ro=rv*t&ho=w*aM/2*t^2+dhd*t|t>=maxUpI/aM&ro=rv*t&ho=(dhd+w*maxUpI)*t-w*maxUpI^2/(2*aM))->abs(r-ro)>rp|w*h>w*ho+hp)&\\forall hNew \\forall dhdNew (0<=tl-to&tl-to < maxUpI/aM&hNew=w*aM/2*(tl-to)^2+dhd*(tl-to)&dhdNew=w*aM*(tl-to)+dhd|tl-to>=maxUpI/aM&hNew=(dhd+w*maxUpI)*(tl-to)-w*maxUpI^2/(2*aM)&dhdNew=dhd+w*maxUpI->\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(-w)*(h-hNew) < (-w)*ho-hp))".asFormula)
                  & Idioms.<(
                    dT("Before hide lower") &
                    hideR('R, "\\forall t \\forall ro \\forall ho ((t <= tl-to_3|tl < 0)&(0<=t&t < max((0,w*(dhfUp-dhd_3)))/aM&ro=rv*t&ho=w*aM/2*t^2+dhd_3*t|t>=max((0,w*(dhfUp-dhd_3)))/aM&ro=rv*t&ho=(dhd_3+w*max((0,w*(dhfUp-dhd_3))))*t-w*max((0,w*(dhfUp-dhd_3)))^2/(2*aM))->abs(r_3-ro)>rp|w*h_3>w*ho+hp)&\\forall hNew \\forall dhdNew (0<=tl-to_3&tl-to_3 < max((0,w*(dhfUp-dhd_3)))/aM&hNew=w*aM/2*(tl-to_3)^2+dhd_3*(tl-to_3)&dhdNew=w*aM*(tl-to_3)+dhd_3|tl-to_3>=max((0,w*(dhfUp-dhd_3)))/aM&hNew=(dhd_3+w*max((0,w*(dhfUp-dhd_3))))*(tl-to_3)-w*max((0,w*(dhfUp-dhd_3)))^2/(2*aM)&dhdNew=dhd_3+w*max((0,w*(dhfUp-dhd_3)))->\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|(-w)*(h_3-hNew) < (-w)*ho-hp))".asFormula) &
                    hideL('L, "aM>=a".asFormula) & hideL('L, "maxUpI=max((0,w*(dhfUp-dhd)))".asFormula) &
                    hideL('L, "w*dhd<=w*dhfUp&w*ao<=aM|w*ao<=0".asFormula) &
                    hideL('L, "w*dhd_3<=w*dhfUp&w*ao<=aM|w*ao<=0".asFormula) &
                    dT("lower separation") &
                    andL('L) & //, "\\forall t \\forall ro \\forall ho ((t <= tl-to|tl < 0)&(0<=t&t < maxUpI/aM&ro=rv*t&ho=w*aM/2*t^2+dhd*t|t>=maxUpI/aM&ro=rv*t&ho=(dhd+w*maxUpI)*t-w*maxUpI^2/(2*aM))->abs(r-ro)>rp|w*h>w*ho+hp)&\\forall hNew \\forall dhdNew ((0<=tl-to&tl-to < maxUpI/aM&hNew=w*aM/2*(tl-to)^2+dhd*(tl-to)&dhdNew=w*aM*(tl-to)+dhd|tl-to>=maxUpI/aM&hNew=(dhd+w*maxUpI)*(tl-to)-w*maxUpI^2/(2*aM)&dhdNew=dhd+w*maxUpI)->\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(-w)*(h-hNew) < (-w)*ho-hp))") &
                    andR('R) & Idioms.<(
                    dT("APPLY LEMMA LOWER") &
                      hideL('L, "\\forall hNew \\forall dhdNew (0<=tl-to&tl-to < maxI/a&hNew=w*a/2*(tl-to)^2+dhd*(tl-to)&dhdNew=w*a*(tl-to)+dhd|tl-to>=maxI/a&hNew=dhf*(tl-to)-w*maxI^2/(2*a)&dhdNew=dhf->\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(w)*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=(w)*a/2*t^2+dhdNew*t|t>=max((0,(w)*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=dhfExtr*t-(w)*max((0,(w)*(dhfExtr-dhdNew)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(w)*(h-hNew) < (w)*ho-hp))".asFormula) &
                      dT("lower lemma") &
                      applyTweakLemma("safeable_safe_implicit"),
                    dT("DONE after tl") &
                      hideL('L, "\\forall t \\forall ro \\forall ho ((t <= tl-to|tl < 0)&(0<=t&t < maxI/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxI/a&ro=rv*t&ho=dhf*t-w*maxI^2/(2*a))->abs(r-ro)>rp|w*h < w*ho-hp)".asFormula) &
                      cutEZ("(0<=tl-to&tl-to < maxI/a) | tl-to >= maxI/a".asFormula, QE) & dT("cutEZ on tl-to") &
                      (allR('R)*) & implyR('R) & dT("skolemize hnew") &
                      orL('L, "(0<=tl-to&tl-to < maxI/a) | tl-to >= maxI/a".asFormula) & Idioms.<(
                        dT("tlmto case 1") &
                        EqualityTactics.abbrv("w*a/2*(tl-to)^2+dhd*(tl-to)".asTerm, Some(Variable("hNew1"))) &
                        EqualityTactics.abbrv("w*a*(tl-to)+dhd".asTerm, Some(Variable("dhdNew1"))) &
                        allL("hNew".asVariable, "hNew1".asTerm)('L) & allL("dhdNew".asVariable, "dhdNew1".asTerm)('L) &
                        implyL('L) & Idioms.<(
                          dT("DONE") &
                          hideR('R, "\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,w*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=w*a/2*t^2+dhdNew*t|t>=max((0,w*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=dhfExtr*t-w*max((0,w*(dhfExtr-dhdNew)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|w*(h_3-hNew) < w*ho-hp)".asFormula) &
                          QE
                          ,
                          dT("DONE tlmto 1") &
                          cut("w*(h-hNew1)>=w*(h_3-hNew) & w*dhdNew>=w*dhdNew1".asFormula) & Idioms.<(
                            (cutShow, dT("DONE proof cut") &
                            hideL('L, "\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,w*(dhfExtr-dhdNew1)))/a&ro=rv*t&ho=w*a/2*t^2+dhdNew1*t|t>=max((0,w*(dhfExtr-dhdNew1)))/a&ro=rv*t&ho=dhfExtr*t-w*max((0,(w)*(dhfExtr-dhdNew1)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|w*(h-hNew1) < w*ho-hp)".asFormula) &
                            hideR('R, "\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,w*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=w*a/2*t^2+dhdNew*t|t>=max((0,w*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=dhfExtr*t-w*max((0,w*(dhfExtr-dhdNew)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|w*(h_3-hNew) < w*ho-hp)".asFormula) &
                            max('L, "max(0,w*(dhf-dhd))".asTerm) &
                            max('L, "max((0,w*(dhf-dhd_3)))".asTerm) &
                            dT("show cut hNew QE") &
                            orL('L, "0<=tl-to_3&tl-to_3 < max_1/a&hNew=w*a/2*(tl-to_3)^2+dhd_3*(tl-to_3)&dhdNew=w*a*(tl-to_3)+dhd_3|tl-to_3>=max_1/a&hNew=dhf*(tl-to_3)-w*max_1^2/(2*a)&dhdNew=dhf".asFormula) &
                            onAll(atomicQE(ArithmeticLibrary.varEliminationLeft("w".asVariable), dT("crushw")))),
                          (cutUse, dT("DONE tlmto 1.2") &
                            hideL('L, "0<=tl-to_3&tl-to_3 < max((0,w*(dhf-dhd_3)))/a&hNew=w*a/2*(tl-to_3)^2+dhd_3*(tl-to_3)&dhdNew=w*a*(tl-to_3)+dhd_3|tl-to_3>=max((0,w*(dhf-dhd_3)))/a&hNew=dhf*(tl-to_3)-w*max((0,w*(dhf-dhd_3)))^2/(2*a)&dhdNew=dhf".asFormula) &
                            hideL('L, "hNew1=w*a/2*(tl-to)^2+dhd*(tl-to)".asFormula) & hideL('L, "dhdNew1=w*a*(tl-to)+dhd".asFormula) &
                            hideL('L, "0<=tl-to&tl-to < maxI/a".asFormula) & hideL('L, "maxI=max((0,w*(dhf-dhd)))".asFormula) &
                            hide('L, "w*dhd>=w*dhf|w*ao>=a".asFormula) & hideL('L, "w*dhd_3>=w*dhf|w*ao>=a".asFormula) &
                            dT("inserting lemma") & insertLemma("safeable_propagateLo") &
                            dT("instantiating") &
                            allL("h0".asVariable, "h-hNew1".asTerm)('L) &
                            allL("v0".asVariable, "dhdNew1".asTerm)('L) &
                            allL("a0".asVariable, "a".asTerm)('L) &
                            allL("vt0".asVariable, "dhfExtr".asTerm)('L) &
                            allL("to0".asVariable, "to".asTerm)('L) &
                            allL("h1".asVariable, "h_3-hNew".asTerm)('L) &
                            allL("v1".asVariable, "dhdNew".asTerm)('L) &
                            allL("a1".asVariable, "a".asTerm)('L) &
                            allL("vt1".asVariable, "dhfExtr".asTerm)('L) &
                            allL("to1".asVariable, "to_3".asTerm)('L) &
                            allL("tl".asVariable, "-1".asTerm)('L) &
                            allL("r".asVariable, "r-rv*(tl-to)".asTerm)('L) &
                            allL("w".asVariable, "w".asTerm)('L) &
                            dT("end inst") & implyL('L) & Idioms.<( // ok to end inst
                              andR('R) & Idioms.<(dT("cid") & closeId,
                                hideL('L, "\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(w)*(dhfExtr-dhdNew1)))/a&ro=rv*t&ho=(w)*a/2*t^2+dhdNew1*t|t>=max((0,(w)*(dhfExtr-dhdNew1)))/a&ro=rv*t&ho=dhfExtr*t-(w)*max((0,(w)*(dhfExtr-dhdNew1)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(w)*(h-hNew1) < (w)*ho-hp)".asFormula) &
                                hideR('R, "\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,w*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=w*a/2*t^2+dhdNew*t|t>=max((0,w*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=dhfExtr*t-w*max((0,w*(dhfExtr-dhdNew)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|w*(h_3-hNew) < w*ho-hp)".asFormula) &
                                dT("qe") & QE
                              ),
                              dT("concl") &
                              hideL('L, "\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(w)*(dhfExtr-dhdNew1)))/a&ro=rv*t&ho=(w)*a/2*t^2+dhdNew1*t|t>=max((0,(w)*(dhfExtr-dhdNew1)))/a&ro=rv*t&ho=dhfExtr*t-(w)*max((0,(w)*(dhfExtr-dhdNew1)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(w)*(h-hNew1) < (w)*ho-hp)".asFormula) &
                              (allR('R)*) &
                              allTRoHoL("Somewhere", "t", "ro", "ho") &
                              abs('R, "abs(r_3-rv*(tl-to_3)-ro)".asTerm) &
                              abs('L, "abs(r-rv*(tl-to)-ro)".asTerm) & dT("qe") & QE
                          )
                          )
                        )
                      ),
                      dT("tlmto case 2") &
                        EqualityTactics.abbrv("dhf*(tl-to)-w*maxI^2/(2*a)".asTerm, Some(Variable("hNew1"))) &
                        allL("hNew".asVariable, "hNew1".asTerm)('L) & allL("dhdNew".asVariable, "dhf".asTerm)('L) &
                        implyL('L) & Idioms.<(
                        dT("DONE") &
                          hideR('R, "\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,w*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=w*a/2*t^2+dhdNew*t|t>=max((0,w*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=dhfExtr*t-w*max((0,(w)*(dhfExtr-dhdNew)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|w*(h_3-hNew) < w*ho-hp)".asFormula) &
                          QE,
                        dT("tlmto 1") &
                          cut("w*(h-hNew1)>=w*(h_3-hNew) & w*dhdNew>=w*dhf".asFormula) & Idioms.<(
                          (cutShow, dT("proof cut") &
                            hideL('L, "\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,w*(dhfExtr-dhf)))/a&ro=rv*t&ho=w*a/2*t^2+dhf*t|t>=max((0,w*(dhfExtr-dhf)))/a&ro=rv*t&ho=dhfExtr*t-w*max((0,w*(dhfExtr-dhf)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|w*(h-hNew1) < w*ho-hp)".asFormula) &
                            hideR('R, "\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,w*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=w*a/2*t^2+dhdNew*t|t>=max((0,w*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=dhfExtr*t-w*max((0,w*(dhfExtr-dhdNew)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|w*(h_3-hNew) < w*ho-hp)".asFormula) &
                            max('L, "max(0,w*(dhf-dhd))".asTerm) &
                            max('L, "max((0,w*(dhf-dhd_3)))".asTerm) &
                            dT("show cut hNew QE") &
                            orL('L, "0<=tl-to_3&tl-to_3 < max_1/a&hNew=w*a/2*(tl-to_3)^2+dhd_3*(tl-to_3)&dhdNew=w*a*(tl-to_3)+dhd_3|tl-to_3>=max_1/a&hNew=dhf*(tl-to_3)-w*max_1^2/(2*a)&dhdNew=dhf".asFormula) &
                            onAll(atomicQE(ArithmeticLibrary.varEliminationLeft("w".asVariable), dT("crushw")))),
                          (cutUse, dT("tlmto 1.2") &
                            hideL('L, "0<=tl-to_3&tl-to_3 < max((0,w*(dhf-dhd_3)))/a&hNew=w*a/2*(tl-to_3)^2+dhd_3*(tl-to_3)&dhdNew=w*a*(tl-to_3)+dhd_3|tl-to_3>=max((0,w*(dhf-dhd_3)))/a&hNew=dhf*(tl-to_3)-w*max((0,w*(dhf-dhd_3)))^2/(2*a)&dhdNew=dhf".asFormula) &
                            hideL('L, "hNew1=dhf*(tl-to)-w*maxI^2/(2*a)".asFormula) &
                            hideL('L, "tl-to>=maxI/a".asFormula) & hideL('L, "maxI=max((0,w*(dhf-dhd)))".asFormula) &
                            hideL('L, "w*dhd>=w*dhf|w*ao>=a".asFormula) & hideL('L, "w*dhd_3>=w*dhf|w*ao>=a".asFormula) &
                            dT("inserting lemma") & insertLemma("safeable_propagateLo") &
                            dT("instantiating") &
                            allL("h0".asVariable, "h-hNew1".asTerm)('L) &
                            allL("v0".asVariable, "dhf".asTerm)('L) &
                            allL("a0".asVariable, "a".asTerm)('L) &
                            allL("vt0".asVariable, "dhfExtr".asTerm)('L) &
                            allL("to0".asVariable, "to".asTerm)('L) &
                            allL("h1".asVariable, "h_3-hNew".asTerm)('L) &
                            allL("v1".asVariable, "dhdNew".asTerm)('L) &
                            allL("a1".asVariable, "a".asTerm)('L) &
                            allL("vt1".asVariable, "dhfExtr".asTerm)('L) &
                            allL("to1".asVariable, "to_3".asTerm)('L) &
                            allL("tl".asVariable, "-1".asTerm)('L) &
                            allL("r".asVariable, "r-rv*(tl-to)".asTerm)('L) &
                            allL("w".asVariable, "w".asTerm)('L) &
                            dT("end inst") & implyL('L) & Idioms.<( // ok to end inst
                              andR('R) & Idioms.<(
                                dT("cid") & closeId,
                                hideL('L, "\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,w*(dhfExtr-dhf)))/a&ro=rv*t&ho=w*a/2*t^2+dhf*t|t>=max((0,w*(dhfExtr-dhf)))/a&ro=rv*t&ho=dhfExtr*t-w*max((0,w*(dhfExtr-dhf)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|w*(h-hNew1) < w*ho-hp)".asFormula) &
                                hideR('R, "\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,w*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=w*a/2*t^2+dhdNew*t|t>=max((0,w*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=dhfExtr*t-w*max((0,w*(dhfExtr-dhdNew)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|w*(h_3-hNew) < w*ho-hp)".asFormula) &
                                dT("qe") & QE
                            ),
                            dT("concl") &
                              hideL('L, "\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(w)*(dhfExtr-dhf)))/a&ro=rv*t&ho=(w)*a/2*t^2+dhf*t|t>=max((0,(w)*(dhfExtr-dhf)))/a&ro=rv*t&ho=dhfExtr*t-(w)*max((0,(w)*(dhfExtr-dhf)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(w)*(h-hNew1) < (w)*ho-hp)".asFormula) &
                              (allR('R)*) &
                              allTRoHoL("Somewhere else", "t", "ro", "ho") &
                              abs('R, "abs(r_3-rv*(tl-to_3)-ro)".asTerm) &
                              abs('L, "abs(r-rv*(tl-to)-ro)".asTerm) & dT("qe") & QE
                          )
                          )
                        )
                      )
                    )
                  ),
                  dT("Before hide upper") & // very similar proof as "Before hide lower". TODO refactor
                    hideR('R, "\\forall t \\forall ro \\forall ho ((t <= tl-to_3|tl < 0)&(0<=t&t < max((0,w*(dhf-dhd_3)))/a&ro=rv*t&ho=w*a/2*t^2+dhd_3*t|t>=max((0,w*(dhf-dhd_3)))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-dhd_3)))^2/(2*a))->abs(r_3-ro)>rp|w*h_3 < w*ho-hp)&\\forall hNew \\forall dhdNew (0<=tl-to_3&tl-to_3 < max((0,w*(dhf-dhd_3)))/a&hNew=w*a/2*(tl-to_3)^2+dhd_3*(tl-to_3)&dhdNew=w*a*(tl-to_3)+dhd_3|tl-to_3>=max((0,w*(dhf-dhd_3)))/a&hNew=dhf*(tl-to_3)-w*max((0,w*(dhf-dhd_3)))^2/(2*a)&dhdNew=dhf->\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,w*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=w*a/2*t^2+dhdNew*t|t>=max((0,w*(dhfExtr-dhdNew)))/a&ro=rv*t&ho=dhfExtr*t-w*max((0,w*(dhfExtr-dhdNew)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|w*(h_3-hNew) < w*ho-hp))".asFormula) &
                    cutEZ("aM>0".asFormula,
                      hideL('L, "\\forall t \\forall ro \\forall ho ((t <= tl-to|tl < 0)&(0<=t&t < maxUpI/aM&ro=rv*t&ho=w*aM/2*t^2+dhd*t|t>=maxUpI/aM&ro=rv*t&ho=(dhd+w*maxUpI)*t-w*maxUpI^2/(2*aM))->abs(r-ro)>rp|w*h>w*ho+hp)&\\forall hNew \\forall dhdNew (0<=tl-to&tl-to < maxUpI/aM&hNew=w*aM/2*(tl-to)^2+dhd*(tl-to)&dhdNew=w*aM*(tl-to)+dhd|tl-to>=maxUpI/aM&hNew=(dhd+w*maxUpI)*(tl-to)-w*maxUpI^2/(2*aM)&dhdNew=dhd+w*maxUpI->\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(-w)*(h-hNew) < (-w)*ho-hp))".asFormula)
                        & hideR('R, "\\forall t \\forall ro \\forall ho ((t <= tl-to_3|tl < 0)&(0<=t&t < max((0,w*(dhfUp-dhd_3)))/aM&ro=rv*t&ho=w*aM/2*t^2+dhd_3*t|t>=max((0,w*(dhfUp-dhd_3)))/aM&ro=rv*t&ho=(dhd_3+w*max((0,w*(dhfUp-dhd_3))))*t-w*max((0,w*(dhfUp-dhd_3)))^2/(2*aM))->abs(r_3-ro)>rp|w*h_3>w*ho+hp)&\\forall hNew \\forall dhdNew (0<=tl-to_3&tl-to_3 < max((0,w*(dhfUp-dhd_3)))/aM&hNew=w*aM/2*(tl-to_3)^2+dhd_3*(tl-to_3)&dhdNew=w*aM*(tl-to_3)+dhd_3|tl-to_3>=max((0,w*(dhfUp-dhd_3)))/aM&hNew=(dhd_3+w*max((0,w*(dhfUp-dhd_3))))*(tl-to_3)-w*max((0,w*(dhfUp-dhd_3)))^2/(2*aM)&dhdNew=dhd_3+w*max((0,w*(dhfUp-dhd_3)))->\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|(-w)*(h_3-hNew) < (-w)*ho-hp))".asFormula)
                        & QE) &
                    hideL('L, "aM>=a".asFormula) &
                    //la(hide, "a>0") & // TODO: only keep aexup
                    hideL('L, "maxI=max((0,w*(dhf-dhd)))".asFormula) &
                    hideL('L, "w*dhd>=w*dhf|w*ao>=a".asFormula) &
                    hideL('L, "w*dhd_3>=w*dhf|w*ao>=a".asFormula) &
                    dT("upper separation") &
                    andL('L) &
                    andR('R) & Idioms.<(
                      dT("APPLY LEMMA UPPER") &
                      hideL('L, "\\forall hNew \\forall dhdNew (0<=tl-to&tl-to < maxUpI/aM&hNew=w*aM/2*(tl-to)^2+dhd*(tl-to)&dhdNew=w*aM*(tl-to)+dhd|tl-to>=maxUpI/aM&hNew=(dhd+w*maxUpI)*(tl-to)-w*maxUpI^2/(2*aM)&dhdNew=dhd+w*maxUpI->\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(-w)*(h-hNew) < (-w)*ho-hp))".asFormula) &
                      dT("upper lemma") & applyTweakLemma("safeable_safe_upimplicit")
                      ,
                      dT("after tl") &
                      hideL('L, "\\forall t \\forall ro \\forall ho ((t <= tl-to|tl < 0)&(0<=t&t < maxUpI/aM&ro=rv*t&ho=w*aM/2*t^2+dhd*t|t>=maxUpI/aM&ro=rv*t&ho=(dhd+w*maxUpI)*t-w*maxUpI^2/(2*aM))->abs(r-ro)>rp|w*h>w*ho+hp)".asFormula) &
                      (allR('R)*) & implyR('R) & dT("skolemize hnew") &
                        Idioms.cases(QE)(
                        (Case("(0<=tl-to&tl-to < maxUpI/aM)".asFormula),
                          dT("tlmto case 1") &
                            EqualityTactics.abbrv("w*aM/2*(tl-to)^2+dhd*(tl-to)".asTerm, Some(Variable("hNew1"))) &
                            EqualityTactics.abbrv("w*aM*(tl-to)+dhd".asTerm, Some(Variable("dhdNew1"))) &
                            allL("hNew".asVariable, "hNew1".asTerm)('L) & allL("dhdNew".asVariable, "dhdNew1".asTerm)('L) &
                            implyL('L) & Idioms.<(
                              hideR('R, "\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|(-w)*(h_3-hNew) < (-w)*ho-hp)".asFormula) &
                              QE,
                              dT("tlmto 1") &
                              cut("w*(h-hNew1)<=w*(h_3-hNew) & w*dhdNew<=w*dhdNew1".asFormula) & Idioms.<(
                              (cutShow, dT("REVIEW, used to be done with old cut show cut hNew") &
                                hideL('L, "\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew1)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew1*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew1)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew1)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(-w)*(h-hNew1) < (-w)*ho-hp)".asFormula) &
                                hideR('R, "\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|(-w)*(h_3-hNew) < (-w)*ho-hp)".asFormula) &
                                max('L, "max(0,w*(dhfUp-dhd))".asTerm) &
                                max('L, "max((0,w*(dhfUp-dhd_3)))".asTerm) &
                                dT("show cut hNew QE") &
                                orL('L, "0<=tl-to_3&tl-to_3 < max_1/aM&hNew=w*aM/2*(tl-to_3)^2+dhd_3*(tl-to_3)&dhdNew=w*aM*(tl-to_3)+dhd_3|tl-to_3>=max_1/aM&hNew=(dhd_3+w*max_1)*(tl-to_3)-w*max_1^2/(2*aM)&dhdNew=dhd_3+w*max_1".asFormula) &
                                onAll(atomicQE(ArithmeticLibrary.varEliminationLeft("w".asVariable), dT("crushw")))
                                ),
                              (cutUse, dT("DONE tlmto 1.2") & hideL('L, "aM>0".asFormula) &
                                hideL('L, "0<=tl-to_3&tl-to_3 < max((0,w*(dhfUp-dhd_3)))/aM&hNew=w*aM/2*(tl-to_3)^2+dhd_3*(tl-to_3)&dhdNew=w*aM*(tl-to_3)+dhd_3|tl-to_3>=max((0,w*(dhfUp-dhd_3)))/aM&hNew=(dhd_3+w*max((0,w*(dhfUp-dhd_3))))*(tl-to_3)-w*max((0,w*(dhfUp-dhd_3)))^2/(2*aM)&dhdNew=dhd_3+w*max((0,w*(dhfUp-dhd_3)))".asFormula) &
                                hideL('L, "hNew1=w*aM/2*(tl-to)^2+dhd*(tl-to)".asFormula) & hideL('L, "dhdNew1=w*aM*(tl-to)+dhd".asFormula) &
                                hideL('L, "0<=tl-to&tl-to < maxUpI/aM".asFormula) & hideL('L, "maxUpI=max((0,w*(dhfUp-dhd)))".asFormula) &
                                hideL('L, "w*dhd<=w*dhfUp&w*ao<=aM|w*ao<=0".asFormula) & hideL('L, "w*dhd_3<=w*dhfUp&w*ao<=aM|w*ao<=0".asFormula) &
                                dT("inserting lemma") & insertLemma("safeable_propagateLo") &
                                dT("instantiating") &
                                allL("h0".asVariable, "h-hNew1".asTerm)('L) &
                                allL("v0".asVariable, "dhdNew1".asTerm)('L) &
                                allL("a0".asVariable, "a".asTerm)('L) &
                                allL("vt0".asVariable, "dhfUpExtr".asTerm)('L) &
                                allL("to0".asVariable, "to".asTerm)('L) &
                                allL("h1".asVariable, "h_3-hNew".asTerm)('L) &
                                allL("v1".asVariable, "dhdNew".asTerm)('L) &
                                allL("a1".asVariable, "a".asTerm)('L) &
                                allL("vt1".asVariable, "dhfUpExtr".asTerm)('L) &
                                allL("to1".asVariable, "to_3".asTerm)('L) &
                                allL("tl".asVariable, "-1".asTerm)('L) &
                                allL("r".asVariable, "r-rv*(tl-to)".asTerm)('L) &
                                allL("w".asVariable, "-w".asTerm)('L) &
                                dT("end inst") & implyL('L) & Idioms.<(
                                  andR('R) & Idioms.<(
                                    closeId,
                                    hideL('L, "\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew1)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew1*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew1)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew1)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(-w)*(h-hNew1) < (-w)*ho-hp)".asFormula) &
                                    hideR('R, "\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|(-w)*(h_3-hNew) < (-w)*ho-hp)".asFormula) &
                                    QE
                                ),
                                dT("concl") &
                                  hideL('L, "\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew1)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew1*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew1)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew1)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(-w)*(h-hNew1) < (-w)*ho-hp)".asFormula) &
                                  (allR('R)*) &
                                  allTRoHoL("Yet somewhere else", "t", "ro", "ho") &
                                  //cutEZ("r_3-rv*(tl-to_3)=r-rv*(tl-to)".asFormula, QE) &
                                  // eqHide("r_3-rv*(tl-to_3)=r-rv*(tl-to)") & closeId // ??? DOES NOW WORK EVEN AFTER INSTANTIATION
                                  abs('R, "abs(r_3-rv*(tl-to_3)-ro)".asTerm) &
                                  abs('L, "abs(r-rv*(tl-to)-ro)".asTerm) & QE
                              )
                              )
                            )
                          )
                        ),
                        (Case("tl-to >= maxUpI/aM".asFormula),
                          dT("tlmto case 2") &
                            EqualityTactics.abbrv("(dhd+w*maxUpI)*(tl-to)-w*maxUpI^2/(2*aM)".asTerm, Some(Variable("hNew1"))) &
                            EqualityTactics.abbrv("dhd+w*maxUpI".asTerm, Some(Variable("dhdNew1"))) &
                            allL("hNew".asVariable, "hNew1".asTerm)('L) & allL("dhdNew".asVariable, "dhdNew1".asTerm)('L) &
                            implyL('L) & Idioms.<(
                              hideR('R, "\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|(-w)*(h_3-hNew) < (-w)*ho-hp)".asFormula) &
                              QE,
                              dT("tlmto 2") &
                              cut("w*(h-hNew1)<=w*(h_3-hNew) & w*dhdNew<=w*dhdNew1".asFormula) & Idioms.<(
                              (cutShow, dT("cut") &
                                hideL('L, "\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew1)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew1*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew1)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew1)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(-w)*(h-hNew1) < (-w)*ho-hp)".asFormula) &
                                hideR('R, "\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|(-w)*(h_3-hNew) < (-w)*ho-hp)".asFormula) &
                                max('L, "max(0,w*(dhfUp-dhd))".asTerm) &
                                max('L, "max((0,w*(dhfUp-dhd_3)))".asTerm) &
                                dT("show cut hNew QE") &
                                orL('L, "0<=tl-to_3&tl-to_3 < max_1/aM&hNew=w*aM/2*(tl-to_3)^2+dhd_3*(tl-to_3)&dhdNew=w*aM*(tl-to_3)+dhd_3|tl-to_3>=max_1/aM&hNew=(dhd_3+w*max_1)*(tl-to_3)-w*max_1^2/(2*aM)&dhdNew=dhd_3+w*max_1".asFormula) &
                                onAll(atomicQE(ArithmeticLibrary.varEliminationLeft("w".asVariable), dT("crushw")))
                                ),
                              (cutUse, dT("tlmto 2.2") & hideL('L, "aM>0".asFormula) &
                                // For future refactoring: This proof is exactly identical as TODO tlmto 1.2, except the hide on dhdNew1
                                hideL('L, "0<=tl-to_3&tl-to_3 < max((0,w*(dhfUp-dhd_3)))/aM&hNew=w*aM/2*(tl-to_3)^2+dhd_3*(tl-to_3)&dhdNew=w*aM*(tl-to_3)+dhd_3|tl-to_3>=max((0,w*(dhfUp-dhd_3)))/aM&hNew=(dhd_3+w*max((0,w*(dhfUp-dhd_3))))*(tl-to_3)-w*max((0,w*(dhfUp-dhd_3)))^2/(2*aM)&dhdNew=dhd_3+w*max((0,w*(dhfUp-dhd_3)))".asFormula) &
                                hideL('L, "hNew1=dhdNew1*(tl-to)-w*maxUpI^2/(2*aM)".asFormula) & hideL('L, "dhdNew1=dhd+w*maxUpI".asFormula) &
                                hideL('L, "tl-to >= maxUpI/aM".asFormula) & hideL('L, "maxUpI=max((0,w*(dhfUp-dhd)))".asFormula) &
                                hideL('L, "w*dhd<=w*dhfUp&w*ao<=aM|w*ao<=0".asFormula) & hideL('L, "w*dhd_3<=w*dhfUp&w*ao<=aM|w*ao<=0".asFormula) &
                                dT("inserting lemma") & insertLemma("safeable_propagateLo") &
                                dT("instantiating") &
                                allL("h0".asVariable, "h-hNew1".asTerm)('L) &
                                allL("v0".asVariable, "dhdNew1".asTerm)('L) &
                                allL("a0".asVariable, "a".asTerm)('L) &
                                allL("vt0".asVariable, "dhfUpExtr".asTerm)('L) &
                                allL("to0".asVariable, "to".asTerm)('L) &
                                allL("h1".asVariable, "h_3-hNew".asTerm)('L) &
                                allL("v1".asVariable, "dhdNew".asTerm)('L) &
                                allL("a1".asVariable, "a".asTerm)('L) &
                                allL("vt1".asVariable, "dhfUpExtr".asTerm)('L) &
                                allL("to1".asVariable, "to_3".asTerm)('L) &
                                allL("tl".asVariable, "-1".asTerm)('L) &
                                allL("r".asVariable, "r-rv*(tl-to)".asTerm)('L) &
                                allL("w".asVariable, "-w".asTerm)('L) &
                                dT("end inst") & implyL('L) & Idioms.<(
                                  andR('R) & Idioms.<(
                                    closeId,
                                    hideL('L, "\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew1)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew1*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew1)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew1)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(-w)*(h-hNew1) < (-w)*ho-hp)".asFormula) &
                                    hideR('R, "\\forall t \\forall ro \\forall ho ((t <= -1-to_3|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew)))^2/(2*a))->abs(r_3-rv*(tl-to_3)-ro)>rp|(-w)*(h_3-hNew) < (-w)*ho-hp)".asFormula) &
                                    QE
                                ),
                                dT("concl") &
                                  hideL('L, "\\forall t \\forall ro \\forall ho ((t <= -1-to|-1 < 0)&(0<=t&t < max((0,(-w)*(dhfUpExtr-dhdNew1)))/a&ro=rv*t&ho=(-w)*a/2*t^2+dhdNew1*t|t>=max((0,(-w)*(dhfUpExtr-dhdNew1)))/a&ro=rv*t&ho=dhfUpExtr*t-(-w)*max((0,(-w)*(dhfUpExtr-dhdNew1)))^2/(2*a))->abs(r-rv*(tl-to)-ro)>rp|(-w)*(h-hNew1) < (-w)*ho-hp)".asFormula) &
                                  (allR('R)*) &
                                  allTRoHoL("Final else", "t", "ro", "ho") &
                                  abs('R, "abs(r_3-rv*(tl-to_3)-ro)".asTerm) &
                                  abs('L, "abs(r-rv*(tl-to)-ro)".asTerm) & QE
                              ) & done
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
        )
        /* End cutUseLbl "Generalization strong enough" */
      ) ) /* End indStepLbl */
    )

    val safeTheorem = proveBy(model.asFormula, safeTac)
    safeTheorem shouldBe 'proved
  }

}
