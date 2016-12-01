/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics.acasxhstp.safeable

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.BelleLabels._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.btactics.{DLBySubst, EqualityTactics, Idioms, SimplifierV2}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser

import scala.language.postfixOps

/**
 * Proves Sect. 5.1: Safe Region for Subsequent Advisories - Two-Sided Safe Region with Immediate Pilot Response
 *
 * Theorem 3: Correctness of implicit two-sided safe regions
 * Lemma 3a: Equivalence of implicit lower and explicit lower region formulation
 * Lemma 3b: Equivalence of implicit upper and explicit upper region formulation
 * Lemma 3: Equivalence of implicit and explicit two-sided region formulation
 * Corollary 2: Correctness of explicit two-sided safe regions

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
class AcasXSafeTwoSided extends AcasXBase {

  private val safeLemmaFormula =
    ("maxI=max((0,w*(dhf-dhd))) &" +
      "(w*dhd>=w*dhf|w*ao>=a) &" +
      "(w=-1|w=1) &" +
      "(\\forall t \\forall ro \\forall ho (0<=t&t < maxI/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxI/a&ro=rv*t&ho=dhf*t-w*maxI^2/(2*a)->abs(r-ro)>rp|w*h < w*ho-hp)) &" +
      "hp>0 & rp>=0 & rv>=0 & a>0 &" +
      "(w*(ao*t_+dhd)>=w*dhf|w*ao>=a) &" +
      "t_ >= 0" +
      "->" +
      "\\forall t \\forall ro \\forall ho (0<=t&t < max((0,w*(dhf-(ao*t_+dhd))))/a&ro=rv*t&ho=w*a/2*t^2+(ao*t_+dhd)*t|t>=max((0,w*(dhf-(ao*t_+dhd))))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-(ao*t_+dhd))))^2/(2*a)->abs((-rv)*t_+r-ro)>rp|w*(-(ao/2*t_^2+dhd*t_)+h) < w*ho-hp)").asFormula

  private val safeUpLemmaFormula =
    ("maxIM=max((0,w*(dhfM-dhd))) &"+
      "(w*dhd<=w*dhfM&w*ao<=aM|w*ao<=0) &" +
      "(w=-1|w=1) &" +
      "(\\forall t \\forall ro \\forall ho (0<=t&t < maxIM/aM&ro=rv*t&ho=w*aM/2*t^2+dhd*t|t>=maxIM/aM&ro=rv*t&ho=(dhd+w*maxIM)*t-w*maxIM^2/(2*aM)->abs(r-ro)>rp|w*h>w*ho+hp)) &" +
      "hp>0 & rp>=0 & rv>=0 & aM>0 &" +
      "(w*(ao*t_+dhd)<=w*dhfM&w*ao<=aM|w*ao<=0) &" +
      "t_ >= 0" +
      "->" +
      "\\forall t \\forall ro \\forall ho (0<=t&t < max((0,w*(dhfM-(ao*t_+dhd))))/aM&ro=rv*t&ho=w*aM/2*t^2+(ao*t_+dhd)*t|t>=max((0,w*(dhfM-(ao*t_+dhd))))/aM&ro=rv*t&ho=((ao*t_+dhd)+w*max((0,w*(dhfM-(ao*t_+dhd)))))*t-w*max((0,w*(dhfM-(ao*t_+dhd))))^2/(2*aM)->abs((-rv)*t_+r-ro)>rp|w*(-(ao/2*t_^2+dhd*t_)+h)>w*ho+hp)").asFormula

  /*** Invariants etc. ***/
  private val condImplLower = ("    ("+
    "      \\forall t \\forall ro \\forall ho"+
    "        ((0 <= t & t < max(0, w * (dhf - dhd)) / a &"+
    "          ro = rv * t & ho = (w * a) / 2 * t^2 + dhd * t) |"+
    "          (t >= max(0, w * (dhf - dhd)) / a &"+
    "            ro = rv * t &"+
    "            ho = dhf * t - w * max(0, w * (dhf - dhd))^2 / (2*a))"+
    "            -> (abs(r - ro) > rp | w * h < w * ho - hp))"+
    "      )").asFormula

  private val condImplUpper = ("("+
    "        \\forall t \\forall ro \\forall ho"+
    "          ((0 <= t & t < max(0, w * (dhfM - dhd)) / aM &"+
    "            ro = rv * t & ho = (w * aM) / 2 * t^2 + dhd * t) |"+
    "            (t >= max(0, w * (dhfM - dhd)) / aM &"+
    "              ro = rv * t &"+
    "              ho = (dhd + w * max(0, w * (dhfM-dhd))) * t "+
    "                   - w * max(0, w * (dhfM - dhd))^2 / (2*aM))"+
    "              -> (abs(r - ro) > rp | w * h > w * ho + hp))"+
    "        )").asFormula

  private val condImpl = Or(condImplLower, condImplUpper)

//  private val invariantStr = "(( (w=-1 | w=1) &"+ condImpl +
//    ") & (hp > 0 & rp >= 0 & rv >= 0 & a > 0 & aM > 0))"

  private val invariant = And(And("w=-1 | w=1".asFormula, condImpl), "hp > 0 & rp >= 0 & rv >= 0 & a > 0 & aM > 0".asFormula) //invariantStr.asFormula

  "ACAS X 2-sided safe" should "prove Theorem 3, lemma safe implicit" in withMathematica { tool =>
    if (lemmaDB.contains("2side_safe_implicit")) lemmaDB.remove("2side_safe_implicit")

    def safeLemmaTac(r: String, h: String, dhd: String) = dT("lemma") & implyR('R) & (andL('L)*) &
      dT("Before skolem") & (allR('R)*) & dT("After skolem") &
      implyR('R) & orR('R) &
      //here we'd want to access previously introduced skolem symbol and
      // time introduced by diffSolution;goal 90
      allL(Variable("t"), "t_ + t".asTerm)('L) & // t_22+t_23: t_ == t_22, t == t_23
      allL(Variable("ro"), "rv*(t_ + t)".asTerm)('L) & // rv*(t_22+t_23)
      dT("Before CUT") &
      cut("0<=t+t_&t+t_<maxI/a|t+t_>=maxI/a".asFormula) & Idioms.<(
      (cutShow, dT("Show Cut") & hideL('L, "maxI=max((0,w*(dhf-dhd)))".asFormula) &
        hideL('L, "\\forall ho (0<=t_+t&t_+t < maxI/a&rv*(t_+t)=rv*(t_+t)&ho=w*a/2*(t_+t)^2+dhd*(t_+t)|t_+t>=maxI/a&rv*(t_+t)=rv*(t_+t)&ho=dhf*(t_+t)-w*maxI^2/(2*a)->abs(r-rv*(t_+t))>rp|w*h < w*ho-hp)".asFormula)
        & hideR('R, s"abs($r-ro)>rp".asFormula) & hideR('R, s"w*$h<w*ho-hp".asFormula) &
        dT("Show Cut 2") & orR('R) &
        orL('L, s"0<=t&t<max((0,w*(dhf-$dhd)))/a&ro=rv*t&ho=w*a/2*t^2+$dhd*t|t>=max((0,w*(dhf-$dhd)))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-$dhd)))^2/(2*a)".asFormula)
        & dT("End CutShowLbl") & atomicQE),
      (cutUse, dT("Use Cut")
        &
        orL('L, "0<=t+t_&t+t_ < maxI/a|t+t_>=maxI/a".asFormula) & Idioms.<(
          dT("Goal 110") & //hideL('L, initDomain) &
          allL(Variable("ho"), "w*a/2*(t+t_)^2 + dhd*(t+t_)".asTerm)('L) &
          dT("instantiate ho 1 Lo") &
          implyL('L, "0<=t_+t&t_+t < maxI/a&rv*(t_+t)=rv*(t_+t)&w*a/2*(t+t_)^2+dhd*(t+t_)=w*a/2*(t_+t)^2+dhd*(t_+t)|t_+t>=maxI/a&rv*(t_+t)=rv*(t_+t)&w*a/2*(t+t_)^2+dhd*(t+t_)=dhf*(t_+t)-w*maxI^2/(2*a)->abs(r-rv*(t_+t))>rp|w*h < w*(w*a/2*(t+t_)^2+dhd*(t+t_))-hp".asFormula)
          & Idioms.<(
            dT("left of -> 1 Lo") & orR('R) &
            hideR('R, "t_+t>=maxI/a&rv*(t_+t)=rv*(t_+t)&w*a/2*(t+t_)^2+dhd*(t+t_)=dhf*(t_+t)-w*maxI^2/(2*a)".asFormula) &
            hideR('R, s"abs($r-ro)>rp".asFormula) & hideR('R, s"w*$h<w*ho-hp".asFormula) &
            hideL('L, "maxI=max((0,w*(dhf-dhd)))".asFormula) & QE & done
            ,
            dT("right of -> 1 Lo") & atomicQE & done
          )
          ,

          dT("final time in straight Lo") &
          allL(Variable("ho"), "dhf*(t+t_) - w*maxI^2/(2*a)".asTerm)('L) &
          dT("instantiate ho 2 Lo") &
          implyL('L, "0<=t_+t&t_+t < maxI/a&rv*(t_+t)=rv*(t_+t)&dhf*(t+t_)-w*maxI^2/(2*a)=w*a/2*(t_+t)^2+dhd*(t_+t)|t_+t>=maxI/a&rv*(t_+t)=rv*(t_+t)&dhf*(t+t_)-w*maxI^2/(2*a)=dhf*(t_+t)-w*maxI^2/(2*a)->abs(r-rv*(t_+t))>rp|w*h < w*(dhf*(t+t_)-w*maxI^2/(2*a))-hp".asFormula)
          & Idioms.<(
          dT("left of -> 2 Lo") & orR('R) &
            hideR('R, "0<=t_+t&t_+t < maxI/a&rv*(t_+t)=rv*(t_+t)&dhf*(t+t_)-w*maxI^2/(2*a)=w*a/2*(t_+t)^2+dhd*(t_+t)".asFormula) &
            hideR('R, s"abs($r-ro)>rp".asFormula) & hideR('R, s"w*$h<w*ho-hp".asFormula) &
            hideL('L, "maxI=max((0,w*(dhf-dhd)))".asFormula) & QE
            ,
            dT("right of -> 2 Lo") & atomicQE & done
          )
        )
        )
    )

    val safeLemma = proveBy(safeLemmaFormula, safeLemmaTac("((-rv)*t_+r)", "(-(ao/2*t_^2+dhd*t_)+h)", "(ao*t_+dhd)"))
    safeLemma shouldBe 'proved
    storeLemma(safeLemma, Some("2side_safe_implicit"))
  }

  it should "prove Theorem 3, lemma up safe implicit" in withMathematica { tool =>
    if (lemmaDB.contains("2side_safe_upimplicit")) lemmaDB.remove("2side_safe_upimplicit")

    //@todo same tactic as above, but with different instances

    def safeUpLemmaTac(r: String, h: String, dhd: String) = dT("lemma Up") & implyR('R) & (andL('L)*) &
      dT("Before skolem Up") & (allR('R)*) & dT("After skolem Up") &
      implyR('R) & orR('R) &
      allL(Variable("t"), "t_ + t".asTerm)('L) &
      allL(Variable("ro"), "rv*(t_ + t)".asTerm)('L) &
      dT("Before CUT") &
      cut("0<=t_+t&t_+t<maxIM/aM|t_+t>=maxIM/aM".asFormula) & Idioms.<(
      (cutShow, dT("Show Cut") & hideL('L, "maxIM=max((0,w*(dhfM-dhd)))".asFormula) &
        hideL('L, "\\forall ho (0<=t_+t&t_+t < maxIM/aM&rv*(t_+t)=rv*(t_+t)&ho=w*aM/2*(t_+t)^2+dhd*(t_+t)|t_+t>=maxIM/aM&rv*(t_+t)=rv*(t_+t)&ho=(dhd+w*maxIM)*(t_+t)-w*maxIM^2/(2*aM)->abs(r-rv*(t_+t))>rp|w*h>w*ho+hp)".asFormula)
        & hideR('R, s"abs($r-ro)>rp".asFormula) & hideR('R, s"w*$h>w*ho+hp".asFormula) &
        dT("Show Cut 2") & orR('R) &
        orL('L, s"0<=t&t<max((0,w*(dhfM-$dhd)))/aM&ro=rv*t&ho=w*aM/2*t^2+$dhd*t|t>=max((0,w*(dhfM-$dhd)))/aM&ro=rv*t&ho=($dhd+w*max((0,w*(dhfM-$dhd))))*t-w*max((0,w*(dhfM-$dhd)))^2/(2*aM)".asFormula)
        & atomicQE)
      ,
      (cutUse, dT("Use Cut") &
        orL('L, "0<=t_+t&t_+t<maxIM/aM|t_+t>=maxIM/aM".asFormula) & Idioms.<(
        dT("final time in parabola") &
          allL(Variable("ho"), "w*aM/2*(t_+t)^2+dhd*(t_+t)".asTerm)('L) &
          dT("instantiate ho 1 Up") &
          implyL('L, "0<=t_+t&t_+t < maxIM/aM&rv*(t_+t)=rv*(t_+t)&w*aM/2*(t_+t)^2+dhd*(t_+t)=w*aM/2*(t_+t)^2+dhd*(t_+t)|t_+t>=maxIM/aM&rv*(t_+t)=rv*(t_+t)&w*aM/2*(t_+t)^2+dhd*(t_+t)=(dhd+w*maxIM)*(t_+t)-w*maxIM^2/(2*aM)->abs(r-rv*(t_+t))>rp|w*h>w*(w*aM/2*(t_+t)^2+dhd*(t_+t))+hp".asFormula)
          & Idioms.<(
          dT("left of -> 1 Up") & orR('R) &
            hideR('R, "t_+t>=maxIM/aM&rv*(t_+t)=rv*(t_+t)&w*aM/2*(t_+t)^2+dhd*(t_+t)=(dhd+w*maxIM)*(t_+t)-w*maxIM^2/(2*aM)".asFormula) &
            hideR('R, s"abs($r-ro)>rp".asFormula) & hideR('R, s"w*$h>w*ho+hp".asFormula) &
            hideL('L, "maxIM=max((0,w*(dhfM-dhd)))".asFormula) & QE & done
          ,
          dT("right of -> 1 Up") & atomicQE & done
        )
        ,
        dT("final time in straight Up") &
          allL(Variable("ho"), "(dhd+w*maxIM)*(t_+t)-w*maxIM^2/(2*aM)".asTerm)('L) &
          dT("instantiate ho 2 Lo") &
          implyL('L, "0<=t_+t&t_+t < maxIM/aM&rv*(t_+t)=rv*(t_+t)&(dhd+w*maxIM)*(t_+t)-w*maxIM^2/(2*aM)=w*aM/2*(t_+t)^2+dhd*(t_+t)|t_+t>=maxIM/aM&rv*(t_+t)=rv*(t_+t)&(dhd+w*maxIM)*(t_+t)-w*maxIM^2/(2*aM)=(dhd+w*maxIM)*(t_+t)-w*maxIM^2/(2*aM)->abs(r-rv*(t_+t))>rp|w*h>w*((dhd+w*maxIM)*(t_+t)-w*maxIM^2/(2*aM))+hp".asFormula)
          & Idioms.<(
          dT("left of -> 2 Up") & orR('R) &
            hideR('R, "0<=t_+t&t_+t < maxIM/aM&rv*(t_+t)=rv*(t_+t)&(dhd+w*maxIM)*(t_+t)-w*maxIM^2/(2*aM)=w*aM/2*(t_+t)^2+dhd*(t_+t)".asFormula) &
            hideR('R, s"abs($r-ro)>rp".asFormula) & hideR('R, s"w*$h>w*ho+hp".asFormula) &
            hideL('L, "maxIM=max((0,w*(dhfM-dhd)))".asFormula) & QE & done
          ,
          dT("right of -> 2 Up") & atomicQE & done
        )
      )
      )
    )

    val safeUpLemma = proveBy(safeUpLemmaFormula, safeUpLemmaTac("((-rv)*t_+r)", "(-(ao/2*t_^2+dhd*t_)+h)", "(ao*t_+dhd)"))
    safeUpLemma shouldBe 'proved
    storeLemma(safeUpLemma, Some("2side_safe_upimplicit"))
  }

  it should "prove Theorem 3: uc lo lemma" in withMathematica { tool =>
    val ucLoTac: BelleExpr =
      dT("before orL") & orL('L, condImpl) & Idioms.<(
        dT("before inst 0 lower") &
          allL(Variable("t"), Number(0))('L) &
          allL(Variable("ro"), Number(0))('L) &
          allL(Variable("ho"), Number(0))('L) & implyL('L) & Idioms.<(
          dT("Use case 1") & hideR('R, "abs(r)>rp|abs(h)>hp".asFormula) &
            EqualityTactics.abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxI"))) &
            max('L, "max(0,w*(dhf-dhd))".asTerm) &
            dT("MinMax Lower") & QE & done
          ,
          dT("Absolute value") &
            abs('R, "abs(r)".asTerm) &
            abs('R, "abs(h)".asTerm) &
            abs('L, "abs(r-0)".asTerm) &
            dT("Use case 2") & QE & done
        ) & done,
        dT("before inst 0 upper") &
          allL(Variable("t"), Number(0))('L) &
          allL(Variable("ro"), Number(0))('L) &
          allL(Variable("ho"), Number(0))('L) & implyL('L) & Idioms.<(
          dT("Use case 1") & hideR('R, "abs(r)>rp|abs(h)>hp".asFormula) &
            EqualityTactics.abbrv("max((0,w*(dhfM-dhd)))".asTerm, Some(Variable("maxIM"))) &
            max('L, "max(0,w*(dhfM-dhd))".asTerm) &
            dT("MinMax Upper") & QE,
          dT("Absolute value") &
            abs('R, "abs(r)".asTerm) &
            abs('R, "abs(h)".asTerm) &
            abs('L, "abs(r-0)".asTerm) &
            dT("Use case 2 upper") & QE & done
        ))

    val ucLoLemma = proveBy(Imply(invariant, "(abs(r)>rp|abs(h)>hp)".asFormula), implyR('R) & (andL('L)*) & ucLoTac)
    ucLoLemma shouldBe 'proved
    storeLemma(ucLoLemma, Some("twosided_implicit_usecase"))
  }

  it should "prove Theorem 3: correctness of implicit two-sided safe regions" in withMathematica { tool =>

    def applyLemma(formula: Formula, apply: BelleExpr) = cut(formula) & Idioms.<(
      (cutUse, dT("use Lemma " + formula) & SimplifierV2.simpTac('L, formula) & closeId & done)
      ,
      (cutShow, cohideR('Rlast, formula) & dT("apply Lemma " + formula) & apply)
    )

    val evolutionDomain =
      ("(( w * dhd >= w * dhf  | w * ao >= a ) &" +
        " ((w * dhd <= w * dhfM & w * ao <= aM) | w * ao <= 0))").asFormula

    val ode = "r'=-rv,h'=-dhd,dhd'=ao".asDifferentialProgram

    /*** Main safe theorem and its tactic ***/
    val safeSeq = KeYmaeraXProblemParser(io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/casestudies/acasx/sttt/twosided_implicit.kyx")).mkString)

    val safeTac = implyR('R) &
      // do not keep constants around, otherwise simplifier will simplify those first and won't recognize invariant
      DLBySubst.loop(invariant, skip)('R) & Idioms.<(
      (initCase, dT("Base case") & prop & done),
      (useCase, dT("Use case") &
        andR('R) & Idioms.<(
          cohide2(-1, 1) & implyRi & by(lemmaDB.get("twosided_implicit_usecase").getOrElse(throw new Exception("Lemma twosided_implicit_usecase must be proved first"))) & done,
          (andL('L) *) & closeId & done
        ) & done)
      ,
      (indStep, dT("Step") & composeb('R) & generalize(invariant)('R) & Idioms.<(
        /*show*/ dT("Generalization Holds") & chase('R) & dT("After chase") & ((SimplifierV2.simpTac('R) & (andL('L)*))*) & dT("Simplified") & normalize & done
          ,
        /*use*/ dT("Generalization Strong Enough") &
          cutEZ(Or(Not(evolutionDomain), evolutionDomain),
            cohideR('R, Or(Not(evolutionDomain), evolutionDomain)) & prop & done) &
          orL('L, Or(Not(evolutionDomain), evolutionDomain)) & Idioms.<(
            hideL('L, invariant) &
            dT("Before DI") &
            cutEZ(Box(ODESystem(ode, evolutionDomain), "0=1".asFormula),
              hideR('R, Box(ODESystem(ode, evolutionDomain), invariant)) & diffInd()('Rlast)) &
            hideL('L, Not(evolutionDomain)) &
            dT("After DI") & diffCut("0=1".asFormula)('R) & Idioms.<(
              /*use*/ dT("After DC 2") & diffWeaken('R) & dT("after DW") &
                implyR('R) & andL('L) & cohideL('L, "0=1".asFormula) & dT("before QE") & QE,
              /*show*/ dT("After DC 1") & closeId & done
            )
          ,
          dT("Before diff. solution") &
            EqualityTactics.abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxI"))) &
            EqualityTactics.abbrv("max((0,w*(dhfM-dhd)))".asTerm, Some(Variable("maxIM"))) &
            diffSolveEnd('R) &
            dT("Diff. Solution") & allR('R) & implyR('R)*2 & (andL('L)*) &
            andR('R) & Idioms.<(
              andR('R) & Idioms.<(
                closeId,
                dT("bla2") & orR('R) &
                orL('L, "\\forall t \\forall ro \\forall ho (0<=t&t < maxI/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxI/a&ro=rv*t&ho=dhf*t-w*maxI^2/(2*a)->abs(r-ro)>rp|w*h < w*ho-hp)|\\forall t \\forall ro \\forall ho (0<=t&t < maxIM/aM&ro=rv*t&ho=w*aM/2*t^2+dhd*t|t>=maxIM/aM&ro=rv*t&ho=(dhd+w*maxIM)*t-w*maxIM^2/(2*aM)->abs(r-ro)>rp|w*h>w*ho+hp)".asFormula)
                & Idioms.<(
                  hideL('L, "maxIM=max((0,w*(dhfM-dhd)))".asFormula) & hideL('L, "aM>0".asFormula) &
                  hideL('L, "w*dhd<=w*dhfM&w*ao<=aM|w*ao<=0".asFormula) &
                  hideL('L, "w*(ao*t_+dhd)<=w*dhfM&w*ao<=aM|w*ao<=0".asFormula) &
                  hideR('R, "\\forall t \\forall ro \\forall ho (0<=t&t < max((0,w*(dhfM-(ao*t_+dhd))))/aM&ro=rv*t&ho=w*aM/2*t^2+(ao*t_+dhd)*t|t>=max((0,w*(dhfM-(ao*t_+dhd))))/aM&ro=rv*t&ho=((ao*t_+dhd)+w*max((0,w*(dhfM-(ao*t_+dhd)))))*t-w*max((0,w*(dhfM-(ao*t_+dhd))))^2/(2*aM)->abs((-rv)*t_+r-ro)>rp|w*(-(ao/2*t_^2+dhd*t_)+h)>w*ho+hp)".asFormula) &
                  dT("lower lemma") &
                  applyLemma(safeLemmaFormula, by(lemmaDB.get("2side_safe_implicit").getOrElse(throw new Exception("Lemma 2side_safe_implicit must be proved first")))) & done
                  ,
                  hideL('L, "maxI=max((0,w*(dhf-dhd)))".asFormula) & hideL('L, "a>0".asFormula) &
                  hideL('L, "w*dhd>=w*dhf|w*ao>=a".asFormula) &
                  hideL('L, "w*(ao*t_+dhd)>=w*dhf|w*ao>=a".asFormula) &
                  hideR('R, "\\forall t \\forall ro \\forall ho (0<=t&t < max((0,w*(dhf-(ao*t_+dhd))))/a&ro=rv*t&ho=w*a/2*t^2+(ao*t_+dhd)*t|t>=max((0,w*(dhf-(ao*t_+dhd))))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-(ao*t_+dhd))))^2/(2*a)->abs((-rv)*t_+r-ro)>rp|w*(-(ao/2*t_^2+dhd*t_)+h) < w*ho-hp)".asFormula) &
                  dT("upper lemma") &
                  applyLemma(safeUpLemmaFormula, by(lemmaDB.get("2side_safe_upimplicit").getOrElse(throw new Exception("Lemma 2side_safe_upimplicit must be proved first")))) & done
                )
              ),
            QE
            )
          ) /* end orL on cutEZ */
          /* End cutUseLbl "Generalization strong enough" */
      )) /* End indStepLbl */
    )

    val safeTheorem = proveBy(safeSeq, safeTac)
    safeTheorem shouldBe 'proved
    //storeLemma(safeTheorem, Some("twosided_implicit")) // stack overflow
  }

//  it should "prove Lemma 3a: implicit-explicit lower equivalence" in {
//    if (!lemmaDB.contains("safe_equivalence")) {
//      println("Proving safe_equivalence lemma...")
//      // Lemma 3a: lower bound proof is the same as Lemma 1, see AcasXSafe
//      (new AcasXSafe).execute("ACAS X safe should prove Lemma 1: equivalence between implicit and explicit region formulation")
//      println("...done")
//    }
//  }
//
//  it should "prove Lemma 3b: implicit-explicit upper equivalence" in {
//    val reductionStr = io.Source.fromFile(folder + "upper_equivalence.key").mkString
//    val reductionSeq = new Sequent(Nil, immutable.IndexedSeq(), immutable.IndexedSeq(KeYmaeraXProblemParser(reductionStr)))
//
//    /*** Helper tactics ***/
//    def oG(s : String) = Tactics.SubLabelBranch(s)
//
//    def instantiateVars(tString : String, roString : String, hoString : String) = la(instantiateT(Variable("t"), tString.asTerm)) & la(instantiateT(Variable("ro"), roString.asTerm)) & la(instantiateT(Variable("ho"), hoString.asTerm))
//
//    def substTactic0(hoString : String) = implyR(1) & la(instantiateT(Variable("t"), "(r-rp)/rv".asTerm)) &
//      la(instantiateT(Variable("ro"), "(r-rp)".asTerm)) &
//      la(instantiateT(Variable("ho"), hoString.asTerm)) &
//      la(implyL) &&
//      (orR(2) & hideL(-1) & hideL(-4) & hideR(1) & cut("r<rp+rv*maxAbbrv/aM | r=rp+rv*maxAbbrv/aM".asFormula) &
//        //TODO: cutting with a<0 | a=0 when we have a<=0 in the antecedant should prove cutShow automatically
//        //or use useAt() instead
//        onBranch(
//          (cutShowLbl, hideR(1) & hideR(1) & hideL(-1) & hideL(-2) & QE
//            ),
//          (cutUseLbl, orL(-5) &&
//            // TODO: tactic for proving A|B -> (C|D) by proving A->C and B->D
//            (
//              hideR(2) & QE
//              ,
//              hideR(1) & QE
//              )
//            )
//        )
//        ,
//        orL(-7) &&
//          (/* abs(r-(r-rp))>rp <-> false */
//            hideL(-1) & hideL(-1) & hideL(-2) & hideL(-2) & hideL(-2) & hideR(1) & QE // TODO: is there a better way to hide a list
//            ,
//            /* amenable to the form G,A -> A */
//            hideL(-1) & hideL(-1) & hideL(-3) & hideL(-3) & QE
//            )
//        )
//
//    def substTactic00(hoString : String) = la(instantiateT(Variable("t"), "(r-rp)/rv".asTerm)) &
//      la(instantiateT(Variable("ro"), "(r-rp)".asTerm)) &
//      la(instantiateT(Variable("ho"), hoString.asTerm)) &
//      la(implyL) &&
//      (orR(2) & hideL(-1) & hideL(-4) & hideR(1) & cut("r>rp+rv*maxAbbrv/aM | r=rp+rv*maxAbbrv/aM".asFormula) &
//        //TODO: cutting with a<0 | a=0 when we have a<=0 in the antecedant should prove cutShow automatically
//        onBranch(
//          (cutShowLbl, hideR(1) & hideR(1) & hideL(-1) & hideL(-2) & QE
//            ),
//          (cutUseLbl, orL(-5) &&
//            // TODO: tactic for proving A|B -> (C|D) by proving A->C and B->D
//            (
//              oG("-- i --") & QE//& hideR(2) //& QE
//              ,
//              oG("-- ii --") & QE//& hideR(1) //& QE
//              )
//            )
//        )
//        ,
//        orL(-7) &&
//          (/* abs(r-(r-rp))>rp <-> false */
//            hideL(-1) & hideL(-1) & hideL(-2) & hideL(-2) & hideL(-2) & hideR(1) & QE // TODO: is there a better way to hide a list
//            ,
//            /* amenable to the form G,A -> A */
//            hideL(-1) & hideL(-1) & hideL(-3) & hideL(-3) & QE
//            )
//        )
//
//    def substTactic1(hoString : String, hidePos: Int) = implyR(1) & la(instantiateT(Variable("t"), "(r+rp)/rv".asTerm)) & la(instantiateT(Variable("ro"), "(r+rp)".asTerm)) & la(instantiateT(Variable("ho"), hoString.asTerm)) & la(implyL) &&
//      (
//        oG("__01___") & ls(hideR) & ls(orR) & hideR(hidePos) & hideL(-1) & hideL(-1) & QE
//        ,
//        oG("__02__") & la(orL) && (oG("rp>0 & abs(rp)>rp") & ls(hideR) & hideL(-1) & hideL(-1) & hideL(-2) & hideL(-2) & hideL(-2) & QE , oG("rv>0 & A*rv^2>0 -> A>0") & hideL(-1) & hideL(-1) & hideL(-3) & hideL(-3) & QE)
//        )
//
//    def tac1() = implyR(1) & ls(andR) &&
//      (
//        oG("(^R 1.1)") & implyR(1) & instantiateVars("0","0","0") & hideL(-1) & la(implyL) &&
//          (
//            hideR(1) & hideL(-3) & hideL(-3) & QE
//            ,
//            hideL(-1) & hideL(-2) & QE
//            )
//        ,
//        oG("(^R 1.2)") & ls(andR) &&
//          (
//            oG("(^R 1.2.1)") & substTactic0("(w * aM) / 2 * (r-rp)^2/rv^2 + dhd * (r-rp)/rv")
//            ,
//            oG("^R 1.2.2)") & andR(1) &&
//              (
//                oG("___0___") & substTactic1("(w * aM) / 2 * (r+rp)^2/rv^2 + dhd * (r+rp)/rv",2)
//                ,
//                oG("___1___") & substTactic1("(dhd+w*maxAbbrv)*(r+rp)/rv-w*maxAbbrv^2/(2*aM)",1)
//                )
//            )
//        )
//    def tac1rv0() = implyR(1) & ls(andR) &&
//      (
//        oG("(^R 1.1)") & implyR(1) & instantiateVars("0","0","0") & la(implyL) &&
//          (
//            oG("___0___") & hideL(-1) & QE
//            ,
//            oG("___1___") & hideL(-1) & QE
//            )
//        ,
//        oG("(^R 1.2)") & ls(andR) &&
//          (
//            oG("(^R 1.2.1)") & hideL(-1) & hideL(-1) & hideL(-1) & ls(implyR) & QE
//            ,
//            oG("^R 1.2.2)") & andR(1) &&
//              (
//                oG("___0___") & hideL(-1) & hideL(-1) & hideL(-1) & ls(implyR) & QE
//                ,
//                /* this branch showed the bug in equivalence_up.key */
//                /*TODO: simplify further before calling QE*/
//                oG("___1___") & implyR(1) & orR(1) & la(MinMaxT, "", Some("max(0,w*(dhfM-dhd))".asTerm)) & la(TacticLibrary.eqLeft(exhaustive=true), "maxAbbrv=max_0") & la(hideT, "maxAbbrv=max_0") & orL(-2) && (
//                  oG("++0++") & andL(-2) & la(TacticLibrary.eqLeft(exhaustive=true), "max_0=0") & la(hideT, "max_0=0") & QE
//                  , oG("++1++") & andL(-2) & la(TacticLibrary.eqLeft(exhaustive=true), "max_0=w*(dhfM-dhd)") & la(hideT, "max_0=w*(dhfM-dhd)") & hideR(2) &  QE
//                  )
//                )
//            )
//        )
//
//    def tac2() = implyR(1) & ls(andR) &&
//      (
//        oG("(^R 1.1)") & implyR(1) & instantiateVars("0","0","0") & hideL(-1) & la(implyL) &&
//          (
//            hideR(1) & hideL(-3) & hideL(-3) & QE
//            ,
//            hideL(-1) & hideL(-2) & QE
//            )
//        ,
//        oG("(^R 1.2)") & ls(andR) &&
//          (
//            oG("(^R 1.2.1)") & substTactic0("(w * aM) / 2 * (r-rp)^2/rv^2 + dhd * (r-rp)/rv")
//            ,
//            oG("^R 1.2.2)") & implyR(1) & orR(1) & hideR(1) &
//              substTactic00("(dhd+w*maxAbbrv)*(r-rp)/rv-w*maxAbbrv^2/(2*aM)")
//            )
//        )
//
//    def tac2rv0() = implyR(1) & ls(andR) &&
//      (
//        oG("(^R 2.1)") & implyR(1) & instantiateVars("0","0","0") & la(implyL) &&
//          (
//            oG("___0___") & hideL(-1) & QE
//            ,
//            oG("___1___") & hideL(-1) & QE
//            )
//        ,
//        oG("(^R 2.2)") & ls(andR) &&
//          (
//            oG("(^R 2.2.1)") & hideL(-1) & hideL(-1) & hideL(-1) & ls(implyR) & QE
//            ,
//            oG("^R 2.2.2)") & ls(implyR) & ls(orR) & cut("((r>rp)|(r=rp))".asFormula) &
//              onBranch (
//                (cutShowLbl, hideR(1) & hideR(1) & hideL(-1) & hideL(-1) & hideL(-2) & QE
//                  ),
//                /*TODO: eqleft sensitive to the ordering */
//                (cutUseLbl, orL(-7) && (oG("r>rp") & hideR(1) & hideL(-4) & QE, oG("r=rp")&la(TacticLibrary.eqLeft(exhaustive=true), "r=rp") & la(hideT, "r=rp") & QE   ))
//              )
//            )
//        )
//
//    def concreteQEHammer1() = andL(-4) & andL(-11) & andL(-12) & la(TacticLibrary.eqLeft(exhaustive=true), "ro=rv*t") & la(hideT, "ro=rv*t") & la(TacticLibrary.eqLeft(exhaustive=true), "ho=w*aM/2*t^2+dhd*t") & la(hideT, "ho=w*aM/2*t^2+dhd*t") & implyL(-4) && (oG("___ A ___") & implyL(-4) && (oG("___ 0 ___")& (la(hideL)*) & hideR(1) & QE,oG("___ 1 ___") & andL(-10) & andL(-11) & implyL(-12) && (oG("___ a ___") & implyL(-11) && (oG("*** i ***") & cut("maxAbbrv>0|maxAbbrv=0".asFormula) & onBranch((cutShowLbl,oG("Show") & hideR(1) & hideR(1) & hideR(1) & hideR(1) & QE),(cutUseLbl,oG("USE") & orL(-11) && (oG(">>") & hideL(-1) & QE,oG("==") & la(TacticLibrary.eqLeft(exhaustive=true), "maxAbbrv=0") & la(hideT, "maxAbbrv=0") & hideR(4) & QE)))  ,oG("*** ii ***") & hideL(-1) & QE),oG("___ b ___") & implyL(-11) && (oG("*** i ***") & orL(-11) && (implyL(-10) && (hideL(-1) & QE, hideL(-1) & QE),implyL(-10) && (hideL(-1) & QE, hideL(-1) & QE)) ,oG("*** ii ***") & orL(-11) && (oG("+++ left +++") & implyL(-10) && (hideL(-1) & QE, hideL(-1) & QE) ,oG("+++ right +++") & implyL(-10) && (oG("  x  ") & hideL(-1) & QE,oG("  y  ") & hideL(-1) & hideL(-10) & QE) )) )) ,oG("___ B ___") & andL(-11) & implyL(-4) && (oG("___ 0 ___") & andL(-11) & andL(-12) & implyL(-11) && (oG("___ a ___") & implyL(-12) && (oG("1") & implyL(-11) && (oG(" i ") & hideL(-1) & QE,oG(" ii ") & hideL(-1) & QE),oG("2") & implyL(-11) & (oG("1") & orL(-11) && (hideL(-1) & QE,hideL(-1)& QE),oG("2") & orL(-11) && (oG(" i ") & implyL(-10) && (hideL(-1) & QE, hideL(-1) & QE),oG(" ii ") & implyL(-10) && (oG("* a *") & orL(-4) && (hideL(-1) & QE,hideL(-1) & QE)   , oG("* b *") & orL(-4) && (hideL(-1) & QE,hideL(-1) & QE) )))) ,oG("___ b ___") & implyL(-12) && (oG("A") & implyL(-11) && (oG(" i ") & implyL(-10) && (hideL(-1)&QE,hideL(-1)&QE),oG(" ii ") & implyL(-10) && (orL(-4) && (hideL(-1)&QE,hideL(-1)&QE), orL(-4) && (hideL(-1)&QE,hideL(-1)&QE))),oG("B") & orL(-13) && (oG("_i_") & implyL(-11) && (oG(" x ") & implyL(-10) && (hideL(-1)&QE,hideL(-1)&QE),oG(" y ") & implyL(-10) && (hideL(-1)&QE,hideL(-1)&QE)),oG("_ii_") & implyL(-11) && (oG(" x ") & implyL(-10) && (orL(-4) && (hideL(-1)&QE,hideL(-1)&QE),orL(-4) && (hideL(-1)&QE,hideL(-1)&QE)),oG(" y ")& implyL(-10) && (orL(-4) && (hideL(-1)&QE,hideL(-1)&QE),orL(-4) && (hideL(-1)&QE,hideL(-1)&QE)) )))),oG("___ 1 ___") & andL(-12) & andL(-11) & andL(-12) & andL(-13) & hideL(-10) & implyL(-15) && (oG("__a __") & hideL(-11) & implyL(-12) && (oG("_ i _") & orL(-4) && (hideL(-1)&QE,hideL(-1)&QE) ,oG("_ ii _") & orL(-4) && (hideL(-1)&QE,hideL(-1)&QE) ),oG("__ b __") & hideL(-11) & orL(-14) && (oG("_ i _") & implyL(-12) && (orL(-4) && (hideL(-1)&QE,hideL(-1)&QE) , orL(-4) && (hideL(-1)&QE,hideL(-1)&QE)) ,oG("_ ii _") & implyL(-12) && (oG("__") & implyL(-12) && (orL(-4) && (hideL(-1)&QE,hideL(-1)&QE) , orL(-4) && (hideL(-1)&QE,hideL(-1)&QE)),oG("____") & orL(-14) && (oG("1") & implyL(-11) && (orL(-4) && (hideL(-1)&QE,hideL(-1)&QE) , orL(-4) && (hideL(-1)&QE,hideL(-1)&QE)) ,oG("2") & implyL(-11) && (oG("i") & implyL(-11) && (orL(-4) && (hideL(-1)&QE,hideL(-1)&QE),orL(-4) && (hideL(-1)&QE,hideL(-1)&QE)),oG("j") & implyL(-11) && (oG(" x ") & implyL(-10) && (orL(-4) && (hideL(-1)&QE,hideL(-1)&QE),orL(-4) && (hideL(-1)&QE,hideL(-1)&QE)), oG(" y ") & implyL(-10) && (oG("**0**") & orL(-4) && (oG("==a==") & la(TacticLibrary.eqLeft(exhaustive=true), "w=-1") & la(hideT, "w=-1") & hideL(-1) & QE,oG("==b==") & la(TacticLibrary.eqLeft(exhaustive=true), "w=1") & la(hideT, "w=1") & hideL(-1) & QE),oG("**1**") & orL(-4) && (oG("==a==") & la(TacticLibrary.eqLeft(exhaustive=true), "w=-1") & la(hideT, "w=-1") & hideL(-1) & QE,oG("==b==") & la(TacticLibrary.eqLeft(exhaustive=true), "w=1") & la(hideT, "w=1") & hideL(-1) & QE)  )  ))  ) ) )) ))
//
//
//    def concreteQEHammer2() = andL(-4) & andL(-11) & la(TacticLibrary.eqLeft(exhaustive=true), "ro=rv*t") & la(hideT, "ro=rv*t") & la(TacticLibrary.eqLeft(exhaustive=true), "ho=(dhd+w*maxAbbrv)*t-w*maxAbbrv^2/(2*aM)") & la(hideT, "ho=(dhd+w*maxAbbrv)*t-w*maxAbbrv^2/(2*aM)") & implyL(-4) && (
//      oG("___ A ___") & implyL(-4) && (
//        oG("___ 0 ___") & (la(hideL)*) & hideR(1) & QE
//        ,oG("___ 1 ___") & andL(-9) & andL(-10) & implyL(-11) && (
//        oG("___ a ___") & implyL(-10) && (
//          oG("*** i ***") & cut("maxAbbrv>0|maxAbbrv=0".asFormula) & onBranch((cutShowLbl,oG("Show") & hideR(1) & hideR(1) & hideR(1) & hideR(1) & QE),(cutUseLbl,oG("USE") & orL(-10) && (oG(">>") & hideL(-1) & orL(-3) && (QE,QE)
//            ,oG("==") & la(TacticLibrary.eqLeft(exhaustive=true), "maxAbbrv=0") & la(hideT, "maxAbbrv=0") & QE)))
//          ,oG("*** ii ***") & hideL(-1) & QE
//          )
//        ,oG("___ b ___") & implyL(-10) && (
//        oG("*** i ***") & orL(-10) && (
//          orL(-4) && (hideL(-1) & QE, hideL(-1) & QE)
//          ,orL(-4) && (hideL(-1) & QE, hideL(-1) & QE)
//          )
//        ,oG("*** ii ***") & orL(-10) && (
//        oG("+++ left +++") & implyL(-9) && (hideL(-1) & QE, hideL(-1) & QE)
//        ,oG("+++ right +++") & implyL(-9) && (
//        oG("  x  ") & hideL(-1) & QE
//        ,oG("  y  ") & hideL(-1) & hideL(-9) & QE
//        )
//        )
//        )
//        )
//        )
//      ,oG("___ B ___") & andL(-10) & implyL(-4) && (
//      oG("___ 0 ___") & andL(-10) & andL(-11) & implyL(-10) && (
//        oG("___ a ___") & implyL(-11) && (
//          oG("1") & implyL(-10) && (
//            oG(" i ") & hideL(-1) & orL(-3) && (QE,QE)
//            ,oG(" ii ") & hideL(-1) & orL(-3) && (QE,QE)
//            )
//          ,oG("2") & implyL(-10) && (
//          oG(" x ") & orL(-10) && (hideL(-1) & orL(-3) && (QE,QE),hideL(-1)& orL(-3) && (QE,QE))
//          ,oG(" y ") & orL(-10) && (
//          oG(" i ") & implyL(-9) && (hideL(-1) & QE, hideL(-1) & QE)
//          ,oG(" ii ") & implyL(-9) && (
//          oG("* a *") & orL(-4) && (hideL(-1) & QE,hideL(-1) & QE)
//          , oG("* b *") & orL(-4) && (hideL(-1) & QE,hideL(-1) & QE)
//          )
//          )
//          )
//          )
//        ,oG("___ b ___") & implyL(-11) && (
//        oG("A") & implyL(-10) && (
//          oG(" i ") & implyL(-9) && (hideL(-1)&QE,hideL(-1)&QE),oG(" ii ") & implyL(-9) && (orL(-4) && (hideL(-1)&QE,hideL(-1)&QE), orL(-4) && (hideL(-1)&QE,hideL(-1)&QE))
//          )
//        ,oG("B") & orL(-12) && (
//        oG("_i_") & implyL(-10) && (oG(" x ") & implyL(-9) && (hideL(-1)&QE,hideL(-1)&QE),oG(" y ") & implyL(-9) && (hideL(-1)&QE,hideL(-1)&QE))
//        ,oG("_ii_") & implyL(-10) && (oG(" x ") & implyL(-9) && (orL(-4) && (hideL(-1)&QE,hideL(-1)&QE),orL(-4) && (hideL(-1)&QE,hideL(-1)&QE)),oG(" y ")& implyL(-9) && (orL(-4) && (hideL(-1)&QE,hideL(-1)&QE),orL(-4) && (hideL(-1)&QE,hideL(-1)&QE)) )
//        )
//        )
//        )
//      ,oG("___ 1 ___") & andL(-11) & andL(-10) & andL(-11) & andL(-12) & hideL(-9) & implyL(-14) && (
//      oG("__ a __") & hideL(-11) & implyL(-12) && (
//        oG("_ i _") & orL(-4) && (hideL(-1)&QE,hideL(-1)&QE)
//        ,oG("_ ii _") & orL(-4) && (hideL(-1)&QE,hideL(-1)&QE)
//        )
//      ,oG("__ b __") & orL(-14) && (
//      oG("_ i _") & implyL(-12) && (
//        oG("__") & orL(-4) && (hideL(-1)&QE,hideL(-1)&QE)
//        ,oG("____") & orL(-14) && (orL(-4) && (hideL(-1)&QE,hideL(-1)&QE) , orL(-4) && (hideL(-1)&QE,hideL(-1)&QE))
//        )
//      ,oG("_ ii _") & implyL(-13) && (orL(-4) && (hideL(-1)&QE,hideL(-1)&QE) , orL(-4) && (hideL(-1)&QE,hideL(-1)&QE))
//      )
//      )
//      )
//      )
//
//    def rvp() = oG("rv>0") & ls(equivR) & onBranch(
//      (equivLeftLbl, oG("(->)") & allR(1) & allR(1) & allR(1) & implyR(1) & andL(-5) & andL(-3) & andL(-7) & andL(-9) & andL(-10) & hideL(-10) & orL(-4) && (
//        oG("___ T1 ___") & concreteQEHammer1  /* Closed ! */
//        ,
//        oG("___ T2 ___") & concreteQEHammer2 /* Closed ! */
//        )
//        ),
//      (equivRightLbl, oG("(<-)")
//        & ls(andR) &&
//        (oG("___ R1 ___") & tac1 /* Closed ! */
//          ,
//          oG("___ R2 ___") & tac2 /* Closed ! */
//          )
//        )
//    )
//
//    def rv0() = la(TacticLibrary.eqLeft(exhaustive=true), "rv=0") & la(hideT, "rv=0") & ls(equivR) & onBranch(
//      (equivLeftLbl, oG("(->)") & allR(1) & allR(1) & allR(1) & implyR(1) & orL(-5) &&
//        (
//          oG("__0__") & andL(-5) & andL(-6) & andL(-7) & la(TacticLibrary.eqLeft(exhaustive=true), "ro=0*t") & la(hideT, "ro=0*t") & la(TacticLibrary.eqLeft(exhaustive=true), "ho=w*aM/2*t^2+dhd*t") & la(hideT, "ho=w*aM/2*t^2+dhd*t") & andL(-4) & implyL(-6) & (oG("__A__") & implyL(-6) && (oG("__I__") & hideR(1) & (la(hideL)*) & QE
//            ,oG("__II__") & andL(-6) & andL(-7) & implyL(-8) && (oG("___a___") & implyL(-6) && (oG("+++ 0 +++") & hideL(-6) & QE , oG("+++ 1 +++") & hideL(-6) & QE ),oG("___b___") & orL(-8) && (oG("+++ 0 +++") & hideL(-7) & QE, oG("+++ 1 +++") & hideL(-7) & QE) ))
//            ,oG("__B__") & implyL(-6) & (oG("__I__") & andL(-6) & andL(-7) & hideL(-7) & andL(-7) & hideL(-7) & QE  ,oG("__II__") & andL(-6) & andL(-6) & andL(-7) & hideL(-9) & andL(-9) & hideL(-9) & andL(-8) & hideL(-9) & QE)
//            )
//          ,
//
//          oG("__1__") & andL(-5) & andL(-6) & la(TacticLibrary.eqLeft(exhaustive=true), "ro=0*t") & la(hideT, "ro=0*t") & la(TacticLibrary.eqLeft(exhaustive=true), "ho=(dhd+w*maxAbbrv)*t-w*maxAbbrv^2/(2*aM)") & la(hideT, "ho=(dhd+w*maxAbbrv)*t-w*maxAbbrv^2/(2*aM)")
//            & andL(-4) & implyL(-6) & (
//            oG("__A__") & implyL(-5) && (oG("__I__") & hideR(1) & (la(hideL)*) & QE, oG("__II__") & andL(-5) & andL(-6) & andL(-7) & hideL(-7) & hideL(-6) & implyL(-6) && (oG("___a___") & hideL(-5) & hideL(-1) & QE ,oG("___b___") & orL(-6) && (oG("+++ 0 +++")& implyL(-5) && (oG("** i **") & QE,oG("** ii **") & QE) ,oG("+++ 1 +++") & implyL(-5) && (oG("** i **") & QE,oG("** ii **") & QE)) ) )
//            ,
//            oG("__B__") & implyL(-5) && (oG("__I__") & andL(-5) & andL(-6) & hideL(-6) & implyL(-6) && (oG("___a___") & orR(1) & implyL(-5) && (oG("+++ 0 +++")& (la(hideL)*) & hideR(4) & hideR(1) & hideR(1) & QE , oG("+++ 1 +++") & hideR(2) & hideR(2) & debug("___a1___") & QE) ,oG("___b___")& orL(-6) && (oG("+++ 0 +++") & andL(-6) & hideL(-5) & hideL(-1) &QE, oG("+++ 1 +++") & hideL(-5) & hideL(-1) & QE )) , oG("__II__") & andL(-5) & andL(-5) & andL(-6) & hideL(-5) & andL(-6) & hideL(-6) & hideL(-7) & andL(-7) & implyL(-8) && (oG("___a___") & implyL(-6) && (oG("** i **") & hideL(-6) & implyL(-5) && (QE,QE),oG("** ii **") & hideL(-6) & implyL(-5) && (orL(-5) && (QE,QE) ,QE)),oG("___b___") & implyL(-6) && (oG("** i **") & hideL(-6) & orL(-6) && (implyL(-5) && (QE,QE),implyL(-5) && (QE,QE)) ,oG("** ii **") & hideL(-6) & orL(-6) && (oG("--- a ---") & orL(-7) && (QE,QE),oG("--- b ---") & orL(-7) && (QE,QE)) ))  )
//            )
//          )
//        ),
//      (equivRightLbl, oG("(<-)")
//        & ls(andR) &&
//        (oG("___ R1 ___") & tac1rv0
//          ,
//          oG("___ R2 ___") & tac2rv0
//          )
//        )
//    )
//
//    def tactic = abbrv("max(0, w*(dhfM - dhd))".asTerm, Some(Variable("maxAbbrv"))) &
//      cut("maxAbbrv>=0".asFormula) & onBranch(
//      (cutShowLbl, hideR(1) & QE)
//      ,
//      (cutUseLbl, implyR(1) &
//        cut("(rv=0|rv>0)".asFormula) & onBranch(
//        (cutShowLbl, hideR(1) & hideL(-1) & QE)
//        ,
//        (cutUseLbl, orL(-4) &&
//          (oG("(rv=0)") & rv0 /* Closed ! */
//            ,
//            oG("(rv>0)") & rvp /* Closed ! */
//            )
//          )
//      )
//        )
//    )
//
//    val reductionProof = helper.runTactic(tactic, new RootNode(reductionSeq))
//    reductionProof shouldBe 'closed
//
//    val lemmaDB = LemmaDBFactory.lemmaDB
//    val equivalenceLemmaID = lemmaDB.add(Lemma(
//      reductionProof.provableWitness,
//      new ToolEvidence(immutable.Map("input" -> reductionStr, "output" -> "true")) :: Nil,
//      Some("upper_equivalence")))
//    print("upper_equivalence.key equivalence lemma proof saved as lemma " + equivalenceLemmaID)
//  }
//
//  it should "prove Lemma 3 (Equivalence of two-sided explicit safe regions) from Lemma 3a (lower) and Lemma 3b (upper) bound equivalences" in {
//    // execute dependent tests if lemmas not already proved
//    if (!lemmaDB.contains("safe_equivalence")) {
//      println("Proving safe_equivalence lemma...")
//      runTest("ACAS X 2-sided safe should prove Lemma 3a: implicit-explicit lower equivalence", new Args(nilReporter))
//      println("...done")
//    }
//    if (!lemmaDB.contains("upper_equivalence")) {
//      println("Proving upper_equivalence lemma...")
//      runTest("ACAS X 2-sided safe should prove Lemma 3b: implicit-explicit upper equivalence", new Args(nilReporter))
//      println("...done")
//    }
//
//    beforeEach()
//
//    val lower = KeYmaeraXProblemParser(io.Source.fromFile(folder + "safe_equivalence.key").mkString)
//    val upper = KeYmaeraXProblemParser(io.Source.fromFile(folder + "upper_equivalence.key").mkString)
//
//    val Imply(lP@And(And(lPhp, And(lPrp, And(lPrv, Greater(la, lz)))), lPw), Equiv(lI, lE)) = lower
//
//    val Imply(uP@And(And(uPhp, And(uPrp, And(uPrv, Greater(ua, uz)))), uPw), Equiv(uI, uE)) = upper
//
//    lPhp shouldBe uPhp
//    lPrp shouldBe uPrp
//    lPrv shouldBe uPrv
//    lPw  shouldBe uPw
//    lz   shouldBe uz
//
//    // how to combine lower/upper equivalence
//    val combine = proveBy("(P() -> (B() <-> C())) & (P() -> (E() <-> F())) -> (P() -> (B()|E() <-> C()|F()))".asFormula, prop)
//    combine shouldBe 'proved
//
//    // lower: weaken unused a_up >= a_lo in p
//    val weaken = proveBy("(B() -> C()) -> (A() & B() -> C())".asFormula, prop)
//    weaken shouldBe 'proved
//
//    // upper: generalize a_up >= a_lo & a_lo > 0 to a_up > 0 in p
//    //@note can't just write (P() & aM>0) & W() -> C()) -> (aM>=a & (P() & a>0) & W() -> C()) because unification doesn't get it
//    val gen = proveBy("((hp > 0 & rp >= 0 & rv >= 0 & aM > 0) & W() -> C()) -> (aM>=a & ((hp > 0 & rp >= 0 & rv >= 0 & a > 0) & W()) -> C())".asFormula,
//      prop & hideL(-3) & hideL(-2) & hideR(1) & QE)
//    gen shouldBe 'proved
//
//    // load lemmas lower/upper equivalence
//    require(lemmaDB.contains("safe_equivalence"), "Lower equivalence lemma must be proved")
//    require(lemmaDB.contains("upper_equivalence"), "Upper equivalence lemma must be proved")
//
//    // cf. STTT: Lemma 3:
//    // P -> (C_impl <-> C_expl), where
//    //    C_impl == L_impl | U_impl,
//    //    C_expl == L_expl | U_expl,
//    //    P == aM>=a & (hp > 0 & rp >= 0 & rv >= 0 & a > 0) & (w=-1 | w=1)
//    val p = And(GreaterEqual(ua, la), lP)
//    val lemma3 = Imply(p, Equiv(Or(lI, uI), Or(lE, uE)))
//    val lemma3Proof = proveBy(lemma3,
//      useAt(combine, PosInExpr(1::Nil))(1) &
//        assertE(And(Imply(p, Equiv(lI, lE)), Imply(p, Equiv(uI, uE))), "Lemma 3: Unexpected form A")(1) &
//        useAt(weaken, PosInExpr(1::Nil))(1, 0::Nil) &
//        assertE(And(Imply(lP, Equiv(lI, lE)), Imply(p, Equiv(uI, uE))), "Lemma 3: Unexpected form B")(1) &
//        useAt(gen, PosInExpr(1::Nil))(1, 1::Nil) &
//        assertE(And(Imply(lP, Equiv(lI, lE)), Imply(uP, Equiv(uI, uE))), "Lemma 3: Unexpected form C")(1) &
//        andR(1) && (
//        by(LookupLemma(lemmaDB, "safe_equivalence").lemma),
//        by(LookupLemma(lemmaDB, "upper_equivalence").lemma))
//    )
//    lemma3Proof shouldBe 'proved
//
//    lemmaDB.add(Lemma(
//      lemma3Proof,
//      ToolEvidence(immutable.Map("input" -> lemma3.toString, "output" -> "true")) :: Nil,
//      Some("lemma3-safe_equivalence_lemma")))
//  }
//
//  it should "prove Lemma 3 fitting the form required by Corollary 3" in {
//    //@note alternative proof so that theorems and lemmas fit together, because twosided_implicit.key uses a>0 & aM>0 instead of aM>=a & a>0
//    //@note this proof stores two lemmas: the actual Lemma 3, and the intermediate step necessary for Corollary 3
//
//    // execute dependent tests if lemmas not already proved
//    if (!lemmaDB.contains("safe_equivalence")) {
//      println("Proving safe_equivalence lemma...")
//      runTest("ACAS X 2-sided safe should prove Lemma 3a: implicit-explicit lower equivalence", new Args(nilReporter))
//      println("...done")
//    }
//    if (!lemmaDB.contains("upper_equivalence")) {
//      println("Proving upper_equivalence lemma...")
//      runTest("ACAS X 2-sided safe should prove Lemma 3b: implicit-explicit upper equivalence", new Args(nilReporter))
//      println("...done")
//    }
//
//    beforeEach()
//
//    val lower = KeYmaeraXProblemParser(io.Source.fromFile(folder + "safe_equivalence.key").mkString)
//    val upper = KeYmaeraXProblemParser(io.Source.fromFile(folder + "upper_equivalence.key").mkString)
//
//    val Imply(lP@And(And(lPhp, And(lPrp, And(lPrv, Greater(la, lz)))), lPw), Equiv(lI, lE)) = lower
//
//    val Imply(uP@And(And(uPhp, And(uPrp, And(uPrv, Greater(ua, uz)))), uPw), Equiv(uI, uE)) = upper
//
//    lPhp shouldBe uPhp
//    lPrp shouldBe uPrp
//    lPrv shouldBe uPrv
//    lPw  shouldBe uPw
//    lz   shouldBe uz
//
//    // how to combine lower/upper equivalence
//    val combine = proveBy("(P() -> (B() <-> C())) & (P() -> (E() <-> F())) -> (P() -> (B()|E() <-> C()|F()))".asFormula, prop)
//    combine shouldBe 'proved
//
//    // upper: generalize a_up >= a_lo & a_lo > 0 to a_up > 0 in p
//    //@note can't just write (P() & aM>0) & W() -> C()) -> (aM>=a & (P() & a>0) & W() -> C()) because unification doesn't get it
//    val gen = proveBy("((hp > 0 & rp >= 0 & rv >= 0 & a>0 & aM > 0) & W() -> C()) -> (aM>=a & ((hp > 0 & rp >= 0 & rv >= 0 & a > 0) & W()) -> C())".asFormula,
//      prop & hideL(-3) & hideL(-2) & hideR(1) & QE)
//    gen shouldBe 'proved
//
//    val weakenLeft = proveBy("((hp > 0 & rp >= 0 & rv >= 0 & a>0) & W() -> C()) -> ((hp > 0 & rp >= 0 & rv >= 0 & a>0 & aM>0) & W() -> C())".asFormula,
//      prop & hideL(-3) & hideL(-2) & hideR(1) & QE)
//    weakenLeft shouldBe 'proved
//    val weakenRight = proveBy("((hp > 0 & rp >= 0 & rv >= 0 & aM>0) & W() -> C()) -> ((hp > 0 & rp >= 0 & rv >= 0 & a>0 & aM>0) & W() -> C())".asFormula,
//      prop & hideL(-3) & hideL(-2) & hideR(1) & QE)
//    weakenRight shouldBe 'proved
//
//    // load lemmas lower/upper equivalence
//    require(lemmaDB.contains("safe_equivalence"), "Lower equivalence lemma must be proved")
//    require(lemmaDB.contains("upper_equivalence"), "Upper equivalence lemma must be proved")
//
//    // cf. STTT: Lemma 3:
//    // P -> (C_impl <-> C_expl), where
//    //    C_impl == L_impl | U_impl,
//    //    C_expl == L_expl | U_expl,
//    //    P == aM>=a & (hp > 0 & rp >= 0 & rv >= 0 & a > 0) & (w=-1 | w=1)
//    val p = And(GreaterEqual(ua, la), lP)
//    val lemma3 = Imply(p, Equiv(Or(lI, uI), Or(lE, uE)))
//
//    // a>0 & aM>0
//    val q = And(And(lPhp, And(lPrp, And(lPrv, And(Greater(la, lz), Greater(ua, uz))))), lPw)
//    val intermediate = Imply(q, Equiv(Or(lI, uI), Or(lE, uE)))
//    val intermediateProof = proveBy(intermediate,
//      useAt(combine, PosInExpr(1::Nil))(1) &
//        assertE(And(Imply(q, Equiv(lI, lE)), Imply(q, Equiv(uI, uE))), "Lemma 3: Unexpected form A")(1) &
//        useAt(weakenLeft, PosInExpr(1::Nil))(1, 0::Nil) &
//        assertE(And(Imply(lP, Equiv(lI, lE)), Imply(q, Equiv(uI, uE))), "Lemma 3: Unexpected form B")(1) &
//        useAt(weakenRight, PosInExpr(1::Nil))(1, 1::Nil) &
//        assertE(And(Imply(lP, Equiv(lI, lE)), Imply(uP, Equiv(uI, uE))), "Lemma 3: Unexpected form C")(1) &
//        andR(1) && (
//        by(LookupLemma(lemmaDB, "safe_equivalence").lemma),
//        by(LookupLemma(lemmaDB, "upper_equivalence").lemma))
//    )
//    intermediateProof shouldBe 'proved
//    lemmaDB.add(Lemma(
//      intermediateProof,
//      ToolEvidence(immutable.Map("input" -> intermediate.toString, "output" -> "true")) :: Nil,
//      Some("lemma3-alt-safe_equivalence_lemma")))
//
//    val lemma3Proof = proveBy(lemma3,
//      useAt(gen, PosInExpr(1::Nil))(1) &
//        assertE(intermediate, "Lemma 3: Unexpected intermediate form")(1) &
//        by(intermediateProof)
//    )
//    lemma3Proof shouldBe 'proved
//
//    lemmaDB.add(Lemma(
//      lemma3Proof,
//      ToolEvidence(immutable.Map("input" -> lemma3.toString, "output" -> "true")) :: Nil,
//      Some("lemma3-safe_equivalence_lemma")))
//  }
//
//  it should "prove Corollary 3 (safety of explicit 2-sided regions) from Theorem 3 (implicit 2-sided safety) and Lemma 3 (implicit-explicit equivalence)" in {
//    val lemmaDB = LemmaDBFactory.lemmaDB
//    val nilReporter = new Reporter() { override def apply(event: Event): Unit = {} }
//    if (!(lemmaDB.contains("twosided_implicit") && lemmaDB.contains("twosided_implicit_usecase"))) {
//      println("Proving twosided_implicit lemma and twosided_implicit_usecase...")
//      runTest("ACAS X 2-sided safe should prove Theorem 3: correctness of implicit two-sided safe regions", new Args(nilReporter))
//      println("...done")
//    }
//    if (!lemmaDB.contains("lemma3-alt-safe_equivalence_lemma")) {
//      println("Proving lemma3-alt-safe_equivalence_lemma...")
//      runTest("ACAS X 2-sided safe should prove Lemma 3 fitting the form required by Corollary 3", new Args(nilReporter))
//      println("...done")
//    }
//
//    // rerun initialization (runTest runs afterEach() at the end)
//    beforeEach()
//
//    val implicitSafety = KeYmaeraXProblemParser(io.Source.fromFile(folder + "twosided_implicit.key").mkString)
//    val theorem3 = LookupLemma(lemmaDB, "twosided_implicit").lemma
//    theorem3.fact.conclusion shouldBe Sequent(Nil, IndexedSeq(), IndexedSeq(implicitSafety))
//
//    val lemma3 = LookupLemma(lemmaDB, "lemma3-alt-safe_equivalence_lemma").lemma
//
//    val Imply(And(a, w), Equiv(e, i)) = lemma3.fact.conclusion.succ.head
//    val Imply(And(p1, And(p2, _)), Box(Loop(Compose(Compose(Choice(maintain, Compose(prgA, Compose(prgB, Test(cimpl)))), act), ode)), And(u, _))) = implicitSafety
//
//    cimpl shouldBe i
//
//    val ucLoFact = LookupLemma(lemmaDB, "twosided_implicit_usecase").lemma.fact
//    val ucLoLemma = TactixLibrary.proveBy(Sequent(Nil, IndexedSeq(a, w, i), IndexedSeq(u)),
//      cut(ucLoFact.conclusion.succ.head) & onBranch(
//        (BranchLabels.cutShowLbl, cohide(2) & by(ucLoFact)),
//        (BranchLabels.cutUseLbl, implyL(-4) && (andR(2) && (andR(2) && (closeId, closeId), closeId), closeId) )
//      )
//    )
//    ucLoLemma.subgoals shouldBe ucLoFact.subgoals
//    if (!ucLoLemma.isProved) println("Proof will be partial. Prove other lemmas first")
//
//    val explicitPrg = Loop(Compose(Compose(Choice(maintain, Compose(prgA, Compose(prgB, Test(e)))), act), ode))
//
//    // explicit safety, construct from implicit safety and lemma 3 (equivalence)
//    val corollary3 = Imply(And(p1, And(p2, e)), Box(explicitPrg, And(u, e)))
//    println("Proving Corollary 3:\n" + corollary3.prettyString)
//
//    val proof = acasXcongruence(lemma3.fact, theorem3.fact, ucLoLemma, corollary3, QE)
//    println("Proof has " + proof.subgoals.size + " open goals")
//    proof shouldBe 'proved
//    proof.proved shouldBe Sequent(Nil, IndexedSeq(), IndexedSeq(corollary3))
//
//    lemmaDB.add(Lemma(proof,
//      ToolEvidence(immutable.Map("input" -> corollary3.prettyString, "output" -> "true")) :: Nil,
//      Some("twosided_explicit")))
//  }

}
