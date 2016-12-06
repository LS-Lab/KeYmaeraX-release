/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics.acasxhstp.safeable

import edu.cmu.cs.ls.keymaerax.btactics.acasxhstp.safeable.CondCongruence._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.BelleLabels._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleAbort, BelleExpr, PosInExpr}
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.arithmetic.speculative.ArithmeticSpeculativeSimplification
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.collection.immutable._
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

  it should "prove Theorem 3: correctness of implicit two-sided safe regions" in {
    if (lemmaDB.contains("twosided_implicit")) lemmaDB.remove("twosided_implicit")
    runLemmaTest("twosided_implicit_usecase", "ACAS X 2-sided safe should prove Theorem 3: uc lo lemma")
    runLemmaTest("2side_safe_upimplicit", "ACAS X 2-sided safe should prove Theorem 3, lemma up safe implicit")
    runLemmaTest("2side_safe_implicit", "ACAS X 2-sided safe should prove Theorem 3, lemma safe implicit")

    withMathematica { tool =>
      beforeEach()

      def applyLemma(formula: Formula, apply: BelleExpr) = cut(formula) & Idioms.<(
        (cutUse, dT("use Lemma " + formula) & SimplifierV2.simpTac('L, formula) & closeId & done)
        ,
        (cutShow, cohideR('Rlast, formula) & dT("apply Lemma " + formula) & apply)
      )

      val evolutionDomain =
        ("(( w * dhd >= w * dhf  | w * ao >= a ) &" +
          " ((w * dhd <= w * dhfM & w * ao <= aM) | w * ao <= 0))").asFormula

      val ode = "r'=-rv,h'=-dhd,dhd'=ao".asDifferentialProgram

      /** * Main safe theorem and its tactic ***/
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
          /*show*/ dT("Generalization Holds") & chase('R) & dT("After chase") & ((SimplifierV2.simpTac('R) & (andL('L) *)) *) & dT("Simplified") & normalize & done
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
              dT("Diff. Solution") & allR('R) & implyR('R) * 2 & (andL('L) *) &
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
  }

  it should "prove Lemma 3a: implicit-explicit lower equivalence" in {
    runLemmaTest("safe_equivalence", "ACAS X safe should prove Lemma 1: equivalence between implicit and explicit region formulation")
  }

  it should "prove Lemma 3b: implicit-explicit upper equivalence" in withMathematica { tool =>
    val reductionFml = KeYmaeraXProblemParser(io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/casestudies/acasx/sttt/upper_equivalence.kyx")).mkString)

    def caseSmasher(caseName: String): BelleExpr = dT(caseName) &
      //@note cases are not pairwise disjoint, meaning that simplifier can't fully simplify on case split; but we can simplify a little further still
      (andL('L)*) & (SimplifierV2.simpTac('Llike, "p_() -> q_()".asFormula)*) & (hideL('L, True)*) &
      (onAll(betaRule*)*) & onAll(dT(s"$caseName QE") & QE) & done

    def caseInst(caseName: String, tInst: String, roInst: String, hoInst: String): BelleExpr =
      dT(caseName) &
      allL("t".asVariable, tInst.asTerm)('L) &
      allL("ro".asVariable, roInst.asTerm)('L) &
      allL("ho".asVariable, hoInst.asTerm)('L) & dT(s"$caseName QE") &
      (onAll(betaRule*)*) & onAll(dT(s"$caseName QE") & QE) & done

    val rvp = max('L, "max(0, w*(dhfM - dhd))".asTerm) & equivR('R) & Idioms.<(
      dT("rv>0 ->") & normalize(skip, skip, skip) & Idioms.cases(
        //@note paper case-distinguishes >0 and <=0
        (Case("w*(dhd+w*maxAbbrv)>=0".asFormula), dT("Case >=0") & Idioms.cases(
            //@note cases are not exhaustive by themselves, only because succedent alternatives and when knowing almost everything else (except case knowledge)
            hideL('L, "(-rp<=r&r<=rp->w*h>hp)&(rp < r&r<=rp+rv*maxAbbrv/aM->w*rv^2*h>aM/2*(r-rp)^2+w*rv*dhd*(r-rp)+rv^2*hp)&(-rp<=r&r < -rp+rv*maxAbbrv/aM->w*rv^2*h>aM/2*(r+rp)^2+w*rv*dhd*(r+rp)+rv^2*hp)&(-rp+rv*maxAbbrv/aM<=r->w*rv*h>w*(dhd+w*maxAbbrv)*(r+rp)-rv*maxAbbrv^2/(2*aM)+rv*hp)".asFormula) &
            hideR('R, "w*h>w*ho+hp".asFormula) &
            ArithmeticSpeculativeSimplification.speculativeQE)(
          (Case("-rp<=r&r<=rp".asFormula), caseSmasher("-> >=0 Case 10")),
          (Case("rp < r&r<=rp+rv*maxAbbrv/aM".asFormula), caseSmasher("-> >=0 Case 11")),
          (Case("-rp<=r&r < -rp+rv*maxAbbrv/aM".asFormula), caseSmasher("-> >=0 Case 12")),
          (Case("-rp+rv*maxAbbrv/aM<=r".asFormula), caseSmasher("-> >=0 Case 13"))
        ) & dT("Case >=0 done") & done)
        ,
        (Case("w*(dhd+w*maxAbbrv)<0".asFormula), dT("Case <0") & Idioms.cases(
            //@note cases are not exhaustive by themselves, only because succedent alternatives and when knowing almost everything else (except case knowledge)
            hideL('L, "(-rp<=r&r<=rp->w*h>hp)&(rp < r&r<=rp+rv*maxAbbrv/aM->w*rv^2*h>aM/2*(r-rp)^2+w*rv*dhd*(r-rp)+rv^2*hp)&(rp+rv*maxAbbrv/aM<=r->w*rv*h>w*(dhd+w*maxAbbrv)*(r-rp)-rv*maxAbbrv^2/(2*aM)+rv*hp)".asFormula) &
            hideR('R, "w*h>w*ho+hp".asFormula) &
            ArithmeticSpeculativeSimplification.speculativeQE & dT("WTF???"))(
          (Case("-rp<=r&r<=rp".asFormula), caseSmasher("-> <0 Case 10")),
          (Case("rp < r&r<=rp+rv*maxAbbrv/aM".asFormula), caseSmasher("-> <0 Case 11")),
          (Case("rp+rv*maxAbbrv/aM<r".asFormula), caseSmasher("-> <0 Case 14"))
        ) & dT("Case <0 done") & done)
      ) & dT("rv>0 -> done") & done,
      dT("rv<0 <-") & Idioms.cases(
        (Case("w*(dhd+w*maxAbbrv)>=0".asFormula), dT("<- <0 Case >=0") & normalize(andR('R), skip, skip) & Idioms.<(
          /*-rp<=r&r<=rp*/ caseInst("<- >=0 Case 11", "0", "0", "0"),
          /*rp < r&r<=rp+rv*maxAbbrv/aM*/ caseInst("<- >=0 Case 11", "(r-rp)/rv", "r-rp", "(w * aM) / 2 * (r-rp)^2/rv^2 + dhd * (r-rp)/rv"),
          /*-rp<=r&r < -rp+rv*maxAbbrv/aM*/ caseInst("<- >=0 Case 12", "(r+rp)/rv", "r+rp", "(w * aM) / 2 * (r+rp)^2/rv^2 + dhd * (r+rp)/rv"),
          /*-rp+rv*maxAbbrv/aM<=r*/ caseInst("<- >=0 Case 13", "(r+rp)/rv", "r+rp", "(dhd+w*maxAbbrv)*(r+rp)/rv-w*maxAbbrv^2/(2*aM)")
        ) & dT("Case >=0 done") & done),
        (Case("w*(dhd+w*maxAbbrv)<0".asFormula), dT("<- <0 Case <0") & normalize(andR('R), skip, skip) & Idioms.<(
          /*"-rp<=r&r<=rp*/ dT("<- <0 Case 10") & caseInst("<- <0 Case 10", "0", "0", "0"),
          /*rp < r&r<=rp+rv*maxAbbrv/aM*/ dT("<- <0 Case 11") & caseInst("<- <0 Case 11", "(r-rp)/rv", "r-rp", "(w * aM) / 2 * (r-rp)^2/rv^2 + dhd * (r-rp)/rv"),
          /*rp+rv*maxAbbrv/aM<r*/ dT("<- <0 Case 14") & caseInst("<- <0 Case 14", "(r-rp)/rv", "r-rp", "(dhd+w*maxAbbrv)*(r-rp)/rv-w*maxAbbrv^2/(2*aM)")
        ) & dT("Case <0 done") & done)
      ) & dT("rv<0 <- done") & done
    )

    val tactic =
      implyR('R) & (andL('L)*) & EqualityTactics.abbrv("max(0, w*(dhfM - dhd))".asTerm, Some(Variable("maxAbbrv"))) &
      cut("maxAbbrv>=0".asFormula) & Idioms.<(
        (cutShow, /*cohide2('L, "maxAbbrv=max(0, w*(dhfM - dhd))")('Rlast)*/ QE & dT("Show maxAbbrv>=0 done") & done)
        ,
        (cutUse, Idioms.cases(
          (Case("rv=0".asFormula), dT("rv=0 case") & atomicQE(equivR('R) | andR('R), dT("rv=0 QE case")) & done),
          (Case("rv>0".asFormula), dT("rv>0 case") & rvp & done)
        ))
    )

    val reductionProof = proveBy(reductionFml, tactic)
    reductionProof shouldBe 'proved
    storeLemma(reductionProof, Some("upper_equivalence"))
  }


//  it should "prove Lemma 3 (Equivalence of two-sided explicit safe regions) from Lemma 3a (lower) and Lemma 3b (upper) bound equivalences" in {
//    if (lemmaDB.contains("lemma3-safe_equivalence_lemma")) lemmaDB.remove("lemma3-safe_equivalence_lemma")
//    // execute dependent tests if lemmas not already proved
//    runLemmaTest("safe_equivalence", "ACAS X 2-sided safe should prove Lemma 3a: implicit-explicit lower equivalence")
//    runLemmaTest("upper_equivalence", "ACAS X 2-sided safe should prove Lemma 3b: implicit-explicit upper equivalence")
//
//    withMathematica { tool =>
//
//      beforeEach()
//
//      val lower = KeYmaeraXProblemParser(io.Source.fromInputStream(
//        getClass.getResourceAsStream("/examples/casestudies/acasx/sttt/safe_equivalence.kyx")).mkString)
//      val upper = KeYmaeraXProblemParser(io.Source.fromInputStream(
//        getClass.getResourceAsStream("/examples/casestudies/acasx/sttt/upper_equivalence.kyx")).mkString)
//
//      val Imply(lP@And(And(lPhp, And(lPrp, And(lPrv, Greater(la, lz)))), lPw), Equiv(lI, lE)) = lower
//
//      val Imply(uP@And(And(uPhp, And(uPrp, And(uPrv, Greater(ua, uz)))), uPw), Equiv(uI, uE)) = upper
//
//      lPhp shouldBe uPhp
//      lPrp shouldBe uPrp
//      lPrv shouldBe uPrv
//      lPw shouldBe uPw
//      lz shouldBe uz
//
//      // how to combine lower/upper equivalence
//      val combine = proveBy("(P() -> (B() <-> C())) & (P() -> (E() <-> F())) -> (P() -> (B()|E() <-> C()|F()))".asFormula, prop)
//      combine shouldBe 'proved
//
//      // lower: weaken unused a_up >= a_lo in p
//      val weaken = proveBy("(B() -> C()) -> (A() & B() -> C())".asFormula, prop)
//      weaken shouldBe 'proved
//
//      // upper: generalize a_up >= a_lo & a_lo > 0 to a_up > 0 in p
//      //@note can't just write (P() & aM>0) & W() -> C()) -> (aM>=a & (P() & a>0) & W() -> C()) because unification doesn't get it
//      val gen = proveBy("((hp > 0 & rp >= 0 & rv >= 0 & aM > 0) & W() -> C()) -> (aM>=a & ((hp > 0 & rp >= 0 & rv >= 0 & a > 0) & W()) -> C())".asFormula,
//        prop & hideL(-3) & hideL(-2) & hideR(1) & QE)
//      gen shouldBe 'proved
//
//      // cf. STTT: Lemma 3:
//      // P -> (C_impl <-> C_expl), where
//      //    C_impl == L_impl | U_impl,
//      //    C_expl == L_expl | U_expl,
//      //    P == aM>=a & (hp > 0 & rp >= 0 & rv >= 0 & a > 0) & (w=-1 | w=1)
//      val p = And(GreaterEqual(ua, la), lP)
//      val lemma3 = Imply(p, Equiv(Or(lI, uI), Or(lE, uE)))
//      val lemma3Proof = proveBy(lemma3,
//        useAt(combine, PosInExpr(1 :: Nil))(1) &
//          assertE(And(Imply(p, Equiv(lI, lE)), Imply(p, Equiv(uI, uE))), "Lemma 3: Unexpected form A")(1) &
//          useAt(weaken, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
//          assertE(And(Imply(lP, Equiv(lI, lE)), Imply(p, Equiv(uI, uE))), "Lemma 3: Unexpected form B")(1) &
//          useAt(gen, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
//          assertE(And(Imply(lP, Equiv(lI, lE)), Imply(uP, Equiv(uI, uE))), "Lemma 3: Unexpected form C")(1) &
//          andR(1) & Idioms.<(
//            by(lemmaDB.get("safe_equivalence").getOrElse(throw new BelleAbort("Incomplete", "Lower equivalence lemma must be proved"))),
//            by(lemmaDB.get("upper_equivalence").getOrElse(throw new BelleAbort("Incomplete", "Upper equivalence lemma must be proved"))))
//      )
//
//      lemma3Proof shouldBe 'proved
//      storeLemma(lemma3Proof, Some("lemma3-safe_equivalence_lemma"))
//    }
//  }
//
//  it should "prove Lemma 3 fitting the form required by Corollary 3" in {
//    //@note alternative proof so that theorems and lemmas fit together, because twosided_implicit.key uses a>0 & aM>0 instead of aM>=a & a>0
//    //@note this proof stores two lemmas: the actual Lemma 3, and the intermediate step necessary for Corollary 3
//
//    if (lemmaDB.contains("lemma3-safe_equivalence_lemma")) lemmaDB.remove("lemma3-safe_equivalence_lemma")
//    if (lemmaDB.contains("lemma3-alt-safe_equivalence_lemma")) lemmaDB.remove("lemma3-alt-safe_equivalence_lemma")
//
//    // execute dependent tests if lemmas not already proved
//    runLemmaTest("safe_equivalence", "ACAS X 2-sided safe should prove Lemma 3a: implicit-explicit lower equivalence")
//    runLemmaTest("upper_equivalence", "ACAS X 2-sided safe should prove Lemma 3b: implicit-explicit upper equivalence")
//
//    withMathematica { tool =>
//
//      beforeEach()
//
//      val lower = KeYmaeraXProblemParser(io.Source.fromInputStream(
//        getClass.getResourceAsStream("/examples/casestudies/acasx/sttt/safe_equivalence.kyx")).mkString)
//      val upper = KeYmaeraXProblemParser(io.Source.fromInputStream(
//        getClass.getResourceAsStream("/examples/casestudies/acasx/sttt/upper_equivalence.kyx")).mkString)
//
//      val Imply(lP@And(And(lPhp, And(lPrp, And(lPrv, Greater(la, lz)))), lPw), Equiv(lI, lE)) = lower
//
//      val Imply(uP@And(And(uPhp, And(uPrp, And(uPrv, Greater(ua, uz)))), uPw), Equiv(uI, uE)) = upper
//
//      lPhp shouldBe uPhp
//      lPrp shouldBe uPrp
//      lPrv shouldBe uPrv
//      lPw shouldBe uPw
//      lz shouldBe uz
//
//      // how to combine lower/upper equivalence
//      val combine = proveBy("(P() -> (B() <-> C())) & (P() -> (E() <-> F())) -> (P() -> (B()|E() <-> C()|F()))".asFormula, prop)
//      combine shouldBe 'proved
//
//      // upper: generalize a_up >= a_lo & a_lo > 0 to a_up > 0 in p
//      //@note can't just write (P() & aM>0) & W() -> C()) -> (aM>=a & (P() & a>0) & W() -> C()) because unification doesn't get it
//      val gen = proveBy("((hp > 0 & rp >= 0 & rv >= 0 & a>0 & aM > 0) & W() -> C()) -> (aM>=a & ((hp > 0 & rp >= 0 & rv >= 0 & a > 0) & W()) -> C())".asFormula,
//        prop & hideL(-3) & hideL(-2) & hideR(1) & QE)
//      gen shouldBe 'proved
//
//      val weakenLeft = proveBy("((hp > 0 & rp >= 0 & rv >= 0 & a>0) & W() -> C()) -> ((hp > 0 & rp >= 0 & rv >= 0 & a>0 & aM>0) & W() -> C())".asFormula,
//        prop & hideL(-3) & hideL(-2) & hideR(1) & QE)
//      weakenLeft shouldBe 'proved
//      val weakenRight = proveBy("((hp > 0 & rp >= 0 & rv >= 0 & aM>0) & W() -> C()) -> ((hp > 0 & rp >= 0 & rv >= 0 & a>0 & aM>0) & W() -> C())".asFormula,
//        prop & hideL(-3) & hideL(-2) & hideR(1) & QE)
//      weakenRight shouldBe 'proved
//
//      // cf. STTT: Lemma 3:
//      // P -> (C_impl <-> C_expl), where
//      //    C_impl == L_impl | U_impl,
//      //    C_expl == L_expl | U_expl,
//      //    P == aM>=a & (hp > 0 & rp >= 0 & rv >= 0 & a > 0) & (w=-1 | w=1)
//      val p = And(GreaterEqual(ua, la), lP)
//      val lemma3 = Imply(p, Equiv(Or(lI, uI), Or(lE, uE)))
//
//      // a>0 & aM>0
//      val q = And(And(lPhp, And(lPrp, And(lPrv, And(Greater(la, lz), Greater(ua, uz))))), lPw)
//      val intermediate = Imply(q, Equiv(Or(lI, uI), Or(lE, uE)))
//      val intermediateProof = proveBy(intermediate,
//        useAt(combine, PosInExpr(1 :: Nil))(1) &
//          assertE(And(Imply(q, Equiv(lI, lE)), Imply(q, Equiv(uI, uE))), "Lemma 3: Unexpected form A")(1) &
//          useAt(weakenLeft, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
//          assertE(And(Imply(lP, Equiv(lI, lE)), Imply(q, Equiv(uI, uE))), "Lemma 3: Unexpected form B")(1) &
//          useAt(weakenRight, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
//          assertE(And(Imply(lP, Equiv(lI, lE)), Imply(uP, Equiv(uI, uE))), "Lemma 3: Unexpected form C")(1) &
//          andR(1) & Idioms.<(
//          by(lemmaDB.get("safe_equivalence").getOrElse(throw new BelleAbort("Incomplete", "Lower equivalence lemma must be proved"))),
//          by(lemmaDB.get("upper_equivalence").getOrElse(throw new BelleAbort("Incomplete", "Upper equivalence lemma must be proved"))))
//      )
//      intermediateProof shouldBe 'proved
//      storeLemma(intermediateProof, Some("lemma3-alt-safe_equivalence_lemma"))
//
//      val lemma3Proof = proveBy(lemma3,
//        useAt(gen, PosInExpr(1 :: Nil))(1) &
//          assertE(intermediate, "Lemma 3: Unexpected intermediate form")(1) &
//          by(intermediateProof)
//      )
//
//      lemma3Proof shouldBe 'proved
//      storeLemma(lemma3Proof, Some("lemma3-safe_equivalence_lemma"))
//    }
//  }
//
//  it should "prove Corollary 3 (safety of explicit 2-sided regions) from Theorem 3 (implicit 2-sided safety) and Lemma 3 (implicit-explicit equivalence)" in {
//    if (lemmaDB.contains("twosided_explicit")) lemmaDB.remove("twosided_explicit")
//
//    runLemmaTest("twosided_implicit", "ACAS X 2-sided safe should prove Theorem 3: correctness of implicit two-sided safe regions")
//    runLemmaTest("twosided_implicit_usecase", "ACAS X 2-sided safe should prove Theorem 3: uc lo lemma")
//    runLemmaTest("lemma3-alt-safe_equivalence_lemma", "ACAS X 2-sided safe should prove Lemma 3 fitting the form required by Corollary 3")
//
//    withMathematica { tool =>
//
//      // rerun initialization (runTest runs afterEach() at the end)
//      beforeEach()
//
//      val implicitSafety = KeYmaeraXProblemParser(io.Source.fromInputStream(
//        getClass.getResourceAsStream("/examples/casestudies/acasx/sttt/twosided_implicit.kyx")).mkString)
//
//      val theorem3 = lemmaDB.get("twosided_implicit").getOrElse(throw new BelleAbort("Incomplete", "2-sided implicit safety must be proved"))
//      theorem3.fact.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(implicitSafety))
//
//      val lemma3 = lemmaDB.get("lemma3-alt-safe_equivalence_lemma").getOrElse(throw new BelleAbort("Incomplete", "2-sided implicit safety alternative must be proved"))
//
//      val Imply(And(a, w), Equiv(e, i)) = lemma3.fact.conclusion.succ.head
//      val Imply(And(p1, And(p2, _)), Box(Loop(Compose(Compose(Choice(maintain, Compose(prgA, Compose(prgB, Test(cimpl)))), act), ode)), And(u, _))) = implicitSafety
//
//      cimpl shouldBe i
//
//      val ucLoFact = lemmaDB.get("twosided_implicit_usecase").getOrElse(throw new BelleAbort("Incomplete", "2-sided implicit usecase must be proved")).fact
//      val ucLoLemma = TactixLibrary.proveBy(Sequent(IndexedSeq(a, w, i), IndexedSeq(u)),
//        cut(ucLoFact.conclusion.succ.head) & Idioms.<(
//          (cutShow, cohide(2) & by(ucLoFact)),
//          (cutUse, implyL(-4) & Idioms.<(andR(2) & Idioms.<(andR(2) & Idioms.<(closeId, closeId), closeId), closeId))
//        )
//      )
//      ucLoLemma.subgoals shouldBe ucLoFact.subgoals
//      if (!ucLoLemma.isProved) println("Proof will be partial. Prove other lemmas first")
//
//      val explicitPrg = Loop(Compose(Compose(Choice(maintain, Compose(prgA, Compose(prgB, Test(e)))), act), ode))
//
//      // explicit safety, construct from implicit safety and lemma 3 (equivalence)
//      val corollary3 = Imply(And(p1, And(p2, e)), Box(explicitPrg, And(u, e)))
//      println("Proving Corollary 3:\n" + corollary3.prettyString)
//
//      val proof: ProvableSig = acasXcongruence(lemma3.fact, theorem3.fact, ucLoLemma, corollary3, QE)
//      println("Proof has " + proof.subgoals.size + " open goals")
//      proof shouldBe 'proved
//      proof.proved shouldBe Sequent(IndexedSeq(), IndexedSeq(corollary3))
//
//      storeLemma(proof, Some("twosided_explicit"))
//    }
//  }

}
