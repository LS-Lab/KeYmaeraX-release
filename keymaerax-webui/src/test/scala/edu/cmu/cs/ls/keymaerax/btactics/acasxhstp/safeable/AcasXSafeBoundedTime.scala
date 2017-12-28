/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics.acasxhstp.safeable

import edu.cmu.cs.ls.keymaerax.btactics.acasxhstp.safeable.SharedTactics._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.BelleLabels._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleAbort, BelleExpr, PosInExpr}

import scala.collection.immutable._
import scala.language.postfixOps

/**
 * Proves Sect. 5.2: Safe Region for Subsequent Advisories - Bounded-Time Safe Regions
 *
 * Theorem 4: Correctness of bounded-time implicit safe regions
 * Lemma 4a: Equivalence of implicit lower and explicit lower region formulation
 * Lemma 4b: Equivalence of implicit upper and explicit upper region formulation
 * Lemma 4: Equivalence of implicit and explicit bounded-time region formulation
 * Corollary 3: Correctness of explicit bounded-time safe regions

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
class AcasXSafeBoundedTime extends AcasXBase {

  private val condImplLower =
    ("(\\forall t \\forall ro \\forall ho"+"\n"+
      " ((t<=tl-to | tl<0) &"+"\n"+
      "  ((0 <= t & t < max(0, w * (dhf - dhd)) / a &"+"\n"+
      "    ro = rv * t & ho = (w * a) / 2 * t^2 + dhd * t) |"+"\n"+
      "   (t >= max(0, w * (dhf - dhd)) / a &"+"\n"+
      "    ro = rv * t &"+"\n"+
      "    ho = dhf * t - w * max(0, w * (dhf - dhd))^2 / (2*a)))"+"\n"+
      "  -> (abs(r - ro) > rp | w * h < w * ho - hp))"+"\n"+
      ")").asFormula
  private val condImplUpper =
    ("(\\forall t \\forall ro \\forall ho"+"\n"+
      " ((t<=tl-to | tl<0) &"+"\n"+
      "  ((0 <= t & t < max(0, w * (dhfM - dhd)) / aM &"+"\n"+
      "    ro = rv * t &"+"\n"+
      "    ho = (w * aM) / 2 * t^2 + dhd * t) |"+"\n"+
      "   (t >= max(0, w * (dhfM - dhd)) / aM &"+"\n"+
      "    ro = rv * t &"+"\n"+
      "    ho = (dhd + w * max(0, w * (dhfM-dhd))) * t "+"\n"+
      "         - w * max(0, w * (dhfM - dhd))^2 / (2*aM)))"+"\n"+
      "  -> (abs(r - ro) > rp | w * h > w * ho + hp))"+"\n"+
      ")").asFormula
  private val condImpl = Or(condImplLower, condImplUpper)
  private val invariant = And(And("(w=-1 | w=1) & (to<=tl | tl<0)".asFormula, condImpl), "(hp > 0 & rp >= 0 & rv >= 0 & a > 0 & aM > 0)".asFormula)

  "ACAS X bounded time" should "prove Theorem 4: correctness of lower bound" in withQE { tool =>
    if (containsLemma("bounded_safe_implicit")) removeLemma("bounded_safe_implicit")

    val safeLemmaFormula =
      """maxI=max((0,w*(dhf-dhd)))	&
        |   t_>=0 &
        |   (t_+to<=tl|tl < 0) &
        |   \forall t \forall ro \forall ho ((t<=tl-to|tl < 0)&(0<=t&t < maxI/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxI/a&ro=rv*t&ho=dhf*t-w*maxI^2/(2*a))->abs(r-ro)>rp|w*h < w*ho-hp) &
        |   hp>0 &
        |   (w*dhd>=w*dhf|w*ao>=a) &
        |   (w*(ao*t_+dhd)>=w*dhf|w*ao>=a) &
        |   (w=-1|w=1) &
        |   rp>=0 &
        |   rv>=0 &
        |   a>0
        | ->
        |   \forall t \forall ro \forall ho ((t<=tl-(t_+to)|tl < 0)&(0<=t&t < max((0,w*(dhf-(ao*t_+dhd))))/a&ro=rv*t&ho=w*a/2*t^2+(ao*t_+dhd)*t|t>=max((0,w*(dhf-(ao*t_+dhd))))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-(ao*t_+dhd))))^2/(2*a))->abs((-rv)*t_+r-ro)>rp|w*(-(ao/2*t_^2+dhd*t_)+h) < w*ho-hp)""".stripMargin.asFormula

    val initDomain = "w*dhd>=w*dhf|w*ao>=a".asFormula

    val safeLemmaTac = dT("lemma") & implyR('R) & (andL('L)*) &
      dT("Before skolem") & (allR('R)*) & dT("After skolem") &
      implyR('R) & orR('R) &
      allL(Variable("t"), "t_+t".asTerm)('L) &
      allL(Variable("ro"), "rv*(t_+t)".asTerm)('L) &
      dT("Before cases") & Idioms.cases(QE)(
        (Case("0<=t_+t & t_+t<maxI/a".asFormula),
          dT("Goal 110") & hideL('L, initDomain) &
            allL(Variable("ho"), "w*a/2*(t_+t)^2 + dhd*(t_+t)".asTerm)('L)
            & dT("instantiate ho 1 Lo") &
            implyL('L, "(t_+t<=tl-to|tl < 0)&(0<=t_+t&t_+t < maxI/a&w*a/2*(t_+t)^2+dhd*(t_+t)=w*a/2*(t_+t)^2+dhd*(t_+t)|t_+t>=maxI/a&w*a/2*(t_+t)^2+dhd*(t_+t)=dhf*(t_+t)-w*maxI^2/(2*a))->abs(r-rv*(t_+t))>rp|w*h < w*(w*a/2*(t_+t)^2+dhd*(t_+t))-hp".asFormula)
            & Idioms.<(
            dT("left of -> 1 Lo") & andL('L) &
              hideR('R, "abs((-rv)*t_+r-ro)>rp".asFormula) & hideR('R, "w*(-(ao/2*t_^2+dhd*t_)+h)<w*ho-hp".asFormula) &
              atomicQE(onAll(betaRule)*, dT("tl 1 QE")) & done,
            dT("right of -> 1 Lo") &
              andL('L, "(t<=tl-(t_+to)|tl < 0)&(0<=t&t < max((0,w*(dhf-(ao*t_+dhd))))/a&ro=rv*t&ho=w*a/2*t^2+(ao*t_+dhd)*t|t>=max((0,w*(dhf-(ao*t_+dhd))))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-(ao*t_+dhd))))^2/(2*a))".asFormula) &
              hideL('L, "t<=tl-(t_+to)|tl < 0".asFormula) &
              atomicQE(onAll(betaRule)*, dT("tl 2 QE")) & done
          )
        ),
        (Case("t_+t>=maxI/a".asFormula),
          dT("final time in straight Lo") &
            allL(Variable("ho"), "dhf*(t_+t) - w*maxI^2/(2*a)".asTerm)('L) &
            dT("instantiate ho 2 Lo") &
            implyL('L, "(t_+t<=tl-to|tl < 0)&dhf*(t_+t)-w*maxI^2/(2*a)=dhf*(t_+t)-w*maxI^2/(2*a)->abs(r-rv*(t_+t))>rp|w*h < w*(dhf*(t_+t)-w*maxI^2/(2*a))-hp".asFormula)
            & Idioms.<(
              dT("left of -> 2 Lo") & andL('L) &
              cohideOnlyR('Rlast) &
              hideL('L, "maxI=max((0,w*(dhf-dhd)))".asFormula) &
              atomicQE(onAll(andR('R))*, dT("final time in straight Lo QE")) & done,
            dT("right of -> 2 Lo") &
              andL('L, "(t<=tl-(t_+to)|tl < 0)&(0<=t&t < max((0,w*(dhf-(ao*t_+dhd))))/a&ro=rv*t&ho=w*a/2*t^2+(ao*t_+dhd)*t|t>=max((0,w*(dhf-(ao*t_+dhd))))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-(ao*t_+dhd))))^2/(2*a))".asFormula) &
              hideL('L, "t_+to<=tl|tl < 0".asFormula) &
              atomicQE(onAll(betaRule)*, dT("right of -> 2 Lo QE")) & done
          )
        )
      )

    val safeLemma = proveBy(safeLemmaFormula, safeLemmaTac)
    safeLemma shouldBe 'proved
    storeLemma(safeLemma, "bounded_safe_implicit")
  }

  it should "prove Theorem 4: correctness of upper bound" in withQE { tool =>
    if (containsLemma("bounded_safe_upimplicit")) removeLemma("bounded_safe_upimplicit")

    //@todo same tactic as above (and probably as in twosided)

    val safeUpLemmaFormula =
      """maxIM=max((0,w*(dhfM-dhd))) &
        |   t_>=0 &
        |   (t_+to<=tl|tl < 0) &
        |   \forall t \forall ro \forall ho ((t<=tl-to|tl < 0)&(0<=t&t < maxIM/aM&ro=rv*t&ho=w*aM/2*t^2+dhd*t|t>=maxIM/aM&ro=rv*t&ho=(dhd+w*maxIM)*t-w*maxIM^2/(2*aM))->abs(r-ro)>rp|w*h>w*ho+hp) &
        |   hp>0 &
        |   (w*dhd<=w*dhfM&w*ao<=aM|w*ao<=0) &
        |   (w*(ao*t_+dhd)<=w*dhfM&w*ao<=aM|w*ao<=0) &
        |   (w=-1|w=1) &
        |   rp>=0 &
        |   rv>=0 &
        |   aM>0
        | ->
        |   \forall t \forall ro \forall ho ((t<=tl-(t_+to)|tl < 0)&(0<=t&t < max((0,w*(dhfM-(ao*t_+dhd))))/aM&ro=rv*t&ho=w*aM/2*t^2+(ao*t_+dhd)*t|t>=max((0,w*(dhfM-(ao*t_+dhd))))/aM&ro=rv*t&ho=(ao*t_+dhd+w*max((0,w*(dhfM-(ao*t_+dhd)))))*t-w*max((0,w*(dhfM-(ao*t_+dhd))))^2/(2*aM))->abs((-rv)*t_+r-ro)>rp|w*(-(ao/2*t_^2+dhd*t_)+h)>w*ho+hp)
        |""".stripMargin.asFormula

    val safeUpLemmaTac = dT("lemma Up") & implyR('R) & (andL('L)*) &
      dT("Before skolem Up") & (allR('R)*) & dT("After skolem Up") &
      implyR('R) & orR('R) &
      allL(Variable("t"), "t_+t".asTerm)('L) &
      allL(Variable("ro"), "rv*(t_+t)".asTerm)('L) &
      dT("Before cases") & Idioms.cases(QE)(
      (Case("0<=t_+t&t_+t<maxIM/aM".asFormula),
        dT("final time in parabola") &
          allL(Variable("ho"), "w*aM/2*(t_+t)^2+dhd*(t_+t)".asTerm)('L) &
          dT("instantiate ho 1 Up") &
          implyL('L, " (t_+t<=tl-to|tl < 0)&(0<=t_+t&t_+t < maxIM/aM&w*aM/2*(t_+t)^2+dhd*(t_+t)=w*aM/2*(t_+t)^2+dhd*(t_+t)|t_+t>=maxIM/aM&w*aM/2*(t_+t)^2+dhd*(t_+t)=(dhd+w*maxIM)*(t_+t)-w*maxIM^2/(2*aM))->abs(r-rv*(t_+t))>rp|w*h>w*(w*aM/2*(t_+t)^2+dhd*(t_+t))+hp".asFormula)
          & Idioms.<(
            dT("left of -> 1 Up") &
            cohideOnlyR('Rlast) &
            hideL('L, "maxIM=max((0,w*(dhfM-dhd)))".asFormula) &
            atomicQE(onAll(andR('R))*, dT("tl 1 QE")) & done
            ,
            dT("right of -> 1 Up") &
            andL('L, "(t<=tl-(t_+to)|tl < 0)&(0<=t&t < max((0,w*(dhfM-(ao*t_+dhd))))/aM&ro=rv*t&ho=w*aM/2*t^2+(ao*t_+dhd)*t|t>=max((0,w*(dhfM-(ao*t_+dhd))))/aM&ro=rv*t&ho=(ao*t_+dhd+w*max((0,w*(dhfM-(ao*t_+dhd)))))*t-w*max((0,w*(dhfM-(ao*t_+dhd))))^2/(2*aM))".asFormula) &
            hideL('L, "t<=tl-(t_+to)|tl < 0".asFormula) &
            atomicQE(onAll(orL('L))*, dT("right of -> 1 Up QE")) & done
        )
      ),
      (Case("t_+t>=maxIM/aM".asFormula),
        dT("final time in straight Up") &
          allL(Variable("ho"), "(dhd+w*maxIM)*(t_+t)-w*maxIM^2/(2*aM)".asTerm)('L) &
          dT("instantiate ho 2 Lo") &
          implyL('L, "(t_+t<=tl-to|tl < 0)&(dhd+w*maxIM)*(t_+t)-w*maxIM^2/(2*aM)=(dhd+w*maxIM)*(t_+t)-w*maxIM^2/(2*aM)->abs(r-rv*(t_+t))>rp|w*h>w*((dhd+w*maxIM)*(t_+t)-w*maxIM^2/(2*aM))+hp".asFormula)
          & Idioms.<(
          dT("left of -> 2 Up") &
            cohideOnlyR('Rlast) &
            hideL('L, "maxIM=max((0,w*(dhfM-dhd)))".asFormula) &
            atomicQE(onAll(andR('R))*, dT("left of -> 2 Up QE")) & done,
          dT("right of -> 2 Up") &
            andL('L, "(t<=tl-(t_+to)|tl < 0)&(0<=t&t < max((0,w*(dhfM-(ao*t_+dhd))))/aM&ro=rv*t&ho=w*aM/2*t^2+(ao*t_+dhd)*t|t>=max((0,w*(dhfM-(ao*t_+dhd))))/aM&ro=rv*t&ho=(ao*t_+dhd+w*max((0,w*(dhfM-(ao*t_+dhd)))))*t-w*max((0,w*(dhfM-(ao*t_+dhd))))^2/(2*aM))".asFormula) &
            hideL('L, "t<=tl-(t_+to)|tl < 0".asFormula) &
            atomicQE(onAll(orL('L))*, dT("right of -> 2 Up QE")) & done
        )
      )
    )

    val safeUpLemma = proveBy(safeUpLemmaFormula, safeUpLemmaTac)
    safeUpLemma shouldBe 'proved
    storeLemma(safeUpLemma, "bounded_safe_upimplicit")
  }

  it should "prove Theorem 4: use case lemma" in withQE { tool =>
    if (containsLemma("bounded_implicit_usecase")) removeLemma("bounded_implicit_usecase")
    val ucLoLemma = proveBy(Imply(invariant, "(abs(r)>rp|abs(h)>hp)".asFormula),
      implyR('R) & (andL('L)*) & SharedTactics.ucLoTac(condImpl))
    ucLoLemma shouldBe 'proved
    storeLemma(ucLoLemma, "bounded_implicit_usecase")
  }

  it should "prove Theorem 4: correctness of implicit bounded-time safe regions" in withQE { tool =>
    if (containsLemma("user/bounded_implicit")) removeLemma("user/bounded_implicit")

    runLemmaTest("bounded_implicit_usecase", "ACAS X bounded time should prove Theorem 4: use case lemma")
    runLemmaTest("bounded_safe_implicit", "ACAS X bounded time should prove Theorem 4: correctness of lower bound")
    runLemmaTest("bounded_safe_upimplicit", "ACAS X bounded time should prove Theorem 4: correctness of upper bound")

    val evolutionDomain = ("((to<=tl | tl<0) &"+
      "(( w * dhd >= w * dhf  | w * ao >= a ) &" +
      " ((w * dhd <= w * dhfM & w * ao <= aM) | w * ao <= 0)))").asFormula

    /*** Main safe theorem and its tactic ***/
    val safeImplicitTLFormula = KeYmaeraXProblemParser( io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/casestudies/acasx/sttt/bounded_implicit.kyx")).mkString)

    val safeTac = implyR('R) & andL('L) &
      DLBySubst.loop(invariant, skip)('R) & Idioms.<(
      (initCase, dT("Base case") & prop & done),
      (useCase, dT("Use case") & hideL('L, "hp>0&rp>=0&rv>=0&a>0&aM>0".asFormula) &
        andR('R) & Idioms.<(
          implyRi & useLemma("bounded_implicit_usecase", None),
          andL('L) & closeId
        ) & done),
      (indStep, dT("Step") & hideL('L, "hp>0&rp>=0&rv>=0&a>0&aM>0".asFormula) & composeb('R) & generalize(invariant)('R) & Idioms.<(
        /*show*/ dT("Generalization Holds") &
          dT("1.21") & chase('R) & dT("After chase") & ((SimplifierV2.simpTac('R) & (andL('L) *)) *) & dT("Simplified") & closeT & done
        ,
        /*use*/ dT("Generalization Strong Enough") & Idioms.cases(
          (Case(Not(evolutionDomain)),
            DifferentialTactics.diffUnpackEvolutionDomainInitially('R) & notL('L) & closeId & done)
          ,
          (Case(evolutionDomain),
            dT("Before diff. solution") &
              EqualityTactics.abbrv("max(0,w*(dhf-dhd))".asTerm, Some(Variable("maxI"))) &
              EqualityTactics.abbrv("max(0,w*(dhfM-dhd))".asTerm, Some(Variable("maxIM"))) &
              solveEnd('R) &
              dT("Diff. Solution") & allR('R) & implyR('R)*2 & (andL('L)*) & dT("Now what?") & SimplifierV2.simpTac('R) & dT("Simplified 2") &
              orR('R) &
              (hideL('L, "to<=tl|tl < 0".asFormula)*) &
              orL('L, "\\forall t \\forall ro \\forall ho ((t<=tl-to|tl < 0)&(0<=t&t < maxI/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxI/a&ro=rv*t&ho=dhf*t-w*maxI^2/(2*a))->abs(r-ro)>rp|w*h < w*ho-hp)|\\forall t \\forall ro \\forall ho ((t<=tl-to|tl < 0)&(0<=t&t < maxIM/aM&ro=rv*t&ho=w*aM/2*t^2+dhd*t|t>=maxIM/aM&ro=rv*t&ho=(dhd+w*maxIM)*t-w*maxIM^2/(2*aM))->abs(r-ro)>rp|w*h>w*ho+hp)".asFormula)
              & Idioms.<(
                dT("Before hide lower") &
                  hideL('L, "maxIM=max((0,w*(dhfM-dhd)))".asFormula) & hideL('L, "aM>0".asFormula) &
                  hideL('L, "w*dhd<=w*dhfM&w*ao<=aM|w*ao<=0".asFormula) &
                  hideL('L, "w*(ao*t_+dhd)<=w*dhfM&w*ao<=aM|w*ao<=0".asFormula) &
                  hideR('R, "\\forall t \\forall ro \\forall ho ((t<=tl-(t_+to)|tl < 0)&(0<=t&t < max(0,w*(dhfM-(ao*t_+dhd)))/aM&ro=rv*t&ho=w*aM/2*t^2+(ao*t_+dhd)*t|t>=max(0,w*(dhfM-(ao*t_+dhd)))/aM&ro=rv*t&ho=(ao*t_+dhd+w*max(0,w*(dhfM-(ao*t_+dhd))))*t-w*max(0,w*(dhfM-(ao*t_+dhd)))^2/(2*aM))->abs((-rv)*t_+r-ro)>rp|w*(-(ao/2*t_^2+dhd*t_)+h)>w*ho+hp)".asFormula) &
                  dT("lower lemma") &
                  useLemma("bounded_safe_implicit", Some(prop)),
                dT("Before hide upper") &
                  hideL('L, "maxI=max((0,w*(dhf-dhd)))".asFormula) & hideL('L, "a>0".asFormula) &
                  hideL('L, "w*dhd>=w*dhf|w*ao>=a".asFormula) &
                  hideL('L, "w*(ao*t_+dhd)>=w*dhf|w*ao>=a".asFormula) &
                  hideR('R, "\\forall t \\forall ro \\forall ho ((t<=tl-(t_+to)|tl < 0)&(0<=t&t < max(0,w*(dhf-(ao*t_+dhd)))/a&ro=rv*t&ho=w*a/2*t^2+(ao*t_+dhd)*t|t>=max(0,w*(dhf-(ao*t_+dhd)))/a&ro=rv*t&ho=dhf*t-w*max(0,w*(dhf-(ao*t_+dhd)))^2/(2*a))->abs((-rv)*t_+r-ro)>rp|w*(-(ao/2*t_^2+dhd*t_)+h) < w*ho-hp)".asFormula) &
                  dT("upper lemma") &
                  useLemma("bounded_safe_upimplicit", Some(prop))
                )
          )
        )
        /* End cutUseLbl "Generalization strong enough" */
      )) /* End indStepLbl */
    )

    val safeTheorem = proveBy(safeImplicitTLFormula, safeTac)
    safeTheorem shouldBe 'proved
    storeLemma(safeTheorem, "bounded_implicit")
  }

  it should "prove Lemma 4a: time-limited implicit-explicit lower equivalence" in withQE { tool =>
    if (containsLemma("bounded_lower_equivalence")) removeLemma("bounded_lower_equivalence")

    val reductionFml = KeYmaeraXProblemParser(io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/casestudies/acasx/sttt/bounded_lower_equivalence.kyx")).mkString)

    def lweqvA(b:BelleExpr,s:BelleExpr,v:BelleExpr) =
        EqualityTactics.abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxA"))) &
        max('L, "max(0,w*(dhf-dhd))".asTerm) &
        andR('R) & Idioms.<(
          implyR('R) & andR('R) & Idioms.<(
              dT("<- 1") & min('R, "min(0,w*dhd)".asTerm) & implyR('R) & (andL('L)*) & Idioms.cases(QE)(
                (Case("rv=0".asFormula), dT("<- 1:rv=0") &
                  allTRoHoL("<- 1:rv=0", "0", "rv*0", "w*a/2*0^2+dhd*0") & b)
                ,
                (Case("rv>0".asFormula), dT("<- 1:rv>0") &
                  allTRoHoL("<- 1:rv>0", "(r+rp)/rv", "rv*((r+rp)/rv)", "w*a/2*((r+rp)/rv)^2+dhd*((r+rp)/rv)") & b/*d*/)
              )
              ,
              andR('R) & Idioms.<(
                dT("<- 2") &
                EqualityTactics.abbrv("min((0,w*dhd))".asTerm, Some(Variable("minA"))) &
                min('L, "min((0,w*dhd))".asTerm) &
                implyR('R) & (andL('L)*) &
                Idioms.cases(QE)(
                  (Case("rv=0".asFormula), dT("<- 2:rv=0") &
                    allTRoHoL("<- 2:rv=0", "-minA/a", "rv*(-minA/a)", "w*a/2*(-minA/a)^2+dhd*(-minA/a)") & b/*f*/)
                  ,
                  (Case("rv>0".asFormula), dT("<- 2:rv>0") &
                    allTRoHoL("<- 2:rv>0", "-minA/a", "rv*(-minA/a)", "w*a/2*(-minA/a)^2+dhd*(-minA/a)") & b/*h*/)
                )
                ,
                andR('R) & Idioms.<(
                  dT("<- 3") & min('R, "min(0,w*dhd)".asTerm) & implyR('R)  & (andL('L)*) &
                  Idioms.cases(QE)(
                    (Case("rv=0".asFormula), dT("<- 3:rv=0") &
                      allTRoHoL("<- 3:rv=0", "0", "rv*0", "w*a/2*0^2+dhd*0") & b/*j*/)
                    ,
                    (Case("rv>0".asFormula), dT("<- 3:rv>0") &
                      allTRoHoL("<- 3:rv>0", "(r-rp)/rv", "rv*((r-rp)/rv)", "w*a/2*((r-rp)/rv)^2+dhd*((r-rp)/rv)") & b/*l*/)
                  )
                      ,
                      dT("<- 4") & implyR('R)  & Idioms.cases(QE)(
                        (Case("rv=0".asFormula), dT("<- 4:rv=0") & closeT)
                        ,
                        (Case("rv>0".asFormula), dT("<- 4:rv>0") &
                          allTRoHoL("<- 4:rv>0", "(r-rp)/rv", "rv*((r-rp)/rv)", "dhf*((r-rp)/rv)-w*maxA^2/(2*a)") & b/*n*/)
                      )
                      )
                  )
              )
          ,
          implyR('R) & andR('R) & Idioms.<(
            dT("<- 5") & implyR('R) &
              Idioms.cases(QE)(
                (Case("rv=0".asFormula), dT("<- 5:rv=0") &
                  allTRoHoL("<- 5:rv=0", "0", "0", "0") & b/*p*/),
                (Case("rv>0".asFormula), dT("<- 5:rv>0") &
                  allTRoHoL("<- 5:rv>0", "(r+rp)/rv", "rv*((r+rp)/rv)", "w*a/2*((r+rp)/rv)^2+dhd*((r+rp)/rv)") & b/*r*/)
              )
            ,
              dT("<- 6") &
              Idioms.cases(QE)(
                (Case("rv=0".asFormula), dT("<- 6:rv=0") &
                  Idioms.cases(QE)(
                    (Case("r>rp".asFormula), closeT),
                    (Case("r<=rp".asFormula), s)
                  )
                )
                ,
                (Case("rv>0".asFormula), dT("<- 6:rv>0") & v)
              )
          )
        )

    val tactic = implyR('R) & equivR('R) & Idioms.<(
      dT("Case ->") &
        (allR('R)*) & dT("After Case -> skolemize") & implyR('R)  &
        andL('L, "(t<=tl-to|tl < 0)&(0<=t&t < max((0,w*(dhf-dhd)))/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=max((0,w*(dhf-dhd)))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-dhd)))^2/(2*a))".asFormula) &
        orL('L, "tl-to < 0&tl>=0|(w*dhf>=0->((-rp<=r&r < -rp-rv*min((0,w*dhd))/a)&(r<=-rp+rv*(tl-to)|tl < 0)->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp)&((-rp-rv*min((0,w*dhd))/a<=r&r<=rp-rv*min((0,w*dhd))/a)&(-min((0,w*dhd))/a<=tl-to|tl < 0)->w*h < (-min((0,w*dhd))^2)/(2*a)-hp)&((rp-rv*min((0,w*dhd))/a < r&r<=rp+rv*max((0,w*(dhf-dhd)))/a)&(r<=rp+rv*(tl-to)|tl < 0)->w*rv^2*h < a/2*(r-rp)^2+w*rv*dhd*(r-rp)-rv^2*hp)&(rp+rv*max((0,w*(dhf-dhd)))/a < r&(r<=rp+rv*(tl-to)|tl < 0)->rv=0|w*rv*h < w*dhf*(r-rp)-rv*max((0,w*(dhf-dhd)))^2/(2*a)-rv*hp))&(w*dhf < 0->((-rp<=r&r < -rp+rv*max((0,w*(dhf-dhd)))/a)&(r < -rp+rv*(tl-to)|tl < 0)->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp)&(-rp+rv*max((0,w*(dhf-dhd)))/a<=r&(r < -rp+rv*(tl-to)|tl < 0)->rv=0&r>rp|w*rv*h < w*dhf*(r+rp)-rv*max((0,w*(dhf-dhd)))^2/(2*a)-rv*hp)&((-rp+rv*(tl-to)<=r&r<=rp+rv*(tl-to))&tl>=0->tl-to<0|0<=tl-to&tl-to<=max((0,w*(dhf-dhd)))/a&w*h < a/2*(tl-to)^2+w*dhd*(tl-to)-hp|tl-to>max((0,w*(dhf-dhd)))/a&w*h < w*dhf*(tl-to)-max((0,w*(dhf-dhd)))^2/(2*a)-hp))".asFormula) & Idioms.<(
          dT("-> : tl-to < 0&tl>=0") &
          Idioms.rememberAs("ACASX_Bounded_Case_Imply0",
            Idioms.cases(QE)(
              (Case("t <= tl-to".asFormula), atomicQE(onAll(orL('L))*, dT("-> : tl-to < 0&tl>=0 QE")) & done)
              ,
              (Case("tl < 0".asFormula),
                hideL('L, "0<=t&t < max((0,w*(dhf-dhd)))/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=max((0,w*(dhf-dhd)))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-dhd)))^2/(2*a)".asFormula) & QE)
              )
          )
          ,
          dT("-> unlimited-time lower equiv") & Idioms.cases(QE)(
            (Case("w*dhf>=0".asFormula),
              dT("Case w*dhf>=0") &
              (andL('L)*) &
              EqualityTactics.abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxA"))) &
              EqualityTactics.abbrv("min((0,w*dhd))".asTerm, Some(Variable("minA"))) &
              max('L, "max(0,w*(dhf-dhd))".asTerm) &
              min('L, "min(0,w*dhd)".asTerm) &
              abs('R, "abs(r-ro)".asTerm) & Idioms.cases(QE)(
                (Case("r < -rp".asFormula), dT("-> 0:r<-rp") & (hideL('Llike, "p_()&q_() -> r_()".asFormula)*3) & QE & done),
                (Case("-rp<=r&r < -rp-rv*minA/a".asFormula), dT("-> 1:(-rp<=r & r < -rp-rv*minA/a)") &
                  (hideL('Llike, "p_()&q_() -> r_()".asFormula)*3) &
                  Idioms.rememberAs("ACASX_Bounded_Case_Imply1",
                    implyL('L, "(r<=-rp+rv*(tl-to)|tl < 0->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp)".asFormula) & Idioms.<(
                      QE & done
                      ,
                      atomicQE(ArithmeticLibrary.exhaustiveBeta, dT("-> 1:(-rp<=r & r < -rp-rv*minA/a) QE")) & done
                    ) & done)
                ),
                (Case("-rp-rv*minA/a<=r&r<=rp-rv*minA/a".asFormula), dT("-> 2: -rp-rv*minA/a<=r&r<=rp-rv*minA/a") &
                  (hideL('Llike, "p_()&q_() -> r_()".asFormula)*3) &
                  Idioms.rememberAs("ACASX_Bounded_Case_Imply2",
                    implyL('L, "-minA/a<=tl-to|tl < 0->w*h < (-minA^2)/(2*a)-hp".asFormula) & Idioms.<(
                      QE & done,
                      atomicQE(ArithmeticLibrary.exhaustiveBeta, dT("-> 2: -rp-rv*minA/a<=r&r<=rp-rv*minA/a QE")) & done
                    ) & done)
                ),
                (Case("rp-rv*minA/a < r&r<=rp+rv*maxA/a".asFormula), dT("-> 3: rv*minA/a<=r&r<=rp-rv*minA/") &
                  (hideL('Llike, "p_()&q_() -> r_()".asFormula)*3) &
                  Idioms.rememberAs("ACASX_Bounded_Case_Imply3",
                    atomicQE(ArithmeticLibrary.exhaustiveBeta, dT("-> 3 QE")) & done
                  )
                ),
                (Case("rp+rv*maxA/a < r".asFormula), dT("-> 4: rp+rv*maxA/a < r") &
                  (hideL('Llike, "p_()&q_() -> r_()".asFormula)*2) &
                  Idioms.rememberAs("ACASX_Bounded_Case_Imply4",
                    atomicQE(ArithmeticLibrary.exhaustiveBeta, dT("-> 4 QE")) & done)
                )
              )
            )
            ,
            (Case("w*dhf<0".asFormula), dT("w*dhf<0") &
              (andL('L)*) &
              EqualityTactics.abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxA"))) &
              max('L, "max(0,w*(dhf-dhd))".asTerm) &
              abs('R, "abs(r-ro)".asTerm) &
              Idioms.cases(QE)(
                (Case("(r< -rp)&(r< -rp+rv*(tl-to)&tl>=0|tl<0)".asFormula), dT("-> 4-5") &
                  (hideL('Llike, "p_()&q_() -> r_()".asFormula)*3) &
                  Idioms.rememberAs("ACASX_Bounded_Case_Imply4to5",
                    atomicQE(ArithmeticLibrary.exhaustiveBeta, dT("-> 4-5 QE")) & done
                  )
                ),
                (Case("(-rp<=r&r < -rp+rv*maxA/a)&(r< -rp+rv*(tl-to)|tl<0)".asFormula), dT("-> 5") &
                  (hideL('Llike, "p_()&q_() -> r_()".asFormula)*2) &
                  Idioms.rememberAs("ACASX_Bounded_Case_Imply5",
                    atomicQE(ArithmeticLibrary.exhaustivePropositional, dT("-> 5 QE")) & done)

                ),
                (Case("(-rp+rv*maxA/a<=r)&(r< -rp+rv*(tl-to)|tl<0)".asFormula), dT("-> 6") &
                  (hideL('Llike, "p_()&q_() -> r_()".asFormula)*2) &
                  Idioms.rememberAs("ACASX_Bounded_Case_Imply6",
                    atomicQE(ArithmeticLibrary.exhaustivePropositional, dT("-> 6 QE")) & done)
                ),
                (Case("(-rp+rv*(tl-to)<=r&r<=rp+rv*(tl-to))&(tl>=0)".asFormula), dT("-> 7") &
                  (hideL('Llike, "p_()&q_() -> r_()".asFormula)*2) &
                  Idioms.rememberAs("ACASX_Bounded_Case_Imply7",
                    atomicQE(ArithmeticLibrary.exhaustiveBeta, dT("-> 7 contradiction QE")) & done)
                ),
                (Case("(r>rp+rv*(tl-to))&(tl>=0)".asFormula),
                  dT("-> 8") &
                    (hideL('Llike, "p_()&q_() -> r_()".asFormula)*3) &
                    Idioms.rememberAs("ACASX_Bounded_Case_Imply8",
                    Idioms.cases(QE)(
                      (Case("rp=0".asFormula), orR('R) & hideR('R, "w*h < w*ho-hp".asFormula) & dT("-> 8 Case rp=0") & QE),
                      (Case("rp>0".asFormula), orL('L, "0<=t&t < maxA/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxA/a&ro=rv*t&ho=dhf*t-w*maxA^2/(2*a)".asFormula) & dT("-> 8 Case rp>0") & onAll(QE))
                    )
                  )
                )
              )
            )
          )
        )
      ,
      dT("<-") & Idioms.cases(QE)(
        (Case("tl<0".asFormula),
          dT("<- unlimited time lower equiv") &
          Idioms.rememberAs("ACASX_Bounded_TimeLowerA", lweqvA(
            ///////////// B
            QE,
            ///////////// S
            Idioms.cases(QE)(
              (Case("(h+w*maxA^2/(2*a))/dhf>=maxA/a".asFormula),
                allTRoHoL("S >= maxA/a", "(h+w*maxA^2/(2*a))/dhf", "0", "h") &
                implyL('L) & Idioms.<(cohideOnlyR('Rlast) & QE, QE)
              ),
              (Case("(h+w*maxA^2/(2*a))/dhf<maxA/a".asFormula),
                allTRoHoL("S < maxA/a", "maxA/a", "0", "dhf*maxA/a-w*maxA^2/(2*a)") &
                implyL('L) & Idioms.<(cohideOnlyR('Rlast) & QE, QE)
              )
            ),
            ///////////// V
            allTRoHoL("<- 6", "(r+rp)/rv", "rv*((r+rp)/rv)", "dhf*((r+rp)/rv)-w*maxA^2/(2*a)") & QE
        ))),
        (Case("tl>=0".asFormula), Idioms.cases(QE)(
          (Case("tl-to<0".asFormula), dT("tl>=0 Case tl-to<0") & QE),
          (Case("tl-to>=0".asFormula),
            dT("tl>=0 Case tl-to>=0") &
              Idioms.rememberAs("ACASX_Bounded_TimeLowerB", lweqvA(
                ///////////// B
                SimplifierV2.fullSimpTac & atomicQE(onAll(implyL('L))*, dT("B QE")),
                ///////////// S
                andR('R) & Idioms.<(
                  allTRoHoL("S inst", "-maxA/a", "rv*(-maxA/a)", "dhf*(-max/a)-w*max^2/(2*a)") & QE,
                  Idioms.cases(QE)(
                    (Case("tl-to > maxA/a".asFormula),
                      allTRoHoL("<- 7: 1", "tl-to", "rv*(tl-to)", "dhf*(tl-to)-w*maxA^2/(2*a)") &
                      SimplifierV2.fullSimpTac & atomicQE(onAll(implyL('L))*, dT("W QE")))
                    ,
                    (Case("tl-to <= maxA/a".asFormula),
                      allTRoHoL("<- 7: 2", "tl-to", "rv*(tl-to)", "w*a/2*(tl-to)^2+dhd*(tl-to)") &
                      SimplifierV2.fullSimpTac & atomicQE(onAll(implyL('L))*, dT("X QE")))
                  )
                ),
                ///////////// V
                (andL('L)*) & SimplifierV2.fullSimpTac & dT("<- V") &
                  andR('R) & Idioms.<(
                    implyR('R) &
                    allTRoHoL("<- 6", "(r+rp)/rv", "rv*((r+rp)/rv)", "dhf*((r+rp)/rv)-w*maxA^2/(2*a)") &
                    atomicQE(ArithmeticLibrary.varEliminationLeft("w".asVariable), dT("<- V QE 1")) & done
                    ,
                    implyR('R) & Idioms.cases(QE)(
                      (Case("tl-to > maxA/a".asFormula),
                        allTRoHoL("<- 7 A", "tl-to", "rv*(tl-to)", "dhf*(tl-to)-w*maxA^2/(2*a)") &
                        atomicQE(ArithmeticLibrary.varEliminationLeft("w".asVariable), dT("<- V QE 2")) & done
                      ),
                      (Case("tl-to <= maxA/a".asFormula),
                        allTRoHoL("<- 7 B", "tl-to", "rv*(tl-to)", "w*a/2*(tl-to)^2+dhd*(tl-to)") &
                        atomicQE(ArithmeticLibrary.varEliminationLeft("w".asVariable), dT("<- V QE 3")) & done)
                    )
                  )
              ))
          )
        ))
      )
    )

    val equivalence = proveBy(reductionFml, tactic)
    equivalence shouldBe 'proved
    storeLemma(equivalence, "bounded_lower_equivalence")
  }

  it should "prove Lemma 4b: time-limited implicit-explicit upper equivalence" in withQE { tool =>
    val reductionFml = KeYmaeraXProblemParser(io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/casestudies/acasx/sttt/bounded_upper_equivalence.kyx")).mkString)

    /*** Label Open Goals ***/
    def oG(s : String) = dT(s) // Tactics.SubLabelBranch(s)

    def substTactic0(hoString: String) = implyR(1) &
      allTRoHoL("substTactic0", "(r-rp)/rv", "(r-rp)", hoString) &
      implyL('L) & Idioms.<(
        oG("a") & andR('R) & onAll(QE)
        ,
        oG("b") & hideL('L, "maxAbbrv=max((0,w*(dhfM-dhd)))".asFormula) & QE)

    def substTactic1(hoString : String, hidePos: Int) =
      allTRoHoL("substTactic1", "(r+rp)/rv", "(r+rp)", hoString) &
      implyL('L) & Idioms.<(
        oG("__01___") & hideL('L, "maxAbbrv=max((0,w*(dhfM-dhd)))".asFormula) & QE
        ,
        oG("__02__") & orL('L) & onAll(QE)
        )

    def tac2() = implyR(1) & andR('R) & Idioms.<(
        oG("1.1") & implyR(1) & allTRoHoL("1.1", "0","0","0") & hideL(-1) & implyL('L) & Idioms.<(
            hideR(1) & hideL(-3) & hideL(-3) & QE
            ,
            hideL(-1) & hideL(-2) & QE
            )
        ,
        oG("1.2") & andR('R) & Idioms.<(
            oG("1.2.1") & substTactic0("(w * aM) / 2 * (r-rp)^2/rv^2 + dhd * (r-rp)/rv") & done
            ,
            oG("1.2.2") & implyR('R) & orR(1) & hideR('R,"rv=0".asFormula) &
              allTRoHoL("1.2.2", "(r-rp)/rv", "(r-rp)", "(dhd+w*maxAbbrv)*(r-rp)/rv-w*maxAbbrv^2/(2*aM)") & implyL('L) & Idioms.<(
              oG(" a ") & hideL('L,"maxAbbrv=max((0,w*(dhfM-dhd)))".asFormula) & QE
              ,
              oG(" b ") & hideL('L,"maxAbbrv=max((0,w*(dhfM-dhd)))".asFormula) & QE
              )
            )
        )

    def tac1() = implyR(1)  & andR('R) & Idioms.<(
        oG("1.1") & implyR(1) & allTRoHoL("1.1", "0","0","0") & hideL(-1) & implyL('L) & Idioms.<(
            hideR(1) & hideL(-3) & hideL(-3) & QE
            ,
            hideL(-1) & hideL(-2) & QE
            )
        ,
        oG("1.2") & andR('R) & Idioms.<(
            oG("1.2.1") & substTactic0("(w * aM) / 2 * (r-rp)^2/rv^2 + dhd * (r-rp)/rv") & done
            ,
            oG("1.2.2") & andR(1) & Idioms.<(
                oG("___0___") & implyR(1) & substTactic1("(w * aM) / 2 * (r+rp)^2/rv^2 + dhd * (r+rp)/rv",2)
                ,
                oG("___1___") & andR('R) & Idioms.<(
                  oG(" x ") & implyR('R) & orR('R) & hideR('R,"rv=0&r>rp".asFormula) &
                    allTRoHoL("", "(r+rp)/rv", "(r+rp)", "(dhd+w*maxAbbrv)*(r+rp)/rv-w*maxAbbrv^2/(2*aM)") &
                    implyL('L) & onAll(oG(" a ") & hideL('L,"maxAbbrv=max((0,w*(dhfM-dhd)))".asFormula) & QE)
                    ,
                    oG(" y ") & implyR('R) & orR('R) & orR('R) & andR('R,"(maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp)&(maxAbbrv/aM>tl-to->w*h>aM/2*(tl-to)^2+w*dhd*(tl-to)+hp)".asFormula) & Idioms.<(
                      oG(" T ") &
                        allTRoHoL(" T ", "tl-to", "rv*(tl-to)", "(dhd+w*maxAbbrv)*(tl-to)-w*maxAbbrv^2/(2*aM)") & implyL('L) & Idioms.<(
                          oG(" a ") & hideL('L,"maxAbbrv=max((0,w*(dhfM-dhd)))".asFormula) & QE
                          ,
                          oG(" b ") & hideR('R,"rv=0&r>rp".asFormula) & implyR('R,"maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp".asFormula) &
                            andL('L,"(hp>0&rp>=0&rv>=0&aM>0)&(w=-1|w=1)&(to<=tl|tl < 0)".asFormula) & andL('L,"(w=-1|w=1)&(to<=tl|tl < 0)".asFormula) &
                            orL('L,"(to<=tl|tl < 0)".asFormula) & Idioms.<(orL('L,"abs(r-rv*(tl-to))>rp|w*h>w*((dhd+w*maxAbbrv)*(tl-to)-w*maxAbbrv^2/(2*aM))+hp".asFormula) & Idioms.<(oG("bug") & QE,QE),QE)
                          )
                        ,
                        oG(" TT ") &
                          allTRoHoL(" TT ", "tl-to", "rv*(tl-to)", "w*aM/2*(tl-to)^2+dhd*(tl-to)") & implyL('L)
                          & Idioms.<(oG(" a ") & hideL('L,"maxAbbrv=max((0,w*(dhfM-dhd)))".asFormula) & QE
                          ,
                          oG(" b ") & hideR('R,"rv=0&r>rp".asFormula) & implyR('R,"maxAbbrv/aM > (tl-to) -> w * h > aM/2 * (tl-to)^2 + w * dhd * (tl-to) + hp".asFormula) & andL('L,"(hp>0&rp>=0&rv>=0&aM>0)&(w=-1|w=1)&(to<=tl|tl < 0)".asFormula) &
                            andL('L,"(w=-1|w=1)&(to<=tl|tl < 0)".asFormula) & orL('L,"(to<=tl|tl < 0)".asFormula) & Idioms.<(orL('L," abs(r-rv*(tl-to))>rp|w*h>w*(w*aM/2*(tl-to)^2+dhd*(tl-to))+hp".asFormula) & Idioms.<(oG("bug") & QE,QE),QE)
                          )
                        )
                    )
                )
            )
        )

    def tac1rv0() = implyR(1) & andR('R) & Idioms.<(
      oG("1.1") & allTRoHoL("1.1", "0","0","0") & hideL(-1) & QE
      ,
      oG("1.2") & andR('R) & Idioms.<(
        oG("A") & (hideL('L)*) & QE
        ,
        oG("B") & andR('R) & Idioms.<(
          oG("X") & (hideL('L)*) & QE
          ,
          oG("Y") & andR('R) & Idioms.<(
            oG("I") & implyR(1) & hideL(-1) & QE
              ,
              oG("II") & implyR(1) & Idioms.cases(QE)(
                (Case("maxAbbrv > aM*(tl-to)".asFormula),
                  oG(" i ") & allTRoHoL(" i ", "tl-to","0","w*aM/2*(tl-to)^2+dhd*(tl-to)") &
                    (andL('L)*) & atomicQE(ArithmeticLibrary.varEliminationLeft("w".asVariable)) & done
                ),
                (Case("maxAbbrv <= aM*(tl-to)".asFormula),
                  oG(" ii ") & allTRoHoL(" ii ", "tl-to","0","(dhd+w*maxAbbrv)*(tl-to)-w*maxAbbrv^2/(2*aM)") &
                    (andL('L)*) & atomicQE(ArithmeticLibrary.varEliminationLeft("w".asVariable)) & done
                )
              )
            )
          )
        )
      )

    def tac2rv0() = implyR(1) & andR('R) & Idioms.<(
        oG("2.1") & implyR(1) & allTRoHoL("2.1", "0","0","0") & implyL('L) & Idioms.<(
            oG("___0___") & hideL(-1) & QE
            ,
            oG("___1___") & hideL(-1) & QE
            )
        ,
        oG("2.2") & andR('R) & Idioms.<(
            oG("___0___") & (hideL('L)*) & QE
            ,
            oG("___1___") & hideL(-1) & QE
            )
        )

    def parabolaInfT() = (andL('L)*) &
      hideL('L,"maxAbbrv=max((0,w*(dhfM-dhd)))".asFormula) &
      atomicQE(ArithmeticLibrary.varEliminationLeft("w".asVariable))

    def nestedcutsQE1() = cut("rp < r&r<=rp+rv*maxAbbrv/aM->w*rv^2*h>aM/2*(r-rp)^2+w*rv*dhd*(r-rp)+rv^2*hp".asFormula) & Idioms.<(
      (cutShow, dT("QE1 Foo") & hideL('L,"-rp<=r&r < -rp+rv*maxAbbrv/aM&(r<=-rp+rv*(tl-to)|tl < 0)->w*rv^2*h>aM/2*(r+rp)^2+w*rv*dhd*(r+rp)+rv^2*hp".asFormula) &
        hideL('L,"-rp+rv*maxAbbrv/aM<=r&(r < -rp+rv*(tl-to)|tl < 0)->w*rv*h>w*(dhd+w*maxAbbrv)*(r+rp)-rv*maxAbbrv^2/(2*aM)+rv*hp".asFormula) &
        hideR('R,"abs(r-ro)>rp|w*h>w*ho+hp".asFormula) & hideR('R,"-rp+rv*(tl-to)<=r&r<=rp+rv*(tl-to)".asFormula) & QE),
      (cutUse, hideL('L,"rp < r&r<=rp+rv*maxAbbrv/aM&(r<=rp+rv*(tl-to)|tl < 0)->w*rv^2*h>aM/2*(r-rp)^2+w*rv*dhd*(r-rp)+rv^2*hp".asFormula) &
        cut("-rp<=r&r < -rp+rv*maxAbbrv/aM->w*rv^2*h>aM/2*(r+rp)^2+w*rv*dhd*(r+rp)+rv^2*hp".asFormula) & Idioms.<(
        (cutShow, dT("QE1 Bar") & hideL('L,"-rp+rv*maxAbbrv/aM<=r&(r < -rp+rv*(tl-to)|tl < 0)->w*rv*h>w*(dhd+w*maxAbbrv)*(r+rp)-rv*maxAbbrv^2/(2*aM)+rv*hp".asFormula) &
          hideL('L,"rp < r&r<=rp+rv*maxAbbrv/aM->w*rv^2*h>aM/2*(r-rp)^2+w*rv*dhd*(r-rp)+rv^2*hp".asFormula) &
          hideR('R,"abs(r-ro)>rp|w*h>w*ho+hp".asFormula) & hideR('R,"-rp+rv*(tl-to)<=r&r<=rp+rv*(tl-to)".asFormula) & QE),
        (cutUse, hideL('L,"-rp<=r&r < -rp+rv*maxAbbrv/aM&(r<=-rp+rv*(tl-to)|tl < 0)->w*rv^2*h>aM/2*(r+rp)^2+w*rv*dhd*(r+rp)+rv^2*hp".asFormula) &
          implyL('L,"-rp+rv*maxAbbrv/aM<=r&(r < -rp+rv*(tl-to)|tl < 0)->w*rv*h>w*(dhd+w*maxAbbrv)*(r+rp)-rv*maxAbbrv^2/(2*aM)+rv*hp".asFormula) & Idioms.<(
          oG("_______1") & hideL('L,"maxAbbrv=max((0,w*(dhfM-dhd)))".asFormula) &
            atomicQE(ArithmeticLibrary.varEliminationLeft("w".asVariable))
            ,
            oG("_______2") &
              Idioms.cases(QE)(
                (Case("aM*(r-rp)<=rv*maxAbbrv".asFormula),
                  implyL('L,"rp < r&r<=rp+rv*maxAbbrv/aM->w*rv^2*h>aM/2*(r-rp)^2+w*rv*dhd*(r-rp)+rv^2*hp".asFormula) & Idioms.<(
                    hideR('R,"-rp+rv*(tl-to)<=r&r<=rp+rv*(tl-to)".asFormula) &
                      hideL('L,"maxAbbrv=max((0,w*(dhfM-dhd)))".asFormula) &
                      atomicQE(ArithmeticLibrary.varEliminationLeft("w".asVariable))
                      ,
                      implyL('L,"-rp<=r&r < -rp+rv*maxAbbrv/aM->w*rv^2*h>aM/2*(r+rp)^2+w*rv*dhd*(r+rp)+rv^2*hp".asFormula) & Idioms.<(
                          oG("__A__") & hideR('R,"-rp+rv*(tl-to)<=r&r<=rp+rv*(tl-to)".asFormula) &
                            hideL('L,"maxAbbrv=max((0,w*(dhfM-dhd)))".asFormula) &
                            atomicQE(ArithmeticLibrary.varEliminationLeft("w".asVariable))
                          ,
                          oG("__B__") & hideL('L,"w*rv*h>w*(dhd+w*maxAbbrv)*(r+rp)-rv*maxAbbrv^2/(2*aM)+rv*hp".asFormula) &
                            hideR('R,"-rp+rv*(tl-to)<=r&r<=rp+rv*(tl-to)".asFormula) &
                            hideL('L,"maxAbbrv=max((0,w*(dhfM-dhd)))".asFormula) &
                            atomicQE(ArithmeticLibrary.varEliminationLeft("w".asVariable))
                        )
                    )
                ),
                (Case("aM*(r-rp) > rv*maxAbbrv".asFormula),
                  hideL('L,"-rp<=r&r < -rp+rv*maxAbbrv/aM->w*rv^2*h>aM/2*(r+rp)^2+w*rv*dhd*(r+rp)+rv^2*hp".asFormula) &
                  hideL('L,"maxAbbrv=max((0,w*(dhfM-dhd)))".asFormula) &
                  atomicQE(ArithmeticLibrary.varEliminationLeft("w".asVariable))
                )
              )
            )
          )
        )
      )
    )


    def nestedcutsQE() =
      cut("rp < r&r<=rp+rv*maxAbbrv/aM->w*rv^2*h>aM/2*(r-rp)^2+w*rv*dhd*(r-rp)+rv^2*hp".asFormula) & Idioms.<(
      (cutShow,
        hideL('L,"-rp<=r&r < -rp+rv*maxAbbrv/aM&(r<=-rp+rv*(tl-to)|tl < 0)->w*rv^2*h>aM/2*(r+rp)^2+w*rv*dhd*(r+rp)+rv^2*hp".asFormula) &
        hideL('L,"-rp+rv*maxAbbrv/aM<=r&(r < -rp+rv*(tl-to)|tl < 0)->w*rv*h>w*(dhd+w*maxAbbrv)*(r+rp)-rv*maxAbbrv^2/(2*aM)+rv*hp".asFormula) &
        hideL('L, "maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp".asFormula) &
        hideR('R, "abs(r-ro)>rp|w*h>w*ho+hp".asFormula) & atomicQE(ArithmeticLibrary.varEliminationLeft("w".asVariable))),
      (cutUse,
        dT("QE Foo") &
        hideL('L,"-rp+rv*maxAbbrv/aM<=r&(r < -rp+rv*(tl-to)|tl < 0)->w*rv*h>w*(dhd+w*maxAbbrv)*(r+rp)-rv*maxAbbrv^2/(2*aM)+rv*hp".asFormula) &
        cut("rp < r&r<=rp+rv*maxAbbrv/aM->w*rv^2*h>aM/2*(r-rp)^2+w*rv*dhd*(r-rp)+rv^2*hp".asFormula) & Idioms.<(
          (cutShow,
            dT("QE Bar") &
            hideL('L,"-rp<=r&r < -rp+rv*maxAbbrv/aM&(r<=-rp+rv*(tl-to)|tl < 0)->w*rv^2*h>aM/2*(r+rp)^2+w*rv*dhd*(r+rp)+rv^2*hp".asFormula) &
            hideL('L,"maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp".asFormula) &
            hideL('L, "rp < r&r<=rp+rv*maxAbbrv/aM&(r<=rp+rv*(tl-to)|tl < 0)->w*rv^2*h>aM/2*(r-rp)^2+w*rv*dhd*(r-rp)+rv^2*hp".asFormula) &
            hideR('R,"abs(r-ro)>rp|w*h>w*ho+hp".asFormula) & atomicQE(ArithmeticLibrary.varEliminationLeft("w".asVariable)))
              ,
          (cutUse,
            hideL('L,"rp < r&r<=rp+rv*maxAbbrv/aM&(r<=rp+rv*(tl-to)|tl < 0)->w*rv^2*h>aM/2*(r-rp)^2+w*rv*dhd*(r-rp)+rv^2*hp".asFormula) &
            oG("evenBetter") &
            cut("-rp<=r&r < -rp+rv*maxAbbrv/aM->w*rv^2*h>aM/2*(r+rp)^2+w*rv*dhd*(r+rp)+rv^2*hp".asFormula) & Idioms.<(
            (cutShow,
              hideL('L," maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp ".asFormula) &
              hideL('L,"rp < r&r<=rp+rv*maxAbbrv/aM->w*rv^2*h>aM/2*(r-rp)^2+w*rv*dhd*(r-rp)+rv^2*hp".asFormula) &
              hideL('L,"rp < r&r<=rp+rv*maxAbbrv/aM->w*rv^2*h>aM/2*(r-rp)^2+w*rv*dhd*(r-rp)+rv^2*hp".asFormula) &
              hideR('R,"abs(r-ro)>rp|w*h>w*ho+hp".asFormula) & QE),
            (cutUse,
              hideL('L,"-rp<=r&r < -rp+rv*maxAbbrv/aM&(r<=-rp+rv*(tl-to)|tl < 0)->w*rv^2*h>aM/2*(r+rp)^2+w*rv*dhd*(r+rp)+rv^2*hp".asFormula) &
              hideL('L,"maxAbbrv=max((0,w*(dhfM-dhd)))".asFormula) &
              atomicQE(ArithmeticLibrary.varEliminationLeft("w".asVariable))
              )
            )
          )
      )
      )
    )

    def lineTl() = (andL('L)*) &
      hideL('L,"rp < r&r<=rp+rv*maxAbbrv/aM&(r<=rp+rv*(tl-to)|tl < 0)->w*rv^2*h>aM/2*(r-rp)^2+w*rv*dhd*(r-rp)+rv^2*hp".asFormula) &
      hideL('L,"-rp<=r&r < -rp+rv*maxAbbrv/aM&(r<=-rp+rv*(tl-to)|tl < 0)->w*rv^2*h>aM/2*(r+rp)^2+w*rv*dhd*(r+rp)+rv^2*hp".asFormula) &
      hideL('L,"to<=tl|tl < 0".asFormula) & hideL('L,"maxAbbrv=max((0,w*(dhfM-dhd)))".asFormula) &
      atomicQE(ArithmeticLibrary.exhaustiveBeta, dT("lineTL QE")) & done

    def parabolaTl() = Idioms.rememberAs("ACASX_Bound_ParabolaTL", (andL('L)*) & hideL('L,"to<=tl|tl < 0".asFormula) &
      Idioms.cases(QE)(
        (Case("aM*(tl-to) < maxAbbrv".asFormula),
          oG("a") &
            implyL('L,"-rp+rv*(tl-to)<=r&r<=rp+rv*(tl-to)->tl < 0|(maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp)&(maxAbbrv/aM>tl-to->w*h>aM/2*(tl-to)^2+w*dhd*(tl-to)+hp)".asFormula) & Idioms.<(
            oG("hard") & hideL('L,"-rp+rv*maxAbbrv/aM<=r&(r < -rp+rv*(tl-to)|tl < 0)->w*rv*h>w*(dhd+w*maxAbbrv)*(r+rp)-rv*maxAbbrv^2/(2*aM)+rv*hp".asFormula) &
            hideL('L,"maxAbbrv=max((0,w*(dhfM-dhd)))".asFormula) &
            atomicQE(ArithmeticLibrary.varEliminationLeft("w".asVariable))
            ,
            orL('L,"tl < 0|(maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp)&(maxAbbrv/aM>tl-to->w*h>aM/2*(tl-to)^2+w*dhd*(tl-to)+hp)".asFormula) & Idioms.<(
              hideL('L,"maxAbbrv=max((0,w*(dhfM-dhd)))".asFormula) &
              atomicQE(ArithmeticLibrary.varEliminationLeft("w".asVariable))
              ,
              (andL('L)*) &
              hideL('L,"-rp+rv*maxAbbrv/aM<=r&(r < -rp+rv*(tl-to)|tl < 0)->w*rv*h>w*(dhd+w*maxAbbrv)*(r+rp)-rv*maxAbbrv^2/(2*aM)+rv*hp".asFormula) &
              hideL('L,"(maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp)".asFormula) &
              hideL('L,"maxAbbrv=max((0,w*(dhfM-dhd)))".asFormula) &
              atomicQE(ArithmeticLibrary.varEliminationLeft("w".asVariable))
            )
          )
        ),
        (Case("aM*(tl-to) >= maxAbbrv".asFormula),
          oG("b") & hideL('L,"t<=tl-to".asFormula) & implyL('L,"-rp+rv*(tl-to)<=r&r<=rp+rv*(tl-to)->tl < 0|(maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp)&(maxAbbrv/aM>tl-to->w*h>aM/2*(tl-to)^2+w*dhd*(tl-to)+hp)".asFormula) & Idioms.<(
            oG("hard") & nestedcutsQE1 & oG("hard DONE")
              ,
              orL('L,"tl < 0|(maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp)&(maxAbbrv/aM>tl-to->w*h>aM/2*(tl-to)^2+w*dhd*(tl-to)+hp)".asFormula) & Idioms.<(
                hideL('L,"maxAbbrv=max((0,w*(dhfM-dhd)))".asFormula) & atomicQE(ArithmeticLibrary.varEliminationLeft("w".asVariable))
                ,
                (andL('L)*) & nestedcutsQE & dT("hard 2 DONE")
                )
            )
        )
      ))


    def lineInfT() = (andL('L)*) & atomicQE(ArithmeticLibrary.varEliminationLeft("w".asVariable))

    def rvp() = Idioms.rememberAs("ACASX_Bound_rvp", oG("rv>0") & equivR('R) & Idioms.<(
      oG("(->)") & allR(1) & allR(1) & allR(1) & implyR(1)
        & Idioms.cases(QE)(
          (Case("w*(dhd+w*maxAbbrv)<=0".asFormula),
            oG("___ T1 ___") & (andL('L)*) &
            orL('L, "0<=t&t < maxAbbrv/aM&ro=rv*t&ho=w*aM/2*t^2+dhd*t|t>=maxAbbrv/aM&ro=rv*t&ho=(dhd+w*maxAbbrv)*t-w*maxAbbrv^2/(2*aM)".asFormula) & Idioms.<(
              oG("parabola") & hideL('L,"rp+rv*maxAbbrv/aM < r&(r<=rp+rv*(tl-to)|tl < 0)->w*rv*h>w*(dhd+w*maxAbbrv)*(r-rp)-rv*maxAbbrv^2/(2*aM)+rv*hp".asFormula) &
              orL('L,"t<=tl-to|tl < 0".asFormula) & onAll(
                oG(" i ")  & hideL('L,"maxAbbrv=max((0,w*(dhfM-dhd)))".asFormula) & QE)
              ,
              oG("line") & orL('L,"t<=tl-to|tl < 0".asFormula) & onAll(
                oG(" i ") & hideL('L,"maxAbbrv=max((0,w*(dhfM-dhd)))".asFormula) & QE)
            )
          ),
          (Case("w*(dhd+w*maxAbbrv) > 0".asFormula),
            oG("___ T2 ___") & (andL('L)*) &
            orL('L, "0<=t&t < maxAbbrv/aM&ro=rv*t&ho=w*aM/2*t^2+dhd*t|t>=maxAbbrv/aM&ro=rv*t&ho=(dhd+w*maxAbbrv)*t-w*maxAbbrv^2/(2*aM)".asFormula) & Idioms.<(
            oG("parabola") & orL('L,"t<=tl-to|tl < 0".asFormula) & Idioms.<(
              oG(" i ") & parabolaTl
                ,
                oG(" ii ") & hideL('L,"-rp+rv*(tl-to)<=r&r<=rp+rv*(tl-to)->tl < 0|(maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp)&(maxAbbrv/aM>tl-to->w*h>aM/2*(tl-to)^2+w*dhd*(tl-to)+hp)".asFormula) & parabolaInfT
              )
              ,
              oG("line") & orL('L,"t<=tl-to|tl < 0".asFormula) & Idioms.<(
                oG(" i ") & lineTl
                  ,
                  oG(" ii ") & hideL('L,"-rp+rv*(tl-to)<=r&r<=rp+rv*(tl-to)->tl < 0|(maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp)&(maxAbbrv/aM>tl-to->w*h>aM/2*(tl-to)^2+w*dhd*(tl-to)+hp)".asFormula) &
                    hideL('L,"maxAbbrv=max((0,w*(dhfM-dhd)))".asFormula) & lineInfT
                )
            )
          )
        )
      ,
      oG("(<-)") & andR('R) & Idioms.<(oG("___ R1 ___") & tac1, oG("___ R2 ___") & tac2)
    ))

    def rv0() = Idioms.rememberAs("ACASX_Bounded_RV0", exhaustiveEqL2R(hide=true)('L, "rv=0".asFormula) & equivR('R) & Idioms.<(
      oG("(->)") & allR(1) & allR(1) & allR(1) & implyR(1) & andL(-4) &
        Idioms.cases(QE)(
          (Case("w*(dhd+w*maxAbbrv)<=0".asFormula), oG("__R1__") & QE),
          (Case("w*(dhd+w*maxAbbrv)>0".asFormula),
            oG("__R2__") & (andL('L)*) & atomicQE(onAll(orL('L))*, dT("__R2__ QE"))
          )
        )
      ,
      oG("(<-)") & andR('R) & Idioms.<(oG("___ R1 ___") & tac1rv0, oG("___ R2 ___") & tac2rv0)
    ))

    def tactic = EqualityTactics.abbrv("max(0, w*(dhfM - dhd))".asTerm, Some(Variable("maxAbbrv"))) &
      cut("maxAbbrv>=0".asFormula) & Idioms.<(
      (cutShow, hideR(1) & QE)
      ,
      (cutUse, implyR(1) &
        cut("(rv=0|rv>0)".asFormula) & Idioms.<(
          (cutShow, hideR(1) & hideL(-1) & QE)
          ,
          (cutUse, orL(-4) & Idioms.<(oG("(rv=0)") & rv0, oG("(rv>0)") & rvp))
        )
      )
    )

    val reductionProof = proveBy(reductionFml, tactic)
    reductionProof shouldBe 'proved

    storeLemma(reductionProof, "bounded_upper_equivalence")
  }

  it should "prove Lemma 4: time-limited implicit-explicit equivalence from Lemma 4a and Lemma 4b" in {
    if (containsLemma("lemma4-bounded_lower_equivalence_lemma")) removeLemma("lemma4-bounded_lower_equivalence_lemma")

    runLemmaTest("bounded_lower_equivalence", "ACAS X bounded time should prove Lemma 4a: time-limited implicit-explicit lower equivalence")
    runLemmaTest("bounded_upper_equivalence", "ACAS X bounded time should prove Lemma 4b: time-limited implicit-explicit upper equivalence")

    beforeEach()
    withQE { _ =>

      val lower = KeYmaeraXProblemParser(io.Source.fromInputStream(
        getClass.getResourceAsStream("/examples/casestudies/acasx/sttt/bounded_lower_equivalence.kyx")).mkString)

      val upper = KeYmaeraXProblemParser(io.Source.fromInputStream(
        getClass.getResourceAsStream("/examples/casestudies/acasx/sttt/bounded_upper_equivalence.kyx")).mkString)

      // lower proof has more general precondition, but does not fit to safety proof -> we are going to ask a less general equivalence question
      val Imply(lP@And(lP1@And(lPhp, And(lPrp, And(lPrv, Greater(la, lz)))), lPw), Equiv(lI, lE)) = lower

      // upper proof has less general precondition, which fits to safety proof
      val Imply(uP@And(And(uPhp, And(uPrp, And(uPrv, Greater(ua, uz)))), uP2@And(uPw, uPt)), Equiv(uI, uE)) = upper

      lPhp shouldBe uPhp
      lPrp shouldBe uPrp
      lPrv shouldBe uPrv
      lPw shouldBe uPw
      lz shouldBe uz

      // upgrade equivalence question to fit proof of lower equivalence
      val upgrade = proveBy("(A() & B() -> (T()|C() <-> D())) -> (A() & (B() & !T()) -> (T()|C() <-> D()))".asFormula, prop)
      upgrade shouldBe 'proved

      // how to combine lower/upper equivalence
      val combine = proveBy("(P() -> (B() <-> C())) & (P() -> (E() <-> F())) -> (P() -> (B()|E() <-> C()|F()))".asFormula, prop)
      combine shouldBe 'proved

      // lower: weaken unused a_up >= a_lo in p
      val weaken = proveBy("(B() -> C()) -> (A() & B() -> C())".asFormula, prop)
      weaken shouldBe 'proved

      // upper: generalize a_up >= a_lo & a_lo > 0 to a_up > 0 in p
      //@note can't just write (P() & aM>0) & W() -> C()) -> (aM>=a & (P() & a>0) & W() -> C()) because unification doesn't get it
      val gen = proveBy("((hp > 0 & rp >= 0 & rv >= 0 & aM > 0) & W() -> C()) -> (aM>=a & ((hp > 0 & rp >= 0 & rv >= 0 & a > 0) & W()) -> C())".asFormula,
        prop & hideL('L, "W()".asFormula) & hideR('R, "C()".asFormula) & QE)
      gen shouldBe 'proved

      // load lemmas lower/upper equivalence
      require(containsLemma("bounded_lower_equivalence"), "Lower bounded-time equivalence lemma must be proved")
      require(containsLemma("bounded_upper_equivalence"), "Upper bounded-time equivalence lemma must be proved")

      // negate time precondition
      val Or(LessEqual(t0, tl1), Less(tl2, z)) = uPt
      tl1 shouldBe tl2
      val negatedTimeCond = Not(And(Less(Minus(tl1, t0), z), GreaterEqual(tl1, z)))

      val negate = proveBy("(to<=tl | tl<0) <-> !(tl-to<0 & tl>=0)".asFormula, QE)
      negate shouldBe 'proved

      // cf. STTT: Lemma 4:
      // P -> (C_impl <-> C_expl), where
      //    C_impl == L_impl | U_impl,
      //    C_expl == L_expl | U_expl,
      //    P == aM>=a & (hp > 0 & rp >= 0 & rv >= 0 & a > 0) & (w=-1 | w=1)
      //@note combine p from lower and upper bound to form least general question
      val p = And(GreaterEqual(ua, la), And(lP1, uP2))
      val lemma4 = Imply(p, Equiv(Or(lI, uI), Or(lE, uE)))

      val lemma4Proof = proveBy(lemma4,
        useAt(combine, PosInExpr(1 :: Nil))(1) &
          assertE(And(Imply(p, Equiv(lI, lE)), Imply(p, Equiv(uI, uE))), "Lemma 4: Unexpected form A")(1) &
          useAt(weaken, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
          assertE(And(Imply(And(lP1, uP2), Equiv(lI, lE)), Imply(p, Equiv(uI, uE))), "Lemma 4: Unexpected form B")(1) &
          useAt(negate, PosInExpr(0 :: Nil))(1, 0 :: 0 :: 1 :: 1 :: Nil) &
          assertE(And(Imply(And(lP1, And(lPw, negatedTimeCond)), Equiv(lI, lE)), Imply(p, Equiv(uI, uE))), "Lemma 4: Unexpected form C")(1) &
          useAt(upgrade, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
          assertE(And(Imply(lP, Equiv(lI, lE)), Imply(p, Equiv(uI, uE))), "Lemma 4: Unexpected form D")(1) &
          useAt(gen, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
          assertE(And(Imply(lP, Equiv(lI, lE)), Imply(uP, Equiv(uI, uE))), "Lemma 4: Unexpected form E")(1) &
          andR(1) & Idioms.<(
          useLemma("bounded_lower_equivalence", None),
          useLemma("bounded_upper_equivalence", None))
      )
      lemma4Proof shouldBe 'proved

      storeLemma(lemma4Proof, "lemma4-bounded_lower_equivalence_lemma")
    }
  }

  it should "prove Lemma 4: alternative proof fitting the form required by Corollary 4" in {
    if (containsLemma("lemma4-bounded_lower_equivalence_lemma")) removeLemma("lemma4-bounded_lower_equivalence_lemma")
    if (containsLemma("lemma4-alt-bounded_lower_equivalence_lemma")) removeLemma("lemma4-alt-bounded_lower_equivalence_lemma")

    //@note alternative proof so that theorems and lemmas fit together, because bounded_implicit.key uses a>0 & aM>0 instead of aM>=a & a>0
    //@note this proof stores two lemmas: the actual Lemma 4, and the intermediate step necessary for Corollary 4
    runLemmaTest("bounded_lower_equivalence", "ACAS X bounded time should prove Lemma 4a: time-limited implicit-explicit lower equivalence")
    runLemmaTest("bounded_upper_equivalence", "ACAS X bounded time should prove Lemma 4b: time-limited implicit-explicit upper equivalence")

    beforeEach()
    withQE { _ =>

      val lower = KeYmaeraXProblemParser(io.Source.fromInputStream(
        getClass.getResourceAsStream("/examples/casestudies/acasx/sttt/bounded_lower_equivalence.kyx")).mkString)
      val upper = KeYmaeraXProblemParser(io.Source.fromInputStream(
        getClass.getResourceAsStream("/examples/casestudies/acasx/sttt/bounded_upper_equivalence.kyx")).mkString)

      // lower proof has more general precondition, but does not fit to safety proof -> we are going to ask a less general equivalence question
      val Imply(lP@And(lP1@And(lPhp, And(lPrp, And(lPrv, Greater(la, lz)))), lPw), Equiv(lI, lE)) = lower

      // upper proof has less general precondition, which fits to safety proof
      val Imply(uP@And(And(uPhp, And(uPrp, And(uPrv, Greater(ua, uz)))), uP2@And(uPw, uPt)), Equiv(uI, uE)) = upper

      lPhp shouldBe uPhp
      lPrp shouldBe uPrp
      lPrv shouldBe uPrv
      lPw shouldBe uPw
      lz shouldBe uz

      // how to combine lower/upper equivalence
      val combine = proveBy("(P() -> (B() <-> C())) & (P() -> (E() <-> F())) -> (P() -> (B()|E() <-> C()|F()))".asFormula, prop)
      combine shouldBe 'proved

      // upper: generalize a_up >= a_lo & a_lo > 0 to a_up > 0 in p
      //@note can't just write (P() & aM>0) & W() -> C()) -> (aM>=a & (P() & a>0) & W() -> C()) because unification doesn't get it
      val gen = proveBy("((hp > 0 & rp >= 0 & rv >= 0 & a>0 & aM > 0) & W() -> C()) -> (aM>=a & ((hp > 0 & rp >= 0 & rv >= 0 & a > 0) & W()) -> C())".asFormula,
        prop & hideL('L, "W()".asFormula) & hideR('R, "C()".asFormula) & QE)
      gen shouldBe 'proved

      val weakenLeft = proveBy("((hp > 0 & rp >= 0 & rv >= 0 & a>0) & W() -> C()) -> ((hp > 0 & rp >= 0 & rv >= 0 & a>0 & aM>0) & W() -> C())".asFormula, prop)
      weakenLeft shouldBe 'proved
      val weakenRight = proveBy("((hp > 0 & rp >= 0 & rv >= 0 & aM>0) & W() -> C()) -> ((hp > 0 & rp >= 0 & rv >= 0 & a>0 & aM>0) & W() -> C())".asFormula, prop)
      weakenRight shouldBe 'proved

      // upgrade equivalence question to fit proof of lower equivalence
      val upgrade = proveBy("(A() & B() -> (T()|C() <-> D())) -> (A() & (B() & !T()) -> (T()|C() <-> D()))".asFormula, prop)
      upgrade shouldBe 'proved

      // negate time precondition
      val Or(LessEqual(t0, tl1), Less(tl2, z)) = uPt
      tl1 shouldBe tl2
      val negatedTimeCond = Not(And(Less(Minus(tl1, t0), z), GreaterEqual(tl1, z)))

      val negate = proveBy("(to<=tl | tl<0) <-> !(tl-to<0 & tl>=0)".asFormula, QE)
      negate shouldBe 'proved

      // load lemmas lower/upper equivalence
      require(containsLemma("bounded_lower_equivalence"), "Lower bounded-time equivalence lemma must be proved")
      require(containsLemma("bounded_upper_equivalence"), "Upper bounded-time equivalence lemma must be proved")

      // cf. STTT: Lemma 4:
      // P -> (C_impl <-> C_expl), where
      //    C_impl == L_impl | U_impl,
      //    C_expl == L_expl | U_expl,
      //    P == aM>=a & (hp > 0 & rp >= 0 & rv >= 0 & a > 0) & (w=-1 | w=1)
      //@note combine p from lower and upper bound to form least general question
      val p = And(GreaterEqual(ua, la), And(lP1, uP2))
      val lemma4 = Imply(p, Equiv(Or(lI, uI), Or(lE, uE)))

      // q rephrases p to a>0 & aM>0
      val q = And(And(lPhp, And(lPrp, And(lPrv, And(Greater(la, lz), Greater(ua, uz))))), uP2)
      val intermediate = Imply(q, Equiv(Or(lI, uI), Or(lE, uE)))

      val intermediateProof = proveBy(intermediate,
        useAt(combine, PosInExpr(1 :: Nil))(1) &
          assertE(And(Imply(q, Equiv(lI, lE)), Imply(q, Equiv(uI, uE))), "Lemma 4: Unexpected form A")(1) &
          useAt(weakenLeft, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
          assertE(And(Imply(And(lP1, uP2), Equiv(lI, lE)), Imply(q, Equiv(uI, uE))), "Lemma 4: Unexpected form B")(1) &
          useAt(weakenRight, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
          assertE(And(Imply(And(lP1, uP2), Equiv(lI, lE)), Imply(uP, Equiv(uI, uE))), "Lemma 4: Unexpected form C")(1) &
          useAt(negate, PosInExpr(0 :: Nil))(1, 0 :: 0 :: 1 :: 1 :: Nil) &
          assertE(And(Imply(And(lP1, And(lPw, negatedTimeCond)), Equiv(lI, lE)), Imply(uP, Equiv(uI, uE))), "Lemma 4: Unexpected form D")(1) &
          useAt(upgrade, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
          assertE(And(Imply(lP, Equiv(lI, lE)), Imply(uP, Equiv(uI, uE))), "Lemma 4: Unexpected form E")(1) &
          andR(1) & Idioms.<(
          useLemma("bounded_lower_equivalence", None),
          useLemma("bounded_upper_equivalence", None))
      )
      intermediateProof shouldBe 'proved
      storeLemma(intermediateProof, "lemma4-alt-bounded_lower_equivalence_lemma")

      val lemma4Proof = proveBy(lemma4,
        useAt(gen, PosInExpr(1 :: Nil))(1) &
          assertE(intermediate, "Lemma 4: Unexpected intermediate form")(1) &
          by(intermediateProof)
      )
      lemma4Proof shouldBe 'proved

      storeLemma(lemma4Proof, "lemma4-bounded_lower_equivalence_lemma")
    }
  }

  it should "prove Corollary 4 (safety of bounded-time explicit regions) from Theorem 4 (bounded-time implicit safety) and Lemma 4 (implicit-explicit equivalence)" in {
    if (containsLemma("bounded_implicit-explicit")) removeLemma("bounded_implicit-explicit")

    runLemmaTest("bounded_implicit", "ACAS X bounded time should prove Theorem 4: correctness of implicit bounded-time safe regions")
    runLemmaTest("lemma4-bounded_lower_equivalence_lemma", "ACAS X bounded time should prove Lemma 4: alternative proof fitting the form required by Corollary 4")
    runLemmaTest("lemma4-alt-bounded_lower_equivalence_lemma", "ACAS X bounded time should prove Lemma 4: alternative proof fitting the form required by Corollary 4")

    // rerun initialization (runTest runs afterEach() at the end)
    beforeEach()
    withQE { _ =>

      val implicitSafety = KeYmaeraXProblemParser(io.Source.fromInputStream(
        getClass.getResourceAsStream("/examples/casestudies/acasx/sttt/bounded_implicit.kyx")).mkString)

      val theorem4 = getLemma("bounded_implicit")
      theorem4.fact.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(implicitSafety))

      val lemma4 = getLemma("lemma4-alt-bounded_lower_equivalence_lemma")

      val Imply(And(a, w), Equiv(e, i)) = lemma4.fact.conclusion.succ.head
      val Imply(And(p1, And(p2, pi)), Box(Loop(Compose(Compose(Choice(maintain, Compose(prgA, Compose(prgB, Compose(prgC, Compose(prgD, Test(cimpl)))))), act), ode)), And(u1, And(u2, _)))) = implicitSafety

      pi shouldBe i
      cimpl shouldBe i

      val ucLoFact = getLemma("bounded_implicit_usecase")
      val ucLoLemma = TactixLibrary.proveBy(Sequent(IndexedSeq(a, w, i), IndexedSeq(u1)),
        cut(ucLoFact.fact.conclusion.succ.head) & Idioms.<(
          (cutShow, cohide(2) & by(ucLoFact)),
          (cutUse, implyL(-4) & Idioms.<(andR(2) & Idioms.<(andR(2) & Idioms.<(closeId, closeId), closeId), closeId))
        )
      )
      ucLoLemma.subgoals shouldBe ucLoFact.fact.subgoals
      if (!ucLoLemma.isProved) println("Proof will be partial. Prove other lemmas first")

      val explicitPrg = Loop(Compose(Compose(Choice(maintain, Compose(prgA, Compose(prgB, Compose(prgC, Compose(prgD, Test(e)))))), act), ode))

      // explicit safety, construct from implicit safety and lemma 4 (equivalence)
      val corollary4 = Imply(And(p1, And(p2, e)), Box(explicitPrg, And(u1, And(u2, e))))
      println("Proving Corollary 4:\n" + corollary4.prettyString)

      val proof = CondCongruence.acasXTLcongruence(lemma4.fact, theorem4.fact, ucLoLemma, corollary4, QE)
      println("Proof has " + proof.subgoals.size + " open goals")
      proof shouldBe 'proved
      proof.proved shouldBe Sequent(IndexedSeq(), IndexedSeq(corollary4))

      storeLemma(proof, "bounded_implicit-explicit")
    }
  }


}
