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
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleAbort, BelleExpr}

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

  "ACAS X bounded time" should "prove Theorem 4: correctness of lower bound" in withMathematica { tool =>
    if (lemmaDB.contains("bounded_safe_implicit")) lemmaDB.remove("bounded_safe_implicit")

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
    storeLemma(safeLemma, Some("bounded_safe_implicit"))
  }

  it should "prove Theorem 4: correctness of upper bound" in withMathematica { tool =>
    if (lemmaDB.contains("bounded_safe_upimplicit")) lemmaDB.remove("bounded_safe_upimplicit")

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
    storeLemma(safeUpLemma, Some("bounded_safe_upimplicit"))
  }

  it should "prove Theorem 4: use case lemma" in withMathematica { tool =>
    if (lemmaDB.contains("bounded_implicit_usecase")) lemmaDB.remove("bounded_implicit_usecase")
    val ucLoLemma = proveBy(Imply(invariant, "(abs(r)>rp|abs(h)>hp)".asFormula),
      implyR('R) & (andL('L)*) & SharedTactics.ucLoTac(condImpl))
    ucLoLemma shouldBe 'proved
    storeLemma(ucLoLemma, Some("bounded_implicit_usecase"))
  }

  it should "prove Theorem 4: correctness of implicit bounded-time safe regions" in withMathematica { tool =>
    if (lemmaDB.contains("bounded_implicit")) lemmaDB.remove("bounded_implicit")

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
          implyRi & by(lemmaDB.get("bounded_implicit_usecase").getOrElse(throw new BelleAbort("Incomplete", "Lemma bounded usecase must be proved"))),
          andL('L) & closeId
        ) & done),
      (indStep, dT("Step") & hideL('L, "hp>0&rp>=0&rv>=0&a>0&aM>0".asFormula) & composeb('R) & generalize(invariant)('R) & Idioms.<(
        /*show*/ dT("Generalization Holds") &
          dT("1.21") & chase('R) & dT("After chase") & ((SimplifierV2.simpTac('R) & (andL('L) *)) *) & dT("Simplified") & closeT & done
        ,
        /*use*/ dT("Generalization Strong Enough") & Idioms.cases(
          (Case(Not(evolutionDomain)),
            hideL('L, invariant) & DifferentialTactics.diffUnpackEvolutionDomainInitially('R) & notL('L) & closeId & done)
          ,
          (Case(evolutionDomain),
            dT("Before diff. solution") &
              EqualityTactics.abbrv("max(0,w*(dhf-dhd))".asTerm, Some(Variable("maxI"))) &
              EqualityTactics.abbrv("max(0,w*(dhfM-dhd))".asTerm, Some(Variable("maxIM"))) &
              diffSolveEnd('R) &
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
                  dT("lower lemma") & PropositionalTactics.toSingleFormula &
                  by(lemmaDB.get("bounded_safe_implicit").getOrElse(throw new BelleAbort("Incomplete", "Lemma bounded_safe_implicit must be proved first"))),
                dT("Before hide upper") &
                  hideL('L, "maxI=max((0,w*(dhf-dhd)))".asFormula) & hideL('L, "a>0".asFormula) &
                  hideL('L, "w*dhd>=w*dhf|w*ao>=a".asFormula) &
                  hideL('L, "w*(ao*t_+dhd)>=w*dhf|w*ao>=a".asFormula) &
                  hideR('R, "\\forall t \\forall ro \\forall ho ((t<=tl-(t_+to)|tl < 0)&(0<=t&t < max(0,w*(dhf-(ao*t_+dhd)))/a&ro=rv*t&ho=w*a/2*t^2+(ao*t_+dhd)*t|t>=max(0,w*(dhf-(ao*t_+dhd)))/a&ro=rv*t&ho=dhf*t-w*max(0,w*(dhf-(ao*t_+dhd)))^2/(2*a))->abs((-rv)*t_+r-ro)>rp|w*(-(ao/2*t_^2+dhd*t_)+h) < w*ho-hp)".asFormula) &
                  dT("upper lemma") & PropositionalTactics.toSingleFormula &
                  by(lemmaDB.get("bounded_safe_upimplicit").getOrElse(throw new BelleAbort("Incomplete", "Lemma bounded_safe_upimplicit must be proved first")))
                )
          )
        )
        /* End cutUseLbl "Generalization strong enough" */
      )) /* End indStepLbl */
    )

    val safeTheorem = proveBy(safeImplicitTLFormula, safeTac)
    safeTheorem shouldBe 'proved
    storeLemma(safeTheorem, Some("bounded_implicit"))
  }

  it should "prove Lemma 4a: time-limited implicit-explicit lower equivalence" in withMathematica { tool =>
    if (lemmaDB.contains("bounded_lower_equivalence")) lemmaDB.remove("bounded_lower_equivalence")

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
    storeLemma(equivalence, Some("bounded_lower_equivalence"))
  }
//
//  it should "prove Lemma 4b: time-limited implicit-explicit upper equivalence" in {
//    val reductionFml = io.Source.fromFile(folder + "bounded_upper_equivalence.key").mkString
//    val reductionSeq = new Sequent(Nil, immutable.IndexedSeq(), immutable.IndexedSeq(KeYmaeraXProblemParser(reductionFml)))
//
//    /*** Label Open Goals ***/
//    def oG(s : String) = Tactics.SubLabelBranch(s)
//
//    def instantiateVars(tString : String, roString : String, hoString : String) = la(instantiateT(Variable("t"), tString.asTerm)) & la(instantiateT(Variable("ro"), roString.asTerm)) & la(instantiateT(Variable("ho"), hoString.asTerm))
//
//    def substTactic0(hoString : String) = implyR(1) & la(instantiateT(Variable("t"), "(r-rp)/rv".asTerm)) &
//      la(instantiateT(Variable("ro"), "(r-rp)".asTerm)) &
//      la(instantiateT(Variable("ho"), hoString.asTerm)) &
//      la(implyL) &&
//      (oG("a") & ls(andR) && (QE,QE)
//        ,
//        oG("b") & hideL(-1) & QE
//        )
//
//    def substTactic1(hoString : String, hidePos: Int) = la(instantiateT(Variable("t"), "(r+rp)/rv".asTerm)) & la(instantiateT(Variable("ro"), "(r+rp)".asTerm)) & la(instantiateT(Variable("ho"), hoString.asTerm)) & la(implyL) &&
//      (
//        oG("__01___") & hideL(-1) & QE
//        ,
//        oG("__02__") & la(orL) && (oG("rp>0 & abs(rp)>rp") & ls(hideR) & hideL(-1) & hideL(-1) & hideL(-2) & hideL(-2) & hideL(-2) & QE , oG("rv>0 & A*rv^2>0 -> A>0") & hideL(-1) & hideL(-1) & hideL(-3) & hideL(-3) & QE)
//        )
//
//    def tac2() = implyR(1) & ls(andR) &&
//      (
//        oG("1.1") & implyR(1) & instantiateVars("0","0","0") & hideL(-1) & la(implyL) &&
//          (
//            hideR(1) & hideL(-3) & hideL(-3) & QE
//            ,
//            hideL(-1) & hideL(-2) & QE
//            )
//        ,
//        oG("1.2") & ls(andR) &&
//          (
//            oG("1.2.1") & substTactic0("(w * aM) / 2 * (r-rp)^2/rv^2 + dhd * (r-rp)/rv")
//            ,
//            oG("1.2.2") & ls(implyR) & orR(1) & ls(hide,"rv=0") &
//              la(instantiateT(Variable("t"), "(r-rp)/rv".asTerm)) & la(instantiateT(Variable("ro"), "(r-rp)".asTerm)) & la(instantiateT(Variable("ho"), "(dhd+w*maxAbbrv)*(r-rp)/rv-w*maxAbbrv^2/(2*aM)".asTerm)) & la(implyL) && (
//              oG(" a ") & la(hide,"maxAbbrv=max((0,w*(dhfM-dhd)))") & QE
//              ,
//              oG(" b ") & la(hide,"maxAbbrv=max((0,w*(dhfM-dhd)))") & QE
//              )
//            )
//        )
//
//    def tac1() = implyR(1)  & ls(andR) &&
//      (
//        oG("1.1") & implyR(1) & instantiateVars("0","0","0") & hideL(-1) & la(implyL) &&
//          (
//            hideR(1) & hideL(-3) & hideL(-3) & QE
//            ,
//            hideL(-1) & hideL(-2) & QE
//            )
//        ,
//        oG("1.2") & ls(andR) &&
//          (
//            oG("1.2.1") & substTactic0("(w * aM) / 2 * (r-rp)^2/rv^2 + dhd * (r-rp)/rv")
//            ,
//            oG("1.2.2") & andR(1) &&
//              (
//                oG("___0___") & implyR(1) & substTactic1("(w * aM) / 2 * (r+rp)^2/rv^2 + dhd * (r+rp)/rv",2)
//                ,
//                oG("___1___") & ls(andR) &&
//                  (oG(" x ") & ls(implyR) & ls(orR) & ls(hide,"rv=0&r>rp") & la(instantiateT(Variable("t"), "(r+rp)/rv".asTerm)) & la(instantiateT(Variable("ro"), "(r+rp)".asTerm)) & la(instantiateT(Variable("ho"), "(dhd+w*maxAbbrv)*(r+rp)/rv-w*maxAbbrv^2/(2*aM)".asTerm)) & la(implyL) &&
//                    (oG(" a ") & la(hide,"maxAbbrv=max((0,w*(dhfM-dhd)))") & QE
//                      ,
//                      oG(" b ") & la(hide,"maxAbbrv=max((0,w*(dhfM-dhd)))") & QE
//                      )
//                    ,
//                    oG(" y ") & ls(implyR) & ls(orR) & ls(orR) & ls(andR,"(maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp)&(maxAbbrv/aM>tl-to->w*h>aM/2*(tl-to)^2+w*dhd*(tl-to)+hp)") &&
//                      (oG(" T ") & la(instantiateT(Variable("t"), "tl-to".asTerm)) & la(instantiateT(Variable("ro"), "rv*(tl-to)".asTerm)) & la(instantiateT(Variable("ho"), "(dhd+w*maxAbbrv)*(tl-to)-w*maxAbbrv^2/(2*aM)".asTerm)) & la(implyL) &&
//                        (oG(" a ") & la(hide,"maxAbbrv=max((0,w*(dhfM-dhd)))") & QE
//                          ,
//                          oG(" b ") & ls(hide,"rv=0&r>rp") & ls(implyR,"maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp") & la(andL,"(hp>0&rp>=0&rv>=0&aM>0)&(w=-1|w=1)&(to<=tl|tl < 0)") & la(andL,"(w=-1|w=1)&(to<=tl|tl < 0)") & la(orL,"(to<=tl|tl < 0)") && (la(orL,"abs(r-rv*(tl-to))>rp|w*h>w*((dhd+w*maxAbbrv)*(tl-to)-w*maxAbbrv^2/(2*aM))+hp") && (oG("bug") & QE,QE),QE)
//                          )
//                        ,
//                        oG(" TT ") & la(instantiateT(Variable("t"), "tl-to".asTerm)) & la(instantiateT(Variable("ro"), "rv*(tl-to)".asTerm)) & la(instantiateT(Variable("ho"), "w*aM/2*(tl-to)^2+dhd*(tl-to)".asTerm)) & la(implyL)
//                          &&(oG(" a ") & la(hide,"maxAbbrv=max((0,w*(dhfM-dhd)))") & QE
//                          ,
//                          oG(" b ") & ls(hide,"rv=0&r>rp") & ls(implyR,"maxAbbrv/aM > (tl-to) -> w * h > aM/2 * (tl-to)^2 + w * dhd * (tl-to) + hp") & la(andL,"(hp>0&rp>=0&rv>=0&aM>0)&(w=-1|w=1)&(to<=tl|tl < 0)") & la(andL,"(w=-1|w=1)&(to<=tl|tl < 0)") & la(orL,"(to<=tl|tl < 0)") && (la(orL," abs(r-rv*(tl-to))>rp|w*h>w*(w*aM/2*(tl-to)^2+dhd*(tl-to))+hp") && (oG("bug") & QE,QE),QE)
//                          )
//                        )
//                    )
//                )
//            )
//        )
//
//    def tac1rv0() = implyR(1) & ls(andR) &&
//      (oG("1.1") & instantiateVars("0","0","0") & hideL(-1) & QE
//        ,
//        oG("1.2") & ls(andR) &&
//          (oG("A") & (la(hideL)*) & QE
//            ,
//            oG("B") & ls(andR) &&
//              (oG("X") & (la(hideL)*) & QE
//                ,
//                oG("Y") & ls(andR) &&
//                  (oG("I") & implyR(1) & hideL(-1) & QE
//                    ,
//                    oG("II") & implyR(1) & cut("maxAbbrv > aM*(tl-to) | maxAbbrv <= aM*(tl-to)".asFormula)  & onBranch(
//                      (cutShowLbl, (la(hideL)*) & QE),
//                      (cutUseLbl,la(orL,"maxAbbrv > aM*(tl-to) | maxAbbrv <= aM*(tl-to)") &&
//                        (
//                          oG(" i ") & instantiateVars("tl-to","0","w*aM/2*(tl-to)^2+dhd*(tl-to)") & implyL(-7) &&
//                            (oG(" x ") & hideL(-1) & QE
//                              ,
//                              oG(" y ") & orR(1) & orR(2) & andR(3) && (oG("p") & hideL(-1) & QE,oG("q") & hideL(-1) & QE)
//                              )
//                          ,
//                          oG(" ii ") & instantiateVars("tl-to","0","(dhd+w*maxAbbrv)*(tl-to)-w*maxAbbrv^2/(2*aM)") & implyL(-7) &&
//                            (oG(" x ") & hideL(-1) & QE
//                              ,
//                              oG(" y ")  & orR(1) & orR(2) & andR(3) && (oG("p") & hideL(-1) & QE,oG("q") & hideL(-1) & QE)
//                              )
//
//                          )
//                        )
//                    )
//                    )
//                )
//            )
//        )
//    def tac2rv0() = implyR(1) & ls(andR) &&
//      (
//        oG("2.1") & implyR(1) & instantiateVars("0","0","0") & la(implyL) &&
//          (
//            oG("___0___") & hideL(-1) & QE
//            ,
//            oG("___1___") & hideL(-1) & QE
//            )
//        ,
//        oG("2.2") & ls(andR) &&
//          (
//            oG("___0___") & (la(hideL)*) & QE
//            ,
//            oG("___1___") & hideL(-1) & QE
//            )
//        )
//
//    def parabolaInfT() = la(andL,"0<=t&t < maxAbbrv/aM&ro=rv*t&ho=w*aM/2*t^2+dhd*t") & la(andL,"t < maxAbbrv/aM&ro=rv*t&ho=w*aM/2*t^2+dhd*t") & la(andL,"ro=rv*t&ho=w*aM/2*t^2+dhd*t") & la(TacticLibrary.eqLeft(exhaustive=true), "ro=rv*t") & la(hideT, "ro=rv*t") & la(TacticLibrary.eqLeft(exhaustive=true), "ho=w*aM/2*t^2+dhd*t") & la(hideT, "ho=w*aM/2*t^2+dhd*t") & la(andL,"(hp>0&rp>=0&rv>=0&aM>0)&(w=-1|w=1)&(to<=tl|tl < 0)") & la(andL,"(w=-1|w=1)&(to<=tl|tl < 0)") & la(hide,"maxAbbrv=max((0,w*(dhfM-dhd)))") & la(orL,"(w=-1|w=1)") &&
//      (la(TacticLibrary.eqLeft(exhaustive=true), "w=-1") & la(hideT, "w=-1") & QE
//        ,
//        la(TacticLibrary.eqLeft(exhaustive=true), "w=1") & la(hideT, "w=1") & QE
//        )
//
//    def nestedcutsQE1() = cut("rp < r&r<=rp+rv*maxAbbrv/aM->w*rv^2*h>aM/2*(r-rp)^2+w*rv*dhd*(r-rp)+rv^2*hp".asFormula) & onBranch ((cutShowLbl,la(hide,"-rp<=r&r < -rp+rv*maxAbbrv/aM&(r<=-rp+rv*(tl-to)|tl < 0)->w*rv^2*h>aM/2*(r+rp)^2+w*rv*dhd*(r+rp)+rv^2*hp") & la(hide,"-rp+rv*maxAbbrv/aM<=r&(r < -rp+rv*(tl-to)|tl < 0)->rv=0&r>rp|w*rv*h>w*(dhd+w*maxAbbrv)*(r+rp)-rv*maxAbbrv^2/(2*aM)+rv*hp") & ls(hide,"abs(r-rv*t)>rp|w*h>w*(w*aM/2*t^2+dhd*t)+hp") & ls(hide,"-rp+rv*(tl-to)<=r&r<=rp+rv*(tl-to)") & QE),
//      (cutUseLbl, la(hide,"rp < r&r<=rp+rv*maxAbbrv/aM&(r<=rp+rv*(tl-to)|tl < 0)->w*rv^2*h>aM/2*(r-rp)^2+w*rv*dhd*(r-rp)+rv^2*hp") & cut("-rp<=r&r < -rp+rv*maxAbbrv/aM->w*rv^2*h>aM/2*(r+rp)^2+w*rv*dhd*(r+rp)+rv^2*hp".asFormula) & onBranch ((cutShowLbl,la(hide,"-rp+rv*maxAbbrv/aM<=r&(r < -rp+rv*(tl-to)|tl < 0)->rv=0&r>rp|w*rv*h>w*(dhd+w*maxAbbrv)*(r+rp)-rv*maxAbbrv^2/(2*aM)+rv*hp") & la(hide,"rp < r&r<=rp+rv*maxAbbrv/aM->w*rv^2*h>aM/2*(r-rp)^2+w*rv*dhd*(r-rp)+rv^2*hp") & ls(hide,"abs(r-rv*t)>rp|w*h>w*(w*aM/2*t^2+dhd*t)+hp") & ls(hide,"-rp+rv*(tl-to)<=r&r<=rp+rv*(tl-to)") & QE),
//        (cutUseLbl,la(hide,"-rp<=r&r < -rp+rv*maxAbbrv/aM&(r<=-rp+rv*(tl-to)|tl < 0)->w*rv^2*h>aM/2*(r+rp)^2+w*rv*dhd*(r+rp)+rv^2*hp") & la(implyL,"-rp+rv*maxAbbrv/aM<=r&(r < -rp+rv*(tl-to)|tl < 0)->rv=0&r>rp|w*rv*h>w*(dhd+w*maxAbbrv)*(r+rp)-rv*maxAbbrv^2/(2*aM)+rv*hp") &&
//          (oG("_______1") & la(hide,"maxAbbrv=max((0,w*(dhfM-dhd)))") & la(orL,"(w=-1|w=1)") &&
//            (la(TacticLibrary.eqLeft(exhaustive=true), "w=-1") & la(hideT, "w=-1") & QE
//              ,
//              la(TacticLibrary.eqLeft(exhaustive=true), "w=1") & la(hideT, "w=1") & QE
//              )
//            ,
//            oG("_______2") & la(orL,"rv=0&r>rp|w*rv*h>w*(dhd+w*maxAbbrv)*(r+rp)-rv*maxAbbrv^2/(2*aM)+rv*hp") && (QE,
//              cut("aM*(r-rp)<=rv*maxAbbrv | aM*(r-rp) > rv*maxAbbrv".asFormula) & onBranch
//              ((cutShowLbl,(la(hideL)*) & QE),
//                (cutUseLbl, la(orL,"aM*(r-rp)<=rv*maxAbbrv | aM*(r-rp) > rv*maxAbbrv") &&
//                  (la(implyL,"rp < r&r<=rp+rv*maxAbbrv/aM->w*rv^2*h>aM/2*(r-rp)^2+w*rv*dhd*(r-rp)+rv^2*hp") &&
//                    (ls(hide,"-rp+rv*(tl-to)<=r&r<=rp+rv*(tl-to)")  & la(hide,"maxAbbrv=max((0,w*(dhfM-dhd)))") & la(orL,"(w=-1|w=1)") &&
//                      (la(TacticLibrary.eqLeft(exhaustive=true), "w=-1") & la(hideT, "w=-1") & QE
//                        ,
//                        la(TacticLibrary.eqLeft(exhaustive=true), "w=1") & la(hideT, "w=1") & QE
//                        )
//                      ,
//                      la(implyL,"-rp<=r&r < -rp+rv*maxAbbrv/aM->w*rv^2*h>aM/2*(r+rp)^2+w*rv*dhd*(r+rp)+rv^2*hp") &&
//                        (
//                          oG("__A__") & ls(hide,"-rp+rv*(tl-to)<=r&r<=rp+rv*(tl-to)")  & la(hide,"maxAbbrv=max((0,w*(dhfM-dhd)))") & la(orL,"(w=-1|w=1)") &&
//                            (la(TacticLibrary.eqLeft(exhaustive=true), "w=-1") & la(hideT, "w=-1") & QE
//                              ,
//                              la(TacticLibrary.eqLeft(exhaustive=true), "w=1") & la(hideT, "w=1") & QE
//                              )
//                          ,
//                          oG("__B__") & la(hide,"w*rv*h>w*(dhd+w*maxAbbrv)*(r+rp)-rv*maxAbbrv^2/(2*aM)+rv*hp") & ls(hide,"-rp+rv*(tl-to)<=r&r<=rp+rv*(tl-to)")  & la(hide,"maxAbbrv=max((0,w*(dhfM-dhd)))") & la(orL,"(w=-1|w=1)") &&
//                            (la(TacticLibrary.eqLeft(exhaustive=true), "w=-1") & la(hideT, "w=-1") & QE
//                              ,
//                              la(TacticLibrary.eqLeft(exhaustive=true), "w=1") & la(hideT, "w=1") & QE
//                              )
//                          )
//                      )
//                    ,
//                    la(hide,"-rp<=r&r < -rp+rv*maxAbbrv/aM->w*rv^2*h>aM/2*(r+rp)^2+w*rv*dhd*(r+rp)+rv^2*hp")
//                      & la(hide,"maxAbbrv=max((0,w*(dhfM-dhd)))") & la(orL,"(w=-1|w=1)") &&
//                      (la(TacticLibrary.eqLeft(exhaustive=true), "w=-1") & la(hideT, "w=-1") & QE
//                        ,
//                        la(TacticLibrary.eqLeft(exhaustive=true), "w=1") & la(hideT, "w=1") & QE
//                        )
//                    )
//                  )
//              )
//              )
//
//            )
//          )
//      )
//        )
//    )
//
//
//    def nestedcutsQE() = cut("rp < r&r<=rp+rv*maxAbbrv/aM->w*rv^2*h>aM/2*(r-rp)^2+w*rv*dhd*(r-rp)+rv^2*hp".asFormula) & onBranch(
//      (cutShowLbl,la(hide,"-rp<=r&r < -rp+rv*maxAbbrv/aM&(r<=-rp+rv*(tl-to)|tl < 0)->w*rv^2*h>aM/2*(r+rp)^2+w*rv*dhd*(r+rp)+rv^2*hp") & la(hide,"-rp+rv*maxAbbrv/aM<=r&(r < -rp+rv*(tl-to)|tl < 0)->rv=0&r>rp|w*rv*h>w*(dhd+w*maxAbbrv)*(r+rp)-rv*maxAbbrv^2/(2*aM)+rv*hp") & la(hide,"maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp") & ls(hide,"abs(r-rv*t)>rp|w*h>w*(w*aM/2*t^2+dhd*t)+hp") & QE),
//      (cutUseLbl,la(hide,"-rp+rv*maxAbbrv/aM<=r&(r < -rp+rv*(tl-to)|tl < 0)->rv=0&r>rp|w*rv*h>w*(dhd+w*maxAbbrv)*(r+rp)-rv*maxAbbrv^2/(2*aM)+rv*hp") & cut("rp < r&r<=rp+rv*maxAbbrv/aM->w*rv^2*h>aM/2*(r-rp)^2+w*rv*dhd*(r-rp)+rv^2*hp".asFormula) & onBranch
//      ((cutShowLbl,la(hide,"-rp<=r&r < -rp+rv*maxAbbrv/aM&(r<=-rp+rv*(tl-to)|tl < 0)->w*rv^2*h>aM/2*(r+rp)^2+w*rv*dhd*(r+rp)+rv^2*hp") & la(hide,"maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp") & la(hide,"rp < r&r<=rp+rv*maxAbbrv/aM->w*rv^2*h>aM/2*(r-rp)^2+w*rv*dhd*(r-rp)+rv^2*hp") & ls(hide,"abs(r-rv*t)>rp|w*h>w*(w*aM/2*t^2+dhd*t)+hp") & QE),
//        (cutUseLbl,la(hide,"rp < r&r<=rp+rv*maxAbbrv/aM&(r<=rp+rv*(tl-to)|tl < 0)->w*rv^2*h>aM/2*(r-rp)^2+w*rv*dhd*(r-rp)+rv^2*hp") & oG("evenBetter") & cut("-rp<=r&r < -rp+rv*maxAbbrv/aM->w*rv^2*h>aM/2*(r+rp)^2+w*rv*dhd*(r+rp)+rv^2*hp".asFormula) & onBranch
//        ((cutShowLbl,la(hide," maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp ") & la(hide,"rp < r&r<=rp+rv*maxAbbrv/aM->w*rv^2*h>aM/2*(r-rp)^2+w*rv*dhd*(r-rp)+rv^2*hp") & la(hide,"rp < r&r<=rp+rv*maxAbbrv/aM->w*rv^2*h>aM/2*(r-rp)^2+w*rv*dhd*(r-rp)+rv^2*hp") & ls(hide,"abs(r-rv*t)>rp|w*h>w*(w*aM/2*t^2+dhd*t)+hp") & QE),
//          (cutUseLbl,la(hide,"-rp<=r&r < -rp+rv*maxAbbrv/aM&(r<=-rp+rv*(tl-to)|tl < 0)->w*rv^2*h>aM/2*(r+rp)^2+w*rv*dhd*(r+rp)+rv^2*hp") &
//            la(hide,"maxAbbrv=max((0,w*(dhfM-dhd)))") & la(orL,"(w=-1|w=1)") &&
//            (la(TacticLibrary.eqLeft(exhaustive=true), "w=-1") & la(hideT, "w=-1") & QE
//              ,
//              la(TacticLibrary.eqLeft(exhaustive=true), "w=1") & la(hideT, "w=1") & QE
//              )
//
//
//            )
//        )
//          )
//
//      )
//        )
//    )
//
//    def lineTl() = la(andL,"t>=maxAbbrv/aM&ro=rv*t&ho=(dhd+w*maxAbbrv)*t-w*maxAbbrv^2/(2*aM)") & la(andL,"ro=rv*t&ho=(dhd+w*maxAbbrv)*t-w*maxAbbrv^2/(2*aM)") & la(TacticLibrary.eqLeft(exhaustive=true), "ro=rv*t") & la(hideT, "ro=rv*t") & la(TacticLibrary.eqLeft(exhaustive=true), "ho=(dhd+w*maxAbbrv)*t-w*maxAbbrv^2/(2*aM)") & la(hideT, "ho=(dhd+w*maxAbbrv)*t-w*maxAbbrv^2/(2*aM)") & la(hide,"rp < r&r<=rp+rv*maxAbbrv/aM&(r<=rp+rv*(tl-to)|tl < 0)->w*rv^2*h>aM/2*(r-rp)^2+w*rv*dhd*(r-rp)+rv^2*hp") & la(hide,"-rp<=r&r < -rp+rv*maxAbbrv/aM&(r<=-rp+rv*(tl-to)|tl < 0)->w*rv^2*h>aM/2*(r+rp)^2+w*rv*dhd*(r+rp)+rv^2*hp") & la(andL,"(hp>0&rp>=0&rv>=0&aM>0)&(w=-1|w=1)&(to<=tl|tl < 0)") & la(andL,"(w=-1|w=1)&(to<=tl|tl < 0)") & la(hideL,"to<=tl|tl < 0") & la(hide,"maxAbbrv=max((0,w*(dhfM-dhd)))") & la(implyL,"-rp+rv*(tl-to)<=r&r<=rp+rv*(tl-to)->tl < 0|rv=0&r>rp|(maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp)&(maxAbbrv/aM>tl-to->w*h>aM/2*(tl-to)^2+w*dhd*(tl-to)+hp)") &&
//      (oG("--Z--") & la(orL,"(w=-1|w=1)") &&
//        (la(TacticLibrary.eqLeft(exhaustive=true), "w=-1") & la(hideT, "w=-1") & QE
//          ,
//          la(TacticLibrary.eqLeft(exhaustive=true), "w=1") & la(hideT, "w=1") & QE
//          )
//        ,
//        la(orL,"tl < 0|rv=0&r>rp|(maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp)&(maxAbbrv/aM>tl-to->w*h>aM/2*(tl-to)^2+w*dhd*(tl-to)+hp)") &&
//          (QE,
//            la(orL,"rv=0&r>rp|(maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp)&(maxAbbrv/aM>tl-to->w*h>aM/2*(tl-to)^2+w*dhd*(tl-to)+hp)") &&
//              (QE
//                ,
//                oG("--Y--") & la(andL,"(maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp)&(maxAbbrv/aM>tl-to->w*h>aM/2*(tl-to)^2+w*dhd*(tl-to)+hp)") & la(hide,"(maxAbbrv/aM>tl-to->w*h>aM/2*(tl-to)^2+w*dhd*(tl-to)+hp)") & la(orL,"(w=-1|w=1)") &&
//                  (la(TacticLibrary.eqLeft(exhaustive=true), "w=-1") & la(hideT, "w=-1") & QE
//                    ,
//                    la(TacticLibrary.eqLeft(exhaustive=true), "w=1") & la(hideT, "w=1") & QE
//                    )
//                )
//            )
//        )
//
//
//    def parabolaTl() = la(andL,"0<=t&t < maxAbbrv/aM&ro=rv*t&ho=w*aM/2*t^2+dhd*t") & la(andL,"t < maxAbbrv/aM&ro=rv*t&ho=w*aM/2*t^2+dhd*t") & la(andL,"ro=rv*t&ho=w*aM/2*t^2+dhd*t") & la(TacticLibrary.eqLeft(exhaustive=true), "ro=rv*t") & la(hideT, "ro=rv*t") & la(TacticLibrary.eqLeft(exhaustive=true), "ho=w*aM/2*t^2+dhd*t") & la(hideT, "ho=w*aM/2*t^2+dhd*t") & la(andL,"(hp>0&rp>=0&rv>=0&aM>0)&(w=-1|w=1)&(to<=tl|tl < 0)") & la(andL,"(w=-1|w=1)&(to<=tl|tl < 0)") & la(hideL,"to<=tl|tl < 0") & cut("aM*(tl-to) < maxAbbrv | aM*(tl-to) >= maxAbbrv".asFormula) & onBranch(
//      (cutShowLbl,(la(hideL)*) & QE),
//      (cutUseLbl,la(orL,"aM*(tl-to) < maxAbbrv | aM*(tl-to) >= maxAbbrv") &&
//        (oG("a") & la(implyL,"-rp+rv*(tl-to)<=r&r<=rp+rv*(tl-to)->tl < 0|rv=0&r>rp|(maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp)&(maxAbbrv/aM>tl-to->w*h>aM/2*(tl-to)^2+w*dhd*(tl-to)+hp)") &&
//          (oG("hard") & la(hide,"-rp+rv*maxAbbrv/aM<=r&(r < -rp+rv*(tl-to)|tl < 0)->rv=0&r>rp|w*rv*h>w*(dhd+w*maxAbbrv)*(r+rp)-rv*maxAbbrv^2/(2*aM)+rv*hp") & la(hide,"maxAbbrv=max((0,w*(dhfM-dhd)))") & la(orL,"(w=-1|w=1)") &&
//            (la(TacticLibrary.eqLeft(exhaustive=true), "w=-1") & la(hideT, "w=-1") & QE
//              ,
//              la(TacticLibrary.eqLeft(exhaustive=true), "w=1") & la(hideT, "w=1") & QE
//              )
//            ,
//            la(orL,"tl < 0|rv=0&r>rp|(maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp)&(maxAbbrv/aM>tl-to->w*h>aM/2*(tl-to)^2+w*dhd*(tl-to)+hp)") &&
//              (la(hide,"maxAbbrv=max((0,w*(dhfM-dhd)))") & la(orL,"(w=-1|w=1)") &&
//                (la(TacticLibrary.eqLeft(exhaustive=true), "w=-1") & la(hideT, "w=-1") & QE
//                  ,
//                  la(TacticLibrary.eqLeft(exhaustive=true), "w=1") & la(hideT, "w=1") & QE
//                  )
//
//                ,
//                la(orL,"rv=0&r>rp|(maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp)&(maxAbbrv/aM>tl-to->w*h>aM/2*(tl-to)^2+w*dhd*(tl-to)+hp)") &&
//                  (QE
//                    ,
//                    la(hide,"-rp+rv*maxAbbrv/aM<=r&(r < -rp+rv*(tl-to)|tl < 0)->rv=0&r>rp|w*rv*h>w*(dhd+w*maxAbbrv)*(r+rp)-rv*maxAbbrv^2/(2*aM)+rv*hp") &
//                      la(andL,"(maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp)&(maxAbbrv/aM>tl-to->w*h>aM/2*(tl-to)^2+w*dhd*(tl-to)+hp)") & la(hide,"(maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp)")  & la(hide,"maxAbbrv=max((0,w*(dhfM-dhd)))") & la(orL,"(w=-1|w=1)") &&
//                      (la(TacticLibrary.eqLeft(exhaustive=true), "w=-1") & la(hideT, "w=-1") & oG("done1") & QE
//                        ,
//                        la(TacticLibrary.eqLeft(exhaustive=true), "w=1") & la(hideT, "w=1") & oG("done2") & QE
//                        )
//
//                    )
//                )
//            )
//          ,
//          oG("b") & la(hideL,"t<=tl-to") & la(implyL,"-rp+rv*(tl-to)<=r&r<=rp+rv*(tl-to)->tl < 0|rv=0&r>rp|(maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp)&(maxAbbrv/aM>tl-to->w*h>aM/2*(tl-to)^2+w*dhd*(tl-to)+hp)") &&
//            (oG("hard") & nestedcutsQE1
//              ,
//              la(orL,"tl < 0|rv=0&r>rp|(maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp)&(maxAbbrv/aM>tl-to->w*h>aM/2*(tl-to)^2+w*dhd*(tl-to)+hp)") &&
//                (la(hide,"maxAbbrv=max((0,w*(dhfM-dhd)))") & la(orL,"(w=-1|w=1)") &&
//                  (la(TacticLibrary.eqLeft(exhaustive=true), "w=-1") & la(hideT, "w=-1") & QE
//                    ,
//                    la(TacticLibrary.eqLeft(exhaustive=true), "w=1") & la(hideT, "w=1") & QE
//                    )
//
//                  ,
//                  la(orL,"rv=0&r>rp|(maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp)&(maxAbbrv/aM>tl-to->w*h>aM/2*(tl-to)^2+w*dhd*(tl-to)+hp)") &&
//                    (QE
//                      ,
//                      la(andL,"(maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp)&(maxAbbrv/aM>tl-to->w*h>aM/2*(tl-to)^2+w*dhd*(tl-to)+hp)") & la(hide,"(maxAbbrv/aM>tl-to->w*h>aM/2*(tl-to)^2+w*dhd*(tl-to)+hp)") & nestedcutsQE
//
//                      )
//                  )
//
//
//              )
//          )
//        )
//    )
//
//
//    def lineInfT() = la(andL,"t>=maxAbbrv/aM&ro=rv*t&ho=(dhd+w*maxAbbrv)*t-w*maxAbbrv^2/(2*aM)") & la(andL,"ro=rv*t&ho=(dhd+w*maxAbbrv)*t-w*maxAbbrv^2/(2*aM)") & la(TacticLibrary.eqLeft(exhaustive=true), "ro=rv*t") & la(hideT, "ro=rv*t") & la(TacticLibrary.eqLeft(exhaustive=true), "ho=(dhd+w*maxAbbrv)*t-w*maxAbbrv^2/(2*aM)") & la(hideT, "ho=(dhd+w*maxAbbrv)*t-w*maxAbbrv^2/(2*aM)") & la(andL,"(hp>0&rp>=0&rv>=0&aM>0)&(w=-1|w=1)&(to<=tl|tl < 0)") & la(andL,"(w=-1|w=1)&(to<=tl|tl < 0)") & la(orL,"(w=-1|w=1)") &&
//      (la(TacticLibrary.eqLeft(exhaustive=true), "w=-1") & la(hideT, "w=-1") & QE
//        ,
//        la(TacticLibrary.eqLeft(exhaustive=true), "w=1") & la(hideT, "w=1") & QE
//        )
//
//
//    def rvp() = oG("rv>0") & ls(equivR) & onBranch(
//      (equivLeftLbl, oG("(->)") & allR(1) & allR(1) & allR(1) & implyR(1)
//        & andL(-5) & cut("w*(dhd+w*maxAbbrv)<=0 | w*(dhd+w*maxAbbrv) > 0".asFormula) & onBranch(
//        (cutShowLbl, (la(hideL)*) & QE),
//        (cutUseLbl, la(orL,"w*(dhd+w*maxAbbrv)<=0 | w*(dhd+w*maxAbbrv) > 0") &&
//          (oG("___ T1 ___") & hideL(-6) & la(implyL) &&
//            (QE,la(andL,"(t<=tl-to|tl < 0)&(0<=t&t < maxAbbrv/aM&ro=rv*t&ho=w*aM/2*t^2+dhd*t|t>=maxAbbrv/aM&ro=rv*t&ho=(dhd+w*maxAbbrv)*t-w*maxAbbrv^2/(2*aM))") & la(andL,"(-rp<=r&r<=rp->w*h>hp)&(rp < r&r<=rp+rv*maxAbbrv/aM&(r<=rp+rv*(tl-to)|tl < 0)->w*rv^2*h>aM/2*(r-rp)^2+w*rv*dhd*(r-rp)+rv^2*hp)&(rp+rv*maxAbbrv/aM < r&(r<=rp+rv*(tl-to)|tl < 0)->rv=0|w*rv*h>w*(dhd+w*maxAbbrv)*(r-rp)-rv*maxAbbrv^2/(2*aM)+rv*hp)") & la(andL," (rp < r&r<=rp+rv*maxAbbrv/aM&(r<=rp+rv*(tl-to)|tl < 0)->w*rv^2*h>aM/2*(r-rp)^2+w*rv*dhd*(r-rp)+rv^2*hp)&(rp+rv*maxAbbrv/aM < r&(r<=rp+rv*(tl-to)|tl < 0)->rv=0|w*rv*h>w*(dhd+w*maxAbbrv)*(r-rp)-rv*maxAbbrv^2/(2*aM)+rv*hp)")  & la(orL, "0<=t&t < maxAbbrv/aM&ro=rv*t&ho=w*aM/2*t^2+dhd*t|t>=maxAbbrv/aM&ro=rv*t&ho=(dhd+w*maxAbbrv)*t-w*maxAbbrv^2/(2*aM)") &&
//              (
//                oG("parabola") & la(hideL," rp+rv*maxAbbrv/aM < r&(r<=rp+rv*(tl-to)|tl < 0)->rv=0|w*rv*h>w*(dhd+w*maxAbbrv)*(r-rp)-rv*maxAbbrv^2/(2*aM)+rv*hp") & la(orL,"t<=tl-to|tl < 0") &&
//                  (oG(" i ")  & la(hide,"maxAbbrv=max((0,w*(dhfM-dhd)))") & QE
//                    ,
//                    oG(" ii ") & la(hide,"maxAbbrv=max((0,w*(dhfM-dhd)))") & QE
//                    )
//                ,
//                oG("line") & la(orL,"t<=tl-to|tl < 0") &&
//                  (oG(" i ") & la(hide,"maxAbbrv=max((0,w*(dhfM-dhd)))") & QE
//                    ,
//                    oG(" ii ") & la(hide,"maxAbbrv=max((0,w*(dhfM-dhd)))") & QE
//                    )
//                ))
//            ,
//            oG("___ T2 ___") & hideL(-7) & la(implyL) &&
//              (QE,la(andL,"(t<=tl-to|tl < 0)&(0<=t&t < maxAbbrv/aM&ro=rv*t&ho=w*aM/2*t^2+dhd*t|t>=maxAbbrv/aM&ro=rv*t&ho=(dhd+w*maxAbbrv)*t-w*maxAbbrv^2/(2*aM))") & la(andL,"(-rp<=r&r<=rp->w*h>hp)&(rp < r&r<=rp+rv*maxAbbrv/aM&(r<=rp+rv*(tl-to)|tl < 0)->w*rv^2*h>aM/2*(r-rp)^2+w*rv*dhd*(r-rp)+rv^2*hp)&(-rp<=r&r < -rp+rv*maxAbbrv/aM&(r<=-rp+rv*(tl-to)|tl < 0)->w*rv^2*h>aM/2*(r+rp)^2+w*rv*dhd*(r+rp)+rv^2*hp)&(-rp+rv*maxAbbrv/aM<=r&(r < -rp+rv*(tl-to)|tl < 0)->rv=0&r>rp|w*rv*h>w*(dhd+w*maxAbbrv)*(r+rp)-rv*maxAbbrv^2/(2*aM)+rv*hp)&(-rp+rv*(tl-to)<=r&r<=rp+rv*(tl-to)->tl < 0|rv=0&r>rp|(maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp)&(maxAbbrv/aM>tl-to->w*h>aM/2*(tl-to)^2+w*dhd*(tl-to)+hp))") & la(andL,"(rp < r&r<=rp+rv*maxAbbrv/aM&(r<=rp+rv*(tl-to)|tl < 0)->w*rv^2*h>aM/2*(r-rp)^2+w*rv*dhd*(r-rp)+rv^2*hp)&(-rp<=r&r < -rp+rv*maxAbbrv/aM&(r<=-rp+rv*(tl-to)|tl < 0)->w*rv^2*h>aM/2*(r+rp)^2+w*rv*dhd*(r+rp)+rv^2*hp)&(-rp+rv*maxAbbrv/aM<=r&(r < -rp+rv*(tl-to)|tl < 0)->rv=0&r>rp|w*rv*h>w*(dhd+w*maxAbbrv)*(r+rp)-rv*maxAbbrv^2/(2*aM)+rv*hp)&(-rp+rv*(tl-to)<=r&r<=rp+rv*(tl-to)->tl < 0|rv=0&r>rp|(maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp)&(maxAbbrv/aM>tl-to->w*h>aM/2*(tl-to)^2+w*dhd*(tl-to)+hp))")& la(andL,"(-rp<=r&r < -rp+rv*maxAbbrv/aM&(r<=-rp+rv*(tl-to)|tl < 0)->w*rv^2*h>aM/2*(r+rp)^2+w*rv*dhd*(r+rp)+rv^2*hp)&(-rp+rv*maxAbbrv/aM<=r&(r < -rp+rv*(tl-to)|tl < 0)->rv=0&r>rp|w*rv*h>w*(dhd+w*maxAbbrv)*(r+rp)-rv*maxAbbrv^2/(2*aM)+rv*hp)&(-rp+rv*(tl-to)<=r&r<=rp+rv*(tl-to)->tl < 0|rv=0&r>rp|(maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp)&(maxAbbrv/aM>tl-to->w*h>aM/2*(tl-to)^2+w*dhd*(tl-to)+hp))") & la(andL,"(-rp+rv*maxAbbrv/aM<=r&(r < -rp+rv*(tl-to)|tl < 0)->rv=0&r>rp|w*rv*h>w*(dhd+w*maxAbbrv)*(r+rp)-rv*maxAbbrv^2/(2*aM)+rv*hp)&(-rp+rv*(tl-to)<=r&r<=rp+rv*(tl-to)->tl < 0|rv=0&r>rp|(maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp)&(maxAbbrv/aM>tl-to->w*h>aM/2*(tl-to)^2+w*dhd*(tl-to)+hp))") & la(orL, "0<=t&t < maxAbbrv/aM&ro=rv*t&ho=w*aM/2*t^2+dhd*t|t>=maxAbbrv/aM&ro=rv*t&ho=(dhd+w*maxAbbrv)*t-w*maxAbbrv^2/(2*aM)") &&
//                (oG("parabola") & la(orL,"t<=tl-to|tl < 0") &&
//                  (oG(" i ") & parabolaTl
//                    ,
//                    oG(" ii ") & la(hide,"-rp+rv*(tl-to)<=r&r<=rp+rv*(tl-to)->tl < 0|rv=0&r>rp|(maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp)&(maxAbbrv/aM>tl-to->w*h>aM/2*(tl-to)^2+w*dhd*(tl-to)+hp)") & parabolaInfT
//                    )
//                  ,
//                  oG("line") & la(orL,"t<=tl-to|tl < 0") &&
//                    (oG(" i ") & lineTl
//                      ,
//                      oG(" ii ") & la(hide,"-rp+rv*(tl-to)<=r&r<=rp+rv*(tl-to)->tl < 0|rv=0&r>rp|(maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp)&(maxAbbrv/aM>tl-to->w*h>aM/2*(tl-to)^2+w*dhd*(tl-to)+hp)") & la(hide,"maxAbbrv=max((0,w*(dhfM-dhd)))") & lineInfT
//                      )
//                  ) )
//            ))
//      )
//        ),
//      (equivRightLbl, oG("(<-)")
//        & ls(andR) &&
//        (oG("___ R1 ___") & tac1
//          ,
//          oG("___ R2 ___") & tac2
//          )
//        )
//    )
//
//    def rv0() = la(TacticLibrary.eqLeft(exhaustive=true), "rv=0") & la(hideT, "rv=0") & ls(equivR) & onBranch(
//      (equivLeftLbl, oG("(->)") & allR(1) & allR(1) & allR(1) & implyR(1) & andL(-4) & cut("w*(dhd+w*maxAbbrv)<=0 | w*(dhd+w*maxAbbrv)>0".asFormula) & onBranch(
//        (cutShowLbl,(la(hideL)*) & QE),
//        (cutUseLbl,orL(-7) &&
//          (oG("__R1__") & hideL(-5) & implyL(-5) &&
//            (QE,
//              andL(-6) & andL(-7) & andL(-4) & hideL(-6) & hideL(-6) & QE
//              )
//            ,
//            oG("__R2__") & hideL(-6) & implyL(-5) &&
//              (QE,
//                andL(-6) & andL(-7) & andL(-8) & andL(-9) & implyL(-10) && (QE,
//                  orL(-10) && (oG("old") & hideL(-7) & hideL(-7) & QE,
//                    oG("hard") & orL(-10) && (hideL(-7) & hideL(-7) & QE, oG("bug") & andL(-4) & orL(-10) && (oG(" v ") & hideL(-6) & hideL(-6) & hideL(-6) & cut("maxAbbrv/aM<=tl-to | maxAbbrv/aM>tl-to".asFormula) & onBranch(
//                      (cutShowLbl, hideL(-1) & QE),
//                      (cutUseLbl,andL(-6) & la(orL,"maxAbbrv/aM<=tl-to|maxAbbrv/aM>tl-to") && (oG(" o ") & hideL(-10) & la(implyL,"maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp") &&
//                        (QE, la(orL,"0<=t&t < maxAbbrv/aM&ro=0*t&ho=w*aM/2*t^2+dhd*t|t>=maxAbbrv/aM&ro=0*t&ho=(dhd+w*maxAbbrv)*t-w*maxAbbrv^2/(2*aM)") && (oG(" a ")  & la(hide,"t<=tl-to") & la(hide,"maxAbbrv=max((0,w*(dhfM-dhd)))") & QE,oG(" b ") & la(hide,"maxAbbrv=max((0,w*(dhfM-dhd)))") & la(hide,"maxAbbrv/aM<=tl-to") & la(hide,"w*(dhd+w*maxAbbrv)>0") & QE  ))  ,
//                        oG(" oo ") & la(hide,"maxAbbrv/aM<=tl-to->w*h>w*(dhd+w*maxAbbrv)*(tl-to)-maxAbbrv^2/(2*aM)+hp") & la(implyL,"maxAbbrv/aM>tl-to->w*h>aM/2*(tl-to)^2+w*dhd*(tl-to)+hp") && (QE,la(orL,"0<=t&t < maxAbbrv/aM&ro=0*t&ho=w*aM/2*t^2+dhd*t|t>=maxAbbrv/aM&ro=0*t&ho=(dhd+w*maxAbbrv)*t-w*maxAbbrv^2/(2*aM)") && (oG(" a ") & la(hide,"maxAbbrv=max((0,w*(dhfM-dhd)))") & la(hide, "w*(dhd+w*maxAbbrv)>0") & QE,oG("b ") & la(hide,"maxAbbrv=max((0,w*(dhfM-dhd)))") & la(hide, "w*(dhd+w*maxAbbrv)>0") & QE   ) )
//                        ))
//                    )
//
//
//                      ,oG(" vv ") & hideL(-1) & QE)  )
//                    )
//                  )
//
//                )
//            )
//          )
//      )),
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
//          (oG("(rv=0)") & rv0
//            ,
//            oG("(rv>0)") & rvp
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
//
//    lemmaDB.add(Lemma(reductionProof.provableWitness, new ToolEvidence(
//      immutable.Map("input" -> reductionFml, "output" -> "true")) :: Nil, Some("bounded_upper_equivalence")))
//  }
//
//  it should "prove Lemma 4: time-limited implicit-explicit equivalence from Lemma 4a and Lemma 4b" in {
//    if (!lemmaDB.contains("bounded_lower_equivalence")) {
//      println("Proving bounded_lower_equivalence lemma...")
//      runTest("ACAS X bounded time should prove Lemma 4a: time-limited implicit-explicit lower equivalence", new Args(nilReporter))
//      println("...done")
//    }
//    if (!lemmaDB.contains("bounded_upper_equivalence")) {
//      println("Proving bounded_upper_equivalence lemma...")
//      runTest("ACAS X bounded time should prove Lemma 4b: time-limited implicit-explicit upper equivalence", new Args(nilReporter))
//      println("...done")
//    }
//
//    beforeEach()
//
//    val lower = KeYmaeraXProblemParser(io.Source.fromFile(folder + "bounded_lower_equivalence.key").mkString)
//    val upper = KeYmaeraXProblemParser(io.Source.fromFile(folder + "bounded_upper_equivalence.key").mkString)
//
//    // lower proof has more general precondition, but does not fit to safety proof -> we are going to ask a less general equivalence question
//    val Imply(lP@And(lP1@And(lPhp, And(lPrp, And(lPrv, Greater(la, lz)))), lPw), Equiv(lI, lE)) = lower
//
//    // upper proof has less general precondition, which fits to safety proof
//    val Imply(uP@And(And(uPhp, And(uPrp, And(uPrv, Greater(ua, uz)))), uP2@And(uPw, uPt)), Equiv(uI, uE)) = upper
//
//    lPhp shouldBe uPhp
//    lPrp shouldBe uPrp
//    lPrv shouldBe uPrv
//    lPw  shouldBe uPw
//    lz   shouldBe uz
//
//    // upgrade equivalence question to fit proof of lower equivalence
//    val upgrade = proveBy("(A() & B() -> (T()|C() <-> D())) -> (A() & (B() & !T()) -> (T()|C() <-> D()))".asFormula, prop)
//    upgrade shouldBe 'proved
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
//    require(lemmaDB.contains("bounded_lower_equivalence"), "Lower bounded-time equivalence lemma must be proved")
//    require(lemmaDB.contains("bounded_upper_equivalence"), "Upper bounded-time equivalence lemma must be proved")
//
//    // negate time precondition
//    val Or(LessEqual(t0, tl1), Less(tl2,z)) = uPt
//    tl1 shouldBe tl2
//    val negatedTimeCond = Not(And(Less(Minus(tl1, t0), z), GreaterEqual(tl1, z)))
//
//    val negate = proveBy("(to<=tl | tl<0) <-> !(tl-to<0 & tl>=0)".asFormula, QE)
//    negate shouldBe 'proved
//
//    // cf. STTT: Lemma 4:
//    // P -> (C_impl <-> C_expl), where
//    //    C_impl == L_impl | U_impl,
//    //    C_expl == L_expl | U_expl,
//    //    P == aM>=a & (hp > 0 & rp >= 0 & rv >= 0 & a > 0) & (w=-1 | w=1)
//    //@note combine p from lower and upper bound to form least general question
//    val p = And(GreaterEqual(ua, la), And(lP1, uP2))
//    val lemma4 = Imply(p, Equiv(Or(lI, uI), Or(lE, uE)))
//
//    val lemma4Proof = proveBy(lemma4,
//      useAt(combine, PosInExpr(1::Nil))(1) &
//        assertE(And(Imply(p, Equiv(lI, lE)), Imply(p, Equiv(uI, uE))), "Lemma 4: Unexpected form A")(1) &
//        useAt(weaken, PosInExpr(1::Nil))(1, 0::Nil) &
//        assertE(And(Imply(And(lP1, uP2), Equiv(lI, lE)), Imply(p, Equiv(uI, uE))), "Lemma 4: Unexpected form B")(1) &
//        useAt(negate, PosInExpr(0::Nil))(1, 0::0::1::1::Nil) &
//        assertE(And(Imply(And(lP1, And(lPw, negatedTimeCond)), Equiv(lI, lE)), Imply(p, Equiv(uI, uE))), "Lemma 4: Unexpected form C")(1) &
//        useAt(upgrade, PosInExpr(1::Nil))(1, 0::Nil) &
//        assertE(And(Imply(lP, Equiv(lI, lE)), Imply(p, Equiv(uI, uE))), "Lemma 4: Unexpected form D")(1) &
//        useAt(gen, PosInExpr(1::Nil))(1, 1::Nil) &
//        assertE(And(Imply(lP, Equiv(lI, lE)), Imply(uP, Equiv(uI, uE))), "Lemma 4: Unexpected form E")(1) &
//        andR(1) && (
//        by(LookupLemma(lemmaDB, "bounded_lower_equivalence").lemma),
//        by(LookupLemma(lemmaDB, "bounded_upper_equivalence").lemma))
//    )
//    lemma4Proof shouldBe 'proved
//
//    lemmaDB.add(Lemma(
//      lemma4Proof,
//      ToolEvidence(immutable.Map("input" -> lemma4.toString, "output" -> "true")) :: Nil,
//      Some("lemma4-bounded_lower_equivalence_lemma")))
//  }
//
//  it should "prove Lemma 4: alternative proof fitting the form required by Corollary 4" in {
//    //@note alternative proof so that theorems and lemmas fit together, because bounded_implicit.key uses a>0 & aM>0 instead of aM>=a & a>0
//    //@note this proof stores two lemmas: the actual Lemma 4, and the intermediate step necessary for Corollary 4
//
//    if (!lemmaDB.contains("bounded_lower_equivalence")) {
//      println("Proving bounded_lower_equivalence lemma...")
//      runTest("ACAS X bounded time should prove Lemma 4a: time-limited implicit-explicit lower equivalence", new Args(nilReporter))
//      println("...done")
//    }
//    if (!lemmaDB.contains("bounded_upper_equivalence")) {
//      println("Proving bounded_upper_equivalence lemma...")
//      runTest("ACAS X bounded time should prove Lemma 4b: time-limited implicit-explicit upper equivalence", new Args(nilReporter))
//      println("...done")
//    }
//
//    beforeEach()
//
//    val lower = KeYmaeraXProblemParser(io.Source.fromFile(folder + "bounded_lower_equivalence.key").mkString)
//    val upper = KeYmaeraXProblemParser(io.Source.fromFile(folder + "bounded_upper_equivalence.key").mkString)
//
//    // lower proof has more general precondition, but does not fit to safety proof -> we are going to ask a less general equivalence question
//    val Imply(lP@And(lP1@And(lPhp, And(lPrp, And(lPrv, Greater(la, lz)))), lPw), Equiv(lI, lE)) = lower
//
//    // upper proof has less general precondition, which fits to safety proof
//    val Imply(uP@And(And(uPhp, And(uPrp, And(uPrv, Greater(ua, uz)))), uP2@And(uPw, uPt)), Equiv(uI, uE)) = upper
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
//    // upgrade equivalence question to fit proof of lower equivalence
//    val upgrade = proveBy("(A() & B() -> (T()|C() <-> D())) -> (A() & (B() & !T()) -> (T()|C() <-> D()))".asFormula, prop)
//    upgrade shouldBe 'proved
//
//    // negate time precondition
//    val Or(LessEqual(t0, tl1), Less(tl2,z)) = uPt
//    tl1 shouldBe tl2
//    val negatedTimeCond = Not(And(Less(Minus(tl1, t0), z), GreaterEqual(tl1, z)))
//
//    val negate = proveBy("(to<=tl | tl<0) <-> !(tl-to<0 & tl>=0)".asFormula, QE)
//    negate shouldBe 'proved
//
//    // load lemmas lower/upper equivalence
//    require(lemmaDB.contains("bounded_lower_equivalence"), "Lower bounded-time equivalence lemma must be proved")
//    require(lemmaDB.contains("bounded_upper_equivalence"), "Upper bounded-time equivalence lemma must be proved")
//
//    // cf. STTT: Lemma 4:
//    // P -> (C_impl <-> C_expl), where
//    //    C_impl == L_impl | U_impl,
//    //    C_expl == L_expl | U_expl,
//    //    P == aM>=a & (hp > 0 & rp >= 0 & rv >= 0 & a > 0) & (w=-1 | w=1)
//    //@note combine p from lower and upper bound to form least general question
//    val p = And(GreaterEqual(ua, la), And(lP1, uP2))
//    val lemma4 = Imply(p, Equiv(Or(lI, uI), Or(lE, uE)))
//
//    // q rephrases p to a>0 & aM>0
//    val q = And(And(lPhp, And(lPrp, And(lPrv, And(Greater(la, lz), Greater(ua, uz))))), uP2)
//    val intermediate = Imply(q, Equiv(Or(lI, uI), Or(lE, uE)))
//
//    val intermediateProof = proveBy(intermediate,
//      useAt(combine, PosInExpr(1::Nil))(1) &
//        assertE(And(Imply(q, Equiv(lI, lE)), Imply(q, Equiv(uI, uE))), "Lemma 4: Unexpected form A")(1) &
//        useAt(weakenLeft, PosInExpr(1::Nil))(1, 0::Nil) &
//        assertE(And(Imply(And(lP1, uP2), Equiv(lI, lE)), Imply(q, Equiv(uI, uE))), "Lemma 4: Unexpected form B")(1) &
//        useAt(weakenRight, PosInExpr(1::Nil))(1, 1::Nil) &
//        assertE(And(Imply(And(lP1, uP2), Equiv(lI, lE)), Imply(uP, Equiv(uI, uE))), "Lemma 4: Unexpected form C")(1) &
//        useAt(negate, PosInExpr(0::Nil))(1, 0::0::1::1::Nil) &
//        assertE(And(Imply(And(lP1, And(lPw, negatedTimeCond)), Equiv(lI, lE)), Imply(uP, Equiv(uI, uE))), "Lemma 4: Unexpected form D")(1) &
//        useAt(upgrade, PosInExpr(1::Nil))(1, 0::Nil) &
//        assertE(And(Imply(lP, Equiv(lI, lE)), Imply(uP, Equiv(uI, uE))), "Lemma 4: Unexpected form E")(1) &
//        andR(1) && (
//        by(LookupLemma(lemmaDB, "bounded_lower_equivalence").lemma),
//        by(LookupLemma(lemmaDB, "bounded_upper_equivalence").lemma))
//    )
//    intermediateProof shouldBe 'proved
//    lemmaDB.add(Lemma(
//      intermediateProof,
//      ToolEvidence(immutable.Map("input" -> intermediate.toString, "output" -> "true")) :: Nil,
//      Some("lemma4-alt-bounded_lower_equivalence_lemma")))
//
//    val lemma4Proof = proveBy(lemma4,
//      useAt(gen, PosInExpr(1::Nil))(1) &
//        assertE(intermediate, "Lemma 4: Unexpected intermediate form")(1) &
//        by(intermediateProof)
//    )
//    lemma4Proof shouldBe 'proved
//
//    lemmaDB.add(Lemma(
//      lemma4Proof,
//      ToolEvidence(immutable.Map("input" -> lemma4.toString, "output" -> "true")) :: Nil,
//      Some("lemma4-bounded_lower_equivalence_lemma")))
//  }
//
//  it should "prove Corollary 4 (safety of bounded-time explicit regions) from Theorem 4 (bounded-time implicit safety) and Lemma 4 (implicit-explicit equivalence)" in {
//    val lemmaDB = LemmaDBFactory.lemmaDB
//    val nilReporter = new Reporter() { override def apply(event: Event): Unit = {} }
//
//    if (!(lemmaDB.contains("bounded_implicit") && lemmaDB.contains("bounded_implicit_usecase"))) {
//      println("Proving bounded_implicit lemma and bounded_implicit_usecase...")
//      runTest("ACAS X bounded time should prove Theorem 4: correctness of implicit bounded-time safe regions", new Args(nilReporter))
//      println("...done")
//    }
//    if (!lemmaDB.contains("lemma4-bounded_lower_equivalence_lemma")) {
//      println("Proving lemma4-bounded_lower_equivalence_lemma...")
//      runTest("ACAS X bounded time should prove Lemma 4: alternative proof fitting the form required by Corollary 4", new Args(nilReporter))
//      println("...done")
//    }
//
//    // rerun initialization (runTest runs afterEach() at the end)
//    beforeEach()
//
//    val implicitSafety = KeYmaeraXProblemParser(io.Source.fromFile(folder + "bounded_implicit.key").mkString)
//    val theorem4 = LookupLemma(lemmaDB, "bounded_implicit").lemma
//    theorem4.fact.conclusion shouldBe Sequent(Nil, IndexedSeq(), IndexedSeq(implicitSafety))
//
//    val lemma4 = LookupLemma(lemmaDB, "lemma4-alt-bounded_lower_equivalence_lemma").lemma.fact
//
//    val Imply(And(a, w), Equiv(e, i)) = lemma4.conclusion.succ.head
//    val Imply(And(p1, And(p2, pi)), Box(Loop(Compose(Compose(Choice(maintain, Compose(prgA, Compose(prgB, Compose(prgC, Compose(prgD, Test(cimpl)))))), act), ode)), And(u1, And(u2, _)))) = implicitSafety
//
//    pi shouldBe i
//    cimpl shouldBe i
//
//    val ucLoFact = LookupLemma(lemmaDB, "bounded_implicit_usecase").lemma.fact
//    val ucLoLemma = TactixLibrary.proveBy(Sequent(Nil, IndexedSeq(a, w, i), IndexedSeq(u1)),
//      cut(ucLoFact.conclusion.succ.head) & onBranch(
//        (BranchLabels.cutShowLbl, cohide(2) & by(ucLoFact)),
//        (BranchLabels.cutUseLbl, implyL(-4) && (andR(2) && (andR(2) && (closeId, closeId), closeId), closeId) )
//      )
//    )
//    ucLoLemma.subgoals shouldBe ucLoFact.subgoals
//    if (!ucLoLemma.isProved) println("Proof will be partial. Prove other lemmas first")
//
//    val explicitPrg = Loop(Compose(Compose(Choice(maintain, Compose(prgA, Compose(prgB, Compose(prgC, Compose(prgD, Test(e)))))), act), ode))
//
//    // explicit safety, construct from implicit safety and lemma 4 (equivalence)
//    val corollary4 = Imply(And(p1, And(p2, e)), Box(explicitPrg, And(u1, And(u2, e))))
//    println("Proving Corollary 4:\n" + corollary4.prettyString)
//
//    val proof = acasXTLcongruence(lemma4, theorem4.fact, ucLoLemma, corollary4, QE)
//    println("Proof has " + proof.subgoals.size + " open goals")
//    proof shouldBe 'proved
//    proof.proved shouldBe Sequent(Nil, IndexedSeq(), IndexedSeq(corollary4))
//
//    lemmaDB.add(Lemma(proof,
//      ToolEvidence(immutable.Map("input" -> corollary4.prettyString, "output" -> "true")) :: Nil,
//      Some("bounded_implicit-explicit")))
//  }


}
