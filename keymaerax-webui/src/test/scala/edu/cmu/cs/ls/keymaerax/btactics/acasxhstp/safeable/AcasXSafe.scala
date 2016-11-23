/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics.acasxhstp.safeable

import edu.cmu.cs.ls.keymaerax.btactics.{EqualityTactics, Idioms, SimplifierV2}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import org.scalatest.Args

import scala.language.postfixOps

/**
 * Proves Sect. 3: Safe regions with immediate pilot reaction and infinite advisory duration.
 *
 * Theorem 1: Correctness of implicit safe regions
 * Lemma 1: Equivalence between implicit and explicit region formulation
 * Corollary 1: Correctness of explicit safe regions

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
class AcasXSafe extends AcasXBase {

  /*** Invariants etc. ***/
  private val invariant = ("( (w= -1 | w=1) & " +
    "      (" +
    "\\forall t \\forall ro \\forall ho" +
    "((0 <= t & t < max(0, w * (dhf - dhd)) / a &" +
    "  ro = rv * t & ho = (w * a) / 2 * t^2 + dhd * t) |" +
    "  (t >= max(0, w * (dhf - dhd)) / a &" +
    "    ro = rv * t & ho = dhf * t - w * max(0, w * (dhf - dhd))^2 / (2*a))" +
    "-> (abs(r - ro) > rp | w * h < w * ho - hp))" +
    "      )) & ( hp>0&rp>=0&rv>=0&a>0 )").asFormula

  private val postcond = "(abs(r)>rp|abs(h)>hp)".asFormula

  private val initDomain = "w*dhd>=w*dhf|w*ao>=a".asFormula

  private lazy val absmax =
    abs('R, "abs(r)".asTerm) &
      abs('R, "abs(h)".asTerm) &
      abs('L, "abs(r-0)".asTerm)

  "ACAS X safe" should "prove use case lemma" in withMathematica { tool =>
    if (lemmaDB.get("nodelay_ucLoLemma").isDefined) lemmaDB.remove("nodelay_ucLoLemma")

    val ucLoFormula = Imply(invariant, postcond)
    val ucLoTac = implyR('R) & (andL('L)*) &
      allL(Variable("t"), Number(0))('L) &
      allL(Variable("ro"), Number(0))('L) &
      allL(Variable("ho"), Number(0))('L) & implyL('L) & Idioms.<(
      dT("Use case 1") & hideR('R, "abs(r)>rp|abs(h)>hp".asFormula) &
        EqualityTactics.abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxI"))) & dT("abbrv") &
        max('L, "max(0,w*(dhf-dhd))".asTerm) & QE & done
      ,
      dT("Absolute value") & absmax & dT("Use case 2") & QE & done
    )

    val ucLoLemma = proveBy(ucLoFormula, ucLoTac)
    ucLoLemma shouldBe 'proved
    storeLemma(ucLoLemma, Some("nodelay_ucLoLemma"))
  }

  it should "prove lower bound safe lemma" in withMathematica { tool =>
    if (lemmaDB.get("nodelay_safeLoLemma").isDefined) lemmaDB.remove("nodelay_safeLoLemma")

    // Formula from print in Theorem 1
    val safeLemmaFormula = """(w*dhd>=w*dhf|w*ao>=a)&(((w=-1|w=1)&\forall t \forall ro \forall ho (0<=t&t < maxI/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxI/a&ro=rv*t&ho=dhf*t-w*maxI^2/(2*a)->abs(r-ro)>rp|w*h < w*ho-hp))&hp>0&rp>=0&rv>=0&a>0)&maxI=max((0,w*(dhf-dhd)))->[{r'=-rv,h'=-dhd,dhd'=ao&w*dhd>=w*dhf|w*ao>=a}](((w=-1|w=1)&\forall t \forall ro \forall ho (0<=t&t < max((0,w*(dhf-dhd)))/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=max((0,w*(dhf-dhd)))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-dhd)))^2/(2*a)->abs(r-ro)>rp|w*h < w*ho-hp))&hp>0&rp>=0&rv>=0&a>0)""".stripMargin.asFormula

    val safeLemmaTac = dT("lemma") & implyR('R) & (andL('L)*) & diffSolveEnd('R) &
      dT("Before skolem") & ((allR('R) | implyR('R))*) & dT("After skolem") &
      SimplifierV2.simpTac(1) & dT("Simplified using known facts") & (allR('R)*) &
      //here we'd want to access previously introduced skolem symbol and
      // time introduced by diffSolution;goal 90
      allL(Variable("t"), "t_+t".asTerm)('L) & // t_22+t_23: t_ == t_22, t == t_23
      allL(Variable("ro"), "rv*(t_+t)".asTerm)('L) & // rv*(t_22+t_23)
      dT("Before CUT") &
      cut("0<=t+t_&t+t_<maxI/a|t+t_>=maxI/a".asFormula) & Idioms.<(
      /* use */ dT("Use Cut") &
        orL('L, "0<=t+t_&t+t_ < maxI/a|t+t_>=maxI/a".asFormula) & Idioms.<(
        dT("Goal 110") & hideL('L, initDomain) &
          allL(Variable("ho"), "w*a/2*(t+t_)^2 + dhd*(t+t_)".asTerm)('L)
          & dT("instantiate ho 1 Lo") &
          implyL('L, "0<=t_+t&t_+t < maxI/a&rv*(t_+t)=rv*(t_+t)&w*a/2*(t+t_)^2+dhd*(t+t_)=w*a/2*(t_+t)^2+dhd*(t_+t)|t_+t>=maxI/a&rv*(t_+t)=rv*(t_+t)&w*a/2*(t+t_)^2+dhd*(t+t_)=dhf*(t_+t)-w*maxI^2/(2*a)->abs(r-rv*(t_+t))>rp|w*h < w*(w*a/2*(t+t_)^2+dhd*(t+t_))-hp".asFormula)
          & Idioms.<(
          dT("left of -> 1 Lo") & orR('R) &
            hideR('R, "t_+t>=maxI/a&rv*(t_+t)=rv*(t_+t)&w*a/2*(t+t_)^2+dhd*(t+t_)=dhf*(t_+t)-w*maxI^2/(2*a)".asFormula) &
            hideL('L, "maxI=max((0,w*(dhf-dhd)))".asFormula) & QE & done,
          dT("right of -> 1 Lo") & atomicQE & done
        ) & done,
        dT("final time in straight Lo") &
          allL(Variable("ho"), "dhf*(t+t_) - w*maxI^2/(2*a)".asTerm)('L) &
          dT("instantiate ho 2 Lo") &
          implyL('L, "0<=t_+t&t_+t < maxI/a&rv*(t_+t)=rv*(t_+t)&dhf*(t+t_)-w*maxI^2/(2*a)=w*a/2*(t_+t)^2+dhd*(t_+t)|t_+t>=maxI/a&rv*(t_+t)=rv*(t_+t)&dhf*(t+t_)-w*maxI^2/(2*a)=dhf*(t_+t)-w*maxI^2/(2*a)->abs(r-rv*(t_+t))>rp|w*h < w*(dhf*(t+t_)-w*maxI^2/(2*a))-hp".asFormula)
          & Idioms.<(
          dT("left of -> 2 Lo") & orR('R) &
            hideR('R, "0<=t_+t&t_+t < maxI/a&rv*(t_+t)=rv*(t_+t)&dhf*(t+t_)-w*maxI^2/(2*a)=w*a/2*(t_+t)^2+dhd*(t_+t)".asFormula) &
            hideL('L, "maxI=max((0,w*(dhf-dhd)))".asFormula) & QE & done,
          dT("right of -> 2 Lo") & atomicQE & done
        ) & done
      ) & done
      ,
      /* show */ dT("Show Cut") & hideL('L, "maxI=max((0,w*(dhf-dhd)))".asFormula) &
        hideL('L, "\\forall ho (0<=t_+t&t_+t < maxI/a&rv*(t_+t)=rv*(t_+t)&ho=w*a/2*(t_+t)^2+dhd*(t_+t)|t_+t>=maxI/a&rv*(t_+t)=rv*(t_+t)&ho=dhf*(t_+t)-w*maxI^2/(2*a)->abs(r-rv*(t_+t))>rp|w*h < w*ho-hp)".asFormula) &
        atomicQE & done
    )

    val safeLemma = proveBy(safeLemmaFormula, safeLemmaTac)
    safeLemma shouldBe 'proved

    storeLemma(safeLemma, Some("nodelay_safeLoLemma"))
  }

  it should "prove Theorem 1: correctness of implicit safe regions" in withMathematica { tool =>
    if (lemmaDB.get("safe_implicit").isDefined) lemmaDB.remove("safe_implicit")

    //@todo prove use case lemma and lower bound safe lemma if not proved already (call other test cases, but beware of teardown)

    /*** Main safe theorem and its tactic ***/
    val safeSeq = KeYmaeraXProblemParser(io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/casestudies/acasx/sttt/safe_implicit.kyx")).mkString)

    val safeTac = implyR('R) & (andL('L)*) & loop(invariant)('R) & Idioms.<(
      dT("Base case") & prop & done
      ,
      dT("Use case") & andR('R) & Idioms.<(
        cohide2(-1, 1) & implyRi & by(lemmaDB.get("nodelay_ucLoLemma").getOrElse(throw new Exception("Lemma nodelay_ucLoLemma must be proved first"))) & done,
        (andL('L)*) & closeId & done
        ) & done
      ,
      dT("Step") & composeb('R) & generalize(invariant)('R) & Idioms.<(
        dT("Generalization Holds") & chase('R) & SimplifierV2.simpTac('R) & normalize & done
        ,
        dT("Generalization Strong Enough") &
          EqualityTactics.abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxI"))) & dT("abbrv2") &
          /*abbrv(Variable("maxI"))(AntePosition(0, PosInExpr(0::1::0::0::0::0::0::0::0::1::1::0::Nil)))*/
          cutEZ("!(w*dhd>=w*dhf|w*ao>=a) | (w*dhd>=w*dhf|w*ao>=a)".asFormula,
            cohide('R, "!(w*dhd>=w*dhf|w*ao>=a) | (w*dhd>=w*dhf|w*ao>=a)".asFormula) & prop & done) &
          orL('L, "!(w*dhd>=w*dhf|w*ao>=a) | (w*dhd>=w*dhf|w*ao>=a)".asFormula) & Idioms.<(
          hideL('L, "maxI=max((0,w*(dhf-dhd)))".asFormula) &
            hideL('L, "((w=-1|w=1)&\\forall t \\forall ro \\forall ho (0<=t&t < maxI/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxI/a&ro=rv*t&ho=dhf*t-w*maxI^2/(2*a)->abs(r-ro)>rp|w*h < w*ho-hp))&(hp>0&rp>=0&rv>=0&a>0)".asFormula) &
            dT("Before DI") &
            // TODO there must be an easier way to use evol domain false initially
            cutEZ("[{r'=-rv,h'=-dhd,dhd'=ao&w*dhd>=w*dhf|w*ao>=a}](0=1)".asFormula, // false as postcondition doesn't work
              hideR('R, "[{r'=-rv,h'=-dhd,dhd'=ao&w*dhd>=w*dhf|w*ao>=a}](((w=-1|w=1)&\\forall t \\forall ro \\forall ho (0<=t&t < max((0,w*(dhf-dhd)))/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=max((0,w*(dhf-dhd)))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-dhd)))^2/(2*a)->abs(r-ro)>rp|w*h < w*ho-hp))&(hp>0&rp>=0&rv>=0&a>0))".asFormula)
                & diffInd(auto = 'full)('R)) &
            hideL('L, "!(w*dhd>=w*dhf|w*ao>=a)".asFormula) &
            dT("After DI") & diffCut("0=1".asFormula)('R) & Idioms.<(
              /* use */ dT("After DC 1") & diffWeaken('R) & dT("after DW") &
              implyR('R) & andL('L) & cohide('L, "0=1".asFormula) & dT("before QE") & QE & done
              ,
              /* show */ dT("After DC 2") & closeId & done
          ) & done
          ,
          dT("Preparing for safeLoLemma") & (andLi*) & implyRi &
            by(lemmaDB.get("nodelay_safeLoLemma").getOrElse(throw new Exception("Lemma nodelay_safeLoLemma must be proved first"))) & done
          ) /* end orL on cutEZ */
          /* End cutUseLbl "Generalization strong enough" */
      ) /* End indStepLbl */
    )

    val safeTheorem = proveBy(safeSeq, safeTac)
    safeTheorem shouldBe 'proved
    storeLemma(safeTheorem, Some("safe_implicit"))
  }

//  it should "prove Lemma 1: equivalence between implicit and explicit region formulation" in {
//    //val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/acasx/safe_equivalence.kyx"))
//    val s = new Sequent(Nil, immutable.IndexedSeq(), immutable.IndexedSeq(
//      KeYmaeraXProblemParser(io.Source.fromFile(folder + "safe_equivalence.kyx").mkString)))
//
//    def dT(s : String) = debugT(s)
//
//    val tactic = ls(implyR) & ls(equivR) & onBranch(
//      (equivLeftLbl, dT("->") &
//        cut("w*dhf>=0 | w*dhf<0".asFormula) &
//        onBranch(
//          (cutShowLbl, ls(cohide,"w*dhf>=0 | w*dhf<0") & QE),
//          (cutUseLbl, la(orL, "w*dhf>=0 | w*dhf<0") &&
//            ( dT("w*dhf>=0") &
//              la(andL, "(w*dhf>=0->(-rp<=r&r < -rp-rv*min((0,w*dhd))/a->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp)&(-rp-rv*min((0,w*dhd))/a<=r&r<=rp-rv*min((0,w*dhd))/a->w*h < (-min((0,w*dhd))^2)/(2*a)-hp)&(rp-rv*min((0,w*dhd))/a < r&r<=rp+rv*max((0,w*(dhf-dhd)))/a->w*rv^2*h < a/2*(r-rp)^2+w*rv*dhd*(r-rp)-rv^2*hp)&(rp+rv*max((0,w*(dhf-dhd)))/a < r->rv=0|w*rv*h < w*dhf*(r-rp)-rv*max((0,w*(dhf-dhd)))^2/(2*a)-rv*hp))&(w*dhf < 0->(-rp<=r&r < -rp+rv*max((0,w*(dhf-dhd)))/a->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp)&(-rp+rv*max((0,w*(dhf-dhd)))/a<=r->rv=0&r>rp|w*rv*h < w*dhf*(r+rp)-rv*max((0,w*(dhf-dhd)))^2/(2*a)-rv*hp))") &
//              la(hide, "w*dhf < 0->(-rp<=r&r < -rp+rv*max((0,w*(dhf-dhd)))/a->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp)&(-rp+rv*max((0,w*(dhf-dhd)))/a<=r->rv=0&r>rp|w*rv*h < w*dhf*(r+rp)-rv*max((0,w*(dhf-dhd)))^2/(2*a)-rv*hp)") &
//              la(implyL, "w*dhf>=0->(-rp<=r&r < -rp-rv*min((0,w*dhd))/a->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp)&(-rp-rv*min((0,w*dhd))/a<=r&r<=rp-rv*min((0,w*dhd))/a->w*h < (-min((0,w*dhd))^2)/(2*a)-hp)&(rp-rv*min((0,w*dhd))/a < r&r<=rp+rv*max((0,w*(dhf-dhd)))/a->w*rv^2*h < a/2*(r-rp)^2+w*rv*dhd*(r-rp)-rv^2*hp)&(rp+rv*max((0,w*(dhf-dhd)))/a < r->rv=0|w*rv*h < w*dhf*(r-rp)-rv*max((0,w*(dhf-dhd)))^2/(2*a)-rv*hp)") &&
//              (
//                ls(hide,"\\forall t \\forall ro \\forall ho (0<=t&t < max((0,w*(dhf-dhd)))/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=max((0,w*(dhf-dhd)))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-dhd)))^2/(2*a)->abs(r-ro)>rp|w*h < w*ho-hp)") & closeId,
//                (ls(skolemizeT)*) &
//                  cut("((r< -rp) | (-rp<=r & r < -rp-rv*min((0,w*dhd))/a) | (-rp-rv*min((0,w*dhd))/a<=r & r<=rp-rv*min((0,w*dhd))/a) | (rp-rv*min((0,w*dhd))/a < r & r<=rp+rv*max((0,w*(dhf-dhd)))/a) | (rp+rv*max((0,w*(dhf-dhd)))/a < r))".asFormula)
//                  & onBranch(
//                  (cutShowLbl, QE),
//                  (cutUseLbl,
//                    abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxA"))) &
//                      abbrv("min((0,w*dhd))".asTerm, Some(Variable("minA"))) &
//                      la(MinMaxT, "", Some("max(0,w*(dhf-dhd))".asTerm)) &
//                      la(MinMaxT, "", Some("min(0,w*dhd)".asTerm)) &
//                      ls(AbsT, "", Some("abs(r-ro)".asTerm)) &
//                      la(orL, "r < -rp|-rp<=r&r < -rp-rv*minA/a|-rp-rv*minA/a<=r&r<=rp-rv*minA/a|rp-rv*minA/a < r&r<=rp+rv*maxA/a|rp+rv*maxA/a < r") &&
//                      (dT("r<-rp") & la(hide,"((-rp<=r&r < -rp-rv*minA/a->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp)&(-rp-rv*minA/a<=r&r<=rp-rv*minA/a->w*h < (-minA^2)/(2*a)-hp)&(rp-rv*minA/a < r&r<=rp+rv*maxA/a->w*rv^2*h < a/2*(r-rp)^2+w*rv*dhd*(r-rp)-rv^2*hp)&(rp+rv*maxA/a < r->rv=0|w*rv*h < w*dhf*(r-rp)-rv*maxA^2/(2*a)-rv*hp))") & QE,
//                        la(andL, "(-rp<=r&r < -rp-rv*minA/a->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp)&(-rp-rv*minA/a<=r&r<=rp-rv*minA/a->w*h < (-minA^2)/(2*a)-hp)&(rp-rv*minA/a < r&r<=rp+rv*maxA/a->w*rv^2*h < a/2*(r-rp)^2+w*rv*dhd*(r-rp)-rv^2*hp)&(rp+rv*maxA/a < r->rv=0|w*rv*h < w*dhf*(r-rp)-rv*maxA^2/(2*a)-rv*hp)") &
//                          la(orL, "-rp<=r&r < -rp-rv*minA/a|-rp-rv*minA/a<=r&r<=rp-rv*minA/a|rp-rv*minA/a < r&r<=rp+rv*maxA/a|rp+rv*maxA/a < r") &&
//                          (dT("-> 1:(-rp<=r & r < -rp-rv*minA/a)") &
//                            la(hide, "(-rp-rv*minA/a<=r&r<=rp-rv*minA/a->w*h < (-minA^2)/(2*a)-hp)&(rp-rv*minA/a < r&r<=rp+rv*maxA/a->w*rv^2*h < a/2*(r-rp)^2+w*rv*dhd*(r-rp)-rv^2*hp)&(rp+rv*maxA/a < r->rv=0|w*rv*h < w*dhf*(r-rp)-rv*maxA^2/(2*a)-rv*hp)") &
//                            //**
//                            la(implyL, "-rp<=r&r < -rp-rv*minA/a->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp") &&
//                            (
//                              ls(hide,"0<=t&t < maxA/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxA/a&ro=rv*t&ho=dhf*t-w*maxA^2/(2*a)->abs_0>rp|w*h < w*ho-hp") & closeId
//                              ,
//                              ls(implyR) & ls(orR) &
//                                cut("t<= (r+rp)/rv | t > (r+rp)/rv".asFormula) & onBranch(
//                                (cutShowLbl, QE),
//                                (cutUseLbl, la(orL, "t<=(r+rp)/rv|t>(r+rp)/rv") &&
//                                  (//dT("t<= (r+rp)/rv") &
//                                    ls(hide, "abs_0>rp") &
//                                      la(orL, "0<=t&t < maxA/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxA/a&ro=rv*t&ho=dhf*t-w*maxA^2/(2*a)") &
//                                      (la(andL)*) & QE
//                                    ,
//                                    //dT("t > (r+rp)/rv") &
//                                    ls(hide, "w*h < w*ho-hp")  & la(orL, "0<=t&t < maxA/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxA/a&ro=rv*t&ho=dhf*t-w*maxA^2/(2*a)") &
//                                      (la(andL)*) & QE
//                                    )
//                                  ))
//                              )
//                            ,
//                            la(hide, "(-rp<=r&r < -rp-rv*minA/a->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp)") &
//                              la(andL, "(-rp-rv*minA/a<=r&r<=rp-rv*minA/a->w*h < (-minA^2)/(2*a)-hp)&(rp-rv*minA/a < r&r<=rp+rv*maxA/a->w*rv^2*h < a/2*(r-rp)^2+w*rv*dhd*(r-rp)-rv^2*hp)&(rp+rv*maxA/a < r->rv=0|w*rv*h < w*dhf*(r-rp)-rv*maxA^2/(2*a)-rv*hp)") &
//                              la(orL, "-rp-rv*minA/a<=r&r<=rp-rv*minA/a|rp-rv*minA/a < r&r<=rp+rv*maxA/a|rp+rv*maxA/a < r") &&
//                              (dT("-> 2: -rp-rv*minA/a<=r&r<=rp-rv*minA/a") &
//                                la(hide, "(rp-rv*minA/a < r&r<=rp+rv*maxA/a->w*rv^2*h < a/2*(r-rp)^2+w*rv*dhd*(r-rp)-rv^2*hp)&(rp+rv*maxA/a < r->rv=0|w*rv*h < w*dhf*(r-rp)-rv*maxA^2/(2*a)-rv*hp)") &
//                                la(implyL, "(-rp-rv*minA/a<=r&r<=rp-rv*minA/a->w*h < (-minA^2)/(2*a)-hp)") &&
//                                (
//                                  ls(hide,"0<=t&t < maxA/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxA/a&ro=rv*t&ho=dhf*t-w*maxA^2/(2*a)->abs_0>rp|w*h < w*ho-hp") & closeId
//                                  ,
//                                  ls(implyR) & ls(orR) & ls(hide, "abs_0>rp") & QE
//                                  )
//                                ,
//                                la(hide, "-rp-rv*minA/a<=r&r<=rp-rv*minA/a->w*h < (-minA^2)/(2*a)-hp") &
//                                  la(andL, "(rp-rv*minA/a < r&r<=rp+rv*maxA/a->w*rv^2*h < a/2*(r-rp)^2+w*rv*dhd*(r-rp)-rv^2*hp)&(rp+rv*maxA/a < r->rv=0|w*rv*h < w*dhf*(r-rp)-rv*maxA^2/(2*a)-rv*hp)") &
//                                  la(orL, "rp-rv*minA/a < r&r<=rp+rv*maxA/a|rp+rv*maxA/a < r") &&
//                                  (dT("-> 3: rv*minA/a<=r&r<=rp-rv*minA/") &
//                                    la(hide, "rp+rv*maxA/a < r->rv=0|w*rv*h < w*dhf*(r-rp)-rv*maxA^2/(2*a)-rv*hp") &
//                                    la(implyL, "rp-rv*minA/a < r&r<=rp+rv*maxA/a->w*rv^2*h < a/2*(r-rp)^2+w*rv*dhd*(r-rp)-rv^2*hp") &&
//                                    (closeId,
//                                      ls(implyR) & cut("t<= (r-rp)/rv | t > (r-rp)/rv".asFormula) & onBranch(
//                                        (cutShowLbl, QE),
//                                        (cutUseLbl, la(orL, "t<=(r-rp)/rv|t>(r-rp)/rv") &&
//                                          (//dT("t<=(r-rp)/rv") &
//                                            //ls(orR) & ls(hide, "w*h < w*ho-hp") &
//                                            la(orL, "0<=t&t < maxA/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxA/a&ro=rv*t&ho=dhf*t-w*maxA^2/(2*a)") &&
//                                              (QE, QE)
//                                            ,
//                                            //dT("t>(r-rp)/rv") &
//                                            //ls(orR) & ls(hide, "abs_0>rp") &
//                                            la(orL, "0<=t&t < maxA/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxA/a&ro=rv*t&ho=dhf*t-w*maxA^2/(2*a)") &&
//                                              (QE, QE)
//                                            ))))
//                                    ,
//                                    dT("-> 4") &
//                                      la(implyL, "rp+rv*maxA/a < r->rv=0|w*rv*h < w*dhf*(r-rp)-rv*maxA^2/(2*a)-rv*hp") &&
//                                      (closeId,
//                                        ls(implyR) & cut("t<= (r-rp)/rv | t > (r-rp)/rv".asFormula) & onBranch(
//                                          (cutShowLbl, QE),
//                                          (cutUseLbl, la(orL, "t<=(r-rp)/rv|t>(r-rp)/rv") &&
//                                            (// dT("t<=(r-rp)/rv") &
//                                              //    ls(orR) & ls(hide, "w*h < w*ho-hp") & // clean up
//                                              la(orL, "0<=t&t < maxA/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxA/a&ro=rv*t&ho=dhf*t-w*maxA^2/(2*a)") &&
//                                                (QE, QE),
//                                              // dT("t>(r-rp)/rv") &
//                                              //    ls(orR) & ls(hide, "abs_0>rp") & // clean up
//                                              la(orL, "0<=t&t < maxA/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxA/a&ro=rv*t&ho=dhf*t-w*maxA^2/(2*a)") &&
//                                                (QE, QE))))
//                                        )
//                                    )
//                                )
//                            ))
//                    )))
//              ,
//              dT("w*dhf<0") &
//                (la(andL)*) & dT("2nd mark") &
//                //	 (ls(allR)*) &
//                (ls(skolemizeT)*) &
//                //         dT("skolemized..") &
//                la(hide, "w*dhf>=0->(-rp<=r&r < -rp-rv*min((0,w*dhd))/a->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp)&(-rp-rv*min((0,w*dhd))/a<=r&r<=rp-rv*min((0,w*dhd))/a->w*h < (-min((0,w*dhd))^2)/(2*a)-hp)&(rp-rv*min((0,w*dhd))/a < r&r<=rp+rv*max((0,w*(dhf-dhd)))/a->w*rv^2*h < a/2*(r-rp)^2+w*rv*dhd*(r-rp)-rv^2*hp)&(rp+rv*max((0,w*(dhf-dhd)))/a < r->rv=0|w*rv*h < w*dhf*(r-rp)-rv*max((0,w*(dhf-dhd)))^2/(2*a)-rv*hp)") &
//                //	 dT("3rd mark") &
//                la(implyL, "w*dhf < 0->(-rp<=r&r < -rp+rv*max((0,w*(dhf-dhd)))/a->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp)&(-rp+rv*max((0,w*(dhf-dhd)))/a<=r->rv=0&r>rp|w*rv*h < w*dhf*(r+rp)-rv*max((0,w*(dhf-dhd)))^2/(2*a)-rv*hp)") &&
//                (closeId
//                  ,
//                  cut("(-rp>r)|(-rp<=r&r < -rp+rv*max((0,w*(dhf-dhd)))/a)|(-rp+rv*max((0,w*(dhf-dhd)))/a<=r)".asFormula) &
//                    onBranch(
//                      (cutShowLbl, QE)
//                      ,
//                      (cutUseLbl, la(orL, "(-rp>r)|(-rp<=r&r < -rp+rv*max((0,w*(dhf-dhd)))/a)|(-rp+rv*max((0,w*(dhf-dhd)))/a<=r)") &&
//                        (
//                          la(hide,"(-rp<=r&r < -rp+rv*max((0,w*(dhf-dhd)))/a->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp)&(-rp+rv*max((0,w*(dhf-dhd)))/a<=r->rv=0&r>rp|w*rv*h < w*dhf*(r+rp)-rv*max((0,w*(dhf-dhd)))^2/(2*a)-rv*hp)") & QE
//                          ,
//                          ls(implyR)  &
//                            abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxA"))) &
//                            la(MinMaxT, "", Some("max(0,w*(dhf-dhd))".asTerm)) &
//                            ls(AbsT, "", Some("abs(r-ro)".asTerm)) &
//                            la(andL, "(-rp<=r&r < -rp+rv*maxA/a->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp)&(-rp+rv*maxA/a<=r->rv=0&r>rp|w*rv*h < w*dhf*(r+rp)-rv*maxA^2/(2*a)-rv*hp)") &
//                            la(orL, "-rp<=r&r < -rp+rv*maxA/a|-rp+rv*maxA/a<=r") &&
//                            (
//                              dT("-> 5") &
//                                la(implyL,"(-rp<=r&r < -rp+rv*maxA/a->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp)") &&
//                                (
//                                  closeId
//                                  ,
//                                  la(hide, "-rp+rv*maxA/a<=r->rv=0&r>rp|w*rv*h < w*dhf*(r+rp)-rv*maxA^2/(2*a)-rv*hp") &
//                                    ls(orR) &
//                                    la(orL, "0<=t&t < maxA/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxA/a&ro=rv*t&ho=dhf*t-w*maxA^2/(2*a)") &&
//                                    (QE, QE)
//                                  )
//                              ,
//                              dT("-> 6") &
//                                la(hide, "-rp<=r&r < -rp+rv*maxA/a->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp") &
//                                la(implyL, "-rp+rv*maxA/a<=r->rv=0&r>rp|w*rv*h < w*dhf*(r+rp)-rv*maxA^2/(2*a)-rv*hp") &&
//                                (
//                                  closeId
//                                  ,
//                                  la(orL, "rv=0&r>rp|w*rv*h < w*dhf*(r+rp)-rv*maxA^2/(2*a)-rv*hp") &&(
//                                    dT("zerocase") &
//                                      la(orL, "0<=t&t < maxA/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxA/a&ro=rv*t&ho=dhf*t-w*maxA^2/(2*a)") & QE
//                                    ,
//                                    ls(orR) & cut("t<= (r+rp)/rv | t > (r+rp)/rv".asFormula) & onBranch(
//                                      (cutShowLbl, QE),
//                                      (cutUseLbl, la(orL, "t<=(r+rp)/rv|t>(r+rp)/rv") &&
//                                        (
//                                          dT("t<= (r+rp)/rv") & ls(hide, "abs_0>rp") &
//                                            la(orL, "0<=t&t < maxA/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxA/a&ro=rv*t&ho=dhf*t-w*maxA^2/(2*a)") &
//                                            (la(andL)*) & QE
//                                          ,
//                                          dT("t > (r+rp)/rv") & ls(hide, "w*h < w*ho-hp")  &
//                                            la(orL, "0<=t&t < maxA/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxA/a&ro=rv*t&ho=dhf*t-w*maxA^2/(2*a)") &
//                                            (la(andL)*) & QE
//                                          ))))
//                                  )
//
//                              )
//                          )
//
//                        ))
//                  )
//              ))
//        ))
//      ,
//      (equivRightLbl, dT("<-") &
//        abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxA"))) &
//        la(MinMaxT, "", Some("max(0,w*(dhf-dhd))".asTerm)) &
//        ls(andR) &&
//        (
//          ls(implyR) & ls(andR) &&
//            (
//              dT("<- 1") & ls(MinMaxT, "", Some("min(0,w*dhd)".asTerm)) & ls(implyR) & (la(andL)*) &
//                cut("rv=0|rv>0".asFormula) & onBranch(
//                (cutShowLbl, QE),
//                (cutUseLbl,
//                  la(orL, "rv=0|rv>0") && (
//                    dT("<- 1:rv=0") &
//                      la(instantiateT(Variable("t"), "0".asTerm)) &
//                      la(instantiateT(Variable("ro"), "rv*0".asTerm)) &
//                      la(instantiateT(Variable("ho"), "w*a/2*0^2+dhd*0".asTerm)) &
//                      la(implyL, "0<=0&0 < maxA/a&rv*0=rv*0&w*a/2*0^2+dhd*0=w*a/2*0^2+dhd*0|0>=maxA/a&rv*0=rv*0&w*a/2*0^2+dhd*0=dhf*0-w*maxA^2/(2*a)->abs(r-rv*0)>rp|w*h < w*(w*a/2*0^2+dhd*0)-hp") &&
//                      (
//                        QE
//                        ,
//                        la(AbsT, "", Some("abs(r-rv*0)".asTerm)) & QE
//                        )
//                    ,
//                    dT("<- 1:rv>0") &
//                      la(instantiateT(Variable("t"), "(r+rp)/rv".asTerm)) &
//                      la(instantiateT(Variable("ro"), "rv*((r+rp)/rv)".asTerm)) &
//                      la(instantiateT(Variable("ho"), "w*a/2*((r+rp)/rv)^2+dhd*((r+rp)/rv)".asTerm)) &
//                      la(implyL, "0<=(r+rp)/rv&(r+rp)/rv < maxA/a&rv*((r+rp)/rv)=rv*((r+rp)/rv)&w*a/2*((r+rp)/rv)^2+dhd*((r+rp)/rv)=w*a/2*((r+rp)/rv)^2+dhd*((r+rp)/rv)|(r+rp)/rv>=maxA/a&rv*((r+rp)/rv)=rv*((r+rp)/rv)&w*a/2*((r+rp)/rv)^2+dhd*((r+rp)/rv)=dhf*((r+rp)/rv)-w*maxA^2/(2*a)->abs(r-rv*((r+rp)/rv))>rp|w*h < w*(w*a/2*((r+rp)/rv)^2+dhd*((r+rp)/rv))-hp") &&
//                      (
//                        QE
//                        ,
//                        la(AbsT, "", Some("abs(r-rv*((r+rp)/rv))".asTerm)) & QE
//                        ))))
//              ,
//              ls(andR) &&
//                (
//                  dT("<- 2") &
//                    abbrv("min((0,w*dhd))".asTerm, Some(Variable("minA"))) &
//                    la(MinMaxT, "", Some("min((0,w*dhd))".asTerm)) &
//                    ls(implyR) & (la(andL)*) &
//                    cut("rv=0|rv>0".asFormula) & onBranch(
//                    (cutShowLbl, QE),
//                    (cutUseLbl,
//                      la(orL, "rv=0|rv>0") && (
//                        dT("<- 2:rv=0") &
//                          la(instantiateT(Variable("t"), "-minA/a".asTerm)) &
//                          la(instantiateT(Variable("ro"), "rv*(-minA/a)".asTerm)) &
//                          la(instantiateT(Variable("ho"), "w*a/2*(-minA/a)^2+dhd*(-minA/a)".asTerm)) &
//                          la(implyL, "0<=-minA/a&-minA/a < maxA/a&rv*(-minA/a)=rv*(-minA/a)&w*a/2*(-minA/a)^2+dhd*(-minA/a)=w*a/2*(-minA/a)^2+dhd*(-minA/a)|-minA/a>=maxA/a&rv*(-minA/a)=rv*(-minA/a)&w*a/2*(-minA/a)^2+dhd*(-minA/a)=dhf*(-minA/a)-w*maxA^2/(2*a)->abs(r-rv*(-minA/a))>rp|w*h < w*(w*a/2*(-minA/a)^2+dhd*(-minA/a))-hp") &&
//                          (
//                            QE
//                            ,
//                            abbrv("r-rv*(-minA/a)".asTerm, Some(Variable("absA"))) &
//                              la(AbsT, "", Some("abs(absA)".asTerm)) & QE
//                            )
//                        ,
//                        dT("<- 2:rv>0") &
//                          la(instantiateT(Variable("t"), "-minA/a".asTerm)) &
//                          la(instantiateT(Variable("ro"), "rv*(-minA/a)".asTerm)) &
//                          la(instantiateT(Variable("ho"), "w*a/2*(-minA/a)^2+dhd*(-minA/a)".asTerm)) &
//                          la(implyL, "0<=-minA/a&-minA/a < maxA/a&rv*(-minA/a)=rv*(-minA/a)&w*a/2*(-minA/a)^2+dhd*(-minA/a)=w*a/2*(-minA/a)^2+dhd*(-minA/a)|-minA/a>=maxA/a&rv*(-minA/a)=rv*(-minA/a)&w*a/2*(-minA/a)^2+dhd*(-minA/a)=dhf*(-minA/a)-w*maxA^2/(2*a)->abs(r-rv*(-minA/a))>rp|w*h < w*(w*a/2*(-minA/a)^2+dhd*(-minA/a))-hp") &&
//                          (
//                            QE
//                            ,
//                            abbrv("r-rv*(-minA/a)".asTerm, Some(Variable("absA"))) &
//                              la(AbsT, "", Some("abs(absA)".asTerm)) & QE
//                            )
//                        )))
//                  ,
//                  ls(andR) &&
//                    (
//                      dT("<- 3") & ls(MinMaxT, "", Some("min(0,w*dhd)".asTerm)) & ls(implyR)  & (la(andL)*) &
//                        cut("rv=0|rv>0".asFormula) & onBranch(
//                        (cutShowLbl, QE),
//                        (cutUseLbl,
//                          la(orL, "rv=0|rv>0") && (
//                            dT("<- 3:rv=0") &
//                              la(instantiateT(Variable("t"), "0".asTerm)) &
//                              la(instantiateT(Variable("ro"), "rv*0".asTerm)) &
//                              la(instantiateT(Variable("ho"), "w*a/2*0^2+dhd*0".asTerm)) &
//                              la(implyL, "0<=0&0 < maxA/a&rv*0=rv*0&w*a/2*0^2+dhd*0=w*a/2*0^2+dhd*0|0>=maxA/a&rv*0=rv*0&w*a/2*0^2+dhd*0=dhf*0-w*maxA^2/(2*a)->abs(r-rv*0)>rp|w*h < w*(w*a/2*0^2+dhd*0)-hp") &&
//                              (
//                                QE
//                                ,
//                                la(AbsT, "", Some("abs(r-rv*0)".asTerm)) & QE
//                                )
//                            ,
//                            dT("<- 3:rv>0") &
//                              la(instantiateT(Variable("t"), "(r-rp)/rv".asTerm)) &
//                              la(instantiateT(Variable("ro"), "rv*((r-rp)/rv)".asTerm)) &
//                              la(instantiateT(Variable("ho"), "w*a/2*((r-rp)/rv)^2+dhd*((r-rp)/rv)".asTerm)) &
//                              la(implyL, "0<=(r-rp)/rv&(r-rp)/rv < maxA/a&rv*((r-rp)/rv)=rv*((r-rp)/rv)&w*a/2*((r-rp)/rv)^2+dhd*((r-rp)/rv)=w*a/2*((r-rp)/rv)^2+dhd*((r-rp)/rv)|(r-rp)/rv>=maxA/a&rv*((r-rp)/rv)=rv*((r-rp)/rv)&w*a/2*((r-rp)/rv)^2+dhd*((r-rp)/rv)=dhf*((r-rp)/rv)-w*maxA^2/(2*a)->abs(r-rv*((r-rp)/rv))>rp|w*h < w*(w*a/2*((r-rp)/rv)^2+dhd*((r-rp)/rv))-hp") &&
//                              (
//                                QE
//                                ,
//                                la(AbsT, "", Some("abs(r-rv*((r-rp)/rv))".asTerm)) & QE
//                                ))))
//                      ,
//                      dT("<- 4") & (la(andL)*) & ls(implyR)  &
//                        cut("rv=0|rv>0".asFormula) & onBranch(
//                        (cutShowLbl, QE),
//                        (cutUseLbl,
//                          la(orL, "rv=0|rv>0") && (
//                            dT("<- 4:rv=0") &
//                              ls(orR) & ls(hide, "w*rv*h < w*dhf*(r-rp)-rv*maxA^2/(2*a)-rv*hp") & QE
//                            ,
//                            dT("<- 4:rv>0") &
//                              ls(orR) & ls(hide, "rv=0") &
//                              la(instantiateT(Variable("t"), "(r-rp)/rv".asTerm)) &
//                              la(instantiateT(Variable("ro"), "rv*((r-rp)/rv)".asTerm)) &
//                              la(instantiateT(Variable("ho"), "dhf*((r-rp)/rv)-w*maxA^2/(2*a)".asTerm)) &
//                              la(implyL, "0<=(r-rp)/rv&(r-rp)/rv < maxA/a&rv*((r-rp)/rv)=rv*((r-rp)/rv)&dhf*((r-rp)/rv)-w*maxA^2/(2*a)=w*a/2*((r-rp)/rv)^2+dhd*((r-rp)/rv)|(r-rp)/rv>=maxA/a&rv*((r-rp)/rv)=rv*((r-rp)/rv)&dhf*((r-rp)/rv)-w*maxA^2/(2*a)=dhf*((r-rp)/rv)-w*maxA^2/(2*a)->abs(r-rv*((r-rp)/rv))>rp|w*h < w*(dhf*((r-rp)/rv)-w*maxA^2/(2*a))-hp") &&
//                              (
//                                ls(hide, "w*rv*h < w*dhf*(r-rp)-rv*maxA^2/(2*a)-rv*hp") & ls(orR) &
//                                  ls(hide, "0<=(r-rp)/rv&(r-rp)/rv < maxA/a&rv*((r-rp)/rv)=rv*((r-rp)/rv)&dhf*((r-rp)/rv)-w*maxA^2/(2*a)=w*a/2*((r-rp)/rv)^2+dhd*((r-rp)/rv)") & QE
//                                ,
//                                la(AbsT, "", Some("abs(r-rv*((r-rp)/rv))".asTerm)) & QE
//                                )
//                            )))
//                      )
//                  )
//              )
//          ,
//          ls(implyR) & ls(andR) && (
//            dT("<- 5")  & (la(andL)*) &
//              cut("rv=0|rv>0".asFormula) & onBranch(
//              (cutShowLbl, QE),
//              (cutUseLbl,
//                la(orL, "rv=0|rv>0") && (
//                  dT("<- 5:rv=0") &
//                    la(instantiateT(Variable("t"), "0".asTerm)) &
//                    la(instantiateT(Variable("ro"), "rv*0".asTerm)) &
//                    la(instantiateT(Variable("ho"), "w*a/2*0^2+dhd*0".asTerm)) &
//                    la(implyL, "0<=0&0 < maxA/a&rv*0=rv*0&w*a/2*0^2+dhd*0=w*a/2*0^2+dhd*0|0>=maxA/a&rv*0=rv*0&w*a/2*0^2+dhd*0=dhf*0-w*maxA^2/(2*a)->abs(r-rv*0)>rp|w*h < w*(w*a/2*0^2+dhd*0)-hp") &&
//                    (
//                      QE
//                      ,
//                      la(AbsT, "", Some("abs(r-rv*0)".asTerm)) & QE
//                      )
//                  ,
//                  dT("<- 5:rv>0") &
//                    la(instantiateT(Variable("t"), "(r+rp)/rv".asTerm)) &
//                    la(instantiateT(Variable("ro"), "rv*((r+rp)/rv)".asTerm)) &
//                    la(instantiateT(Variable("ho"), "w*a/2*((r+rp)/rv)^2+dhd*((r+rp)/rv)".asTerm)) &
//                    la(implyL, "0<=(r+rp)/rv&(r+rp)/rv < maxA/a&rv*((r+rp)/rv)=rv*((r+rp)/rv)&w*a/2*((r+rp)/rv)^2+dhd*((r+rp)/rv)=w*a/2*((r+rp)/rv)^2+dhd*((r+rp)/rv)|(r+rp)/rv>=maxA/a&rv*((r+rp)/rv)=rv*((r+rp)/rv)&w*a/2*((r+rp)/rv)^2+dhd*((r+rp)/rv)=dhf*((r+rp)/rv)-w*maxA^2/(2*a)->abs(r-rv*((r+rp)/rv))>rp|w*h < w*(w*a/2*((r+rp)/rv)^2+dhd*((r+rp)/rv))-hp") &&
//                    (
//                      QE
//                      ,
//                      la(AbsT, "", Some("abs(r-rv*((r+rp)/rv))".asTerm)) & QE
//                      ))))
//            ,
//            dT("<- 6") & (la(andL)*) & ls(implyR) &
//              cut("rv=0|rv>0".asFormula) & onBranch(
//              (cutShowLbl, QE),
//              (cutUseLbl,
//                la(orL, "rv=0|rv>0") && (
//                  dT("<- 6:rv=0") & ls(orR)  &
//                    cut("r>rp|r<=rp".asFormula) & onBranch(
//                    (cutShowLbl, ls(cohide, "r>rp|r<=rp") & QE),
//                    (cutUseLbl, la(orL, "r>rp|r<=rp") &&
//                      (
//                        ls(hide, "w*rv*h < w*dhf*(r+rp)-rv*maxA^2/(2*a)-rv*hp") & QE
//                        ,
//                        ls(hide, "rv=0&r>rp") &
//                          cut("(h+w*maxA^2/(2*a))/dhf>=maxA/a|(h+w*maxA^2/(2*a))/dhf<maxA/a".asFormula) & onBranch(
//                          (cutShowLbl,ls(hide,"w*rv*h < w*dhf*(r+rp)-rv*maxA^2/(2*a)-rv*hp") & QE),
//                          (cutUseLbl, la(orL, "(h+w*maxA^2/(2*a))/dhf>=maxA/a|(h+w*maxA^2/(2*a))/dhf<maxA/a") &&
//                            (
//                              la(instantiateT(Variable("t"), "(h+w*maxA^2/(2*a))/dhf".asTerm)) &
//                                la(instantiateT(Variable("ro"), "0".asTerm)) &
//                                la(instantiateT(Variable("ho"), "h".asTerm)) &
//                                la(implyL) &&
//                                (ls(hide,"w*rv*h < w*dhf*(r+rp)-rv*maxA^2/(2*a)-rv*hp") & dT("foo1") & QE, QE)
//                              ,
//                              la(instantiateT(Variable("t"), "maxA/a".asTerm)) &
//                                la(instantiateT(Variable("ro"), "0".asTerm)) &
//                                la(instantiateT(Variable("ho"), "dhf*maxA/a-w*maxA^2/(2*a)".asTerm)) &
//                                la(implyL) &&
//                                (ls(hide,"w*rv*h < w*dhf*(r+rp)-rv*maxA^2/(2*a)-rv*hp") & QE, QE)
//                              ))))))
//                  ,
//                  dT("<- 6:rv>0") & ls(orR) & ls(hide, "rv=0&r>rp") &
//                    la(instantiateT(Variable("t"), "(r+rp)/rv".asTerm)) &
//                    la(instantiateT(Variable("ro"), "rv*((r+rp)/rv)".asTerm)) &
//                    la(instantiateT(Variable("ho"), "dhf*((r+rp)/rv)-w*maxA^2/(2*a)".asTerm)) &
//                    la(implyL, "0<=(r+rp)/rv&(r+rp)/rv < maxA/a&rv*((r+rp)/rv)=rv*((r+rp)/rv)&dhf*((r+rp)/rv)-w*maxA^2/(2*a)=w*a/2*((r+rp)/rv)^2+dhd*((r+rp)/rv)|(r+rp)/rv>=maxA/a&rv*((r+rp)/rv)=rv*((r+rp)/rv)&dhf*((r+rp)/rv)-w*maxA^2/(2*a)=dhf*((r+rp)/rv)-w*maxA^2/(2*a)->abs(r-rv*((r+rp)/rv))>rp|w*h < w*(dhf*((r+rp)/rv)-w*maxA^2/(2*a))-hp") &&
//                    (QE, la(AbsT, "", Some("abs(r-rv*((r+rp)/rv))".asTerm)) & QE)
//                  )))
//            )
//          )
//
//        )
//    )
//
//    val equivalence = helper.runTactic(tactic, new RootNode(s))
//    equivalence shouldBe 'closed
//
//    // create evidence (traces input into tool and output from tool)
//    val equivalenceEvidence = new ToolEvidence(immutable.Map("input" -> s.toString, "output" -> "true")) :: Nil
//    // add lemma into DB, which creates an ID for it. use the ID to apply the lemma
//    val equivalenceLemmaID = lemmaDB.add(Lemma(equivalence.provableWitness, equivalenceEvidence, Some("safe_equivalence")))
//    print("safe_equivalence.kyx equivalence lemma proof saved as lemma " + equivalenceLemmaID)
//  }
//
//  it should "prove Corollary 1: explicit region safety from implicit region safety and conditional equivalence" in {
//    // proof dependency
//    // execute other proofs to create lemmas, so that this proof does not fail when run in isolation on
//    // a fresh machine
//    if (!(lemmaDB.contains("safe_implicit") && lemmaDB.contains("nodelay_ucLoLemma"))) {
//      println("Proving safe_implicit lemma and nodelay_ucLoLemma...")
//      runTest("ACAS X safe should prove Theorem 1: correctness of implicit safe regions", new Args(nilReporter))
//      println("...done")
//    }
//    if (!lemmaDB.contains("safe_equivalence")) {
//      println("Proving safe_equivalence lemma...")
//      runTest("ACAS X safe should prove Lemma 1: equivalence between implicit and explicit region formulation", new Args(nilReporter))
//      println("...done")
//    }
//
//    // rerun initialization (runTest runs afterEach() at the end)
//    beforeEach()
//
//    // load lemmas
//
//    val acasximplicit = KeYmaeraXProblemParser(io.Source.fromFile(folder + "safe_implicit.kyx").mkString)
//    val acasxexplicit = KeYmaeraXProblemParser(io.Source.fromFile(folder + "safe_explicit.kyx").mkString)
//    val implicitExplicit = KeYmaeraXProblemParser(io.Source.fromFile(folder + "safe_equivalence.kyx").mkString)
//    val lem = true
//    val acasximplicitP = if (lem && lemmaDB.contains("safe_implicit")) LookupLemma(lemmaDB, "safe_implicit").lemma.fact else Provable.startProof(acasximplicit)
//    val implicitExplicitP = if (lem && lemmaDB.contains("safe_equivalence")) LookupLemma(lemmaDB, "safe_equivalence").lemma.fact else Provable.startProof(implicitExplicit)
//
//    // extract formula fragments
//    val equivalence = implicitExplicitP.conclusion.succ.head
//    val Imply(And(a,w), Equiv(_,i)) = equivalence // extract subformulas A()&W(w) -> (Ce(...)<->Ci(...))
//    val Imply(And(_, And(_, _)), Box(Loop(_), And(u, _))) = acasximplicit
//    val ucLoFact = if (lemmaDB.contains("nodelay_ucLoLemma")) LookupLemma(lemmaDB, "nodelay_ucLoLemma").lemma.fact else Provable.startProof(Imply(And(w,And(i,a)), u))
//    val ucLoLemma = TactixLibrary.proveBy(Sequent(Nil, IndexedSeq(a, w, i), IndexedSeq(u)),
//      cut(ucLoFact.conclusion.succ.head) & onBranch(
//        (BranchLabels.cutShowLbl, cohide(2) & by(ucLoFact)),
//        (BranchLabels.cutUseLbl, implyL(-4) & (andR(2) & (andR(2) & (closeId , closeId), closeId), closeId) )
//      )
//    )
//    ucLoLemma.subgoals shouldBe ucLoFact.subgoals
//    if (!ucLoLemma.isProved) println("Proof will be partial. Prove other lemmas first")
//
//    if (!acasximplicitP.isProved || !implicitExplicitP.isProved) println("Proof will be partial. Prove other lemmas first")
//    val proof = acasXcongruence(implicitExplicitP, acasximplicitP, ucLoLemma, acasxexplicit, QE)
//
//    println("Proof has " + proof.subgoals.size + " open goals")
//    proof shouldBe 'proved
//    proof.proved shouldBe Sequent(Nil, IndexedSeq(), IndexedSeq(acasxexplicit))
//    // finalize resulting proof as a lemma
//    lemmaDB.add(Lemma(proof, ToolEvidence(immutable.Map("input" -> acasxexplicit.toString, "output" -> "true")) :: Nil, Some("safe_explicit")))
//  }

}
