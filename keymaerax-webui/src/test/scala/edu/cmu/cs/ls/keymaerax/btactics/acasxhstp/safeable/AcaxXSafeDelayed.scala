/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.btactics.acasxhstp.safeable

import edu.cmu.cs.ls.keymaerax.bellerophon.{OnAll, PosInExpr, SuccPosition}
import edu.cmu.cs.ls.keymaerax.btactics.BelleLabels._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.acasxhstp.safeable.CondCongruence._
import edu.cmu.cs.ls.keymaerax.btactics.{SimplifierV2, _}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tags.SlowTest

import scala.collection.immutable._
import scala.language.postfixOps

/**
  * Proves Sect. 4: Safe region for a delayed pilot response
  *
  * Theorem 2: Correctness of implicit delayed safe regions

  * @see Jean-Baptiste Jeannin et al.: A Formally Verified Hybrid System for Safe Advisories in the Next-Generation
  *      Airborne Collision Avoidance System, STTT.
  *
  * @author Khalil Ghorbal
  * @author Jean-Baptiste Jeannin
  * @author Yanni A. Kouskoulas
  * @author Stefan Mitsch
  * @author Andre Platzer
  *
  * @author Yong Kiam Tan (porting from KeYmaera)
  */
@SlowTest
class AcaxXSafeDelayed extends AcasXBase {

  it should "parse Theorem 2: correctness of implicit safe regions" in {
    val safeSeq = KeYmaeraXProblemParser(io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/casestudies/acasx/sttt/safe_delay_implicit.kyx")).mkString)
  }

  /*** Invariants etc. ***/
  private val invariant = ("( (w= -1 | w=1) & " +
    "\\forall t \\forall rt \\forall ht \\forall hd \\forall dhd"+
    "((rt  = rv * t & "+
    "   (0 <= t & t < max(0,d) & ht = -(w*ad)/(2)*t^2 + dho*t |"+
    "   (hd  = -(w*ad)/(2)* max(0,d)^2+ dho*max(0,d) & dhd-dho = -w*ad* max(0,d)) &"+
    "   ( 0<=t-max(0,d) & t-max(0,d) < (max(0,w*(dhf-dhd)))/(ar) & ht-hd  =(w*ar)/(2)*(t-max(0,d))^2+ dhd * (t-max(0,d)) |"+
    "     t-max(0,d) >= (max(0,w*(dhf-dhd)))/(ar) & ht-hd =dhf*(t-max(0,d))-(w*max(0,w*(dhf-dhd))^2)/(2*ar) )))"+
    "  -> ( abs(r-rt) > rp |  w*(h-ht)  < -hp) )) & (rp >= 0 & hp > 0 & rv >= 0 & ar > 0 & ad >= 0 & dp>=0 & dl>=0)"
    ).asFormula

  private val postcond = "(abs(r)>rp|abs(h)>hp)".asFormula

  private val initDomain = "w*dhd>=w*dhf|w*ao>=a".asFormula

  private lazy val absmax =
    abs('R, "abs(r)".asTerm) &
      abs('R, "abs(h)".asTerm) &
      abs('L, "abs(r-0)".asTerm)

  it should "prove delay use case lemma" ignore withMathematica { tool =>
    if (lemmaDB.contains("delay_ucLoLemma"))
      lemmaDB.remove("delay_ucLoLemma")

    val orConv = proveBy("(P_() | Q_()) <-> (!P_() -> Q_())".asFormula, prop)
    val maxConv = proveBy("!(0<max((0,F_()))) -> max(0,F_()) = 0".asFormula, QE)

    val ucLoFormula = Imply(invariant, postcond)

    //The main change in this tactic from the no-delay case was the extra quantifiers
    val ucLoTac = implyR('R) & (andL('L) *) &
      allL(Variable("t"), Number(0))('L) &
      //todo: allL doesn't seem to be correctly checking that the variable being instantiated actually exists
      allL(Variable("rt"), Number(0))('L) &
      allL(Variable("ht"), Number(0))('L) &
      allL(Variable("hd"), "-(w*ad)/(2)* max(0,d)^2+ dho*max(0,d)".asTerm)('L) & //set h^d to the const value defined in "const"
      allL(Variable("dhd"), "-(w*ad)*max(0,d) + dho".asTerm)('L) & //set v^d to the const value defined in "const" (moving v over)
      dT("Imply") &
      implyL('L) < (
        dT("Use case 1") & hideR('R, "abs(r)>rp|abs(h)>hp".asFormula) &
          EqualityTactics.abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxI"))) & dT("abbrv") &
          max('L, "max(0,w*(dhf-dhd))".asTerm) & QE & done,
        dT("Absolute value") & absmax & QE
        )
    val ucLoLemma = proveBy(ucLoFormula, ucLoTac)
    ucLoLemma shouldBe 'proved
    storeLemma(ucLoLemma, Some("delay_ucLoLemma"))
  }

  it should "foo"  in withMathematica { tool =>
    val antes = IndexedSeq(" tl<=dl".asFormula,
      " d<=0->w*dho>=w*dhf|w*a>=ar".asFormula,
      " tl=0".asFormula,
      " w*a>=-ad".asFormula,
      " w=-1|w=1".asFormula,
      " \\forall t \\forall rt \\forall ht \\forall hd \\forall dhd (rt=rv*t&(0<=t&t < max((0,d))&ht=-w*ad/2*t^2+dho*t|(hd=-w*ad/2*max((0,d))^2+dho*max((0,d))&dhd-dho=-w*ad*max((0,d)))&(0<=t-max((0,d))&t-max((0,d)) < max((0,w*(dhf-dhd)))/ar&ht-hd=w*ar/2*(t-max((0,d)))^2+dhd*(t-max((0,d)))|t-max((0,d))>=max((0,w*(dhf-dhd)))/ar&ht-hd=dhf*(t-max((0,d)))-w*max((0,w*(dhf-dhd)))^2/(2*ar)))->abs(r-rt)>rp|w*(h-ht) < -hp)".asFormula,
      " rp>=0	".asFormula,
      " hp>0".asFormula,
      " rv>=0	".asFormula,
      " ar>0".asFormula,
      " ad>=0	".asFormula,
      "  dp>=0	".asFormula,
      "  dl>=0	".asFormula,
      "  t_>=0	".asFormula,
      "  t_+tl<=dl&(-1*t_+d<=0->w*(a*t_+dho)>=w*dhf|w*a>=ar)".asFormula)
    //"  \\forall s_ (0<=s_&s_<=t_->s_+tl<=dl&(-1*s_+d<=0->w*(a*s_+dho)>=w*dhf|w*a>=ar))".asFormula)

    val succ = IndexedSeq("rt=rv*t&(0<=t&t < max((0,-1*t_+d))&ht=-w*ad/2*t^2+(a*t_+dho)*t|(hd=-w*ad/2*max((0,-1*t_+d))^2+(a*t_+dho)*max((0,-1*t_+d))&dhd-(a*t_+dho)=-w*ad*max((0,-1*t_+d)))&(0<=t-max((0,-1*t_+d))&t-max((0,-1*t_+d)) < max((0,w*(dhf-dhd)))/ar&ht-hd=w*ar/2*(t-max((0,-1*t_+d)))^2+dhd*(t-max((0,-1*t_+d)))|t-max((0,-1*t_+d))>=max((0,w*(dhf-dhd)))/ar&ht-hd=dhf*(t-max((0,-1*t_+d)))-w*max((0,w*(dhf-dhd)))^2/(2*ar)))->abs((-rv)*t_+r-rt)>rp|w*(-(a/2*t_^2+dho*t_)+h-ht) < -hp".asFormula)

    val rewriteEq = proveBy("F_() - G_() = H_() <-> F_() = H_() + G_()".asFormula, QE)

    val pr = proveBy(Sequent(antes, succ),
      implyR(1) &
        (andL('L) *) &
        allL(Variable("t"), "t_+t".asTerm)('L) &
        allL(Variable("rt"), "rv*(t_+t)".asTerm)('L) &
        (andL('L) *) &
        dT("case splits") &
        cut("0<=t_+t & (t_+t < max(0,d)) | 0<=t_+t - max(0,d) &  t_+t - max(0,d) < max(0, w*(dhf - (-w*ad*max(0,d)+dho)))/ar | t_+t - max(0,d) >=max(0, w*(dhf - (-w*ad*max(0,d)+dho)))/ar".asFormula)
          < (
          dT("use") & orL(-19)
            < (
            dT("case 1: 0<=t_+t & (t_+t < max(0,d))") &
              nil
//              allL(Variable("ht"), "-w*ad/2*(t_+t)^2+dho*(t_+t)".asTerm )('L) &
//              allL(Variable("hd"), "-w*ad/2 * max(0,d)^2 + dho*max(0,d)".asTerm )('L) &
//              allL(Variable("dhd"), "- w * ad * max(0,d) + dho".asTerm )('L) &
//              SimplifierV2.simpTac(-6) & //Discharge the implication
//              orR(1) & orL(-6) <( eqL2R(-17)(1) & cohide2(-6,1) & QE, nil ) &
//              orL(-18) <(
//                dT("true case") &
//                hideR(1) &
//                hideL(-16) &
//                hideL(-2) &
//                (andL('L)*) &
//                exhaustiveEqL2R(true)(-20) &
//                ArithmeticSimplification.smartHide &
//                QE,
//                max('L,"max(0,d)".asTerm) & orL(-20) &
//                dT("contra") //both or branches should be false because t- max(0,d-t_) < 0
//              )
            ,
            orL(-19)
              < (
              dT("case 2") & nil, //SimplifierV2.simpTac(-18),
              dT("case 3") &
              allL(Variable("ht"), "dhf*(t_+t-max((0,d)))-w*max((0,w*(dhf-(- w * ad * max(0,d) + dho))))^2/(2*ar) + (-w*ad/2*max(0,d)^2 + dho * max(0,d))".asTerm )('L) &
              allL(Variable("hd"), "-w*ad/2 * max(0,d)^2 + dho*max(0,d)".asTerm )('L) &
              allL(Variable("dhd"), "- w * ad * max(0,d) + dho".asTerm )('L) &
              SimplifierV2.simpTac(-6) &
              dT("after insts") &
                nil //SimplifierV2.simpTac(-18)
              )
            )
          ,
          dT("show") &
          hideR(1) &
          orL(-18)
          <(
            nil,
//                (andL('L)*) & dT("cut case 1") &
//                implyRi(AntePos(18),SuccPos(0)) &
//                implyRi(AntePos(17),SuccPos(0)) &
//                implyRi(AntePos(13),SuccPos(0)) &
//                cohideR(1) & QE,
          (andL('L)*) & orL(-18) <(
            (andL('L)*) &
            ArithmeticSimplification.smartHide &
            implyRi(AntePos(19),SuccPos(0)) &
            implyRi(AntePos(18),SuccPos(0)) &
            implyRi(AntePos(12),SuccPos(0)) &
            dT("cut case 2") &
            cohideR(1) & QE
            ,
          dT("cut case 3") &
            cut("t>=0".asFormula) <(
              implyRi(AntePos(20),SuccPos(0)) &
              implyRi(AntePos(13),SuccPos(0)) &
              dT("use") &
              cohideR(1) & QE
              ,
              hideR(1) & (andL('L)*) &
              dT("cut") &
              implyRi(AntePos(19),SuccPos(0)) &
              implyRi(AntePos(9),SuccPos(0)) &
              cohideR(1) & QE
              )
            )
          )
        )
    )
  }

  it should "prove delay lower bound safe lemma" ignore withMathematica { tool =>
    if (lemmaDB.contains("delay_safeLoLemma")) lemmaDB.remove("delay_safeLoLemma")

    // Formula from print in Theorem 2
    val safeLemmaFormula = """((((w=-1|w=1)&\forall t \forall rt \forall ht \forall hd \forall dhd (rt=rv*t&(0<=t&t < max((0,d))&ht=-w*ad/2*t^2+dho*t|(hd=-w*ad/2*max((0,d))^2+dho*max((0,d))&dhd-dho=-w*ad*max((0,d)))&(0<=t-max((0,d))&t-max((0,d)) < max((0,w*(dhf-dhd)))/ar&ht-hd=w*ar/2*(t-max((0,d)))^2+dhd*(t-max((0,d)))|t-max((0,d))>=max((0,w*(dhf-dhd)))/ar&ht-hd=dhf*(t-max((0,d)))-w*max((0,w*(dhf-dhd)))^2/(2*ar)))->abs(r-rt)>rp|w*(h-ht) < -hp))&rp>=0&hp>0&rv>=0&ar>0&ad>=0&dp>=0&dl>=0)&tl=0&w*a>=-ad)&tl<=dl&(d<=0->w*dho>=w*dhf|w*a>=ar)->[{r'=-rv,h'=-dho,dho'=a,d'=-1,tl'=1&tl<=dl&(d<=0->w*dho>=w*dhf|w*a>=ar)}](((w=-1|w=1)&\forall t \forall rt \forall ht \forall hd \forall dhd (rt=rv*t&(0<=t&t < max((0,d))&ht=-w*ad/2*t^2+dho*t|(hd=-w*ad/2*max((0,d))^2+dho*max((0,d))&dhd-dho=-w*ad*max((0,d)))&(0<=t-max((0,d))&t-max((0,d)) < max((0,w*(dhf-dhd)))/ar&ht-hd=w*ar/2*(t-max((0,d)))^2+dhd*(t-max((0,d)))|t-max((0,d))>=max((0,w*(dhf-dhd)))/ar&ht-hd=dhf*(t-max((0,d)))-w*max((0,w*(dhf-dhd)))^2/(2*ar)))->abs(r-rt)>rp|w*(h-ht) < -hp))&rp>=0&hp>0&rv>=0&ar>0&ad>=0&dp>=0&dl>=0)""".stripMargin.asFormula

    val safeLemmaTac = dT("lemma") & implyR('R) & (andL('L)*) & dT("solving") & diffSolve('R) &
      dT("Before skolem") & ((allR('R) | implyR('R))*) & dT("After skolem") &
      SimplifierV2.simpTac(1) & dT("Simplified using known facts") & (allR('R)*) &
      allL(Variable("t"), "t_+t".asTerm)('L) & // t_22+t_23: t_ == t_22, t == t_23
      allL(Variable("ro"), "rv*(t_+t)".asTerm)('L) & // rv*(t_22+t_23)
      dT("Before CUT")

    val safeLemma = proveBy(safeLemmaFormula, safeLemmaTac)
    //    safeLemma shouldBe 'proved

    println(safeLemma)
    //    storeLemma(safeLemma, Some("nodelay_safeLoLemma"))
  }

  it should "prove Theorem 2: correctness of delayed implicit safe regions" ignore {
    if (lemmaDB.contains("safe_delay_implicit")) lemmaDB.remove("safe_delay_implicit")
    runLemmaTest("delay_ucLoLemma", "ACAS X safe should prove delay use case lemma")
    runLemmaTest("nodelay_safeLoLemma", "ACAS X safe should prove lower bound safe lemma")

    withMathematica { tool =>
      beforeEach()

      /** * Main safe theorem and its tactic ***/
      val safeSeq = KeYmaeraXProblemParser(io.Source.fromInputStream(
        getClass.getResourceAsStream("/examples/casestudies/acasx/sttt/safe_delay_implicit.kyx")).mkString)

      val safeTac = implyR('R) & (andL('L) *) & loop(invariant)('R) & Idioms.<(
        (initCase, dT("Base case") & prop & done)
        ,
        (useCase,
          dT("Use case") & andR('R) & Idioms.<(
            cohide2(-1, 1) & implyRi &
              by(lemmaDB.get("delay_ucLoLemma").getOrElse(throw new Exception("Lemma delay_ucLoLemma must be proved first"))) & done,
            (andL('L) *) & closeId & done
          ) & done
          )
        ,
        (indStep, dT("Step") & composeb('R) & generalize(And(invariant,"tl=0 & w*a>= -ad".asFormula))('R) &
          //Splits into G |- [discrete][ODE], then show G |- [discrete] G'  & G' |- [ODE] G
          dT("generalized") <
            (
              dT("Generalization Holds") & chase('R) &(andL('L)*) & SimplifierV2.simpTac('R) & close
              ,
              dT("Generalization Strong Enough") &
                //EqualityTactics.abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxI"))) & dT("abbrv2") &
                DifferentialTactics.diffUnpackEvolutionDomainInitially(1) &
                dT("Preparing for safeLoLemma") & (andLi *) & implyRi &
                dT("status")
              //by(lemmaDB.get("nodelay_safeLoLemma").getOrElse(throw new Exception("Lemma nodelay_safeLoLemma must be proved first"))) & done

              )

          )
      )

      val safeTheorem = proveBy(safeSeq, safeTac)

      println(safeTheorem)
      //      safeTheorem shouldBe 'proved
      //      storeLemma(safeTheorem, Some("safe_implicit"))
    }
  }


}
