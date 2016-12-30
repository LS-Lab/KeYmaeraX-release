/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.btactics.acasxhstp.safeable

import edu.cmu.cs.ls.keymaerax.btactics.acasxhstp.safeable.SharedTactics._
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.BelleLabels._
import edu.cmu.cs.ls.keymaerax.btactics.SimplifierV3._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
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

  private lazy val absmax =
    abs('R, "abs(r)".asTerm) &
      abs('R, "abs(h)".asTerm) &
      abs('L, "abs(r-0)".asTerm)

  //Rewrites away every top-level equality in the antecedent
  private val exhEq:DependentTactic = new SingleGoalDependentTactic("exhaust equalities") {
    override def computeExpr(seq: Sequent): BelleExpr = {
      val foo = seq.ante.zipWithIndex.filter( _._1 match {case Equal(v:Variable,_) => true case  _ => false} )
      foo.foldLeft(nil)((tac: BelleExpr,f:(Formula,Int)) => exhaustiveEqL2R(true)(-(f._2+1)) & tac)
    }
  }

  it should "prove delay use case lemma" in withMathematica { tool =>
    if (lemmaDB.contains("delay_ucLoLemma"))
      lemmaDB.remove("delay_ucLoLemma")

    val ucLoFormula = Imply(invariant, postcond)

    //The main change in this tactic from the no-delay case was the extra quantifiers
    val ucLoTac = implyR('R) & eAndL &
      allL(Variable("t"), Number(0))('L) &
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

  it should "prove implicit delay case arithmetic" in withMathematica { tool =>
    if (lemmaDB.contains("delay_implicitArith"))
      lemmaDB.remove("delay_implicitArith")

    val antes = IndexedSeq(
      "tl<=dl".asFormula,
      "d<=0->w*dho>=w*dhf|w*a>=ar".asFormula,
      "tl=0".asFormula,
      "w*a>=-ad".asFormula,
      "w=-1|w=1".asFormula,
      "\\forall t \\forall rt \\forall ht \\forall hd \\forall dhd (rt=rv*t&(0<=t&t < max((0,d))&ht=-w*ad/2*t^2+dho*t|(hd=-w*ad/2*max((0,d))^2+dho*max((0,d))&dhd-dho=-w*ad*max((0,d)))&(0<=t-max((0,d))&t-max((0,d)) < max((0,w*(dhf-dhd)))/ar&ht-hd=w*ar/2*(t-max((0,d)))^2+dhd*(t-max((0,d)))|t-max((0,d))>=max((0,w*(dhf-dhd)))/ar&ht-hd=dhf*(t-max((0,d)))-w*max((0,w*(dhf-dhd)))^2/(2*ar)))->abs(r-rt)>rp|w*(h-ht) < -hp)".asFormula,
      "rp>=0	".asFormula,
      "hp>0".asFormula,
      "rv>=0	".asFormula,
      "ar>0".asFormula,
      "ad>=0	".asFormula,
      "dp>=0	".asFormula,
      "dl>=0	".asFormula,
      "t_>=0	".asFormula,
      "\\forall s_ (0<=s_&s_<=t_->s_+tl<=dl&(-s_+d<=0->w*(a*s_+dho)>=w*dhf|w*a>=ar))".asFormula)

    val succ = IndexedSeq("rt=rv*t&(0<=t&t < max((0,-t_+d))&ht=-w*ad/2*t^2+(a*t_+dho)*t|(hd=-w*ad/2*max((0,-t_+d))^2+(a*t_+dho)*max((0,-t_+d))&dhd-(a*t_+dho)=-w*ad*max((0,-t_+d)))&(0<=t-max((0,-t_+d))&t-max((0,-t_+d)) < max((0,w*(dhf-dhd)))/ar&ht-hd=w*ar/2*(t-max((0,-t_+d)))^2+dhd*(t-max((0,-t_+d)))|t-max((0,-t_+d))>=max((0,w*(dhf-dhd)))/ar&ht-hd=dhf*(t-max((0,-t_+d)))-w*max((0,w*(dhf-dhd)))^2/(2*ar)))->abs((-rv)*t_+r-rt)>rp|w*(-(a/2*t_^2+dho*t_)+h-ht) < -hp".asFormula)

    val rewriteEq = proveBy("F_() - G_() = H_() <-> F_() = H_() + G_()".asFormula, QE)
    val minusSimp1 = proveBy("F_() + G_() - G_() = F_()".asFormula,TactixLibrary.QE)
    val minusSimp2 = proveBy("F_() - G_() + G_() = F_()".asFormula,TactixLibrary.QE)
    val custom1 = proveBy("F_() = 0 -> (F_() = 0)".asFormula,implyR(1) & close)

    val minus = ( (t:Term) =>
      t match {
        case Minus(Plus(a,b), c) if b == c => List(minusSimp1)
        case Plus(Minus(a,b),c) if b == c => List(minusSimp2)
        case _ => List()
      }
    )

    //Common useful rewrites in this tactic (rewriteEq should be applied more judiciously)
    val fullSimp = SimplifierV3.fullSimpTac(List(custom1),taxs = composeIndex(minus,defaultTaxs,arithGroundIndex))
    val simp = SimplifierV3.simpTac(List(custom1),taxs = composeIndex(minus,defaultTaxs,arithGroundIndex))

    val pr = proveBy(Sequent(antes, succ),
      implyR('R) & eAndL &
      allL(Variable("t"), "t_+t".asTerm)('L) &
      allL(Variable("rt"), "rv*(t_+t)".asTerm)('L) &
      eAndL &
      dT("case splits") &
      cut("0<=t_+t & (t_+t < max(0,d)) | 0<=t_+t - max(0,d) &  t_+t - max(0,d) < max(0, w*(dhf - (-w*ad*max(0,d)+dho)))/ar | t_+t - max(0,d) >=max(0, w*(dhf - (-w*ad*max(0,d)+dho)))/ar".asFormula)
      //Proof proceeds by 3-way casing on this cut, and then casing on the original or formula, contradicting where possible
      <(
        dT("use") &
        eOrLPos(-18) &
        dT("cases")
        <(
          dT("case 1: 0<=t_+t & (t_+t < max(0,d))") &
          allL(Variable("s_"),"t_".asTerm )('L) &
          allL(Variable("ht"), "-w*ad/2*(t_+t)^2+dho*(t_+t)".asTerm )('L) &
          allL(Variable("hd"), "-w*ad/2 * max(0,d)^2 + dho*max(0,d)".asTerm )('L) &
          allL(Variable("dhd"), "- w * ad * max(0,d) + dho".asTerm )('L) &
          fullSimp &
          dT("pos") &
          orR(1) & orL(-6) <( eqL2R(-16)(1) & cohide2(-6,1) & QE, nil ) &
          orL(-17) <(
            dT("true case") &
            hideR(1) &
            hideL(-15) &
            hideL(-2) &
            eAndL &
            exhaustiveEqL2R(true)(-19) &
            ArithmeticSimplification.smartHide &
            QE
          ,
            dT("contra") &
            cutEZ("t - max(0,-t_+d) <0".asFormula, cohide2(-18,3) & QE) &
            eAndL &
            hideR(1) &
            simp(-19) &
            eAndL &
            hideAllBut(-23,-16,-10,1) &
            atomicQE
          )
        ,
          dT("case 2: 0<=t_+t - max(0,d) &  t_+t - max(0,d) < max(0, w*(dhf - (-w*ad*max(0,d)+dho)))/ar ") &
          eAndL &
          allL(Variable("ht"), " (w*ar/2 * ((t_+t)-max(0,d))^2)+ (-w*ad*max(0,d)+dho)*((t_+t)-max(0,d)) + (-w*ad/2*max(0,d)^2 + dho * max(0,d))".asTerm )('L) &
          allL(Variable("hd"), "-w*ad/2 * max(0,d)^2 + dho*max(0,d)".asTerm )('L) &
          allL(Variable("dhd"), "- w * ad * max(0,d) + dho".asTerm )('L) &
          simp(-6) &
          dT("after insts") &
          //  contradict the first branch
          orL(-17) <( hideAllBut(-10,-17,-18,1) & QE,nil) &
          orR(1) &  orL(-6) <( eqL2R(-16)(1) & cohide2(-6,1) & QE, nil ) &
          hideR(1) &
          EqualityTactics.abbrv("- w * ad * max(0,d) +dho".asTerm, Some(Variable("abv1"))) &
          eqL2R(-20)(-6) &
          max('L,"max(0,-t_+d)".asTerm) &
          dT("abbrv, then max split") & //note: original proof only hides one instance of this for some reason...
          hideL(-2) &
          orL(-20)
          <(
            dT("d-t_ <= 0 case") &
            eAndL &
            fullSimp &
            //hide max_0 = 0
            max('L,"max(0,d)".asTerm) &
            cutEZ("max_1 >= 0".asFormula, hideAllBut(-24,2) & QE) &
            dT("pos") &
            orL(-19) <(  //The big original case split
              dT("l branch") &
              hideL(-24) & hideL(-18) & orL(-4) &
              OnAll (exhEq & ArithmeticSimplification.smartHide & dT("before") & heuQE)
            ,
              dT("r branch") &
              cutEZ("t_>=max_1".asFormula, hideAllBut(-24,-20,-13,2) & QE) &
              hideL(-20) & max('L,"max(0,w * (dhf -abv1))".asTerm) & dT("maxsplit") & orL(-26)
              <(
                dT("lt") & hideAllBut(-16,-17,-26,1) & QE , //contra
                dT("gt") & dupL(-14) &
                allL(Variable("s_"), "max_1".asTerm )(-14) & simp(-14) & eAndL &
                implyL(-26) < ( cohide2(-21,2) & QE ,nil) &
                orL(-21)<(
                  eAndL & dT("d<=0") &
                  hideL(-23) & simp(-5) & orL(-4) &
                  OnAll (exhEq & ArithmeticSimplification.smartHide & dT("before") & QE)
                  ,
                  dT("0<=d") &
                  bCases("w*a>=ar".asFormula)
                  <(
                    dT("w*a>=ar") &
                    SimplifierV3.simpTac(List(rewriteEq))(-20) &
                    exhEq & dT("rewritten") &
                    fullSimp &
                    hideL(-20) & hideL(-18) &
                    max('L,"max((0,w*(dhf-(a*t_+dho))))".asTerm) &
                    hideL(-21) &
                    hideL(-18) &
                    hideL(-16) &
                    hideL(-1) &
                    orL(-19) & OnAll( eAndL & simp(-16)& dT("here") & orL(-2) ) &
                    OnAll(exhEq & ArithmeticSimplification.smartHide & fullSimp) & nil
                    <(
                      dT("1") & QE,
                      dT("2") & heuQE,
                      dT("3") & QE,
                      dT("4") & QE
                    )
                    ,
                    dT("!w*a>=ar")  &
                    allL(Variable("s_"), "t_".asTerm )(-24) &
                    simp(-24) &
                    eAndL &
                    SimplifierV3.simpTac(List(rewriteEq))(-20) &
                    exhEq &
                    dT("rewritten") &
                    implyL(-25) <(cohide2(-16,2) & QE, nil ) &
                    simp(-18) &
                    dT("cancel impl") &
                    //todo:smart list hideL that sorts the indices
                    hideL(-23) &
                    hideL(-22) &
                    hideL(-21) &
                    hideL(-6) &
                    ArithmeticSimplification.hideFactsAbout("dl") &
                    hideL(-1) &
                    fullSimp &
                    max('L,"max((0,w*(dhf-(a*t_+dho))))".asTerm) &
                    orL(-18) & OnAll( eAndL & simp(-16)& orL(-2) ) &
                    OnAll(exhEq & ArithmeticSimplification.smartHide & simp(1) & QE)
                  )
                )
              )
            )
          ,
            dT("other way") &
            allL(Variable("s_"),"t_".asTerm )(-14) &
            simp(-14) &
            cutEZ("0<=d & max(0,d) = d".asFormula, hideAllBut(-20,-13,2) & QE) &
            eAndL &
            exhaustiveEqL2R(true)(-24) &
            simp(-5) &
            hideL(-19) &
            ArithmeticSimplification.smartHide &
            orL(-17) <(
              eAndL &
              dT("left") &
              SimplifierV3.fullSimpTac(List(rewriteEq)) &
              exhEq &
              QE
              ,
              eAndL &
              dT("right") &
              orL(-4) & OnAll(
              SimplifierV3.fullSimpTac(List(rewriteEq)) &
              exhEq &
              QE)
            )
          )
        ,
          dT("case 3: t_+t - max(0,d) >=max(0, w*(dhf - (-w*ad*max(0,d)+dho)))/ar") &
          eAndL &
          allL(Variable("ht"), "dhf*(t_+t-max((0,d)))-w*max((0,w*(dhf-(- w * ad * max(0,d) + dho))))^2/(2*ar) + (-w*ad/2*max(0,d)^2 + dho * max(0,d))".asTerm )('L) &
          allL(Variable("hd"), "-w*ad/2 * max(0,d)^2 + dho*max(0,d)".asTerm )('L) &
          allL(Variable("dhd"), "- w * ad * max(0,d) + dho".asTerm )('L) &
          simp(-6) &
          dT("after insts") &
          //contradict the first branch
          orL(-17) <( hideAllBut(-17,-18,-10,1) & QE, nil) &
          dT("res") &
          orR(1) & orL(-6) <( eqL2R(-16)(1) & cohide2(-6,1) & QE, nil ) &
          hideR(1) &
          EqualityTactics.abbrv("- w * ad * max(0,d) +dho".asTerm, Some(Variable("abv1"))) &
          max('L,"max(0,-t_+d)".asTerm) &
          dT("abbrv, then max split") &
          orL(-20)
          <(
            dT("d-t_ <= 0 case") &
            eAndL &
            dupL(-15) &
            allL(Variable("s_"),"t_".asTerm )(-15) &
            allL(Variable("s_"),"max(0,d)".asTerm )(-24) &
            fullSimp &
            implyL(-24) <( hideAllBut(-14,-20,2) & QE,nil) &
            eAndL &
            implyL(-26) <( cohide(2) & QE,nil) &
            max('L,"max(0,d)".asTerm) &
            dT("pos") &
            orL(-27)
            <(
              eAndL &
              SimplifierV3.fullSimpTac(List(rewriteEq)) &
              dT("0>=d") &
              hideL(-2) & ArithmeticSimplification.hideFactsAbout("dl") & hideL(-1) & orL(-3) &
              OnAll (exhEq & ArithmeticSimplification.smartHide & dT("before") & heuQE) //Fast
            ,
              dT("0 < d") &
              orL(-18) //Split on the main prop
              <(
                dT("0<=t&t < max((0,w*(dhf-dhd)))/ar&ht-hd=w*ar/2*t^2+dhd*t branch") &
                eAndL &
                SimplifierV3.fullSimpTac(List(rewriteEq)) &
                exhEq &
                hideL(-2) &
                bCases("w*a>=ar".asFormula)
                <(
                  dT("w*a>=ar") &
                  hideL(-18) & hideL(-16) &
                  max('L,"max(0,w*(dhf-(0+(a*t_+dho))))".asTerm) &
                  orL(-21)
                  <(
                    dT("contra") & //because max(0,...) > 0
                    hideAllBut(-21,-19,-17,1) & QE
                  ,
                    dT("prove") &
                    max('L,"max(0,w*(dhf-(-w*ad*d+dho)))".asTerm) &
                    orL(-22) & OnAll(orL(-3)) &
                    OnAll (exhEq & ArithmeticSimplification.smartHide & ArithmeticSimplification.hideFactsAbout("dl") & dT("before") & QE)
                  )
                ,
                  dT("!w*a>=ar") &
                  orL(-3) &
                  OnAll(ArithmeticSimplification.smartHide & ArithmeticSimplification.hideFactsAbout("dl") & dT("before") & QE)
                )
              ,
                dT("t>=max((0,w*(dhf-dhd)))/ar&ht-hd=dhf*t-w*max((0,w*(dhf-dhd)))^2/(2*ar)") &
                eAndL &
                SimplifierV3.fullSimpTac(List(rewriteEq)) &
                exhEq &
                hideL(-2) &
                fullSimp &
                bCases("w*a>=ar".asFormula)
                <(
                  dT("w*a>=ar") &
                  hideL(-18) & hideL(-16) &
                  max('L,"max(0,w*(dhf-(-w*ad*d+dho)))".asTerm) & orL(-20)
                  <(
                    dT("0>=w*(dhf-(-w*ad*d+dho))") &
                    max('L,"max(0,w*(dhf-(a*t_+dho)))".asTerm) & orL(-21) &
                    OnAll(orL(-3)) &
                    OnAll (exhEq & ArithmeticSimplification.smartHide & ArithmeticSimplification.hideFactsAbout("dl") & dT("before") & QE)
                  ,
                    dT("0<w*(dhf-(-w*ad*d+dho))") &
                    max('L,"max(0,w*(dhf-(a*t_+dho)))".asTerm) & orL(-21) &
                    OnAll(orL(-3)) &
                    OnAll (eAndL & exhEq & ArithmeticSimplification.smartHide & ArithmeticSimplification.hideFactsAbout("dl"))
                      <( QE, QE, QE, fullSimp & heuQE)
                  )
                ,
                  dT("!w*a>=ar") &
                  fullSimp &
                  max('L,"max(0,w*(dhf-(-w*ad*d+dho)))".asTerm) & orL(-22) & OnAll (
                    max('L,"max(0,w*(dhf-(a*t_+dho)))".asTerm) & orL(-23) &
                    OnAll(orL(-3)) &
                    OnAll (exhEq & ArithmeticSimplification.smartHide & ArithmeticSimplification.hideFactsAbout("dl") & dT("before") & QE)
                  )
                )
              )
            )
          ,
            dT("t_ < d") &
            allL(Variable("s_"),"t_".asTerm )(-15) &
            simp(-15) &
            cutEZ("0<=d & max(0,d) = d".asFormula,
              hideAllBut(-20,-14,2) & QE) &
            eAndL &
            exhaustiveEqL2R(true)(-25) &
            simp(-6) &
            hideL(-19) &
            hideL(-2) &
            eAndL &
            orL(-18) <(
              eAndL &
              dT("left") &
              SimplifierV3.fullSimpTac(List(rewriteEq)) &
              exhaustiveEqL2R(true)(-21) &
              orL(-4) &
              OnAll(
                exhEq &
                ArithmeticSimplification.smartHide &
                ArithmeticSimplification.hideFactsAbout("dl") &
                heuQE)
              ,
              eAndL &
              dT("right") &
              SimplifierV3.fullSimpTac(List(rewriteEq)) &
              exhaustiveEqL2R(true)(-21) &
              exhaustiveEqL2R(true)(-16) &
              max('L,"max((0,w*(dhf-(-w*ad*d+dho))))".asTerm) &
              orL(-23) &
              OnAll(
                eAndL &
                orL(-4) &
                OnAll(max('L,"max((0,w*(dhf-dhd)))".asTerm) & orL('L)) &
                OnAll(
                  eAndL &
                  ArithmeticSimplification.smartHide &
                  ArithmeticSimplification.hideFactsAbout("dl") &
                  dT("QEing") & QE)
              )
            )
          )
        )
      ,
        dT("show") &
        hideR(1) &
        orL(-17) //eOrLPos inapplicable because of And in the way
        <(
          eAndL & dT("cut case 1") &
          hideAllBut(-18,-17,-14,1) & QE
        ,
          eAndL & orL(-17)
          <(
            dT("cut case 2") &
            hideAllBut(-14,-17,1) & heuQE
          ,
            dT("cut case 3") &
            cut("t>=0".asFormula)
            <(
              hideAllBut(-20,-14,1) & QE
            ,
              hideR(1) & eAndL &
              dT("cut") &
              hideAllBut(-19,-10,1) & QE
            )
          )
        )
      )
    )

    pr shouldBe 'proved
    storeLemma(pr, Some("delay_implicitArith"))
  }

  it should "prove delay lower bound safe lemma" in withMathematica { tool =>
    if (lemmaDB.contains("delay_safeLoLemma")) lemmaDB.remove("delay_safeLoLemma")

    // Formula from print in Theorem 2
    val safeLemmaFormula = """((((w=-1|w=1)&\forall t \forall rt \forall ht \forall hd \forall dhd (rt=rv*t&(0<=t&t < max((0,d))&ht=-w*ad/2*t^2+dho*t|(hd=-w*ad/2*max((0,d))^2+dho*max((0,d))&dhd-dho=-w*ad*max((0,d)))&(0<=t-max((0,d))&t-max((0,d)) < max((0,w*(dhf-dhd)))/ar&ht-hd=w*ar/2*(t-max((0,d)))^2+dhd*(t-max((0,d)))|t-max((0,d))>=max((0,w*(dhf-dhd)))/ar&ht-hd=dhf*(t-max((0,d)))-w*max((0,w*(dhf-dhd)))^2/(2*ar)))->abs(r-rt)>rp|w*(h-ht) < -hp))&rp>=0&hp>0&rv>=0&ar>0&ad>=0&dp>=0&dl>=0)&tl=0&w*a>=-ad)&tl<=dl&(d<=0->w*dho>=w*dhf|w*a>=ar)->[{r'=-rv,h'=-dho,dho'=a,d'=-1,tl'=1&tl<=dl&(d<=0->w*dho>=w*dhf|w*a>=ar)}](((w=-1|w=1)&\forall t \forall rt \forall ht \forall hd \forall dhd (rt=rv*t&(0<=t&t < max((0,d))&ht=-w*ad/2*t^2+dho*t|(hd=-w*ad/2*max((0,d))^2+dho*max((0,d))&dhd-dho=-w*ad*max((0,d)))&(0<=t-max((0,d))&t-max((0,d)) < max((0,w*(dhf-dhd)))/ar&ht-hd=w*ar/2*(t-max((0,d)))^2+dhd*(t-max((0,d)))|t-max((0,d))>=max((0,w*(dhf-dhd)))/ar&ht-hd=dhf*(t-max((0,d)))-w*max((0,w*(dhf-dhd)))^2/(2*ar)))->abs(r-rt)>rp|w*(h-ht) < -hp))&rp>=0&hp>0&rv>=0&ar>0&ad>=0&dp>=0&dl>=0)""".stripMargin.asFormula

    val safeLemmaTac = dT("lemma") & implyR('R) & eAndL & dT("solving") & diffSolve('R) &
      dT("Before skolem") & ((allR('R) | implyR('R))*) & dT("After skolem") &
      SimplifierV3.simpTac()(1) & dT("Simplified using known facts") & (allR('R)*) &
      by(lemmaDB.get("delay_implicitArith").getOrElse(throw new Exception("Lemma delay_implicitArith must be proved first")))

    val safeLemma = proveBy(safeLemmaFormula, safeLemmaTac)
    safeLemma shouldBe 'proved

    storeLemma(safeLemma, Some("delay_safeLoLemma"))
  }

  it should "prove Theorem 2: correctness of delayed implicit safe regions" in {
    if (lemmaDB.contains("safe_delay_implicit")) lemmaDB.remove("safe_delay_implicit")
    runLemmaTest("delay_ucLoLemma", "ACAS X safe should prove delay use case lemma")
    runLemmaTest("delay_implicitArith", "ACAS X safe should prove implicit delay case arithmetic")
    runLemmaTest("delay_safeLoLemma", "ACAS X safe should prove lower bound safe lemma")

    withMathematica { tool =>
      beforeEach()

      /** * Main safe theorem and its tactic ***/
      val safeSeq = KeYmaeraXProblemParser(io.Source.fromInputStream(
        getClass.getResourceAsStream("/examples/casestudies/acasx/sttt/safe_delay_implicit.kyx")).mkString)

      val safeTac = implyR('R) & eAndL & loop(invariant)('R) & Idioms.<(
        (initCase, dT("Base case") & prop & done)
        ,
        (useCase,
          dT("Use case") & andR('R) & Idioms.<(
            cohide2(-1, 1) & implyRi &
              by(lemmaDB.get("delay_ucLoLemma").getOrElse(throw new Exception("Lemma delay_ucLoLemma must be proved first"))) & done,
            eAndL & closeId & done
          ) & done
          )
        ,
        (indStep, dT("Step") & composeb('R) & generalize(And(invariant,"tl=0 & w*a>= -ad".asFormula))('R) &
          //Splits into G |- [discrete][ODE], then show G |- [discrete] G'  & G' |- [ODE] G
          dT("generalized") <
            (
              dT("Generalization Holds") & chase('R) & eAndL & dT("what") & SimplifierV3.simpTac()('R) &  dT("res") &close
              ,
              dT("Generalization Strong Enough") &
                DifferentialTactics.diffUnpackEvolutionDomainInitially(1) &
                dT("Preparing for delay_safeLoLemma") & (andLi *) & implyRi &
                dT("status") &
                by(lemmaDB.get("delay_safeLoLemma").getOrElse(throw new Exception("Lemma delay_safeLoLemma must be proved first"))) & done

              )

          )
      )

      val safeTheorem = proveBy(safeSeq, safeTac)

      println(safeTheorem)
      safeTheorem shouldBe 'proved
      storeLemma(safeTheorem, Some("safe_delay_implicit"))
    }
  }


}
