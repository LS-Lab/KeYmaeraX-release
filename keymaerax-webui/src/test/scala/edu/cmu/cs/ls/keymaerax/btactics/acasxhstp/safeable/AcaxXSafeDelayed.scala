/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.btactics.acasxhstp.safeable

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.BelleLabels._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms.{nil => _, _}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors.FormulaAugmentor
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

  //inclusive
  private def hideRange(l:Int,u:Int) : BelleExpr = {
    List.range(l,u,1).foldLeft(nil)((tac: BelleExpr,i:Int) => hideL(-i) & tac)
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

  //Rewrites away every top-level equality in the antecedent
  private val exhEq:DependentTactic = new SingleGoalDependentTactic("exhaust equalities") {
    override def computeExpr(seq: Sequent): BelleExpr = {
      val foo = seq.ante.zipWithIndex.filter( _._1 match {case Equal(v:Variable,_) => true case  _ => false} )
      foo.foldLeft(nil)((tac: BelleExpr,f:(Formula,Int)) => exhaustiveEqL2R(true)(-(f._2+1)) & tac)
    }
  }


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
      " \\forall s_ (0<=s_&s_<=t_->s_+tl<=dl&(-1*s_+d<=0->w*(a*s_+dho)>=w*dhf|w*a>=ar))".asFormula)
    //"  \\forall s_ (0<=s_&s_<=t_->s_+tl<=dl&(-1*s_+d<=0->w*(a*s_+dho)>=w*dhf|w*a>=ar))".asFormula)

    val succ = IndexedSeq("rt=rv*t&(0<=t&t < max((0,-1*t_+d))&ht=-w*ad/2*t^2+(a*t_+dho)*t|(hd=-w*ad/2*max((0,-1*t_+d))^2+(a*t_+dho)*max((0,-1*t_+d))&dhd-(a*t_+dho)=-w*ad*max((0,-1*t_+d)))&(0<=t-max((0,-1*t_+d))&t-max((0,-1*t_+d)) < max((0,w*(dhf-dhd)))/ar&ht-hd=w*ar/2*(t-max((0,-1*t_+d)))^2+dhd*(t-max((0,-1*t_+d)))|t-max((0,-1*t_+d))>=max((0,w*(dhf-dhd)))/ar&ht-hd=dhf*(t-max((0,-1*t_+d)))-w*max((0,w*(dhf-dhd)))^2/(2*ar)))->abs((-rv)*t_+r-rt)>rp|w*(-(a/2*t_^2+dho*t_)+h-ht) < -hp".asFormula)

    val rewriteEq = proveBy("F_() - G_() = H_() <-> F_() = H_() + G_()".asFormula, QE)

    val diffProps = proveBy(" F_() >= G_() | F_() < G_()".asFormula, QE)

    val subInEq = proveBy("  (C_() - A_() < D_() - B_() ) -> (A_() < B_() -> C_() < D_()) ".asFormula,QE)

    val squareNeg = proveBy("(-F_())^2 = (F_())^2".asFormula,QE)

    val pr = proveBy(Sequent(antes, succ),
      implyR(1) &
        (andL('L) *) &
        allL(Variable("t"), "t_+t".asTerm)('L) &
        allL(Variable("rt"), "rv*(t_+t)".asTerm)('L) &
        (andL('L) *) &
        dT("case splits") &
        cut("0<=t_+t & (t_+t < max(0,d)) | 0<=t_+t - max(0,d) &  t_+t - max(0,d) < max(0, w*(dhf - (-w*ad*max(0,d)+dho)))/ar | t_+t - max(0,d) >=max(0, w*(dhf - (-w*ad*max(0,d)+dho)))/ar".asFormula)
          //Proof proceeds by or casing on this cut, and then casing on the original or formula, contradicting where possible
          < (
          dT("use") & orL(-18)
            < (
              dT("case 1: 0<=t_+t & (t_+t < max(0,d))") &
              allL(Variable("s_"),"t_".asTerm )(-15) &
              SimplifierV2.simpTac(-15) &
              allL(Variable("ht"), "-w*ad/2*(t_+t)^2+dho*(t_+t)".asTerm )('L) &
              allL(Variable("hd"), "-w*ad/2 * max(0,d)^2 + dho*max(0,d)".asTerm )('L) &
              allL(Variable("dhd"), "- w * ad * max(0,d) + dho".asTerm )('L) &
              SimplifierV2.simpTac(-6) & //Discharge the implication
              dT("pos") &
              orR(1) & orL(-6) <( eqL2R(-16)(1) & cohide2(-6,1) & QE, nil ) &
              orL(-17) <(
                dT("true case") &
                hideR(1) &
                hideL(-15) &
                hideL(-2) &
                (andL('L)*) &
                exhaustiveEqL2R(true)(-19) &
                ArithmeticSimplification.smartHide &
                QE,
                dT("contra") &
                cutEZ("t - max(0,-t_+d) <0".asFormula, cohide2(-18,3) & QE) &
                (andL('L)*) &
                hideR(1) &
                SimplifierV2.simpTac(-19) &
                (andL('L)*) &
                implyRi(AntePos(22),SuccPos(0)) &
                implyRi(AntePos(15),SuccPos(0)) &
                implyRi(AntePos(9),SuccPos(0)) &
                cohideR(1) &
                atomicQE
                )
            ,
            (andL('L)*) &
            orL(-18)
            < (
              dT("case 2: 0<=t_+t - max(0,d) &  t_+t - max(0,d) < max(0, w*(dhf - (-w*ad*max(0,d)+dho)))/ar ") &
              allL(Variable("ht"), " (w*ar/2 * ((t_+t)-max(0,d))^2)+ (-w*ad*max(0,d)+dho)*((t_+t)-max(0,d)) + (-w*ad/2*max(0,d)^2 + dho * max(0,d))".asTerm )('L) &
              allL(Variable("hd"), "-w*ad/2 * max(0,d)^2 + dho*max(0,d)".asTerm )('L) &
              allL(Variable("dhd"), "- w * ad * max(0,d) + dho".asTerm )('L) &
              SimplifierV2.simpTac(-6) &
              dT("after insts") &
              //  contradict the first branch
              orL(-17) <( ArithmeticSimplification.smartHide &
                implyRi(AntePos(16),SuccPos(0)) &
                implyRi(AntePos(15),SuccPos(0)) &
                implyRi(AntePos(9),SuccPos(0)) &
                cohideR(1) & QE,nil) &
              orR(1) &  orL(-6) <( eqL2R(-16)(1) & cohide2(-6,1) & QE, nil ) &
              hideR(1) &
              EqualityTactics.abbrv("- w * ad * max(0,d) +dho".asTerm, Some(Variable("abv1"))) &
              eqL2R(-19)(-6) &
              max('L,"max(0,-1*t_+d)".asTerm) &
              dT("abbrv, then max split") & //note: original proof only hides one instance of this for some reason...
              orL(-20)
              <(
                dT("d-t_ <= 0 case") &
                (andL('L)*) & SimplifierV2.simpTac(-18) & SimplifierV2.simpTac(-23) & SimplifierV2.simpTac(-24) &
                //hide max_0 = 0
                max('L,"max(0,d)".asTerm) &
                cutEZ("max_1 >= 0".asFormula, hideR(1) & implyRi(AntePos(24),SuccPos(0)) & cohideR(1) & QE) &
                dT("pos") &
                orL(-18) <(
                  dT("l branch") &
                  SimplifierV2.simpTac(-15) &
                  hideL(-25) & hideL(-17) & hideL(-2) & orL(-4) &
                  OnAll (exhEq & ArithmeticSimplification.smartHide & dT("before") & QE) //~2minutes each
                  ,
                  dT("r branch") &
                    cutEZ("t_>=max_1".asFormula, hideR(1) &
                     //todo: easier way to hide all but some assumptions for QE
                     implyRi(AntePos(24),SuccPos(0)) & implyRi(AntePos(20),SuccPos(0)) & implyRi(AntePos(13),SuccPos(0)) & cohideR(1) & QE ) &
                  hideL(-21) & max('L,"max(0,w * (dhf -abv1))".asTerm) & dT("maxsplit") & orL(-27)
                  <(
                    dT("lt") &
                      implyRi(AntePos(26),SuccPos(0)) &
                      implyRi(AntePos(19),SuccPos(0)) & implyRi(AntePos(18),SuccPos(0)) & cohideR(1) & QE , //contra
                    dT("gt") &
                      //todo: Easier way to instantiate forall assumption twice?
                      cutEZ("\\forall s_ (0<=s_&s_<=t_->s_+tl<=dl&(-1*s_+d<=0->w*(a*s_+dho)>=w*dhf|w*a>=ar))".asFormula, cohide2(-15,2) & prop) &
                      allL(Variable("s_"), "max_1".asTerm )(-15) & SimplifierV2.simpTac(-15) & (andL('L)*) &
                      implyL(-27) < ( cohide2(-22,2) & QE ,nil) &
                      orL(-22)<(
                        (andL('L)*) & dT("d<=0") &
                        hideL(-24) & hideL(-2) & SimplifierV2.simpTac(-6) & orL(-4) &
                        OnAll (exhEq & ArithmeticSimplification.smartHide & dT("before") & QE)
                        ,
                        hideL(-2) &
                        cutEZ("w*a>=ar | !w*a>=ar".asFormula, cohideR(2) & prop) &
                        dT("0<=d") &
                        orL(-31) <(
                          dT("w*a>=ar") &
                          useAt(rewriteEq)(-20) &
                          SimplifierV2.simpTac(-20) & exhEq & dT("rewritten") &
                          hideL(-20) & hideL(-18) &
                          max('L,"max((0,w*(dhf-(a*t_+dho))))".asTerm) &
                          hideL(-21) &
                          hideL(-18) &
                          hideL(-16) &
                          hideL(-1) &
                          orL(-19) & OnAll( (andL('L)*) &SimplifierV2.simpTac(-16)& dT("here") & orL(-2) ) &
                          OnAll(exhEq & ArithmeticSimplification.smartHide &
                            SimplifierV2.simpTac(-2) &
                            SimplifierV2.simpTac(-8) &
                            SimplifierV2.simpTac(1) )
                          <(
                            dT("1") & QE,
                            dT("2") &
                            //useAt(squareNeg)(0,("-(-(a/2*t_^2+dho*t_)+h-(dhf*t-(-(-(dhf-(a*t_+dho)))^2)/(2*ar))) < -hp".asFormula).find("(-(dhf-(a*t_+dho)))^2".asTerm).get) &
                            nil //QE chokes on second case for some reason
//                              EqualityTactics.abbrv("-ad".asTerm, Some(Variable("add"))) &
//                              cutEZ("add<=0".asFormula, exhaustiveEqL2R(-14) & cohide2(-5,2) & QE) &dT("abbrv") &
//                              cutEZ("!(0>=-1*(dhf-(dho+a*t_)))".asFormula, cohide2(-13,2) & QE) & hideL(-14) & hideL(-13) & hideL(-5) &
//                              notL('L) & dT("foo") &
//                              cutEZ("d>=0".asFormula,cohide2(-11,3) & QE) & hideL(-11) &
//                              QE
                            ,
                            dT("3") & QE,dT("4") & QE)
                          ,
                          dT("!w*a>=ar")  &
                            allL(Variable("s_"), "t_".asTerm )(-24) &
                            SimplifierV2.simpTac(-24) &
                            (andL('L)*) &
                            useAt(rewriteEq)(-20) &
                            SimplifierV2.simpTac(-20) & exhEq &
                            dT("rewritten") &
                            implyL(-25) <(cohide2(-16,2) & QE, nil ) &
                            SimplifierV2.simpTac(-18) &
                            dT("cancel impl") &
                            //todo:smart list hideL that sorts the indices
                            hideL(-23) &
                            hideL(-22) &
                            hideL(-21) &
                            hideL(-6) &
                            ArithmeticSimplification.hideFactsAbout("dl") &
                            max('L,"max((0,w*(dhf-(a*t_+dho))))".asTerm) &
                            orL(-18) & OnAll( (andL('L)*) & SimplifierV2.simpTac(-16)& orL(-2) ) &
                            OnAll(exhEq & ArithmeticSimplification.smartHide & SimplifierV2.simpTac(1))
                              <(
                              dT("1") & QE,
                              dT("2") & QE,
                              dT("3") & QE,
                              dT("4") & QE)
                        )
                      )
                  )
                )
              ,
              dT("other way") &
              allL(Variable("s_"),"t_".asTerm )(-15) &
              SimplifierV2.simpTac(-15) &
              cutEZ("0<=d & max(0,d) = d".asFormula,
                hideR(1) & implyRi(AntePos(19),SuccPos(0)) & implyRi(AntePos(13),SuccPos(0)) & cohideR(1) & QE) &
              (andL('L)*) &
              exhaustiveEqL2R(true)(-25) &
              SimplifierV2.simpTac(-6) &
              hideL(-18) &
              hideL(-2) &
              ArithmeticSimplification.smartHide &
              orL(-15) <(
                (andL('L)*) &
                dT("left") &
                useAt(rewriteEq)(-24) &
                useAt(rewriteEq)(-21) &
                exhEq &
                SimplifierV2.simpTac(-5) &
                SimplifierV2.simpTac(1) &
                QE
                ,
                (andL('L)*) &
                dT("right") &
                orL(-4) & OnAll(
                useAt(rewriteEq)(-23) &
                useAt(rewriteEq)(-21) &
                exhEq &
                SimplifierV2.simpTac(-3) &
                SimplifierV2.simpTac(1) &
                QE)
                )
              )
            ,
              dT("case 3: t_+t - max(0,d) >=max(0, w*(dhf - (-w*ad*max(0,d)+dho)))/ar") &
              allL(Variable("ht"), "dhf*(t_+t-max((0,d)))-w*max((0,w*(dhf-(- w * ad * max(0,d) + dho))))^2/(2*ar) + (-w*ad/2*max(0,d)^2 + dho * max(0,d))".asTerm )('L) &
              allL(Variable("hd"), "-w*ad/2 * max(0,d)^2 + dho*max(0,d)".asTerm )('L) &
              allL(Variable("dhd"), "- w * ad * max(0,d) + dho".asTerm )('L) &
              SimplifierV2.simpTac(-6) &
              dT("after insts") &
              //contradict the first branch
              orL(-18) <( ArithmeticSimplification.smartHide &
                implyRi(AntePos(17),SuccPos(0)) &
                implyRi(AntePos(16),SuccPos(0)) &
                implyRi(AntePos(9),SuccPos(0)) &
                cohideR(1) & QE,nil) &
              dT("res") & nil
//              orR(1) &  orL(-6) <( eqL2R(-17)(1) & cohide2(-6,1) & QE, nil ) &
//              hideR(1) &
//              max('L,"max(0,-1*t_+d)".asTerm) &
//              orL(-20)
//              <(
//                dT("=0") & nil //todo: needs work, naive splits don't work
//                ,
//              dT("other way") &
//              cutEZ("0<=d & max(0,d) = d".asFormula,
//                hideR(1) & implyRi(AntePos(19),SuccPos(0)) & implyRi(AntePos(13),SuccPos(0)) & cohideR(1) & QE) &
//              (andL('L)*) &
//              exhaustiveEqL2R(true)(-23) &
//              SimplifierV2.simpTac(-6) &
//              hideL(-16) &
//              hideL(-2) &
//              ArithmeticSimplification.smartHide &
//              dT("here") &
//              orL(-15) <(
//                nil
////                (andL('L)*) &
////                orL(-4) & OnAll(
////                useAt(rewriteEq)(-22) &
////                useAt(rewriteEq)(-19) &
////                exhEq &
////                SimplifierV2.simpTac(-4) &
////                SimplifierV2.simpTac(1) &
////                QE)
//                ,
//                (andL('L)*) &
//                orL(-4) & OnAll(
//                useAt(rewriteEq)(-21) &
//                useAt(rewriteEq)(-19) &
//                exhEq &
//                dT("right") &
//                SimplifierV2.simpTac(-3) &
//                SimplifierV2.simpTac(1) &
//                QE)
//                )
//              )
            )
          )
          ,
          dT("show") &
            hideR(1) &
            orL(-17)
              <(
              (andL('L)*) & dT("cut case 1") &
              implyRi(AntePos(17),SuccPos(0)) &
              implyRi(AntePos(16),SuccPos(0)) &
              implyRi(AntePos(13),SuccPos(0)) &
              cohideR(1) & QE,
              (andL('L)*) & orL(-17) <(
                (andL('L)*) &
                  ArithmeticSimplification.smartHide &
                  dT("cut case 2") &
                  implyRi(AntePos(18),SuccPos(0)) &
                  implyRi(AntePos(17),SuccPos(0)) &
                  implyRi(AntePos(12),SuccPos(0)) &
                  cohideR(1) & QE
                ,
                dT("cut case 3") &
                  cut("t>=0".asFormula) <(
                    implyRi(AntePos(19),SuccPos(0)) &
                      implyRi(AntePos(13),SuccPos(0)) &
                      dT("use") &
                      cohideR(1) & QE
                    ,
                    hideR(1) & (andL('L)*) &
                      dT("cut") &
                      implyRi(AntePos(18),SuccPos(0)) &
                      implyRi(AntePos(9),SuccPos(0)) &
                      cohideR(1) & QE
                    )
                )
              )
        )
    )
    println(pr)

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
