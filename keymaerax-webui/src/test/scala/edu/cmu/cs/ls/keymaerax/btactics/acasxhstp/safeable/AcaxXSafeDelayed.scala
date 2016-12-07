/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.btactics.acasxhstp.safeable

import edu.cmu.cs.ls.keymaerax.bellerophon.{OnAll, PosInExpr, SuccPosition}
import edu.cmu.cs.ls.keymaerax.btactics.BelleLabels._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.acasxhstp.safeable.CondCongruence._
import edu.cmu.cs.ls.keymaerax.btactics.{EqualityTactics, Idioms, SimplifierV2}
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
    "   0 <= t & t < max(0,d) & ht = -(w*ad)/(2)*t^2 + dho*t |"+
    "   (hd  = -(w*ad)/(2)* max(0,d)^2+ dho*max(0,d) & dhd-dho = -w*ad* max(0,d)) &"+
    "   ( 0<=t-max(0,d) & t-max(0,d) < (max(0,w*(dhf-dhd)))/(ar) & ht-hd  =(w*ar)/(2)*(t-max(0,d))^2+ dhd * (t-max(0,d)) |"+
    "     t-max(0,d) >= (max(0,w*(dhf-dhd)))/(ar) & ht-hd =dhf*(t-max(0,d))-(w*max(0,w*(dhf-dhd))^2)/(2*ar) ))"+
    "  -> ( abs(r-rt) > rp |  w*(h-ht)  < -hp) )) & (rp >= 0 & hp > 0 & rv >= 0 & ar > 0 & ad >= 0 & dp>=0 & dl>=0)"
    ).asFormula

  private val postcond = "(abs(r)>rp|abs(h)>hp)".asFormula

  private val initDomain = "w*dhd>=w*dhf|w*ao>=a".asFormula

  private lazy val absmax =
    abs('R, "abs(r)".asTerm) &
      abs('R, "abs(h)".asTerm) &
      abs('L, "abs(r-0)".asTerm)

  it should "prove delay use case lemma" in withMathematica { tool =>
    if (lemmaDB.contains("delay_ucLoLemma")) lemmaDB.remove("delay_ucLoLemma")

    val orConv = proveBy("(P_() | Q_()) <-> (!P_() -> Q_())".asFormula, prop)
    val maxConv = proveBy("!(0<max((0,F_()))) -> max(0,F_()) = 0".asFormula, QE)

    val ucLoFormula = Imply(invariant, postcond)
    val ucLoTac = implyR('R) & (andL('L) *) &
      allL(Variable("t"), Number(0))('L) &
      allL(Variable("ro"), Number(0))('L) &
      allL(Variable("ho"), Number(0))('L) &
      allL(Variable("hd"), "-(w*ad)/(2)* max(0,d)^2+ dho*max(0,d)".asTerm)('L) & //set h^d to the const value defined in "const"
      allL(Variable("dhd"), "-(w*ad)*max(0,d) + dho".asTerm)('L) & //set v^d to the const value defined in "const" (moving v over)
      dT("Imply") &
      implyL('L) < (
        dT("Left imply") & hideR(1) & SimplifierV2.simpTac(1) & //way too slow
          useAt(orConv)(1) & implyR(1) & useAt(maxConv)(-9) &
          SimplifierV2.simpTac(1) & //Slower
          andR(1) < (QE,
            EqualityTactics.abbrv("max((0,w*(dhf-dho)))".asTerm, Some(Variable("maxI"))) &
              max('L, "max(0,w*(dhf-dho))".asTerm) & QE)
        ,
        dT("proof imply") & absmax & QE
        )
    val ucLoLemma = proveBy(ucLoFormula, ucLoTac)
    ucLoLemma shouldBe 'proved
    storeLemma(ucLoLemma, Some("delay_ucLoLemma"))
  }


  it should "prove Theorem 2: correctness of delayed implicit safe regions" in {
    if (lemmaDB.contains("safe_delay_implicit")) lemmaDB.remove("safe_delay_implicit")
    runLemmaTest("delay_ucLoLemma", "ACAS X safe should prove delay use case lemma")
    //    runLemmaTest("nodelay_safeLoLemma", "ACAS X safe should prove lower bound safe lemma")

    withMathematica { tool =>
      beforeEach()

      /** * Main safe theorem and its tactic ***/
      val safeSeq = KeYmaeraXProblemParser(io.Source.fromInputStream(
        getClass.getResourceAsStream("/examples/casestudies/acasx/sttt/safe_delay_implicit.kyx")).mkString)

      val safeTac = implyR('R) & (andL('L) *) & loop(invariant)('R) & Idioms.<(
        (initCase, dT("Base case") & prop & done)
        ,
        (useCase, dT("Use case") & andR('R) & Idioms.<(
          cohide2(-1, 1) & implyRi &
            by(lemmaDB.get("delay_ucLoLemma").getOrElse(throw new Exception("Lemma delay_ucLoLemma must be proved first"))) & done,
          (andL('L) *) & closeId & done
        ) & done)
        ,
        (indStep, dT("Step") & nil)
      )

      val safeTheorem = proveBy(safeSeq, safeTac)

      println(safeTheorem)
      //      safeTheorem shouldBe 'proved
      //      storeLemma(safeTheorem, Some("safe_implicit"))
    }
  }


}
