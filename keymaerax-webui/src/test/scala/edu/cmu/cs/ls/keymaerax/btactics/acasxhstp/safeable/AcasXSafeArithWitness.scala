/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics.acasxhstp.safeable

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.BelleLabels._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.PolynomialArith._
import edu.cmu.cs.ls.keymaerax.btactics.acasxhstp.safeable.CondCongruence._
import edu.cmu.cs.ls.keymaerax.btactics.acasxhstp.safeable.SharedTactics._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tags.SlowTest

import scala.collection.immutable._
import scala.language.postfixOps

/**
 * Re-proves ACAS X Safe with arithmetic witnesses in place of calls to QE
 *
 * @author Yong Kiam Tan
 */
@SlowTest
class AcasXSafeArithWitness extends AcasXBase {

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
      abs('R, "abs(h)".asTerm)

  private lazy val fQE = dT("foo") & normaliseNNF &dT("foo2") & OnAll(ratTac)

  "ACAS X safe" should "prove use case lemma" in withMathematica { tool => withDatabase { db =>
    if (lemmaDB.contains("nodelay_ucLoLemma")) lemmaDB.remove("nodelay_ucLoLemma")

    val w2 = List(((List(),List((1,"abs_0","r","1"),(7,"r","-wit__5^2 + rp","1"),(1,"abs_1","h","1"),(6,"h","-wit__6^2 + hp","1"),(7,"hp","wit_^2 + wit__6^2","1"),(3,"rp","wit__2^2","1"),(3,"rv","wit__3^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("2","wit__0*wit__6"),("2","wit_*wit__0^2*wit__6"),("1","wit__0^2*wit__6^2"),("2","wit_*wit__0")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"-wit_^4*wit__0^4"),(1,"(w - 1)*wit_^2*wit__0^2 - wit__0^2*wit__6^2 - 1"),(2,"0"),(3,"0"),(4,"0")).map (s => (s._1,s._2.asTerm))))),
      ((List(),List((1,"abs_0","-r","1"),(7,"r","wit__5^2 - rp","-1"),(1,"abs_1","h","1"),(6,"h","-wit__6^2 + hp","1"),(7,"hp","wit_^2 + wit__6^2","1"),(3,"rp","wit__2^2","1"),(3,"rv","wit__3^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("2","wit__0*wit__6"),("2","wit_*wit__0^2*wit__6"),("1","wit__0^2*wit__6^2"),("2","wit_*wit__0")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"-wit_^4*wit__0^4"),(1,"(w - 1)*wit_^2*wit__0^2 - wit__0^2*wit__6^2 - 1"),(2,"0"),(3,"0"),(4,"0")).map (s => (s._1,s._2.asTerm))))),
      ((List(),List((1,"abs_0","r","1"),(7,"r","-wit__5^2 + rp","1"),(1,"abs_1","-h","1"),(6,"h","wit__6^2 - hp","-1"),(3,"rp","wit__2^2","1"),(3,"rv","wit__3^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("35097314/2280395","hp*wit__0*wit__1"),("20685253/2280395","32682806/20685253*hp*wit__0^3*wit__6 - 16341403/20685253*wit__0^3*wit__6^3 - 33716803/20685253*wit__0*wit__6"),("48786410331877/47170547514935","-2*hp*wit__0^3*wit__6 + wit__0^3*wit__6^3 - 3*wit__0*wit__6"),("45726498/2280395","-wit__0^2*wit__6^3*wit_ - wit__6*wit_"),("47851992/2280395","hp*wit__0^2*wit__6*wit__1"),("61073048/2280395","hp*wit__0^2 + 2207789/61073048*wit__0^2*wit__6^2"),("3051889678454031/139270673293960","wit__0^2*wit__6^2")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"-15268262/2280395*wit_^2*wit__0^6*wit__6^8 - 30536524/2280395*hp^4*wit_^2*wit__0^6 - hp^3*wit_^2*wit__0^4 + 1/2280395*(76341310*hp*wit_^2*wit__0^6 - 43446103*wit_^2*wit__0^4)*wit__6^6 - 3/2280395*(45804786*hp^2*wit_^2*wit__0^6 - 28203937*hp*wit_^2*wit__0^4)*wit__6^4 + 1/2280395*(106877834*hp^3*wit_^2*wit__0^6 - 38885313*hp^2*wit_^2*wit__0^4)*wit__6^2"),(1,"15268262/2280395*w*wit_^2*wit__0^4*wit__6^6 - 30536524/2280395*(hp^3*w + hp^3)*wit_^2*wit__0^4 - 1/2280395*(2280395*hp^2*w + 32816919*hp^2)*wit_^2*wit__0^2 - 1/2280395*(15268262*(4*hp*w + hp)*wit_^2*wit__0^4 - (43446103*w - 15268262)*wit_^2*wit__0^2)*wit__6^4 - hp*wit_^2 + 1/2280395*(15268262*(5*hp^2*w + 3*hp^2)*wit_^2*wit__0^4 - (41165708*hp*w - 2358683*hp)*wit_^2*wit__0^2 - 43446103*wit_^2)*wit__6^2"),(2,"-47851992/2280395*hp*wit__0^4*wit__6^2 - 35097314/2280395*hp*wit__0^2"),(3,"0"),(4,"0"),(5,"-15268262/2280395*wit__0^6*wit__6^6 - 61073048/2280395*hp^2*wit__0^4 + 1/2280395*(61073048*hp*wit__0^6 - 89172601*wit__0^4)*wit__6^4 - 35097314/2280395*hp*wit__0^2 - 2/2280395*(30536524*hp^2*wit__0^6 - 12987867*hp*wit__0^4 + 38092367*wit__0^2)*wit__6^2 - 1")).map (s => (s._1,s._2.asTerm))))),
      ((List(),List((1,"abs_0","-r","1"),(7,"r","wit__5^2 - rp","-1"),(1,"abs_1","-h","1"),(6,"h","wit__6^2 - hp","-1"),(3,"rp","wit__2^2","1"),(3,"rv","wit__3^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("35097314/2280395","hp*wit__0*wit__1"),("20685253/2280395","32682806/20685253*hp*wit__0^3*wit__6 - 16341403/20685253*wit__0^3*wit__6^3 - 33716803/20685253*wit__0*wit__6"),("48786410331877/47170547514935","-2*hp*wit__0^3*wit__6 + wit__0^3*wit__6^3 - 3*wit__0*wit__6"),("45726498/2280395","-wit__0^2*wit__6^3*wit_ - wit__6*wit_"),("47851992/2280395","hp*wit__0^2*wit__6*wit__1"),("61073048/2280395","hp*wit__0^2 + 2207789/61073048*wit__0^2*wit__6^2"),("3051889678454031/139270673293960","wit__0^2*wit__6^2")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"-15268262/2280395*wit_^2*wit__0^6*wit__6^8 - 30536524/2280395*hp^4*wit_^2*wit__0^6 - hp^3*wit_^2*wit__0^4 + 1/2280395*(76341310*hp*wit_^2*wit__0^6 - 43446103*wit_^2*wit__0^4)*wit__6^6 - 3/2280395*(45804786*hp^2*wit_^2*wit__0^6 - 28203937*hp*wit_^2*wit__0^4)*wit__6^4 + 1/2280395*(106877834*hp^3*wit_^2*wit__0^6 - 38885313*hp^2*wit_^2*wit__0^4)*wit__6^2"),(1,"15268262/2280395*w*wit_^2*wit__0^4*wit__6^6 - 30536524/2280395*(hp^3*w + hp^3)*wit_^2*wit__0^4 - 1/2280395*(2280395*hp^2*w + 32816919*hp^2)*wit_^2*wit__0^2 - 1/2280395*(15268262*(4*hp*w + hp)*wit_^2*wit__0^4 - (43446103*w - 15268262)*wit_^2*wit__0^2)*wit__6^4 - hp*wit_^2 + 1/2280395*(15268262*(5*hp^2*w + 3*hp^2)*wit_^2*wit__0^4 - (41165708*hp*w - 2358683*hp)*wit_^2*wit__0^2 - 43446103*wit_^2)*wit__6^2"),(2,"-47851992/2280395*hp*wit__0^4*wit__6^2 - 35097314/2280395*hp*wit__0^2"),(3,"0"),(4,"0"),(5,"-15268262/2280395*wit__0^6*wit__6^6 - 61073048/2280395*hp^2*wit__0^4 + 1/2280395*(61073048*hp*wit__0^6 - 89172601*wit__0^4)*wit__6^4 - 35097314/2280395*hp*wit__0^2 - 2/2280395*(30536524*hp^2*wit__0^6 - 12987867*hp*wit__0^4 + 38092367*wit__0^2)*wit__6^2 - 1")).map (s => (s._1,s._2.asTerm))))))

    val tac2 =
      w2.map(
        w =>
        {
          linearElim(w._2) & genWitnessTac(w._1,w._3,w._4) & done
        }
      )
    val ucLoFormula = Imply(invariant, postcond)
    val ucLoTac = implyR('R) & (andL('L)*) &
      allL(Variable("t"), Number(0))('L) &
      allL(Variable("ro"), Number(0))('L) &
      allL(Variable("ho"), Number(0))('L) & implyL('L) & Idioms.<(
      dT("Use case 1") & hideR('R, "abs(r)>rp|abs(h)>hp".asFormula) &
        EqualityTactics.abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxI"))) & dT("abbrv") &
        max('L, "max(0,w*(dhf-dhd))".asTerm) & SimplifierV3.fullSimpTac() & dT("foo") & QE
      ,
      dT("Absolute value") & SimplifierV3.fullSimpTac() & orR(1) & orL(-2) <(close,nil) &
        absmax & orL(-7) & OnAll(orL(-8)) & dT("Use case 2") & OnAll(fQE) & printGoal & BranchTactic(tac2)
    )

    val ucLoLemma = proveBy(ucLoFormula, ucLoTac)
    ucLoLemma shouldBe 'proved
    storeLemma(ucLoLemma, Some("nodelay_ucLoLemma"))

//    // reprove with spoon-feeding interpreter to create extractable tactic
//    val proofId = db.createProof(createAcasXProblemFile(ucLoFormula))
//    val interpreter = SpoonFeedingInterpreter(proofId, db.db.createProof, listener(db.db), SequentialInterpreter)
//    interpreter(ucLoTac, BelleProvable(ProvableSig.startProof(ucLoFormula)))
//
//    val tactic = db.extractTactic(proofId)
//    val expectedTactic = BelleParser(io.Source.frcd omInputStream(getClass.getResourceAsStream("/examples/casestudies/acasx/sttt/safe_uclo.kyt")).mkString)
//    tactic shouldBe expectedTactic
  }}
  
}
