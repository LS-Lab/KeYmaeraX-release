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

  private lazy val fQE = normaliseNNF & OnAll(ratTac) & OnAll(resortEqs)

  "ACAS X safe" should "prove use case lemma" in withMathematica { tool => withDatabase { db =>
    if (lemmaDB.contains("nodelay_ucLoLemma")) lemmaDB.remove("nodelay_ucLoLemma")

    val w1 = List(((List(1),List((1,"maxI","max_0","1"),(1,"max_0","0","1"),(1,"rp","wit__0^2","1"),(1,"rv","wit__1^2","1"),(5,"a","wit_^2","1"),(4,"hp","wit__5^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(),Some(List((0,"0"),(1,"0"),(2,"0"),(3,"1/2")).map (s => (s._1,s._2.asTerm))))),
      ((List(1,2),List((1,"maxI","max_0","1"),(1,"max_0","-(dhd - dhf)*w","1"),(1,"rp","wit__0^2","1"),(1,"rv","wit__1^2","1"),(4,"a","wit__5^2","1"),(3,"hp","wit__4^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__2*wit__5^3*wit_")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"0"),(1,"-(dhd - dhf)*w*wit__5^4"),(2,"0"),(3,"-wit__2^2*wit__5^6")).map (s => (s._1,s._2.asTerm))))),
      ((List(1),List((1,"maxI","max_0","1"),(1,"max_0","0","1"),(1,"rp","wit__0^2","1"),(1,"rv","wit__1^2","1"),(2,"hp","wit__5^2","1"),(2,"a","wit_^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(),Some(List((0,"0"),(1,"0"),(2,"-wit_^2")).map (s => (s._1,s._2.asTerm))))),
      ((List(1),List((1,"maxI","max_0","1"),(1,"max_0","0","1"),(1,"rp","wit__0^2","1"),(1,"rv","wit__1^2","1"),(4,"a","wit_^2","1"),(3,"hp","wit__5^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(),Some(List((0,"0"),(1,"0"),(2,"0"),(3,"-1/2")).map (s => (s._1,s._2.asTerm))))),
      ((List(1),List((1,"maxI","max_0","1"),(1,"max_0","-(dhd - dhf)*w","1"),(1,"rp","wit__0^2","1"),(1,"rv","wit__1^2","1"),(1,"hp","wit__4^2","1"),(1,"a","wit__5^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(),Some(List((0,"0"),(1,"0"),(2,"-wit__5^2")).map (s => (s._1,s._2.asTerm))))),
      ((List(1),List((1,"maxI","max_0","1"),(1,"max_0","-(dhd - dhf)*w","1"),(1,"rp","wit__0^2","1"),(1,"rv","wit__1^2","1"),(3,"a","wit__5^2","1"),(2,"hp","wit__4^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(),Some(List((0,"0"),(1,"0"),(2,"0"),(3,"-1/2")).map (s => (s._1,s._2.asTerm))))))

    val w2 = List(((List(0),List((1,"abs_0","r","1"),(4,"r","-wit__2^2 + rp","1"),(1,"abs_1","h","1"),(3,"h","-wit__3^2 + hp","1"),(1,"rp","wit__0^2","1"),(1,"rv","wit__1^2","1"),(2,"hp","wit__3^2 + wit__5^2","1"),(4,"a","wit_^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1/4","w*wit__6*wit__7 + wit__6*wit__7"),("1/4","-w*wit__3*wit__6 + wit__3*wit__6"),("1/4","w*wit__5*wit__6 + wit__5*wit__6")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"-1/4*wit__6^2*wit__7^2 - 1/4*(wit__3^2 + wit__5^2)*wit__6^2"),(1,"0"),(2,"-(w - 1)*wit__5^2 + wit__3^2 - 2*wit__7^2"),(3,"-2*(w + 1)*wit__5^2 + 1/2*(w - 3)*wit__6^2 - 2*wit__3^2")).map (s => (s._1,s._2.asTerm))))),
      ((List(0),List((1,"abs_0","-r","1"),(4,"r","wit__2^2 - rp","-1"),(1,"abs_1","h","1"),(3,"h","-wit__3^2 + hp","1"),(1,"rp","wit__0^2","1"),(1,"rv","wit__1^2","1"),(1,"hp","wit__3^2 + wit__4^2","1"),(3,"a","wit__7^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1/4","w*wit__5*wit__6 + wit__5*wit__6"),("1/4","-w*wit__3*wit__5 + wit__3*wit__5"),("1/4","w*wit__4*wit__5 + wit__4*wit__5")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"-1/4*wit__5^2*wit__6^2 - 1/4*(wit__3^2 + wit__4^2)*wit__5^2"),(1,"-(w - 1)*wit__4^2 + wit__3^2 - 2*wit__6^2"),(2,"-2*(w + 1)*wit__4^2 + 1/2*(w - 3)*wit__5^2 - 2*wit__3^2"),(3,"0")).map (s => (s._1,s._2.asTerm))))),
      ((List(0),List((1,"abs_0","r","1"),(4,"r","-wit__2^2 + rp","1"),(1,"abs_1","-h","1"),(3,"h","wit__3^2 - hp","-1"),(1,"rp","wit__0^2","1"),(1,"rv","wit__1^2","1"),(3,"hp","wit__6^2","1"),(3,"a","wit__7^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("2","wit__5*wit__6"),("1","wit__3*wit_"),("1","wit__3*wit__6")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"-wit__3^4 + 2*wit__3^2*wit__6^2 - wit__6^4"),(1,"0"),(2,"-2*wit__6^2"),(3,"-wit__3^2")).map (s => (s._1,s._2.asTerm))))),
      ((List(0),List((1,"abs_0","-r","1"),(4,"r","wit__2^2 - rp","-1"),(1,"abs_1","-h","1"),(3,"h","wit__3^2 - hp","-1"),(1,"rp","wit__0^2","1"),(1,"rv","wit__1^2","1"),(2,"hp","wit__5^2","1"),(2,"a","wit__6^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("2","wit__4*wit__5"),("1","wit__3*wit_"),("1","wit__3*wit__5")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"-wit__3^4 + 2*wit__3^2*wit__5^2 - wit__5^4"),(1,"-2*wit__5^2"),(2,"0"),(3,"-wit__3^2")).map (s => (s._1,s._2.asTerm))))))

    val tac1 =
      w1.map(
        w =>
        {
          linearElim(w._2) & genWitnessTac(w._1,w._3,w._4) & done
        }
      )

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
        max('L, "max(0,w*(dhf-dhd))".asTerm) & SimplifierV3.fullSimpTac() & orL(-7) & OnAll(fQE) & printGoal & BranchTactic(tac1)
      ,
      dT("Absolute value") & SimplifierV3.fullSimpTac() & orR(1) & orL(-2) <(close,nil) &
        absmax & orL(-7) & OnAll(orL(-8)) & dT("Use case 2") & OnAll(fQE) & printGoal & BranchTactic(tac2)
    )

    val ucLoLemma = proveBy(ucLoFormula, ucLoTac)
    print(ucLoLemma)
//    ucLoLemma shouldBe 'proved
//    storeLemma(ucLoLemma, Some("nodelay_ucLoLemma"))

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
