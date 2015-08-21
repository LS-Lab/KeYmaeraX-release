/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
/**
 * @author Stefan Mitsch
 * @note Code Review: 2015-05-01
 */
package edu.cmu.cs.ls.keymaerax.core

import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter

/**
 * Lemmas are named Provables, supported by some evidence of how they came about.
 * Created by smitsch on 4/28/15.
 * @author Stefan Mitsch
 * @see LookupLemma
 * @see RCF.proveArithmetic
 * @see LemmaDB
 * @note Construction is not soundness-critical so constructor is not private, because Provables can only be constructed by prover core.
 */
final case class Lemma(fact: Provable, evidence: List[Evidence], name: Option[String] = None) {
  assert(fact.isProved, "Only provable facts can be added as lemmas " + fact)
  //@note could allow more general forms of lemmas.
  assert(fact.conclusion.ante.isEmpty, "Currently only lemmas with empty antecedents are allowed " + fact)
  assert(fact.conclusion.succ.size == 1, "Currently only lemmas with exactly one formula in the succedent are allowed " + fact)

  override def toString: String = {
    val lemmaName = name match {
      case Some(n) => n
      case None => ""
    }
    "Lemma \"" + lemmaName + "\".\n  " +
      KeYmaeraXPrettyPrinter(fact.conclusion.succ.head) +
      "\nEnd.\n\n" +
      evidence.mkString("\n\n")
  }

}

/** Correctness evidence for lemmas */
sealed trait Evidence
case class ProofEvidence(/*proof : List[LoadedBranch]*/) extends Evidence
case class ToolEvidence(info : Map[String,String]) extends Evidence {
  override def toString: String =
    "Tool.\n  " + info.map(entry => entry._1 + " \"\"\"\"" + entry._2 + "\"\"\"\"").mkString("\n  ") + "\nEnd."
}
case class ExternalEvidence(/*file:File*/) extends Evidence
