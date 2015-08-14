/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
/**
 * @author Stefan Mitsch
 * @note Code Review: 2015-05-01
 */
package edu.cmu.cs.ls.keymaerax.core

import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXPrettyPrinter, Evidence}

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
  assert(fact.isProved, "Lemma provable is not actually proved")
  //@todo allow more general forms of lemmas?
  assert(fact.conclusion.ante.isEmpty, "Antecedent is not empty")
  assert(fact.conclusion.succ.size == 1, "Succedent contains not exactly one formula")

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
