/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
/**
 * @author Stefan Mitsch
 * @note Code Review: 2015-08-24
 */
package edu.cmu.cs.ls.keymaerax.core

import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXLemmaParser // external reference for contracts only

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
  require(fact.isProved, "Only provable facts can be added as lemmas " + fact)
  //@note could allow more general forms of lemmas.
  require(fact.conclusion.ante.isEmpty, "Currently only lemmas with empty antecedents are allowed " + fact)
  require(fact.conclusion.succ.size == 1, "Currently only lemmas with exactly one formula in the succedent are allowed " + fact)

  /** A string representation of this lemma that will reparse as this lemma. */
  override def toString: String = {
    val lemmaName = name match {
      case Some(n) => n
      case None => ""
    }
    "Lemma \"" + lemmaName + "\".\n  " +
      fact.conclusion.succ.head.prettyString +
      "\nEnd.\n\n" +
      evidence.mkString("\n\n")
  } ensuring(r => KeYmaeraXLemmaParser(r)._2==fact.conclusion.succ.head, "Printed lemma should parse to conclusion")

}

/** "Weak" Correctness evidence for lemmas */
trait Evidence

