/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
 * @author Stefan Mitsch
 * @note Code Review: 2015-08-24
 */
package edu.cmu.cs.ls.keymaerax.core

import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXLemmaParser

import scala.collection.immutable

object Lemma {
  /**
   * Parses a lemma from a string.
   * @param lemma The lemma in string form.
   * @return The lemma.
   * @note soundness-critical, only call with true facts that come from serialized lemmas.
   */
  def fromString(lemma: String): Lemma = {
    //@note should ensure that string was indeed produced by KeYmaera X
    val (name, formula, evidence) = KeYmaeraXLemmaParser(lemma)
    val fact = Provable.toolFact(new Sequent(Nil,
      immutable.IndexedSeq(),
      immutable.IndexedSeq(formula)))
    Lemma(fact, evidence :: Nil, name)
  } ensuring(r => KeYmaeraXLemmaParser(r.toString) == (r.name, r.fact.conclusion.succ.head, r.evidence.head),
    "Reparse of printed parse result should be original parse result")
}

/**
 * Lemmas are named Provables, supported by some evidence of how they came about.
 * The soundness-critical part in a lemma is its provable fact, which can only be obtained from the prover core.
 * @example{{{
 * // prove a lemma
 * val proved = TactixLibrary.proveBy(
 *    Sequent(Nil, IndexedSeq(), IndexedSeq("true | x>5".asFormula)),
 *    orR(1) & close
 *  )
 * // store a lemma
 * val lemmaDB = LemmaDBFactory.lemmaDB
 * val evidence = ToolEvidence(immutable.Map("input" -> proved.toString, "output" -> "true")) :: Nil))
 * val lemmaID = lemmaDB.add(
 *   Lemma(proved, evidence, Some("Lemma <?> test"))
 * )
 * // use a lemma
 * LookupLemma(lemmaDB, lemmaID)
 * }}}
 * @author Stefan Mitsch
 * @see [[LookupLemma]]
 * @see [[RCF.proveArithmetic]]
 * @see [[LemmaDB]]
 * @see [[Lemma.fromString]]
 * @note Construction is not soundness-critical so constructor is not private, because Provables can only be constructed by prover core.
 */
final case class Lemma(fact: Provable, evidence: List[Evidence], name: Option[String] = None) {
  insist(fact.isProved, "Only provable facts can be added as lemmas " + fact)
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

