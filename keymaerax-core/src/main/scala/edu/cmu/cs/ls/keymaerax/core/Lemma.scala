/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
 * @author Stefan Mitsch
 * @note Code Review: 2015-08-24
 */
package edu.cmu.cs.ls.keymaerax.core

import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXPrettyPrinter, KeYmaeraXExtendedLemmaParser}

object Lemma {
  /**
   * Parses a lemma from its string representation.
   * @param lemma The lemma in string form.
   * @return The lemma.
   * @note soundness-critical, only call with true facts that come from serialized lemmas.
   * @see [[Lemma.toString]]
   */
  def fromString(lemma: String): Lemma = {
    //@note should ensure that string was indeed produced by KeYmaera X
    val (name, sequents, evidence) = KeYmaeraXExtendedLemmaParser(lemma)
    val fact = Provable.oracle(sequents.head, sequents.tail.toIndexedSeq)
    Lemma(fact, evidence :: Nil, name)
  } ensuring(r => KeYmaeraXExtendedLemmaParser(r.myString) == (r.name, r.fact.conclusion +: r.fact.subgoals, r.evidence.head),
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
  //@note Now allowing more general forms of lemmas. @todo check for soundness.
//  insist(fact.isProved, "Only provable facts can be added as lemmas " + fact)
  //@note could allow more general forms of lemmas.
//  require(fact.conclusion.ante.isEmpty, "Currently only lemmas with empty antecedents are allowed " + fact)
//  require(fact.conclusion.succ.size == 1, "Currently only lemmas with exactly one formula in the succedent are allowed " + fact)

  /** A string representation of this lemma that will reparse as this lemma.
    * @see [[Lemma.fromString()]] */
  override def toString: String = {
    myString
    //@note soundness-critical check that reparse succeeds as expected
  } ensuring(r => Lemma.fromString(r) == this, "Printed lemma should reparse to this original lemma")

  private def myString: String = {
    "Lemma \"" + name.getOrElse("") + "\".\n" +
     sequentToString(fact.conclusion) + "\n" +
     fact.subgoals.map(sequentToString).mkString("\n") + "\n" +
    "End.\n" +
     evidence.mkString("\n\n") + "\n"
  }

  /** Produces a sequent block in Lemma file format */
  private def sequentToString(s: Sequent) = {
    //@note Regarding side-conditions:
    //If ante or succ contains no formulas, then we just get a newline. In that case the newline is ignored by the parser.
    "Sequent.\n" +
      s.ante.map(x => "Formula: " + KeYmaeraXPrettyPrinter.fullPrinter(x)).mkString("\n") +
      "\n==>\n" +
      s.succ.map(x => "Formula: " + KeYmaeraXPrettyPrinter.fullPrinter(x)).mkString("\n")
  }
}

/** "Weak" Correctness evidence for lemmas */
trait Evidence

