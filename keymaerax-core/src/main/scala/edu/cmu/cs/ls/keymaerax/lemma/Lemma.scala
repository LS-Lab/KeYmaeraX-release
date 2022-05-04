/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
 * @author Stefan Mitsch
 * @note Code Review: 2016-08-17
 */
package edu.cmu.cs.ls.keymaerax.lemma

import edu.cmu.cs.ls.keymaerax.{Configuration, lemma}
import edu.cmu.cs.ls.keymaerax.btactics.macros._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.{Declaration, KeYmaeraXExtendedLemmaParser}
import edu.cmu.cs.ls.keymaerax.pt._
import edu.cmu.cs.ls.keymaerax.tools.ToolEvidence

// require favoring immutable Seqs for unmodifiable Lemma evidence

import scala.collection.immutable
import scala.collection.immutable._

/** Facility for reading lemmas back in from their string representation.
  */
object Lemma {
  //@todo disable lemma compatibility mode. This will require some version update code because old lemma dbs (both SQLite and file lemma db) will fail to work.
  private val LEMMA_COMPAT_MODE = Configuration(Configuration.Keys.LEMMA_COMPATIBILITY) == "true"

  /**
    * Parses a lemma from its string representation.
    * @param lemma The lemma in string form.
    * @return The lemma.
    * @note soundness-critical, only call with true facts that come from serialized lemmas.
    * @see [[Lemma.toString]]
    */
  def fromString(lemma: String): Lemma = {
    fromStringInternal(lemma)
  } ensures(r => matchesInput(r, lemma), "Reparse of printed parse result should be original parse result")

  /** This contract turns out to be a huge bottleneck when loading proofs on the UI, so it worth checking the contract
    * as quickly as possible. If converting the lemma back into a string already gives exactly the string we started with,
    * then we know it was parsed correctly. If not, proceed to check that the lemma, when printed and then
    * parsed a second time*, produces the same lemma. We consider this second condition sufficient because for lemmas that
    * contain comments, the first check needs not succeed.
    * @note not soundness-critical, because only used for checking whether a re-read gives the same result.
    * @note performance bottleneck for loading
    */
  private def matchesInput(result: Lemma, input: String): Boolean = {
    //@note performance is optimized since contract-free stringify calls are used here for rechecking purposes
    val str = result.toStringInternal
    str == input || KeYmaeraXExtendedLemmaParser(str) == (result.name, result.fact.underlyingProvable, result.evidence)
  }

  /** Parses a lemma from its string representation (without consistency checking). */
  private def fromStringInternal(lemma: String): Lemma = {
    val (storedName, provable, evidence) = KeYmaeraXExtendedLemmaParser(lemma)
    val fact =
      if (ProvableSig.PROOF_TERMS_ENABLED) {
        TermProvable(ElidingProvable(provable, Declaration(Map.empty)), storedName match { case Some(n) =>
          DerivedAxiomInfo.allInfoByStoredName.get(n) match {
            case Some(info) => AxiomTerm(info.canonicalName)
            case None =>
              if (DerivedRuleInfo.allInfo.contains(n)) RuleTerm(n)
              else NoProof
          }
        case None => FOLRConstant(provable.conclusion.succ.head) }, Declaration(Map.empty))
      } else {
        ElidingProvable(provable, Declaration(Map.empty))
      }
    Lemma(fact, evidence, storedName) //@todo also load proof terms.
  }

  /** Returns true if `evidence` contains version evidence, false otherwise. */
  private def containsVersionEvidence(evidence: List[Evidence]): Boolean = evidence.exists({
    case ToolEvidence(infos) => infos.exists(_._1 == "kyxversion")
    case _ => false
  })

  /** Computes the required extra evidence to add to `fact` in order to turn it into a lemma */
  def requiredEvidence(fact: ProvableSig, evidence: List[Evidence] = Nil): List[Evidence] = {
    if (!containsVersionEvidence(evidence)) evidence :+ ToolEvidence(("kyxversion", edu.cmu.cs.ls.keymaerax.core.VERSION) :: Nil)
    else evidence
  }
}

/**
  * Lemmas are named Provables, supported by some evidence of how they came about.
  * The soundness-critical part in a lemma is its provable fact, which can only be obtained from the prover core.
 *
  * @example {{{
  * // prove a lemma
  * val proved = TactixLibrary.proveBy(
  *    Sequent(IndexedSeq(), IndexedSeq("true | x>5".asFormula)),
  *    orR(1) & close
  *  )
  * // store a lemma
  * val lemmaDB = LemmaDBFactory.lemmaDB
  * val evidence = ToolEvidence(immutable.Map("input" -> proved.toString, "output" -> "true")) :: Nil))
  * val lemmaID = lemmaDB.add(
  *   Lemma(proved, evidence, Some("Lemma <?> test"))
  * )
  *
  * // retrieve a lemma
  * val lemmaFact = lemmaDB.get(lemmaID).get.fact
  * // use a lemma literally
  * TactixLibrary.by(lemmaFact)
  * // use a uniform substitution instance of a lemma
  * TactixLibrary.byUS(lemmaFact)
  * }}}
  * @author Stefan Mitsch
  * @see [[ProvableSig.proveArithmeticLemma]]
  * @see [[edu.cmu.cs.ls.keymaerax.lemma.LemmaDB]]
  * @see [[lemma.Lemma.fromString]]
  * @note Construction is not soundness-critical so constructor is not private, because Provables can only be constructed by prover core.
  */
final case class Lemma(fact: ProvableSig, evidence: immutable.List[Evidence], name: Option[String] = None) {
  insist(name.getOrElse("").forall(c => c!='\"'), "no escape characters in names: " + name)
  assert(hasStamp, "Lemma should have kyxversion (unless compatibility mode, which is " + Lemma.LEMMA_COMPAT_MODE + ")\nbut got\n" + this.toStringInternal)
  private def hasStamp: Boolean = Lemma.LEMMA_COMPAT_MODE || Lemma.containsVersionEvidence(evidence)

  /** A string representation of this lemma that will reparse as this lemma.
    * @see [[Lemma.fromString()]] */
  override def toString: String = {
    toStringInternal
    //@note soundness-critical check that reparse succeeds as expected
  } ensures(r =>  {
    val reparsed = Lemma.fromStringInternal(r)
    reparsed.fact.underlyingProvable == fact.underlyingProvable &&
    reparsed.evidence == evidence &&
    reparsed.name == name
    },
    "Printed lemma should reparse to this original lemma\n\n" + toStringInternal)

  /** Produces a string representation of this lemma that is speculated to reparse as this lemma
    * and will be checked to do so in [[toString]]. */
  private def toStringInternal: String = {
    "Lemma \"" + name.getOrElse("") + "\".\n" +
      "\"" + Provable.toStorageString(fact.underlyingProvable) + "\"\n" +
      "End.\n" +
      evidence.mkString("\n\n") + "\n"
  }
}

/** "Weak" Correctness evidence for lemmas */
trait Evidence

