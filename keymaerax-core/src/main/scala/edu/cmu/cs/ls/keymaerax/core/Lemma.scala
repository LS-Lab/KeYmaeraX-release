/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
 * @author Stefan Mitsch
 * @note Code Review: 2016-03-09
 */
package edu.cmu.cs.ls.keymaerax.core

import java.security.MessageDigest

import edu.cmu.cs.ls.keymaerax.parser.{FullPrettyPrinter, KeYmaeraXExtendedLemmaParser}
import edu.cmu.cs.ls.keymaerax.tools.{HashEvidence, ToolEvidence}

// require favoring immutable Seqs for unmodifiable Lemma evidence

import scala.collection.immutable
import scala.collection.immutable._

/** Facility for reading lemmas back in from their string representation.
  */
object Lemma {
  //@todo disable lemma compatibility mode. This will require some version update code because old lemma dbs (both SQLite and file lemma db) will fail to work.
  private val LEMMA_COMPAT_MODE = System.getProperty("LEMMA_COMPAT_MODE", "true")=="true"
  private[this] val digest = MessageDigest.getInstance("MD5")

  /** The pretty printer that is used for lemma storage purposes */
  private val printer = FullPrettyPrinter

  /**
    * Parses a lemma from its string representation.
    * @param lemma The lemma in string form.
    * @return The lemma.
    * @note soundness-critical, only call with true facts that come from serialized lemmas.
    * @see [[Lemma.toString]]
    */
  def fromString(lemma: String): Lemma = {
    val internalLemma = fromStringInternal(lemma)
    //@todo should verify checkSum of the above string here against the checksum of internalLemma.

    //Check that the resulting lemma has
    internalLemma.evidence.find(_.isInstanceOf[HashEvidence]) match {
      case Some(HashEvidence(hash)) =>
        assert(hash == internalLemma.checksum,
          "Expected hashed evidence to match hash of conclusion + subgoals: " + internalLemma.name + "\n" + lemma)
      case None => {
        if(LEMMA_COMPAT_MODE) println(s"WARNING: ${internalLemma.name.getOrElse("An unnamed lemma")} was reloaded without a hash confirmation.")
        else throw new CoreException("Cannot reload a lemma without some Hash evidence: " + internalLemma.name)
      }
    }

    internalLemma
  } ensuring(r => matchesInput(r, lemma), "Reparse of printed parse result should be original parse result")

  /** This contract turns out to be a huge bottleneck when loading proofs on the UI, so it worth checking the contract
    * as quickly as possible. If converting the lemma back into a string already gives exactly the string we started with,
    * then we know it was parsed correctly. If not, proceed to check that the lemma, when printed and then
    * parsed a second time*, produces the same lemma. We consider this second condition sufficient because for lemmas that
    * contain comments, the first check needs not succeed.
    * @note performance bottleneck for loading
    */
  private def matchesInput(result: Lemma, input:String): Boolean = {
    //@note performance could be optimized by using contract-free stringify calls here for rechecking purposes
    val str = result.toStringInternal
    str == input || KeYmaeraXExtendedLemmaParser(str) == (result.name, result.fact.conclusion +: result.fact.subgoals, result.evidence)
  }

  /** Parses a lemma from its string representation (without consistency checking). */
  private def fromStringInternal(lemma: String): Lemma = {
    //@note should ensure that string was indeed produced by KeYmaera X
    val (name, sequents, evidence) = KeYmaeraXExtendedLemmaParser(lemma)
    //@note soundness-critical
    val fact = Provable.oracle(sequents.head, sequents.tail.toIndexedSeq)
    Lemma(fact, evidence, name)
  }

  /** Compute the checksum for the given Provable, which provides some protection against accidental changes. */
  final def checksum(fact: Provable): String =
    digest((fact.conclusion +: fact.subgoals.toList).map(_.prettyString).mkString(","))

  /** Checksum computation implementation */
  private def digest(s: String): String = digest.digest(s.getBytes).map("%02x".format(_)).mkString

  /** Computes the required extra evidence to add to `fact` in order to turn it into a lemma */
  def requiredEvidence(fact: Provable, evidence: List[Evidence] = Nil): List[Evidence] = {
    val versionEvidence = {
      val hasVersionEvidence = evidence.exists(x => x match {
        case ToolEvidence(infos) => infos.exists(_._1 == "kyxversion")
        case _ => false
      })
      if(!hasVersionEvidence) Some(ToolEvidence(("kyxversion", edu.cmu.cs.ls.keymaerax.core.VERSION) :: Nil))
      else None
    }

    val hashEvidence = {
      val hasHashEvidence = evidence.exists(_.isInstanceOf[HashEvidence])
      if (!hasHashEvidence) Some(HashEvidence(checksum(fact)))
      else None
    }

    val newEvidence = (versionEvidence, hashEvidence) match {
      case (Some(l), Some(r)) => evidence :+ l :+ r
      case (Some(l), None) => evidence :+ l
      case (None, Some(r)) => evidence :+ r
      case _ => evidence
    }

    newEvidence
  }
}

/**
  * Lemmas are named Provables, supported by some evidence of how they came about.
  * The soundness-critical part in a lemma is its provable fact, which can only be obtained from the prover core.
  * @example{{{
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
  * @see [[RCF.proveArithmetic]]
  * @see [[edu.cmu.cs.ls.keymaerax.lemma.LemmaDB]]
  * @see [[Lemma.fromString]]
  * @note Construction is not soundness-critical so constructor is not private, because Provables can only be constructed by prover core.
  */
final case class Lemma(fact: Provable, evidence: immutable.List[Evidence], name: Option[String] = None) {
  assert(hasStamp, "Lemma should have kyxversion and checksum stamps (unless compatibility mode) " + this)
  private def hasStamp: Boolean = Lemma.LEMMA_COMPAT_MODE || {
    val hasVersionEvidence = evidence.exists(x => x match {
      case ToolEvidence(infos) => infos.exists(_._1 == "kyxversion")
      case _ => false
    })
    val hasHashEvidence = evidence.exists(_.isInstanceOf[HashEvidence])
    hasVersionEvidence && hasHashEvidence
  }


  /** The checksum of this Lemma, used for lightweight storage consistency checking purposes.
    * @ensures \result == Lemma.checksum(fact)
    */
  lazy val checksum: String = Lemma.checksum(fact)

  //@todo name is alphabetical and not "\".\n false"
  //@note Now allowing more general forms of lemmas. @todo check for soundness.
//  insist(fact.isProved, "Only provable facts can be added as lemmas " + fact)
  //@note could allow more general forms of lemmas.
//  require(fact.conclusion.ante.isEmpty, "Currently only lemmas with empty antecedents are allowed " + fact)
//  require(fact.conclusion.succ.size == 1, "Currently only lemmas with exactly one formula in the succedent are allowed " + fact)

  /** A string representation of this lemma that will reparse as this lemma.
    * @see [[Lemma.fromString()]] */
  override def toString: String = {
    toStringInternal
    //@note soundness-critical check that reparse succeeds as expected
  } ensuring(r => Lemma.fromStringInternal(r) == this, "Printed lemma should reparse to this original lemma\n\n" + toStringInternal + "\n\n" +
    (if (Lemma.fromStringInternal(toStringInternal).fact == fact) " same fact " else " different fact ") +
    (if (Lemma.fromStringInternal(toStringInternal).evidence == evidence) " same evidence " else " different evidence " + Lemma.fromStringInternal(toStringInternal).evidence.mkString("\n\n")) +
    (if (Lemma.fromStringInternal(toStringInternal).name == name) " same name " else " different name ")
  )

  /** Produces a string representation of this lemma that is speculated to reparse as this lemma
    * and will be checked to do so in [[toString]]. */
  private def toStringInternal: String = {
    "Lemma \"" + name.getOrElse("") + "\".\n" +
      sequentToString(fact.conclusion) + "\n" +
      fact.subgoals.map(sequentToString).mkString("\n") + "\n" +
      "End.\n" +
      //@todo should add checkSum of the above printed string here.
      evidence.mkString("\n\n") + "\n"
  }

  /** Produces a sequent block in Lemma file format */
  private def sequentToString(s: Sequent): String = {
    //@note Regarding side-conditions:
    //If ante or succ contains no formulas, then we just get a newline. In that case the newline is ignored by the parser.
    //@note It is enough to use contract-free stringify since toString will reparse the entire lemma in its ensuring contract again.
    "Sequent.\n" +
      s.ante.map(x => "Formula: " + Lemma.printer.stringify(x)).mkString("\n") +
      "\n==>\n" +
      s.succ.map(x => "Formula: " + Lemma.printer.stringify(x)).mkString("\n")
  }
}

/** "Weak" Correctness evidence for lemmas */
trait Evidence

