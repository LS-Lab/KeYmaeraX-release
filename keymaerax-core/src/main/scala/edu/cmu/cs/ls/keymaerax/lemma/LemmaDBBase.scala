/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * @note Code Review 2016-08-16
  */
package edu.cmu.cs.ls.keymaerax.lemma

import edu.cmu.cs.ls.keymaerax.core.Lemma
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXExtendedLemmaParser
import edu.cmu.cs.ls.keymaerax.pt.{NoProof, NoProofTermProvable, PTProvable, ProvableSig}

/**
  * Common Lemma Database implemented from string-based storage primitives.
  * Common logic shared by most lemma DB implementations. Most lemma DB's can (and should) be implemented
  * by extending this class and implementing the abstract methods for basic storage operations.
  *
  * Created by bbohrer on 8/3/16.
  */
abstract class LemmaDBBase extends LemmaDB {
  /** Reads a list of lemmas with the given identifiers from the storage, giving back to-be-parsed lemmas. */
  def readLemmas(ids: List[LemmaID]): Option[List[String]]
  /** Write the string representation `lemma` of a lemma under the name `id`. */
  def writeLemma(id: LemmaID, lemma:String): Unit
  /** Creates an identifier for a lemma, without any content. */
  def createLemma(): LemmaID


  override def get(ids: List[LemmaID]): Option[List[Lemma]] = {
    readLemmas(ids).map(_.map(Lemma.fromString)) //@todo This should be over-ridden in every implementation so maybe we should just leave it abstract.
  }

  /** Performance */
  private val REDUNDANT_CHECKS = false
  private def saveLemma(lemma:Lemma, id:LemmaID): Unit = {
    val alternativeFact =
      if(ProvableSig.PROOF_TERMS_ENABLED) {
        PTProvable(NoProofTermProvable(lemma.fact.underlyingProvable), NoProof())
      } else {
        lemma.fact
      }
    val alternativeLemma = Lemma(alternativeFact, lemma.evidence, lemma.name)
    if (REDUNDANT_CHECKS) {
      //@see[[edu.cmu.cs.ls.keymaerax.core.alternativeLemma]]
      val parse = KeYmaeraXExtendedLemmaParser(alternativeLemma.toString)
      assert(parse._1 == alternativeLemma.name, "reparse of printed alternativeLemma's name should be identical to original alternativeLemma")
      assert(parse._2 == alternativeLemma.fact.conclusion +: alternativeLemma.fact.subgoals, s"reparse of printed alternativeLemma's fact ${alternativeLemma.fact.conclusion +: alternativeLemma.fact.subgoals}should be identical to original alternativeLemma ${parse._2}")
      assert(parse._3 == alternativeLemma.evidence, "reparse of printed alternativeLemma's evidence should be identical to original alternativeLemma")
    }

    writeLemma(id, alternativeLemma.toString)
    // read again to make sure we will get the alternativeLemma we just stored
    get(id) match {
      case None =>
        throw new IllegalStateException("alternativeLemma " + id + " was not successfully inserted in database.")
      case Some(got) =>
        if (got != alternativeLemma) {
          val b1 = got.fact == alternativeLemma.fact
          val b1a = got.fact.underlyingProvable == alternativeLemma.fact.underlyingProvable
          val b1b = got.fact.asInstanceOf[PTProvable].pt == alternativeLemma.fact.asInstanceOf[PTProvable].pt
          val b2 = got.evidence == alternativeLemma.evidence
          val b3 = got.name == alternativeLemma.name
          remove(id)
          throw new IllegalStateException(s"alternativeLemma retrieved back from DB after storing it differed from alternativeLemma in memory -> deleted\n\tOriginal: ${alternativeLemma.toString}\n\tReloaded: ${got.toString}")
        }
    }
  }

  override def  add(lemma: Lemma): LemmaID = {
    val id = this.synchronized {
      // synchronize to make sure concurrent calls use distinct ID's
      lemma.name match {
        case Some(n) =>
          val got = get(n)
          val isOk = got == None || got == Some(lemma)
          if(!isOk) {
            require(isOk,
              "Lemma name " + n + " must be unique, or DB content must already have stored the identical lemma: \n" + lemma)
          }
          n
        case None => createLemma()
      }
    }
    saveLemma(lemma, id)
    id.toString
  }

  /** Turns a list of options into a list or to a None if any list element was None.
    * For convenience when implementing bulk get() from individual get() */
  protected def flatOpt[T](L:List[Option[T]]):Option[List[T]] =
  L.foldRight[Option[List[T]]](Some(Nil)){
    case (Some(x),Some(xs)) => Some(x::xs)
    case _ => None
  }
}
