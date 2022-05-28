/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * @note Code Review 2016-08-16
  */
package edu.cmu.cs.ls.keymaerax.lemma

import edu.cmu.cs.ls.keymaerax.btactics.macros.{DerivedAxiomInfo, DerivedRuleInfo}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXExtendedLemmaParser
import edu.cmu.cs.ls.keymaerax.pt.{AxiomTerm, ElidingProvable, NoProof, ProvableSig, RuleTerm, TermProvable}

/**
  * Common Lemma Database implemented from string-based storage primitives.
  * Common logic shared by most lemma DB implementations. Most lemma DBs can (and should) be implemented
  * by extending this class and implementing the abstract methods for basic storage operations.
  *
  * @author Brandon Bohrer
  */
abstract class LemmaDBBase extends LemmaDB {
  /** Reads a list of lemmas with the given identifiers from the storage, giving back to-be-parsed lemmas. */
  protected def readLemmas(ids: List[LemmaID]): Option[List[String]]
  /** Write the string representation `lemma` of a lemma under the name `id`. */
  protected def writeLemma(id: LemmaID, lemma: String): Unit
  /** Creates an identifier for a lemma, without any content. */
  protected def createLemma(): LemmaID

  /** @inheritdoc */
  final override def get(ids: List[LemmaID]): Option[List[Lemma]] = {
    readLemmas(ids).map(_.map(Lemma.fromString)).map(_.map(lemma =>
      if (ProvableSig.PROOF_TERMS_ENABLED) {
        val term = lemma.name match {
          case Some(n) =>
            DerivedAxiomInfo.allInfoByStoredName.get(n) match {
              case Some(info) => AxiomTerm(info.canonicalName)
              case None =>
                if (DerivedRuleInfo.allInfo.contains(n)) RuleTerm(n)
                else NoProof
            }
          case None => NoProof
        }
        Lemma(TermProvable(ElidingProvable(lemma.fact.underlyingProvable, lemma.fact.defs), term, lemma.fact.defs), lemma.evidence, lemma.name)
      } else {
        lemma
      }
    ))
  } ensures(r => r match {
    case Some(lemmas) =>
      // lemma names must match id except when name==None
      lemmas.zip(ids).forall({ case (l, id) => l.name.forall(_ == id) })
    case None => !ids.forall(contains)
  })

  /** Performance */
  private val REDUNDANT_CHECKS = false

  /** @inheritdoc */
  private def saveLemma(lemma: Lemma, id: LemmaID): Unit = {
    require(lemma.name.isEmpty || lemma.name.contains(id), "Lemma name " + lemma.name + " does not match id " + id)
    val alternativeLemma = proofTermLemma(lemma)
    if (REDUNDANT_CHECKS) {
      //@see[[edu.cmu.cs.ls.keymaerax.core.alternativeLemma]]
      val parse = KeYmaeraXExtendedLemmaParser(alternativeLemma.toString)
      assert(parse._1 == alternativeLemma.name, "reparse of printed alternativeLemma's name should be identical to original alternativeLemma")
      assert(parse._2 == alternativeLemma.fact.underlyingProvable, s"reparse of printed alternativeLemma's fact ${alternativeLemma.fact} should be identical to original alternativeLemma ${parse._2}")
      assert(parse._3 == alternativeLemma.evidence, "reparse of printed alternativeLemma's evidence should be identical to original alternativeLemma")
    }

    writeLemma(id, alternativeLemma.toString)
    // read again to make sure we will get the alternativeLemma we just stored
    get(id) match {
      case None =>
        throw new IllegalStateException("Lemma " + id + " was not successfully inserted in database.")
      case Some(got) =>
        if (proofTermLemma(got) != alternativeLemma) {
          remove(id)
          throw new IllegalStateException(s"Lemma retrieved back from DB after storing it differed from lemma in memory -> deleted\n\tOriginal: ${alternativeLemma.toString}\n\tReloaded: ${got.toString}")
        }
    }
  } ensures(get(id).contains(proofTermLemma(lemma)), "Source lemma and saved lemma differ:\n\tOriginal: " + lemma.toString + "\n\tReloaded: " + get(id).toString)

  /** @inheritdoc */
  override def add(lemma: Lemma): LemmaID = {
    // synchronize to make sure concurrent calls use distinct IDs
    val id = this.synchronized {
      // `lemma.name` empty or not stored, or the lemma stored under `lemma.name` is identical to `lemma`
      require(lemma.name.flatMap(get) match { case None => true case Some(l) => l == lemma },
        "Lemma name " + lemma.name + " must be unique, or DB content must already have stored the identical lemma:\n" + lemma)
      lemma.name match {
        case Some(n) => n
        case None => createLemma()
      }
    }
    //@note overwrites pre-existing identical lemma
    saveLemma(lemma, id)
    id
  } ensures(r => get(r).contains(proofTermLemma(lemma)))

  /** Turns a list of options into a list or to a None if any list element was None.
    * For convenience when implementing bulk get() from individual get() */
  protected def flatOpt[T](l: List[Option[T]]): Option[List[T]] = l.foldRight[Option[List[T]]](Some(Nil)) {
    case (Some(x), Some(xs)) => Some(x::xs)
    case _ => None
  } ensures(r => if (l.exists(_.isEmpty)) r.isEmpty else r.contains(l.flatten))

  /** Returns the lemma with a [[TermProvable]] in place of `lemma.fact` if proof terms are enable. Returns the lemma unmodified otherwise. */
  private def proofTermLemma(lemma: Lemma): Lemma = {
    if (ProvableSig.PROOF_TERMS_ENABLED) {
      //@todo QE cache
      Lemma(TermProvable(ElidingProvable(lemma.fact.underlyingProvable, lemma.fact.defs), NoProof, lemma.fact.defs), lemma.evidence, lemma.name)
    }
    else lemma
  } ensures(r => r.name == lemma.name && r.evidence == lemma.evidence && r.fact.underlyingProvable == lemma.fact.underlyingProvable)
}
