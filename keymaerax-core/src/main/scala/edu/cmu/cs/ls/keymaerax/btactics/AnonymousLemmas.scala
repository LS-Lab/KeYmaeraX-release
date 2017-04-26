/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import java.io.File
import java.util.UUID

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.core.{Formula, Lemma}
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.ToolEvidence

import scala.collection.immutable

/**
  * Stores lemmas without user-defined name.
  * @author Stefan Mitsch
  */
object AnonymousLemmas {
  private val lemmaDB = LemmaDBFactory.lemmaDB

  //@todo cache

  /** Remembers a lemma (returns previously proven lemma or proves fresh if non-existent). */
  def remember(fml: Formula, t: BelleExpr, namespace: String = ""): Lemma = {
    find(fml, namespace).getOrElse(store(TactixLibrary.proveBy(fml, t), namespace))
  }

  /** Stores an anonymous lemma. */
  def store(p: ProvableSig, namespace: String = ""): Lemma = {
    assert(p.conclusion.ante.isEmpty && p.conclusion.succ.size == 1, "Can store only lemmas with sequents of the form `|- conclusion`, but got " + p.conclusion.prettyString)
    //@todo store tactic as evidence and link lookup to tactic extraction
    val evidence = ToolEvidence(immutable.List("input" -> p.conclusion.prettyString, "output" -> "true")) :: Nil
    val id = lemmaDB.add(Lemma(p, Lemma.requiredEvidence(p, evidence),
      Some(generateName(p.conclusion.succ.head, namespace))))
    getAnonymousLemma(id, p.conclusion.succ.head).get
  }

  /** Indicates whether or not the formula fml is available as an anonymous lemma. */
  def contains(fml: Formula, namespace: String = ""): Boolean = find(fml, namespace).isDefined

  /** Looks up a lemma for formula `fml` in the `namespace`. */
  def find(fml: Formula, namespace: String = ""): Option[Lemma] = getAnonymousLemma(generateName(fml, namespace), fml)

  /** Generates a name for a lemma. */
  private def generateName(fml: Formula, namespace: String): String = {
    namespace + File.separator + UUID.nameUUIDFromBytes(fml.prettyString.getBytes)
  }

  /** Looks up and anonymizes a lemma. */
  private def getAnonymousLemma(id: lemmaDB.LemmaID, fml: Formula): Option[Lemma] = {
    lemmaDB.get(id) match {
      case None => None
      case Some(lemma) if lemma.fact.conclusion.succ.head == fml => Some(Lemma(lemma.fact, lemma.evidence, None)) //@note make anonymous, otherwise we look up non-existent ProvableInfo
      case Some(lemma) if lemma.fact.conclusion.succ.head != fml => throw new IllegalStateException("Anonymous lemma " + lemma + " does not conclude expected formula " + fml)
    }
  }
}
