/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import java.io.File
import java.util.UUID
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, BuiltInTactic}
import edu.cmu.cs.ls.keymaerax.core.{Formula, Sequent}
import edu.cmu.cs.ls.keymaerax.lemma.{Lemma, LemmaDBFactory}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.ToolEvidence
import TacticFactory._
import edu.cmu.cs.ls.keymaerax.infrastruct.{ProvableHelper, UnificationTools}
import edu.cmu.cs.ls.keymaerax.parser.Declaration

import scala.collection.immutable

/**
  * Stores lemmas without user-defined name.
  * @author Stefan Mitsch
  */
object AnonymousLemmas {
  private val lemmaDB = LemmaDBFactory.lemmaDB

  /** A tactic `t` that caches its result in the lemma cache. */
  def cacheTacticResult(t: => BelleExpr, namespace: String, defs: Declaration): BuiltInTactic = anons ((provable: ProvableSig) => {
    val subderivations = provable.subgoals.map(remember(_, t, namespace).fact).zipWithIndex
    subderivations.foldRight(provable)({ case ((sub, i), p) =>
      val subst = UnificationTools.collectSubst(p.underlyingProvable, i, sub.underlyingProvable, defs)
      p.reapply(ProvableHelper.exhaustiveSubst(p.underlyingProvable, subst))(sub, i)
    })
  })

  /** Remembers a lemma (returns previously proven lemma or proves fresh if non-existent). */
  def remember(fml: Formula, t: BelleExpr, namespace: String = ""): Lemma =
    remember(Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(fml)), t, namespace)

  /** Remembers a lemma (returns previously proven lemma or proves fresh if non-existent). */
  def remember(s: Sequent, t: BelleExpr, namespace: String): Lemma =
    find(s, namespace).getOrElse(store(TactixLibrary.proveBy(s, t), namespace))

  /** Stores an anonymous lemma. */
  def store(p: ProvableSig, namespace: String): Lemma = {
    //@todo store tactic as evidence and link lookup to tactic extraction
    val evidence = ToolEvidence(immutable.List("input" -> p.conclusion.prettyString, "output" -> "true")) :: Nil
    val id = lemmaDB.add(Lemma(p, Lemma.requiredEvidence(p, evidence),
      Some(generateName(p.conclusion, namespace))))
    getAnonymousLemma(id, p.conclusion).get
  }

  /** Indicates whether or not the formula fml is available as an anonymous lemma. */
  def contains(fml: Formula, namespace: String): Boolean = find(fml, namespace).isDefined

  /** Indicates whether or not the Sequent `s` is available as an anonymous lemma. */
  def contains(s: Sequent, namespace: String): Boolean = find(s, namespace).isDefined

  /** Looks up a lemma for formula `fml` in the `namespace`. */
  def find(fml: Formula, namespace: String): Option[Lemma] = find(Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(fml)), namespace)

  /** Looks up a lemma for sequent `s` in the `namespace`. */
  def find(s: Sequent, namespace: String): Option[Lemma] = getAnonymousLemma(generateName(s, namespace), s)

  /** Generates a name for a lemma. */
  private def generateName(s: Sequent, namespace: String): String = {
    namespace + File.separator + UUID.nameUUIDFromBytes(s.prettyString.getBytes)
  }

  /** Looks up and anonymizes a lemma. */
  private def getAnonymousLemma(id: lemmaDB.LemmaID, s: Sequent): Option[Lemma] = {
    lemmaDB.get(id) match {
      case None => None
      case Some(lemma) if lemma.fact.conclusion == s => Some(Lemma(lemma.fact, lemma.evidence, None)) //@note make anonymous, otherwise we look up non-existent ProvableInfo
      case Some(lemma) if lemma.fact.conclusion != s => throw new IllegalStateException("Anonymous lemma " + lemma + " does not conclude expected " + s.prettyString)
    }
  }
}
