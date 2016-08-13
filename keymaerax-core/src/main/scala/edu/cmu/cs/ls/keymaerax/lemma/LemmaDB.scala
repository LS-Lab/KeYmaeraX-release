/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * @note Code Review 2016-08-02
  */
package edu.cmu.cs.ls.keymaerax.lemma

import edu.cmu.cs.ls.keymaerax.core.Lemma
import edu.cmu.cs.ls.keymaerax.tools.{HashEvidence, ToolEvidence}

/**
  * Store and retrieve lemmas from a lemma database. Use [[edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory.lemmaDB]] to get
 * an instance of a lemma database.
 *
 * @author Stefan Mitsch
 * @see Lemma
 * @example Storing and using a lemma
 * {{{
 * import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
 * val lemmaDB = LemmaDBFactory.lemmaDB
 * // prove a lemma
 * val proved = TactixLibrary.proveBy(
 *    Sequent(IndexedSeq(), IndexedSeq("true | x>5".asFormula)),
 *    orR(1) & close
 *  )
 * // store a lemma
 * val evidence = ToolEvidence(immutable.Map("input" -> proved.toString, "output" -> "true")) :: Nil))
 * val lemmaID = lemmaDB.add(
 *   Lemma(proved, evidence, Some("Lemma <?> test"))
 * )
 * // use a lemma
 * LookupLemma(lemmaDB, lemmaID)
 * }}}
 */
trait LemmaDB {

  type LemmaID = String

  /**
   * Indicates whether or not this lemma DB contains a lemma with the specified ID.
 *
   * @param lemmaID Identifies the lemma.
    *
    *
   * @return True, if this lemma DB contains a lemma with the specified ID; false otherwise.
   */
  def contains(lemmaID: LemmaID): Boolean = get(lemmaID).isDefined

  /**
   * Returns the lemma with the given name or None if non-existent.
 *
   * @param lemmaID Identifies the lemma.
   * @return The lemma, if found under the given lemma ID. None otherwise.
   * @ensures contains(lemmaID) && \result==Some(l) && l.name == lemmaID
   *         || !contains(lemmaID) && \result==None
   */
  def get(lemmaID: LemmaID): Option[Lemma] = get(List(lemmaID)).flatMap(_.headOption)

  def get(lemmaIDs: List[LemmaID]):Option[List[Lemma]]

  /**
   * Adds a new lemma to this lemma DB, with a unique name or None, which will automatically assign a name.
 *
   * @param lemma The lemma whose Provable will be inserted under its name.
   * @return Internal lemma identifier.
   * @requires if (lemma.name==Some(n)) then !contains(n)
   * @ensures  if (lemma.name==Some(n)) then \result==n  (usually)
   */
  def add(lemma: Lemma): LemmaID

  /** Should return true if removed and false if not. Should not throw errors on failure to remove. */
  def remove(name: LemmaID): Boolean

  /** Delete the whole lemma database */
  def deleteDatabase(): Unit

  /** For convenience when implementing bulk get() from individual get() */
  protected def flatOpt[T](L:List[Option[T]]):Option[List[T]] =
    L.foldRight[Option[List[T]]](Some(Nil)){
      case (Some(x),Some(xs)) => Some(x::xs)
      case _ => None
    }
}
