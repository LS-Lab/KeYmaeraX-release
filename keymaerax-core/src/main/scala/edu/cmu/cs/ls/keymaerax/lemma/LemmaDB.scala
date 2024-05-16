/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/** @note Code Review 2016-08-16 */
package edu.cmu.cs.ls.keymaerax.lemma

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.info.VersionNumber

/**
 * Store and retrieve lemmas from a lemma database. Use [[edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory.lemmaDB]] to get
 * an instance of a lemma database.
 *
 * @author
 *   Stefan Mitsch
 * @see
 *   Lemma
 * @example
 *   Storing and using a lemma
 *   {{{
 *   import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
 *   val lemmaDB = LemmaDBFactory.lemmaDB
 *   // prove a lemma
 *   val proved = TactixLibrary.proveBy(
 *      Sequent(IndexedSeq(), IndexedSeq("true | x>5".asFormula)),
 *      orR(1) & close
 *    )
 *   // store a lemma
 *   val evidence = ToolEvidence(immutable.Map("input" -> proved.toString, "output" -> "true")) :: Nil))
 *   val lemmaID = lemmaDB.add(
 *     Lemma(proved, evidence, Some("Lemma <?> test"))
 *   )
 *   // use a lemma
 *   LookupLemma(lemmaDB, lemmaID)
 *   }}}
 */
trait LemmaDB {

  /** Identifies a lemma. */
  type LemmaID = String

  /**
   * Indicates whether or not this lemma DB contains a lemma with the specified ID.
   * @param lemmaID
   *   Identifies the lemma.
   * @return
   *   True, if this lemma DB contains a lemma with the specified ID; false otherwise.
   */
  def contains(lemmaID: LemmaID): Boolean

  /**
   * Returns the lemma with the given name or None if non-existent.
   * @param lemmaID Identifies the lemma.
   * @return The lemma, if found under the given lemma ID. None otherwise.
   * @ensures contains(lemmaID) && \result == Some(l) && l.name == lemmaID
   *         || !contains(lemmaID) && \result == None
   */
  def get(lemmaID: LemmaID): Option[Lemma] = get(List(lemmaID)).flatMap(_.headOption) ensures
    (r =>
      // lemma name must match id except when name==None
      contains(lemmaID) && r.isDefined && r.get.name.forall(_ == lemmaID) || !contains(lemmaID) && r.isEmpty
    )

  /**
   * Returns the lemmas with IDs `lemmaIDs` or None if any of the `lemmaIDs` does not exist.
   * @param lemmaIDs Identifies the lemmas.
   * @return The list of lemmas, if all `lemmaIDs` exist. None otherwise.
   * @ensures lemmaIDs.forall(contains) && \result == Some(l) && l.names == lemmaIDs
   *         || !lemmaIDs.forall(contains) && \result == None
   */
  def get(lemmaIDs: List[LemmaID]): Option[List[Lemma]]

  /**
   * Adds a new lemma to this lemma DB, with a unique name or None, which will automatically assign a name.
   * @param lemma
   *   The lemma whose Provable will be inserted under its name.
   * @return
   *   Internal lemma identifier.
   * @requires
   *   if (lemma.name==Some(n)) then !contains(n)
   * @ensures
   *   contains(\result) && if (lemma.name==Some(n)) then \result==n (usually)
   */
  def add(lemma: Lemma): LemmaID

  /**
   * Delete the lemma of the given identifier, throwing exceptions if that was unsuccessful.
   * @param name
   *   Identifies the lemma.
   * @ensures
   *   !contains(name)
   */
  def remove(name: LemmaID): Unit

  /** Removes all lemmas in `folder`. */
  def removeAll(folder: String): Unit

  /** Delete the whole lemma database */
  def deleteDatabase(): Unit

  /** Returns the version of this lemma database. */
  def version(): VersionNumber

}
