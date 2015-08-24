/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
/**
 * @author Stefan Mitsch
 * @note Code Review: 2015-08-24
 */
package edu.cmu.cs.ls.keymaerax.core

/**
 * Store and retrieve lemmas.
 *
 * Created by smitsch on 4/27/15.
 * @author Stefan Mitsch
 * @see Lemma
 * @example Storing and using a lemma
 * {{{
 * val lemmaDB = new FileLemmaDB
 * // prove a lemma
 * val proved = TactixLibrary.proveBy(
 *    Sequent(Nil, IndexedSeq(), IndexedSeq("true | x>5".asFormula)),
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
   * @param lemmaID Identifies the lemma.
   * @return True, if this lemma DB contains a lemma with the specified ID; false otherwise.
   */
  def contains(lemmaID: LemmaID): Boolean

  /**
   * Returns the lemma with the given name or None if non-existent.
   * @param lemmaID Identifies the lemma.
   * @return The lemma, if found under the given lemma ID. None otherwise.
   * @ensures contains(lemmaID) && \result==Some(l) && l.name == lemmaID
   *         || !contains(lemmaID) && \result==None
   */
  def get(lemmaID: LemmaID): Option[Lemma]

  /**
   * Adds a new lemma to this lemma DB, with a unique name or None, which will automatically assign a name.
   * @param lemma The lemma whose Provable will be inserted under its name.
   * @return Internal lemma identifier.
   * @requires if (lemma.name==Some(n)) then !contains(n)
   * @ensures  if (lemma.name==Some(n)) then \result==n  (usually)
   */
  def add(lemma: Lemma): LemmaID
}
