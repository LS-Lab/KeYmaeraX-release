/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
/**
 * @author Stefan Mitsch
 * @note Code Review: 2015-05-01
 */
package edu.cmu.cs.ls.keymaerax.core

/**
 * Store and retrieve lemmas.
 *
 * Created by smitsch on 4/27/15.
 * @author Stefan Mitsch
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
   * @return The lemma, if found. None otherwise.
   * @ensures contains(lemmaID) && \result==Some(l) && l.name == lemmaID
   *         || !contains(lemmaID) && \result==None
   */
  def get(lemmaID: LemmaID): Option[Lemma]

  /**
   * Adds a new lemma to this lemma DB, with a unique name or None, which will automatically assign a name.
   * @param lemma The lemma to add.
   * @return The lemma ID.
   * @requires if (lemma.name==Some(n)) then !contains(n)
   */
  private[core] def add(lemma: Lemma): LemmaID
}
