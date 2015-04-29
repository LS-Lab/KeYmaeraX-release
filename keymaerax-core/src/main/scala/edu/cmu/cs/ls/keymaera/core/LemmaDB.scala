package edu.cmu.cs.ls.keymaera.core

/**
 * Store and retrieve lemmas.
 *
 * Created by smitsch on 4/27/15.
 * @author Stefan Mitsch
 */
trait LemmaDB {
  /**
   * Indicates whether or not this lemma DB contains a lemma with the specified ID.
   * @param lemmaID Identifies the lemma.
   * @return True, if this lemma DB contains a lemma with the specified ID; false otherwise.
   */
  def contains(lemmaID: String): Boolean

  /**
   * Returns a lemma.
   * @param lemmaID Identifies the lemma.
   * @return The lemma, if found. None otherwise.
   */
  def get(lemmaID: String): Option[Lemma]

  /**
   * Adds a lemma to this lemma DB.
   * @param lemma The lemma to add.
   * @return The lemma ID.
   */
  private[core] def add(lemma: Lemma): String
}
