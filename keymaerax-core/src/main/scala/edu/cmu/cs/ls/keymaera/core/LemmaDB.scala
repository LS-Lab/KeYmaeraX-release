package edu.cmu.cs.ls.keymaera.core

/**
 * Store and retrieve lemmas.
 *
 * Created by smitsch on 4/27/15.
 * @author Stefan Mitsch
 */
trait LemmaDB {
  /**
   * Returns the lemma's conclusion.
   * @param lemmaID Identifies the lemma.
   * @return The conclusion.
   */
  def getLemmaConclusion(lemmaID: String): Formula

  /**
   * Adds a lemma to this lemma DB. The lemma is proved using some tool, which provided evidence of the correctness of
   * the lemma.
   * @param conclusion The lemma's conclusion.
   * @param evidence Evidence that the lemma is correct: (input to the tool, tool output)
   * @return The lemma ID, if added successfully; None otherwise.
   */
  private[core] def addLemma(conclusion: Formula, evidence: (String, String)): Option[String]
}
