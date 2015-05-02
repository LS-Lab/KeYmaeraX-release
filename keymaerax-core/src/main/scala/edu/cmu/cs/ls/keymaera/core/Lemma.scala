/**
 * @author Stefan Mitsch
 * @note Code Review: 2015-05-01
 */
package edu.cmu.cs.ls.keymaera.core

import edu.cmu.cs.ls.keymaera.parser.Evidence

/**
 * Lemmas are named Provables, supported by some evidence.
 * Created by smitsch on 4/28/15.
 * @author Stefan Mitsch
 * @note Construction is not soundness-critical so constructor is not private, because Provables can only be constructed by prover core.
 */
final case class Lemma(fact: Provable, evidence: List[Evidence], name: Option[String] = None)
