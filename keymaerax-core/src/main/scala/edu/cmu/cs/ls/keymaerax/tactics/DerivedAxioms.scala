/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import scala.collection.immutable._

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.Evidence

import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
 * Derived Axioms.
 * @author aplatzer
 * @see [[edu.cmu.cs.ls.keymaerax.core.AxiomBase]]
 */
object DerivedAxioms {
  private val derivedEvidence: List[Evidence] = Nil

  private def derivedAxiom(name: String, fact: Provable) = {require(fact.isProved); Lemma(fact, derivedEvidence, Some(name))}

  /**
   * {{{Axiom "!! double negation".
   *  p() <-> !(!p())
   * End.
   * }}}
   * @Derived
   */
  lazy val doubleNegationAxiom: Lemma = derivedAxiom("!! double negation",
    Provable.startProof(Sequent(Nil, IndexedSeq(), IndexedSeq("p() <-> !(!p())".asFormula)))
      (EquivRight(SuccPos(0)), 0)
      // right branch
      (NotLeft(AntePos(0)), 1)
      (NotRight(SuccPos(1)), 1)
      (Close(AntePos(0),SuccPos(0)), 1)
      // left branch
      (NotRight(SuccPos(0)), 0)
      (NotLeft(AntePos(1)), 0)
      (Close(AntePos(0),SuccPos(0)), 0)
  )

}
