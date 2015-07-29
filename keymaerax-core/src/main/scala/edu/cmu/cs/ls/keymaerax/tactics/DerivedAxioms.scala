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

  /** Derive an axiom from the given provable, package it up as a Lemma and make it available */
  //@todo add to FileLemmaDB
  private def derivedAxiom(name: String, fact: Provable) = {require(fact.isProved); Lemma(fact, derivedEvidence, Some(name))}

  private val x = Variable("x_", None, Real)
  private val px = PredOf(Function("p_", None, Real, Bool), x)
  private val pany = PredOf(Function("p_", None, Real, Bool), Anything)
  private val qx = PredOf(Function("q_", None, Real, Bool), x)
  private val qany = PredOf(Function("q_", None, Real, Bool), Anything)
  private val fany = FuncOf(Function("f_", None, Real, Real), Anything)
  private val gany = FuncOf(Function("g_", None, Real, Real), Anything)
  private val ctxt = Function("ctx_", None, Real, Real) // function symbol
  private val ctxf = Function("ctx_", None, Real, Bool) // predicate symbol
  private val context = Function("ctx_", None, Bool, Bool) // predicational symbol

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

  /**
   * {{{Axiom "exists dual".
   *   (\exists x . p(x)) <-> !(\forall x . (!p(x)))
   * End.
   * }}}
   * @Derived
   */
//  lazy val existsDualAxiom: Lemma = derivedAxiom("exists dual",
//    Provable.startProof(Sequent(Nil, IndexedSeq(), IndexedSeq("\\exists x q(x) <-> !(\\forall x (!q(x)))".asFormula)))
//      (CutRight("\\exists x q(x) <-> !!(\\exists x (!!q(x)))".asFormula, SuccPos(0)), 0)
//      // right branch
//      (EquivifyRight(SuccPos(0)), 1)
//      (AxiomaticRule("CE congruence", USubst(
//        SubstitutionPair(PredicationalOf(context, DotFormula), "\\exists x q(x) <-> !⎵".asFormula) ::
//          SubstitutionPair(pany, "!\\exists x !!q(x)".asFormula) ::
//          SubstitutionPair(qany, "\\forall x !q(x)".asFormula) :: Nil
//      )), 1)
//      (CommuteEquivRight(SuccPos(0)), 1)
//      (Axiom("all dual"), 1)
//      (Close(AntePos(0),SuccPos(0)), 1)
//  )
}
