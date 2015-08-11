/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.tactics.Tactics.{Tactic, ApplyRule}

import scala.collection.immutable._

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.Evidence

import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
 * Derived Axioms.
 * @author Andre Platzer
 * @see [[edu.cmu.cs.ls.keymaerax.core.AxiomBase]]
 */
object DerivedAxioms {
  /** Database for derived axioms */
  //@todo which lemma db to use?
  val derivedAxiomDB = new FileLemmaDB
  type LemmaID = String
  private val derivedEvidence: List[Evidence] = Nil

  /** Derive an axiom from the given provable, package it up as a Lemma and make it available */
  //@todo add to FileLemmaDB
  private def derivedAxiom(name: String, fact: Provable): ApplyRule[LookupLemma] = {
    require(fact.isProved, "only proved Provables would be accepted as derived axioms")
    val lemma = Lemma(fact, derivedEvidence, Some(name))
    val lemmaID = LookupLemma.addLemma(derivedAxiomDB, lemma)
    val lemmaRule = LookupLemma(derivedAxiomDB, lemmaID)
    new ApplyRule(lemmaRule) {
      override def applicable(node: ProofNode): Boolean = node.sequent.sameSequentAs(lemma.fact.conclusion)
    }
  }

  /** Derive an axiom for the given derivedAxiom with the given tactic, package it up as a Lemma and make it available */
  private def derivedAxiom(name: String, derived: Sequent, tactic: Tactic): ApplyRule[LookupLemma] = {
    val rootNode = new RootNode(derived)
    //@todo what/howto ensure it's been initialized already
    Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, rootNode))
    assert(rootNode.isClosed, "tactics proving derived axioms should close the proof")
    val witness: Provable = rootNode.provableWitness
    assert(witness.isProved, "tactics proving derived axioms should produce proved Provables")
    derivedAxiom(name, witness)
  }

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
  lazy val doubleNegationAxiom = derivedAxiom("!! double negation",
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
   * {{{Axiom "abs".
   *   (abs(s()) = t()) <->  ((s()>=0 & t()=s()) | (s()<0 & t()=-s()))
   * End.
   * }}}
   * @Derived from built-in arithmetic abs in [[edu.cmu.cs.ls.keymaerax.tools.Mathematica]]
   */
  lazy val abs = derivedAxiom("abs",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(abs(s()) = t()) <->  ((s()>=0 & t()=s()) | (s()<0 & t()=-s()))".asFormula)),
    TactixLibrary.master
  )

  /**
   * {{{Axiom "exists dual".
   *   (\exists x . p(x)) <-> !(\forall x . (!p(x)))
   * End.
   * }}}
   * @Derived
   */
//  lazy val existsDualAxiom: LookupLemma = derivedAxiom("exists dual",
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
