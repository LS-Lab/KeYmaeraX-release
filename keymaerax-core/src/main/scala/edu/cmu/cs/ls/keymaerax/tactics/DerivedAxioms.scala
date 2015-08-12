/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.tactics.Tactics.{PositionTactic, Tactic, ApplyRule}

import scala.collection.immutable
import scala.collection.immutable._

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.{ToolEvidence, Evidence}

import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
 * Derived Axioms.
 * @author Andre Platzer
 * @see [[edu.cmu.cs.ls.keymaerax.core.AxiomBase]]
 */
object DerivedAxioms {
  import TactixLibrary._
  /** Database for derived axioms */
  //@todo which lemma db to use?
  val derivedAxiomDB = new FileLemmaDB
  type LemmaID = String

  /** Derive an axiom from the given provable, package it up as a Lemma and make it available */
  private def derivedAxiom(name: String, fact: Provable): ApplyRule[LookupLemma] = {
    require(fact.isProved, "only proved Provables would be accepted as derived axioms")
    // create evidence (traces input into tool and output from tool)
    val evidence = new ToolEvidence(immutable.Map("input" -> fact.toString, "output" -> "true")) :: Nil
    val lemma = Lemma(fact, evidence, Some(name))
    // first check whether the lemma DB already contains identical lemma name
    val lemmaID = if (derivedAxiomDB.contains(name)) {
      // identical lemma contents with identical name, so reuse ID
      if (derivedAxiomDB.get(name) == Some(lemma)) name
      else throw new IllegalStateException("Prover already has a different lemma filed under the same name " + derivedAxiomDB.get(name))
    } else {
      LookupLemma.addLemma(derivedAxiomDB, lemma)
    }
    val lemmaRule = LookupLemma(derivedAxiomDB, lemmaID)
    new ApplyRule(lemmaRule) {
      override def applicable(node: ProofNode): Boolean = node.sequent.sameSequentAs(lemma.fact.conclusion)
    }
  }

  /** Derive an axiom for the given derivedAxiom with the given tactic, package it up as a Lemma and make it available */
  private def derivedAxiom(name: String, derived: Sequent, tactic: Tactic): ApplyRule[LookupLemma] = {
    //@todo optimize: no need to prove if already filed in derivedAxiomDB anyhow
    val witness = tactic2Provable(derived, tactic)
    assert(witness.isProved, "tactics proving derived axioms should produce proved Provables")
    derivedAxiom(name, witness)
  }

  /**
   * Convert a tactic for a goal to the resulting Provable
   * @see [[TactixLibrary.by(Provable)]]
   */
  private[tactics] def tactic2Provable(goal: Sequent, tactic: Tactic): Provable = {
    val rootNode = new RootNode(goal)
    //@todo what/howto ensure it's been initialized already
    Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, rootNode))
    rootNode.provableWitness
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
   * {{{Axiom "<-> reflexive".
   *  p() <-> p()
   * End.
   * }}}
   * @Derived
   */
  lazy val equivReflexiveAxiom = derivedAxiom("<-> reflexive",
    Provable.startProof(Sequent(Nil, IndexedSeq(), IndexedSeq("p() <-> p()".asFormula)))
      (EquivRight(SuccPos(0)), 0)
      // right branch
      (Close(AntePos(0),SuccPos(0)), 1)
      // left branch
      (Close(AntePos(0),SuccPos(0)), 0)
  )

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
    TactixLibrary.QE //TactixLibrary.master
  )

  /**
   * {{{Axiom "exists dual".
   *   (\exists x . p(x)) <-> !(\forall x . (!p(x)))
   * End.
   * }}}
   * @Derived
   */
  lazy val existsDualAxiom = derivedAxiom("exists dual",
    Sequent(Nil, IndexedSeq(), IndexedSeq("\\exists x q(x) <-> !(\\forall x (!q(x)))".asFormula)),
    useAt("all dual")(SuccPosition(0, PosInExpr(1::0::Nil))) &
      useAt(doubleNegationAxiom)(SuccPosition(0, PosInExpr(1::Nil))) &
      useAt(doubleNegationAxiom)(SuccPosition(0, PosInExpr(1::0::Nil))) &
      useAt(equivReflexiveAxiom)(SuccPosition(0))
  )

  //@todo this is somewhat indirect. Maybe it'd be better to represent derived axioms merely as Lemma and auto-wrap them within their ApplyRule[LookupLemma] tactics on demand.
  private def useAt(lem: ApplyRule[LookupLemma]): PositionTactic = TactixLibrary.useAt(lem.rule.lemma.fact)

  private def useAt(axiom: String): PositionTactic =
    TactixLibrary.useAt(Provable.startProof(Sequent(Nil, IndexedSeq(), IndexedSeq(Axiom.axioms(axiom))))(Axiom(axiom), 0))

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
