/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax

/**
 * KeYmaera X Kernel:
 * Soundness-critical core of the Axiomatic Tactical Theorem Prover KeYmaera X
 * ==============================================================================================
 *
 * Defines the [[edu.cmu.cs.ls.keymaerax.core.Expression syntax]],
 * [[edu.cmu.cs.ls.keymaerax.core.StaticSemantics static semantics]],
 * [[edu.cmu.cs.ls.keymaerax.core.USubst uniform substitutions]],
 * [[edu.cmu.cs.ls.keymaerax.core.Axiom axioms]], and
 * [[edu.cmu.cs.ls.keymaerax.core.Rule proof rules]] for constructing
 * [[edu.cmu.cs.ls.keymaerax.core.Provable proof certificates]] of
 * [[http://symbolaris.com/logic/dL.html differential dynamic logic]].
 * Provides basic [[edu.cmu.cs.ls.keymaerax.core.LemmaDB lemma data base]],
 * [[edu.cmu.cs.ls.keymaerax.core.QETool real arithmetic interfaces]],
 * [[edu.cmu.cs.ls.keymaerax.core.CoreException error reporting]], and
 * [[edu.cmu.cs.ls.keymaerax.core.SetLattice set lattice management]].
 * 
 * ==Usage Overview==
 * The KeYmaera X Kernel package provides the soundness-critical core of KeYmaera X.
 * It provides ways of constructing proofs that, by construction, can only be constructed using
 * the proof rules that the KeYmaera X Kernel provides.
 * The [[[[edu.cmu.cs.ls.keymaerax.tactic tactics]] that KeYmaera X provides give you a more powerful and flexible and easier way of
 * constructing and searching for proofs, but they internally reduce to what is shown here.
 *
 * ===Constructing Proofs===
 * The proof certificates of KeYmaera X are of type [[edu.cmu.cs.ls.keymaerax.core.Provable]].
 * [[edu.cmu.cs.ls.keymaerax.core.Provable.startProof]] begins a new proof of a
 * [[edu.cmu.cs.ls.keymaerax.core.Sequent]] containing the conjectured differential dynamic logic formula.
 * A proof rule of type [[edu.cmu.cs.ls.keymaerax.core.Rule]] can be applied to any subgoal of a
 * [[edu.cmu.cs.ls.keymaerax.core.Provable]] by [[edu.cmu.cs.ls.keymaerax.core.Provable.apply]] to advance the proof
 * until that Provable has been proved since [[edu.cmu.cs.ls.keymaerax.core.Provable.isProved]] is true.
 * Subgoals are identified by integers.
 * {{{
 *   import scala.collection.immutable._
 *   val verum = new Sequent(Seq(), IndexedSeq(), IndexedSeq(True))
 *   // conjecture
 *   val provable = Provable.startProof(verum)
 *   // construct a proof
 *   val proof = provable(CloseTrue(SuccPos(0)), 0)
 *   // check if proof successful, i.e. no remaining subgoals
 *   if (proof.isProved) println("Successfully proved " + proof.proved)
 * }}}
 * Of course, [[edu.cmu.cs.ls.keymaerax.tactics]] make it much easier to describe proof search procedures
 * compared to the above explicit proof construction.
 * The tactics internally construct proofs this way, but add additional flexibility and
 * provide convenient ways of expressing proof search strategies in a tactic language.
 *
 * ===Combining Proofs===
 * Multiple Provable objects for subderivations obtained from different sources can also be merged
 * into a single Provable object with [[edu.cmu.cs.ls.keymaerax.core.Provable.apply]]([[edu.cmu.cs.ls.keymaerax.core.Provable]],Int).
 * The above example can be continued to merge proofs as follows:
 * {{{
 *   // ... continued from above
 *   val more = new Sequent(Seq(), IndexedSeq(),
 *       IndexedSeq(Imply(Greater(Variable("x"), Number(5)), True)))
 *   // another conjecture
 *   val moreProvable = Provable.startProof(more)
 *   // construct another (partial) proof
 *   val moreProof = moreProvable(ImplyRight(SuccPos(0)), 0)(HideLeft(AntePos(0)), 0)
 *   // merge proofs by gluing their Provables together
 *   val mergedProof = moreProof(proof, 0)
 *   // check if proof successful, i.e. no remaining subgoals
 *   if (mergedProof.isProved) println("Successfully proved " + mergedProof.proved)
 * }}}
 * More styles for proof construction are shown in [[edu.cmu.cs.ls.keymaerax.core.Provable]].
 *
 * ==Differential Dynamic Logic==
 * The language of [[http://symbolaris.com/logic/dL.html differential dynamic logic]] is described
 * in KeYmaera X by its [[edu.cmu.cs.ls.keymaerax.core.Expression syntax]] and [[edu.cmu.cs.ls.keymaerax.core.StaticSemantics static semantics]].
 *
 * ===Syntax===
 * The immutable algebraic data structures for the expressions of differential dynamic logic are of type
 * [[edu.cmu.cs.ls.keymaerax.core.Expression]].
 * Expressions are categorized according to their kind by the syntactic categories
 * of the grammar of differential dynamic logic:
 *
 * 1. terms are of type [[edu.cmu.cs.ls.keymaerax.core.Term]] of kind [[edu.cmu.cs.ls.keymaerax.core.TermKind]]
 *
 * 2. formulas are of type [[edu.cmu.cs.ls.keymaerax.core.Formula]] of kind [[edu.cmu.cs.ls.keymaerax.core.FormulaKind]]
 *
 * 3. hybrid programs are of type [[edu.cmu.cs.ls.keymaerax.core.Program]] of kind [[edu.cmu.cs.ls.keymaerax.core.ProgramKind]]
 *
 * See [[http://arxiv.org/pdf/1503.01981.pdf Section 2.1]]
 *
 * ===Static Semantics===
 * The static semantics of differential dynamic logic is captured in
 * [[edu.cmu.cs.ls.keymaerax.core.StaticSemantics]]
 * in terms of the [[edu.cmu.cs.ls.keymaerax.core.StaticSemantics#freeVars(edu.cmu.cs.ls.keymaerax.core.Expression) free variables]] and
 * [[edu.cmu.cs.ls.keymaerax.core.StaticSemantics#boundVars(edu.cmu.cs.ls.keymaerax.core.Expression) bound variables]] that expressions have
 * as well as their [[edu.cmu.cs.ls.keymaerax.core.StaticSemantics#signature(edu.cmu.cs.ls.keymaerax.core.Expression) signatures]] (set of occurring symbols).
 * See [[http://arxiv.org/pdf/1503.01981.pdf Section 2.3]]
 *
 * ==Theorem Prover==
 * The KeYmaera X Prover Kernel provides [[edu.cmu.cs.ls.keymaerax.core.UniformSubstitutionRule uniform substitutions]],
 * [[edu.cmu.cs.ls.keymaerax.core.BoundRenaming bound variable renaming]], and
 * [[edu.cmu.cs.ls.keymaerax.core.Axiom axioms]] of differential dynamic logic.
 * For efficiency, it also directly provides propositional sequent proof rules and
 * [[edu.cmu.cs.ls.keymaerax.core.Skolemize Skolemization]].
 *
 * ===Axioms===
 * The axioms and axiomatic rules of differential dynamic logic can be looked up with
 * [[edu.cmu.cs.ls.keymaerax.core.Axiom]] and [[edu.cmu.cs.ls.keymaerax.core.AxiomaticRule]] respectively.
 * All available axioms are listed in [[edu.cmu.cs.ls.keymaerax.core.Axiom.axioms]],
 * all available axiomatic rules are listed in [[edu.cmu.cs.ls.keymaerax.core.AxiomaticRule.rules]]
 * which both ultimately come from the file [[edu.cmu.cs.ls.keymaerax.core.AxiomBase]].
 * See [[http://arxiv.org/pdf/1503.01981.pdf Sections 4 and 5.0]]
 *
 * ===Uniform Substitutions===
 * [[edu.cmu.cs.ls.keymaerax.core.USubst Uniform substitutions]] uniformly replace all occurrences of a given predicate p(.) by a formula in (.)
 * and likewise for function symbols f(.) and program constants.
 * Uniform substitutions and their application mechanism for differential dynamic logic
 * are implemented in [[edu.cmu.cs.ls.keymaerax.core.USubst]].
 * See [[http://arxiv.org/pdf/1503.01981.pdf Section 3.0]]
 *
 * The proof rule [[edu.cmu.cs.ls.keymaerax.core.UniformSubstitutionRule]] applies uniform substitutions as a proof rule.
 * The [[edu.cmu.cs.ls.keymaerax.core.AxiomaticRule]] generates uniform substitution instances of axiomatic rules.
 * See [[http://arxiv.org/pdf/1503.01981.pdf Section 4]]
 *
 * ===Sequent Proof Rules===
 * All proof rules for differential dynamic logic, including the uniform substitution and bound variable renaming rules as well as
 * efficient propositional sequent proof rules and Skolemization [[edu.cmu.cs.ls.keymaerax.core.Skolemize]]
 * are all of type [[edu.cmu.cs.ls.keymaerax.core.Rule]], which are the only proof rules that can ever be applied to a proof.
 * See [[http://dx.doi.org/10.1007/s10817-008-9103-8 sequent calculus]]
 *
 * ==Additional Capabilities==
 * ===Lemma Mechanism===
 * A lemma database and an interface to real arithmetic decision procedures are defined in
 * [[edu.cmu.cs.ls.keymaerax.core.LemmaDB]] and [[edu.cmu.cs.ls.keymaerax.core.QETool]]
 * along with an implementation of a lemma data base using files [[edu.cmu.cs.ls.keymaerax.core.FileLemmaDB]].
 *
 * ===Error Reporting===
 * Errors from the prover core are reported as exceptions of type [[edu.cmu.cs.ls.keymaerax.core.ProverException]]
 * whose main responsibility is to propagate problems in traceable ways to the user by augmenting them
 * with contextual information.
 *
 * ===Set Lattice===
 * A data structure for sets (or rather lattice completions of sets) is provided in
 * [[edu.cmu.cs.ls.keymaerax.core.SetLattice]] based on Scala's immutable sets.
 *
 * @author Andre Platzer
 * @see Andre Platzer. [[http://www.cs.cmu.edu/~aplatzer/pub/usubst.pdf A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015.
 * @see Andre Platzer. [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981]], 2015.
 * @see "Nathan Fulton, Stefan Mitsch, Jan-David Quesel, Marcus Volp and Andre Platzer. KeYmaera X: An axiomatic tactical theorem prover for hybrid systems.  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015."
 * @see Andre Plater. [[http://dx.doi.org/10.1109/LICS.2012.64 The complete proof theory of hybrid systems]]. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012
 * @see Andre Platzer. [[http://dx.doi.org/10.1007/s10817-008-9103-8 Differential dynamic logic for hybrid systems]]. Journal of Automated Reasoning, 41(2), pages 143-189, 2008.
 * @see [[edu.cmu.cs.ls.keymaerax.core.Provable]]
 * @see [[edu.cmu.cs.ls.keymaerax.core.Expression]]
 * @see [[edu.cmu.cs.ls.keymaerax.core.StaticSemantics]]
 * @see [[edu.cmu.cs.ls.keymaerax.core.USubst]]
 * @see [[edu.cmu.cs.ls.keymaerax.core.Lemma]]
 */
package object core {}
