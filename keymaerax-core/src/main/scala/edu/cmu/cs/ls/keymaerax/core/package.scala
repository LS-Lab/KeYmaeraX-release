package edu.cmu.cs.ls.keymaerax

/**
 * =KeYmaera X: An Axiomatic Tactical Theorem Prover=
 * KeYmaera X Kernel: Soundness-critical core of the KeYmaera X theorem prover.
 * 
 * Defines the syntax, static semantics, uniform substitutions, axioms, and proof rules of
 * differential dynamic logic.
 * Provides lemma data base, real arithmetic interfaces, error reporting, and set lattice management.
 * 
 * ==Usage Overview==
 * The KeYmaera X Kernel package provides the soundness-critical core of KeYmaera X.
 * It provides ways of constructing proofs that, by construction, can only be constructed using
 * the proof rules that the KeYmaera X Kernel provides.
 * The tactics that KeYmaera X provides give you a more powerful and flexible and easier way of
 * constructing and searching for proofs, but they internally reduce to what is shown here.
 *
 * ===Constructing Proofs===
 * The proof certificates of KeYmaera X are [[edu.cmu.cs.ls.keymaerax.core.Provable]] objects.
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
 *   // check if proof successful
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
 *   val more = new Sequent(Seq(), IndexedSeq(),
 *       IndexedSeq(Imply(Greater(Variable("x"), Number(5)), True)))
 *   // another conjecture
 *   val moreProvable = Provable.startProof(more)
 *   // construct another (partial) proof
 *   val moreProof = moreProvable(ImplyRight(SuccPos(0)), 0)(HideLeft(AntePos(0)), 0)
 *   // merge proofs by gluing their Provables together
 *   val mergedProof = moreProof(proof, 0)
 *   // check if proof successful
 *   if (mergedProof.isProved) println("Successfully proved " + mergedProof.proved)
 * }}}
 *
 * ==Differential Dynamic Logic==
 * The language of differential dynamic logic is described in KeYmaera X by its syntax and static semantics.
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
 * in terms of the free variables and bound variables that expressions have as well as their signatures
 * (set of occurring symbols).
 * See [[http://arxiv.org/pdf/1503.01981.pdf Section 2.3]]
 *
 * ==Theorem Prover==
 * The KeYmaera X Prover Kernel provides uniform substitutions, bound variable renamings,
 * axioms of differential dynamic logic.
 * For efficiency, it also directly provides propositional sequent proof rules and Skolemization.
 *
 * ===Uniform Substitutions===
 * Uniform substitutions and their application mechanism for differential dynamic logic
 * are implemented in [[edu.cmu.cs.ls.keymaerax.core.USubst]].
 * See [[http://arxiv.org/pdf/1503.01981.pdf Section 3.0]]
 *
 * The proof rule [[edu.cmu.cs.ls.keymaerax.core.UniformSubstitutionRule]] applies uniform substitutions as a proof rule.
 * The [[edu.cmu.cs.ls.keymaerax.core.AxiomaticRule]] generates uniform substitution instances of axiomatic rules.
 * See [[http://arxiv.org/pdf/1503.01981.pdf Section 4]]
 *
 * ===Axioms===
 * The axioms and axiomatic rules of differential dynamic logic are all listed in [[edu.cmu.cs.ls.keymaerax.core.AxiomBase]].
 * See [[http://arxiv.org/pdf/1503.01981.pdf Sections 4 and 5.0]]
 *
 * ===Sequent Proof Rules===
 * All proof rules for differential dynamic logic, including the uniform substitution and bound variable renaming rules as well as
 * efficient propositional sequent proof rules and Skolemization [[edu.cmu.cs.ls.keymaerax.core.Skolemize]]
 * are all of type [[edu.cmu.cs.ls.keymaerax.core.Rule]], which are the only proof rules that can ever be applied to a proof.
 * See [[http://dx.doi.org/10.1007/s10817-008-9103-8 sequent calculus]]
 *
 * ==Additional Capabilities==
 * ===Error Reporting===
 * Errors from the prover core are reported as exceptions of type [[edu.cmu.cs.ls.keymaerax.core.ProverException]]
 * whose main responsibility is to propagate problems in traceable ways to the user by augmenting them
 * with contextual information.
 *
 * ===Lemma Mechanism===
 * A lemma database and an interface to real arithmetic decision procedures are defined in
 * [[edu.cmu.cs.ls.keymaerax.core.LemmaDB]] and [[edu.cmu.cs.ls.keymaerax.core.QETool]]
 * along with an implementation of a lemma data base using files [[edu.cmu.cs.ls.keymaerax.core.FileLemmaDB]]
 *
 * ===Set Lattice===
 * A data structure for sets (or rather lattice completions of sets) is provided in
 * [[edu.cmu.cs.ls.keymaerax.core.SetLattice]] based on Scala's immutable sets.
 *
 * @author aplatzer
 * @see Andre Platzer. [[http://www.cs.cmu.edu/~aplatzer/pub/usubst.pdf A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015.
 * @see Andre Platzer. [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981]], 2015.
 * @see "Nathan Fulton, Stefan Mitsch, Jan-David Quesel, Marcus Volp and Andre Platzer. KeYmaera X: An axiomatic tactical theorem prover for hybrid systems.  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015."
 * @see Andre Plater. [[http://dx.doi.org/10.1109/LICS.2012.64 The complete proof theory of hybrid systems]]. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012
 * @see Andre Platzer. [[http://dx.doi.org/10.1007/s10817-008-9103-8 Differential dynamic logic for hybrid systems]]. Journal of Automated Reasoning, 41(2), pages 143-189, 2008.
 */
package object core {}
