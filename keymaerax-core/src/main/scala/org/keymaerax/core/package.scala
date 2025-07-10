/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Differential Dynamic Logic prover Microkernel.
 *
 * @author
 *   Andre Platzer
 * @see
 *   [[org.keymaerax.Bibliography.JarPlatzer17 A complete uniform substitution calculus for differential dynamic logic]]
 * @see
 *   [[org.keymaerax.Bibliography.ToclPlatzer15 Differential game logic]]
 * @see
 *   [[org.keymaerax.Bibliography.LicsPlatzer12b]]
 * @note
 *   Code Review: 2020-02-17
 */
package org.keymaerax

import scala.annotation.elidable
import scala.collection.immutable

/**
 * KeYmaera X Kernel is the soundness-critical core of the Axiomatic Tactical Theorem Prover KeYmaera X.
 *
 * =KeYmaera X Kernel=
 *
 * The KeYmaera X Kernel implements [[org.keymaerax.Bibliography.JarPlatzer17 Differential Dynamic Logic]] and defines
 *
 *   - Syntax of
 * [[http://lfcps.org/logic/dL.html differential dynamic logic]]:
 *   - [[org.keymaerax.core.Expression Syntax of dL Expressions]]
 *   - [[org.keymaerax.core.StaticSemantics Static Semantics]]
 *
 *   - Proof Construction of [[org.keymaerax.core.Provable proof certificates]] from
 *     - [[org.keymaerax.core.Provable.axioms axioms]]
 *     - [[org.keymaerax.core.USubst Uniform substitutions]]
 *     - [[org.keymaerax.core.URename Uniform renamings]]
 *     - [[org.keymaerax.core.Rule Proof rules]]
 *
 *   - Provides basic
 *     [[org.keymaerax.core.Provable.fromStorageString(storedProvable:String):edu\.cmu\.cs\.ls\.keymaerax\.core\.Provable* Stored Provables as Strings]],
 *     [[org.keymaerax.core.QETool real arithmetic interfaces]], [[org.keymaerax.core.CoreException error reporting]],
 *     and [[org.keymaerax.core.SetLattice set lattice management]] for sets of symbols.
 *
 * ==Usage Overview==
 * The KeYmaera X Kernel package provides the ''soundness-critical core of
 * [[org.keymaerax.Bibliography.CadeFultonMQVP15 KeYmaera X]]''. It provides ways of constructing proofs that, by
 * construction, can only be constructed using the proof rules that the KeYmaera X Kernel provides. The
 * [[org.keymaerax.btactics proof tactics]] that KeYmaera X provides give you a more powerful and flexible and easier
 * way of constructing and searching for proofs, but they internally reduce to what is shown here.
 *
 * ===Constructing Proofs===
 * The proof certificates of KeYmaera X are of type [[org.keymaerax.core.Provable]].
 * [[org.keymaerax.core.Provable.startProof(goal:edu\.cmu\.cs\.ls\.keymaerax\.core\.Sequent):edu\.cmu\.cs\.ls\.keymaerax\.core\.Provable*]]
 * begins a new proof of a [[org.keymaerax.core.Sequent]] containing the conjectured differential dynamic logic formula.
 * A proof rule of type [[org.keymaerax.core.Rule]] can be applied to any subgoal of a [[org.keymaerax.core.Provable]]
 * by
 * [[org.keymaerax.core.Provable.apply(rule:edu\.cmu\.cs\.ls\.keymaerax\.core\.Rule,subgoal:edu\.cmu\.cs\.ls\.keymaerax\.core\.Provable\.Subgoal):edu\.cmu\.cs\.ls\.keymaerax\.core\.Provable*]]
 * to advance the proof until that Provable has been proved since [[org.keymaerax.core.Provable.isProved]] is true.
 * Subgoals are identified by integers.
 * {{{
 *   import scala.collection.immutable._
 *   val verum = new Sequent(IndexedSeq(), IndexedSeq(True))
 *   // conjecture
 *   val provable = Provable.startProof(verum)
 *   // construct a proof
 *   val proof = provable(CloseTrue(SuccPos(0)), 0)
 *   // check if proof successful, i.e. no remaining subgoals
 *   if (proof.isProved) println("Successfully proved " + proof.proved)
 * }}}
 * Of course, [[org.keymaerax.btactics]] make it much easier to describe proof search procedures compared to the above
 * explicit proof construction. The tactics internally construct proofs this way, but add additional flexibility and
 * provide convenient ways of expressing proof search strategies in a tactic language.
 *
 * ===Combining Proofs===
 * Multiple Provable objects for subderivations obtained from different sources can also be merged into a single
 * Provable object by substitution with [[org.keymaerax.core.Provable.apply(org.keymaerax.core.Provable,Int)]]. The
 * above example can be continued to merge proofs as follows:
 * {{{
 *   // ... continued from above
 *   val more = new Sequent(IndexedSeq(),
 *       IndexedSeq(Imply(Greater(Variable("x"), Number(5)), True)))
 *   // another conjecture
 *   val moreProvable = Provable.startProof(more)
 *   // construct another (partial) proof
 *   val moreProof = moreProvable(ImplyRight(SuccPos(0)), 0)(HideLeft(AntePos(0)), 0)
 *   // merge proofs by gluing their Provables together (substitution)
 *   val mergedProof = moreProof(proof, 0)
 *   // check if proof successful, i.e. no remaining subgoals
 *   if (mergedProof.isProved) println("Successfully proved " + mergedProof.proved)
 * }}}
 * [[org.keymaerax.core.Provable More styles for proof construction are shown in Provable's]].
 *
 * ==Differential Dynamic Logic==
 * The language of [[http://lfcps.org/logic/dL.html differential dynamic logic]] is described in KeYmaera X by its
 * [[org.keymaerax.core.Expression syntax]] and [[org.keymaerax.core.StaticSemantics static semantics]].
 *
 * ===Syntax===
 * The immutable algebraic data structures for the expressions of differential dynamic logic are of type
 * [[org.keymaerax.core.Expression]]. Expressions are categorized according to their kind by the syntactic categories of
 * the grammar of differential dynamic logic:
 *
 *   1. [[org.keymaerax.core.Term terms]] are of type [[org.keymaerax.core.Term]] of kind
 *      [[org.keymaerax.core.TermKind]]
 *   1. [[org.keymaerax.core.Formula formulas]] are of type [[org.keymaerax.core.Formula]] of kind
 *      [[org.keymaerax.core.FormulaKind]]
 *   1. [[org.keymaerax.core.Program hybrid programs]] are of type [[org.keymaerax.core.Program]] of kind
 *      [[org.keymaerax.core.ProgramKind]]
 *   1. [[org.keymaerax.core.DifferentialProgram differential programs]] are of type
 *      [[org.keymaerax.core.DifferentialProgram]] of kind [[org.keymaerax.core.DifferentialProgramKind]]
 *
 * See
 * [[org.keymaerax.Bibliography.JarPlatzer17 A complete uniform substitution calculus for differential dynamic logic]]
 * Section 2.1
 *
 * ===Static Semantics===
 * The static semantics of differential dynamic logic is captured in [[org.keymaerax.core.StaticSemantics]] in terms of
 * the [[org.keymaerax.core.StaticSemantics.freeVars(org.keymaerax.core.Expression) free variables]] and
 * [[org.keymaerax.core.StaticSemantics.boundVars(org.keymaerax.core.Expression) bound variables]] that expressions have
 * as well as their [[org.keymaerax.core.StaticSemantics.signature(org.keymaerax.core.Expression) signatures]] (set of
 * occurring symbols). See
 * [[org.keymaerax.Bibliography.JarPlatzer17 A complete uniform substitution calculus for differential dynamic logic]]
 * Section 2.4
 *
 * ==Theorem Prover==
 * The KeYmaera X Prover Kernel provides [[org.keymaerax.core.USubst uniform substitutions]],
 * [[org.keymaerax.core.UniformRenaming uniform]] and [[org.keymaerax.core.BoundRenaming bound variable renaming]], and
 * [[org.keymaerax.core.Provable.axioms axioms]] of differential dynamic logic. For efficiency, it also directly
 * provides propositional sequent proof rules and [[org.keymaerax.core.Skolemize Skolemization]].
 *
 * ===Axioms===
 * The axioms and axiomatic rules of differential dynamic logic can be looked up with
 * [[org.keymaerax.core.Provable.axioms]] and [[org.keymaerax.core.Provable.rules]] respectively. All available axioms
 * are listed in [[org.keymaerax.core.Provable.axioms]], all available axiomatic rules are listed in
 * [[org.keymaerax.core.Provable.rules]] which both ultimately come from the file [[org.keymaerax.core.AxiomBase]]. See
 * [[org.keymaerax.Bibliography.JarPlatzer17 A complete uniform substitution calculus for differential dynamic logic]]
 * Sections 4 and 5.0. Additional axioms are available as derived axioms and lemmas in [[org.keymaerax.btactics.Ax]].
 *
 * ===Uniform Substitutions===
 * [[org.keymaerax.core.USubst Uniform substitutions]] uniformly replace all occurrences of a given predicate p(.) by a
 * formula in (.) and likewise for function symbols f(.) and program constants. Uniform substitutions and their
 * application mechanism for differential dynamic logic are implemented in [[org.keymaerax.core.USubst]]. See
 * [[org.keymaerax.Bibliography.JarPlatzer17 A complete uniform substitution calculus for differential dynamic logic]]
 * Section 3 and [[org.keymaerax.Bibliography.CadePlatzer19 Uniform substitution at one fell swoop]] one-pass Section 3.
 *
 * [[org.keymaerax.core.USubst Uniform substitutions]] can be used on proof certificates with the
 * [[org.keymaerax.core.Provable.apply(subst:edu\.cmu\.cs\.ls\.keymaerax\.core\.USubst):edu\.cmu\.cs\.ls\.keymaerax\.core\.Provable*]],
 * including uniform substitution instances of axioms or axiomatic rules. See
 * [[org.keymaerax.Bibliography.JarPlatzer17 A complete uniform substitution calculus for differential dynamic logic]]
 * Section 3.
 *
 * ===Sequent Proof Rules===
 * All proof rules for differential dynamic logic, including the uniform substitution and bound variable renaming rules
 * as well as efficient propositional sequent proof rules and Skolemization [[org.keymaerax.core.Skolemize]] are all of
 * type [[org.keymaerax.core.Rule]], which are the only proof rules that can ever be applied to a proof. See
 * [[org.keymaerax.Bibliography.JarPlatzer08 sequent calculus]].
 *
 * ==Additional Capabilities==
 * ===Stored Provable Mechanism===
 * A Stored Provable represents a Provable as a String that can be reloaded later as well as an interface to real
 * arithmetic decision procedures are defined in [[org.keymaerax.core.Provable.fromStorageString()]] and
 * [[org.keymaerax.core.QETool]].
 *
 * ===Error Reporting===
 * Errors from the prover core are reported as exceptions of type [[org.keymaerax.core.ProverException]] whose main
 * responsibility is to propagate problems in traceable ways to the user by augmenting them with contextual information.
 * The prover core throws exceptions of type [[org.keymaerax.core.CoreException]].
 *
 * ===Set Lattice===
 * A data structure for sets (or rather lattice completions of sets) is provided in [[org.keymaerax.core.SetLattice]]
 * based on Scala's immutable sets.
 *
 * ===Overall Code Complexity===
 * Overall, the majority of the KeYmaera X Prover Microkernel implementation consists of data structure declarations or
 * similar mostly self-evident code. This includes straightforward variable categorization in [[StaticSemantics]]. The
 * highest complexity is for the [[USubstOne uniform substitution application mechanism]]. The highest information
 * density is in the [[AxiomBase axiom list]].
 *
 * @author
 *   Andre Platzer
 * @see
 *   [[org.keymaerax.Bibliography.JarPlatzer17 A complete uniform substitution calculus for differential dynamic logic]]
 * @see
 *   [[org.keymaerax.Bibliography.CadePlatzer19 Uniform substitution at one fell swoop]]
 * @see
 *   [[org.keymaerax.Bibliography.JacmPlatzerT20 Differential equation invariance axiomatization]]
 * @see
 *   [[org.keymaerax.Bibliography.CadePlatzer15 A uniform substitution calculus for differential dynamic logic]]
 * @see
 *   [[org.keymaerax.Bibliography.CadePlatzer18 Uniform substitution for differential game logic]]
 * @see
 *   [[org.keymaerax.Bibliography.Platzer18 Logical Foundations of Cyber-Physical Systems]]
 * @see
 *   [[org.keymaerax.Bibliography.CadeFultonMQVP15 KeYmaera X: An aXiomatic tactical theorem prover for hybrid systems]]
 * @see
 *   [[org.keymaerax.Bibliography.ToclPlatzer15 Differential game logic]]
 * @see
 *   [[org.keymaerax.Bibliography.LicsPlatzer12a Logics of dynamical systems]]
 * @see
 *   [[org.keymaerax.Bibliography.LicsPlatzer12b]]
 * @see
 *   [[org.keymaerax.Bibliography.JarPlatzer08]]
 * @see
 *   [[org.keymaerax.core.Provable]]
 * @see
 *   [[org.keymaerax.core.Expression]]
 * @see
 *   [[org.keymaerax.core.StaticSemantics]]
 * @see
 *   [[org.keymaerax.core.USubstOne]]
 * @note
 *   Code Review 2020-02-17
 */
package object core {

  /** The encoding used for storing lemmas and other artifacts. */
  val ENCODING: String = "UTF-8"

  /** The uniform substitution type to use */
  type USubst = USubstOne

  /** USubst factory method, forwards to constructor. */
  def USubst(subsDefsInput: immutable.Seq[SubstitutionPair]): USubst = USubstOne(subsDefsInput)

  /** true if USubstChurch is used, false if USubstOne is used */
  private[core] val usubstChurch = USubst(immutable.Seq()).getClass.getSimpleName == "USubstChurch"

  /**
   * Insist on `requirement` being true, throwing a [[CoreException]] if false. This method is a `require` coming from
   * the prover core that cannot be disabled. Blame is on the caller of the method for violating the contract.
   *
   * @param requirement
   *   the expression to test for being true
   * @param message
   *   a String explaining what is expected.
   * @see
   *   [[scala.Predef.require()]]
   */
  @inline
  final def insist(requirement: Boolean, message: => Any): Unit = {
    if (!requirement) throw new CoreException("Core requirement failed: " + message)
  }

  /**
   * Check that the given expression `e` does not throw an exception.
   * @return
   *   - `true` if `e` completed without raising any exceptions or errors.
   *   - `false` if `e` raised an exception or error.
   * @example
   *   {{{
   *   insist(noException(complicatedComputation), "The complicated computation should complete without throwing exceptions")
   *   }}}
   */
  @inline
  final def noException[T](e: => T): Boolean =
    try { e; true }
    catch { case _: Throwable => false }

  /**
   * Java-style assertions, disabled by default, enabled with `java -ea`, disable with `java -da`. Scala-style elidable
   * at compile-time with `-Xdisable-assertions`
   *
   * Lazy evaluation of `condition` on `argument`, lazy evaluation of message.
   * @author
   *   Fabian Immler
   */
  @elidable(elidable.ASSERTION) @inline
  def assertion[A](condition: A => Boolean, argument: A, message: => Any): A = Assertion
    .assertion((x: A) => condition(x): java.lang.Boolean, argument, () => message.asInstanceOf[AnyRef])

  /** see [[assertion]] */
  @elidable(elidable.ASSERTION) @inline
  def assertion[A](condition: A => Boolean, argument: A): A = Assertion
    .assertion((x: A) => condition(x): java.lang.Boolean, argument)

  /** see [[assertion]] */
  @elidable(elidable.ASSERTION) @inline
  def assertion(condition: => Boolean): Unit = Assertion.assertion(() => condition)

  /** see [[assertion]] */
  @elidable(elidable.ASSERTION) @inline
  def assertion(condition: => Boolean, message: => Any): Unit = Assertion
    .assertion(() => condition: java.lang.Boolean, () => message.asInstanceOf[AnyRef])

  /**
   * Contracts (like [[scala.Predef.Ensuring]]) implemented with Java-style assertions (see [[assertion]])
   * @author
   *   Fabian Immler
   */
  implicit final class Ensures[A](private val self: A) extends AnyVal {

    /**
     * Java-style lazy-evaluation postcondition assertion that can be enabled with `java -ea`, disabled with `java -da`.
     */
    def ensures(cond: => Boolean): A = { assertion(cond); self }

    /**
     * Java-style lazy-evaluation postcondition assertion that can be enabled with `java -ea`, disabled with `java -da`.
     */
    def ensures(cond: => Boolean, msg: => Any): A = { assertion(cond, msg); self }

    /**
     * Java-style lazy-evaluation postcondition assertion that can be enabled with `java -ea`, disabled with `java -da`.
     */
    def ensures(cond: A => Boolean): A = { assertion(cond, self); self }

    /**
     * Java-style lazy-evaluation postcondition assertion that can be enabled with `java -ea`, disabled with `java -da`.
     */
    def ensures(cond: A => Boolean, msg: => Any): A = { assertion(cond, self, msg); self }

  }

}
