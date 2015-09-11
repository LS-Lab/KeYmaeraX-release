/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax

import edu.cmu.cs.ls.keymaerax.tactics.Tactics

/**
 * Tactics framework providing base tactics, tactic combinators,
 * tactics execution and scheduling and continuations engine,
 * as well as presupplied proof search strategies.
 *                                    [[edu.cmu.cs.ls.keymaera.type ]]
 * The KeYmaera X Tactic provides
 *
 *   - Tactic library
 *     - [[edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary]]: Main tactic library
 *     - [[edu.cmu.cs.ls.keymaerax.tactics.HilbertCalculus]]: Hilbert Calculus for differential dynamic logic
 *     - [[edu.cmu.cs.ls.keymaerax.tactics.UnifyUSCalculus]]: Unification-based Uniform Substitution Calculus.
 *     - [[edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary]]: Additional tactic library
 *     - [[edu.cmu.cs.ls.keymaerax.tactics.DerivedAxioms]]: Derived Axioms proved from the base axioms from the core [[edu.cmu.cs.ls.keymaerax.core.Axiom]]
 *     - Many other singleton objects define additional tactics.
 *   - Tactic framework for [[edu.cmu.cs.ls.keymaerax.tactics.Tactics Scheduled Tactics]]
 *     - [[edu.cmu.cs.ls.keymaerax.tactics.Tactics.Tactic]]: Base type for scheduled tactics with tactic combinators.
 *     - [[edu.cmu.cs.ls.keymaerax.tactics.Tactics.KeYmaeraScheduler]]: Tactic scheduler starting and managing scheduled tactics.
 *     - [[edu.cmu.cs.ls.keymaerax.tactics.ProofNode]]: Proof search data structure for scheduled tactics.
 *   - Tactic framework for Hilbert-style Forward Tactics: Tactics are functions `Provable=>Provable`
 *     - [[edu.cmu.cs.ls.keymaerax.tactics.UnifyUSCalculus.ForwardTactic]]: Forward Hilbert-style tactics `Provable=>Provable`
 *     - [[edu.cmu.cs.ls.keymaerax.tactics.UnifyUSCalculus.ForwardPositionTactic]]: Positional forward Hilbert-style tactics `Position=>(Provable=>Provable)`
 *     - [[edu.cmu.cs.ls.keymaerax.tactics.UnifyUSCalculus]]: Forward Hilbert-style tactic combinators.
 *   - Tactic tools
 *     - [[edu.cmu.cs.ls.keymaerax.tactics.Position]]: Tactic positioning types.
 *     - [[edu.cmu.cs.ls.keymaerax.tactics.UnificationMatch]]: Unification matchers.
 *     - [[edu.cmu.cs.ls.keymaerax.tactics.RenUSubst]]: Renaming uniform substitutions, combining uniform renaming with uniform substitution.
 *     - [[edu.cmu.cs.ls.keymaerax.tactics.Augmentors]]: Implicit convenience additions of helper functions to formulas, terms, programs, sequents.
 *     - [[edu.cmu.cs.ls.keymaerax.tactics.Context]]: Convenience representation of formulas used as contexts that provide ways of substituting expressions in.
 *
 * All tactics are implemented on top of [[edu.cmu.cs.ls.keymaerax.core.Provable]] proof certificates.
 * [[edu.cmu.cs.ls.keymaerax.tactics.ProofNode]] provide a useful data structure for the tactics to
 * manage the progress of the proof as well as its agenda and alternatives.
 * The Provables that tactics produce can be extracted with [[edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary.proveBy()]]
 *
 * =Proof Styles=
 * KeYmaera X supports many different proof styles, including combinations of the following styles:
 *
 * 1. Explicit proof certificates directly program the proof rules from the core.
 *
 * 2. Explicit proofs use tactics to describe a proof directly mentioning all or most proof steps.
 *
 * 3. Proof by search relies mainly on proof search with occasional additional guidance.
 *
 * 4. Proof by pointing points out facts and where to use them.
 *
 * ===Explicit Proof Certificates===
 * The most explicit types of proofs can be constructed directly using the
 * [[edu.cmu.cs.ls.keymaerax.core.Provable]] certificates in KeYmaera X's kernel.
 * Also see [[edu.cmu.cs.ls.keymaerax.core]].
 *
 * {{{
 *  import edu.cmu.cs.ls.keymaerax.core._
 *  // explicit proof certificate construction of |- !!p() <-> p()
 *  val proof = (Provable.startProof(
 *    Sequent(Nil, IndexedSeq(), IndexedSeq("!!p() <-> p()".asFormula)))
 *    (EquivRight(SuccPos(0)), 0)
 *    // right branch
 *      (NotRight(SuccPos(0)), 1)
 *      (NotLeft(AntePos(1)), 1)
 *      (Close(AntePos(0),SuccPos(0)), 1)
 *    // left branch
 *      (NotLeft(AntePos(0)), 0)
 *      (NotRight(SuccPos(1)), 0)
 *      (Close(AntePos(0),SuccPos(0)), 0)
 *  )
 * }}}
 *
 * ===Explicit Proofs===
 * Explicit proofs construct similarly explicit proof steps, just with explicit tactics from [[edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary TactixLibrary]]:
 * {{{
 * import TactixLibrary._
 * // Explicit proof tactic for |- !!p() <-> p()
 * val proof = TactixLibrary.proveBy(
 *    Sequent(Nil, IndexedSeq(), IndexedSeq("!!p() <-> p()".asFormula)),
 *    equivR(SuccPos(0)) & onBranch(
 *      (equivRightLbl,
 *        notR(SuccPos(0)) &
 *        notL(AntePos(1)) &
 *        closeId),
 *      (equivLeftLbl,
 *        notL(AntePos(0)) &
 *        notR(SuccPos(1)) &
 *        closeId)
 *    )
 * )
 * }}}
 *
 * ===Proof by Search===
 * Proof by search primarily relies on proof search procedures to conduct a proof.
 * That gives very short proofs but, of course, they are not always entirely informative about how the proof worked.
 * It is easiest to see in simple situations where propositional logic proof search will find a proof
 * but works well in more general situations, too.
 * {{{
 * import TactixLibrary._
 * // Proof by search of |- (p() & q()) & r() <-> p() & (q() & r())
 * val proof = TactixLibrary.proveBy(
 *    Sequent(Nil, IndexedSeq(), IndexedSeq("(p() & q()) & r() <-> p() & (q() & r())".asFormula)),
 *    prop
 * )
 * }}}
 *
 * ===Proof by Pointing===
 * Proof by pointing emphasizes the facts to use and is implicit about the details on how to use them exactly.
 * Proof by pointing works by pointing to a position in the sequent and using a given fact at that position.
 * For example, for proving
 *
 * `   __<v:=2*v+1;>v!=0__ <-> 2*v+1!=0 `
 *
 * it is enough to point to the highlighted position
 * using the "<> dual" axiom fact
 * `  ![a;]!p(??) <-> __<a;>p(??)__ `
 * at the highlighted position to reduce the proof to a proof of
 *
 * `  !__[v:=2*v+1;]!(v!=0)__ <-> 2*v+1!=0 `
 *
 * which is, in turn, easy to prove by pointing to the highlighted position using the "[:=] assign" axiom
 * `  __[x:=t();]p(x)__ <-> p(t())`
 * at the highlighted position to reduce the proof to
 *
 * `  __!!(2*v+1!=0)__ <-> 2*v+1!=0 `
 *
 * Finally, using double negation `__!!p()__ <-> p()` at the highlighted position yields the following
 *
 * `  __2*v+1!=0 <-> 2*v+1!=0__ `
 *
 * which easily proves by reflexivity `__p() <-> p()__`.
 *
 * Proof by pointing matches the highlighted position against the highlighted position
 * in the fact and does what it takes to use that knowledge.
 * There are multiple variations of proof by pointing in [[edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary.useAt]]
 * and [[edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary.byUS]].
 * The above proof by pointing implements directly in KeYmaera X:
 *
 * {{{
 * import TactixLibrary._
 * import DerivedAxioms._
 * // Proof by pointing of  |- &lt;v:=2*v+1;&gt;v!=0 <-> 2*v+1!=0
 * val proof = TactixLibrary.proveBy(
 *   Sequent(Nil, IndexedSeq(), IndexedSeq("&lt;v:=2*v+1;&gtlq(v) <-> q(2*v+1)".asFormula)),
 *   // use "<> dual" axiom backwards at the indicated position on
 *   // |- __&lt;v:=2*v+1;&gt;q(v)__ <-> q(2*v+1)
 *   useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 0::Nil)) &
 *   // use "[:=] assign" axiom forward at the indicated position on
 *   // |- !__[v:=2*v+1;]!q(v)__ <-> q(2*v+1)
 *   useAt("[:=] assign")(SuccPosition(0, 0::0::Nil)) &
 *   // use double negation at the indicated position on
 *   // |- __!!q(2*v+1)__ <-> q(2*v+1)
 *   useAt(doubleNegationAxiom)(SuccPosition(0, 0::Nil)) &
 *   // close by (an instance of) reflexivity |- p() <-> p()
 *   // |- q(2*v+1) <-> q(2*v+1)
 *   byUS(equivReflexiveAxiom)
 * )
 * }}}
 *
 * [[edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary.stepAt]] also uses proof by pointing
 * but figures out the appropriate fact to use on its own.
 *
 * {{{
 * import TactixLibrary._
 * // Proof by pointing of  |- &lt;a;++b;&gt;p(x) <-> (&lt;a;&gt;p(x) | &lt;b;&gt;p(x))
 * val proof = TactixLibrary.proveBy(
 *   Sequent(Nil, IndexedSeq(), IndexedSeq("&lt;a;++b;&gt;p(x) <-> (&lt;a;&gt;p(x) | &lt;b;&gt;p(x))".asFormula)),
 *   // use "<> dual" axiom backwards at the indicated position on
 *   // |- __&lt;a;++b;&gt;p(x)__  <->  &lt;a;&gt;p(x) | &lt;b;&gt;p(x)
 *   useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 0::Nil)) &
 *   // use "[++] choice" axiom forward at the indicated position on
 *   // |- !__[a;++b;]!p(x)__  <->  &lt;a;&gt;p(x) | &lt;b;&gt;p(x)
 *   useAt("[++] choice")(SuccPosition(0, 0::0::Nil)) &
 *   // use "<> dual" axiom forward at the indicated position on
 *   // |- !([a;]!p(x) & [b;]!p(x))  <->  __&lt;a;&gt;p(x)__ | &lt;b;&gt;p(x)
 *   useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 1::0::Nil)) &
 *   // use "<> dual" axiom forward at the indicated position on
 *   // |- !([a;]!p(x) & [b;]!p(x))  <->  ![a;]!p(x) | __&lt;b;&gt;p(x)__
 *   useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 1::1::Nil)) &
 *   // use propositional logic to show
 *   // |- !([a;]!p(x) & [b;]!p(x))  <->  ![a;]!p(x) | ![b;]!p(x)
 *   prop
 * )
 * }}}
 *
 * Likewise, for proving
 *
 * `  x>5 |- !([x:=x+1; ++ x:=0;]x>=6) | x<2 `
 *
 * it is enough to point to the highlighted position
 *
 * `  x>5 |- !(__[x:=x+1; ++ x:=0;]x>=6__) | x<2 `
 *
 * and using the "[++] choice" axiom fact
 * `  __[a;++b;]p(??)__ <-> [a;]p(??) & [b;]p(??) `
 * to reduce the proof to a proof of
 *
 * `  x>5 |- !([x:=x+1;]x>6 & [x:=0;]x>=6) | x<2 `
 *
 * which is, in turn, easy to prove by pointing to the assignments using "[:=] assign" axioms
 * and ultimately asking propositional logic.
 *
 * More proofs by pointing are in [[edu.cmu.cs.ls.keymaerax.tactics.DerivedAxioms]]
 *
 * @todo Expand descriptions
 * @see [[edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary]]
 * @see [[edu.cmu.cs.ls.keymaerax.tacticsinterface]]
 */
package object tactics {}
