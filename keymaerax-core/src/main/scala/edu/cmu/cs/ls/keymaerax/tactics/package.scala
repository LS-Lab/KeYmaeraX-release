/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax

/**
 * Tactics framework providing base tactics, tactic combinators,
 * tactics execution and scheduling and continuations engine,
 * as well as presupplied proof search strategies.
 *
 * Main tactics are provided in [[edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary]]
 *
 * All tactics are implemented on top of [[edu.cmu.cs.ls.keymaerax.core.Provable]] proof certificates.
 * [[edu.cmu.cs.ls.keymaerax.tactics.ProofNode]] provide a useful data structure for the tactics to
 * manage the progress of the proof as well as its agenda and alternatives.
 * The Provables that tactics produce can be extracted with [[edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary.proveBy()]]
 *
 * =Proof Styles=
 * KeYmaera X supports many different proof styles, which can aso be mixed.
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
 * [[edu.cmu.cs.ls.keymaerax.core.Provable]] certificates in KeYmaera X.
 * Also see [[edu.cmu.cs.ls.keymaerax.core]].
 *
 * {{{
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
 * Explicit proofs construct similarly explicit proof steps, just with tactics:
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
 * `  x>5 |- !([x:=x+1; ++ x:=0;]x>=6) | x<2 `
 *
 * it is enough to point to the highlighted position
 *
 * `  x>5 |- !(__[x:=x+1; ++ x:=0;]x>=6__) | x<2 `
 *
 * and using the "[++] choice" axiom fact
 *
 * `  __[a;++b;]p(??)__ <-> [a;]p(??) & [b;]p(??) `
 *
 * to reduce the proof to a proof of
 *
 * `  x>5 |- !([x:=x+1;]x>6 & [x:=0;]x>=6) | x<2 `
 *
 * which is, in turn, easy to prove by pointing to the assignments using "[:=] assign" axioms
 * and ultimately asking propositional logic.
 *
 * Proof by pointing matches the highlighted position against the highlighted position
 * in the fact and does what it takes to use that knowledge.
 * There are multiple variations of proof by pointing in [[edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary.useAt]]
 * and [[edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary.by]]
 *
 * {{{
 * import TactixLibrary._
 * import DerivedAxioms._
 * // Proof by pointing of  |- <v:=g();>q(v) <-> q(g())
 * val proof = TactixLibrary.proveBy(
 *   Sequent(Nil, IndexedSeq(), IndexedSeq("<v:=g();>q(v) <-> q(g())".asFormula)),
 *   // use "<> dual" axiom backwards at the indicated position on
 *   // |- __<v:=g();>q(v)__ <-> q(g())
 *   useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 0::Nil)) &
 *   // use "[:=] assign" axiom forward at the indicated position on
 *   // |- !__[v:=g();]!q(v)__ <-> q(g())
 *   useAt("[:=] assign")(SuccPosition(0, 0::0::Nil)) &
 *   // use double negation at the indicated position on
 *   // |- __!!q(g())__ <-> q(g())
 *   useAt(doubleNegationAxiom)(SuccPosition(0, 0::Nil)) &
 *   // close by (an instance of) reflexivity |- p() <-> p()
 *   // |- q(g()) <-> q(g())
 *   byUS(equivReflexiveAxiom)
 * )
 * }}}
 *
 * [[edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary.step]] also uses proof by pointing
 * but figures out the appropriate fact to use on its own.
 *
 * {{{
 * import TactixLibrary._
 * // Proof by pointing of  |- <a;++b;>p(x) <-> (<a;>p(x) | <b;>p(x))
 * val proof = TactixLibrary.proveBy(
 *   Sequent(Nil, IndexedSeq(), IndexedSeq("<a;++b;>p(x) <-> (<a;>p(x) | <b;>p(x))".asFormula)),
 *   // use "<> dual" axiom backwards at the indicated position on
 *   // |- __<a;++b;>p(x)__  <->  <a;>p(x) | <b;>p(x)
 *   useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 0::Nil)) &
 *   // use "[++] choice" axiom forward at the indicated position on
 *   // |- !__[a;++b;]!p(x)__  <->  <a;>p(x) | <b;>p(x)
 *   useAt("[++] choice")(SuccPosition(0, 0::0::Nil)) &
 *   // use "<> dual" axiom forward at the indicated position on
 *   // |- !([a;]!p(x) & [b;]!p(x))  <->  __<a;>p(x)__ | <b;>p(x)
 *   useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 1::0::Nil)) &
 *   // use "<> dual" axiom forward at the indicated position on
 *   // |- !([a;]!p(x) & [b;]!p(x))  <->  ![a;]!p(x) | __<b;>p(x)__
 *   useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 1::1::Nil)) &
 *   // use propositional logic to show
 *   // |- !([a;]!p(x) & [b;]!p(x))  <->  ![a;]!p(x) | ![b;]!p(x)
 *   prop
 * )
 * }}}
 *
 * @todo Expand descriptions
 * @see [[edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary]]
 * @see [[edu.cmu.cs.ls.keymaerax.tacticsinterface]]
 */
package object tactics {}
