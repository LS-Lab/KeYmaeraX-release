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
 *     1. [[edu.cmu.cs.ls.keymaerax.core.Provable Explicit proof certificates]] directly program the proof rules from the core.
 *
 *     2. [[edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary.orR Explicit proofs]] use tactics to describe a proof directly mentioning all or most proof steps.
 *
 *     3. [[edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary.prop Proof by search]] relies mainly on proof search with occasional additional guidance.
 *
 *     4. [[edu.cmu.cs.ls.keymaerax.tactics.UnifyUSCalculus.useAt() Proof by pointing]] points out facts and where to use them.
 *
 *     5. [[edu.cmu.cs.ls.keymaerax.tactics.UnifyUSCalculus.CE() Proof by congruence]] is based on equivalence or equality or implicational rewriting within a context.
 *
 *     6. [[edu.cmu.cs.ls.keymaerax.tactics.UnifyUSCalculus.chase() Proof by chase]] is based on chasing away operators at an indicated position.
 *
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
 *
 * ===Explicit Proofs===
 * Explicit proofs construct similarly explicit proof steps, just with explicit tactics from [[edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary TactixLibrary]]:
 * {{{
 * import TactixLibrary._
 * import BranchLabels._
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
 * Common tactics for proof by search include
 * [[edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary.prop()]],
 * [[edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary.master()]] and the like.
 *
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
 *   Sequent(Nil, IndexedSeq(), IndexedSeq("&lt;v:=2*v+1;&gt;q(v) <-> q(2*v+1)".asFormula)),
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
 * [[edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary.stepAt]] also uses proof by pointing
 * but figures out the appropriate fact to use on its own. Here's a similar proof:
 * {{{
 *  import TactixLibrary._
 *  // Proof by pointing with steps of  |- <a;++b;>p(x) <-> (<a;>p(x) | <b;>p(x))
 *  val proof = TactixLibrary.proveBy(
 *    Sequent(Nil, IndexedSeq(), IndexedSeq("<a;++b;>p(x) <-> (<a;>p(x) | <b;>p(x))".asFormula)),
 *    // use "<> dual" axiom backwards at the indicated position on
 *    // |- __<a;++b;>p(x)__  <->  <a;>p(x) | <b;>p(x)
 *    useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 0::Nil)) &
 *    // |- !__[a;++b;]!p(x)__  <->  <a;>p(x) | <b;>p(x)
 *    // step "[++] choice" axiom forward at the indicated position
 *    stepAt(SuccPosition(0, 0::0::Nil)) &
 *    // |- __!([a;]!p(x) & [b;]!p(x))__  <-> <a;>p(x) | <b;>p(x)
 *    // step deMorgan forward at the indicated position
 *    stepAt(SuccPosition(0, 0::Nil)) &
 *    // |- __![a;]!p(x)__ | ![b;]!p(x)  <-> <a;>p(x) | <b;>p(x)
 *    // step "<> dual" forward at the indicated position
 *    stepAt(SuccPosition(0, 0::0::Nil)) &
 *    // |- <a;>p(x) | __![b;]!p(x)__  <-> <a;>p(x) | <b;>p(x)
 *    // step "<> dual" forward at the indicated position
 *    stepAt(SuccPosition(0, 0::1::Nil)) &
 *    // |- <a;>p(x) | <b;>p(x)  <-> <a;>p(x) | <b;>p(x)
 *    byUS("<-> reflexive")
 *  )
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
 *
 * ===Proof by Congruence===
 * [[edu.cmu.cs.ls.keymaerax.tactics.UnifyUSCalculus.CE() Proof by congruence]] is based on
 * equivalence or equality or implicational rewriting within a context.
 * This proof style can make quite quick inferences leading to significant progress using
 * the CE, CQ, CT congruence proof rules or combinations thereof.
 * {{{
 *    import TactixLibrary._
 *    // |- x*(x+1)>=0 -> [y:=0;x:=__x^2+x__;]x>=y
 *    val proof = proveBy("x*(x+1)>=0 -> [y:=0;x:=x^2+x;]x>=y".asFormula,
 *      CE(proveBy("x*(x+1)=x^2+x".asFormula, QE)) (SuccPosition(0, 1::0::1::1::Nil)) &
 *      // |- x*(x+1)>=0 -> [y:=0;x:=__x*(x+1)__;]x>=y by CE/CQ using x*(x+1)=x^2+x at the indicated position
 *      // step uses top-level operator [;]
 *      stepAt(SuccPosition(0, 1::Nil)) &
 *      // |- x*(x+1)>=0 -> [y:=0;][x:=x*(x+1);]x>=y
 *      // step uses top-level operator [:=]
 *      stepAt(SuccPosition(0, 1::Nil)) &
 *      // |- x*(x+1)>=0 -> [x:=x*(x+1);]x>=0
 *      // step uses top-level [:=]
 *      stepAt(SuccPosition(0, 1::Nil)) &
 *      // |- x*(x+1)>=0 -> x*(x+1)>=0
 *      prop
 *    )
 * }}}
 * Proof by congruence can also make use of a fact in multiple places at once by defining an appropriate context C:
 * {{{
 *   import TactixLibrary._
 *   val C = Context("x<5 & ⎵ -> [{x' = 5*x & ⎵}](⎵ & x>=1)".asFormula)
 *   // |- x<5 & __x^2<4__ -> [{x' = 5*x & __x^2<4__}](__x^2<4__ & x>=1)
 *   val proof = proveBy("x<5 & x^2<4 -> [{x' = 5*x & x^2<4}](x^2<4 & x>=1)".asFormula,
 *     CE(proveBy("-2<x&x<2<->x^2<4".asFormula, QE), C) (SuccPosition(0)))
 *   )
 *   // |- x<5 & (__-2<x&x<2__) -> [{x' = 5*x & __-2<x&x<2__}]((__-2<x&x<2__) & x>=1) by CE
 *   println(proof.subgoals)
 * }}}
 *
 *
 * ===Proof by Chase===
 * Proof by chase chases the expression at the indicated position forward
 * until it is chased away or can't be chased further without critical choices.
 * The canonical examples use [[edu.cmu.cs.ls.keymaerax.tactics.UnifyUSCalculus.chase()]] to chase away differential forms:
 * {{{
 * import TactixLibrary._
 * val proof = proveBy("[{x'=22}](2*x+x*y>=5)'".asFormula,
 *  // chase the differential prime away in the postcondition
 *  chase(1, 1 :: Nil)
 *  // |- [{x'=22}]2*x'+(x'*y+x*y')>=0
 * )
 * // Remaining subgoals: |- [{x'=22}]2*x'+(x'*y+x*y')>=0
 * println(proof.subgoals)
 * }}}
 * {{{
 * import TactixLibrary._
 * val proof = proveBy("[{x'=22}](2*x+x*y>=5)' <-> [{x'=22}]2*x'+(x'*y+x*y')>=0".asFormula,
 *   // chase the differential prime away in the left postcondition
 *   chase(1, 0:: 1 :: Nil) &
 *   // |- [{x'=22}]2*x'+(x'*y+x*y')>=0 <-> [{x'=22}]2*x'+(x'*y+x*y')>=0
 *   byUS("<-> reflexive")
 * )
 * }}}
 * Yet [[edu.cmu.cs.ls.keymaerax.tactics.UnifyUSCalculus.chase()]] is also useful to chase away other operators, say, modalities:
 * {{{
 * import TactixLibrary._
 * // proof by chase of |- [?x>0;x:=x+1;x:=2*x; ++ ?x=0;x:=1;]x>=1
 * val proof = TactixLibrary.proveBy(
 *   Sequent(Nil, IndexedSeq(), IndexedSeq("[?x>0;x:=x+1;x:=2*x; ++ ?x=0;x:=1;]x>=1".asFormula)),
 *   // chase the box in the succedent away
 *   chase(1,Nil) &
 *   // |- (x>0->2*(x+1)>=1)&(x=0->1>=1)
 *   QE
 * )
 * }}}
 *
 * @todo Expand descriptions
 * @see [[edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary]]
 * @see [[edu.cmu.cs.ls.keymaerax.tactics.HilbertCalculus]]
 * @see [[edu.cmu.cs.ls.keymaerax.tactics.UnifyUSCalculus]]
 * @see [[TacticExamples]]
 */
package object tactics {}
