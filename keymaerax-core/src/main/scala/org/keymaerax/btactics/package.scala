/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax

/**
 * Tactic library in the [[org.keymaerax.bellerophon Bellerophon]] tactic language.
 *
 *   - `[[org.keymaerax.btactics.TactixLibrary]]` Main tactic library consisting of:
 *     - `[[org.keymaerax.btactics.HilbertCalculus HilbertCalculus]]` Hilbert Calculus for differential dynamic logic
 *     - `[[org.keymaerax.btactics.SequentCalculus SequentCalculus]]` Sequent Calculus for propositional and first-order
 *       logic
 *     - `[[org.keymaerax.btactics.HybridProgramCalculus HybridProgramCalculus]]` Hybrid Program Calculus for
 *       differential dynamic logic
 *     - `[[org.keymaerax.btactics.DifferentialEquationCalculus DifferentialEquationCalculus]]` Differential Equation
 *       Calculus for differential dynamic logic
 *     - `[[org.keymaerax.btactics.UnifyUSCalculus UnifyUSCalculus]]` Unification-based Uniform Substitution Calculus
 *
 *   - Tactic tools
 *     - [[org.keymaerax.btactics.AxIndex] AxIndex]: Axiom Indexing data structures for canonical proof strategies. - [[org.keymaerax.btactics.DerivationInfoRegistry DerivationInfo]]:
 *       Meta-information for derivation steps such as axioms for user interface etc.
 *
 * All tactics are implemented in the [[org.keymaerax.bellerophon Bellerophon tactic language]], including its dependent
 * tactics, which ultimately produce [[org.keymaerax.core.Provable]] proof certificates by the
 * [[org.keymaerax.bellerophon.Interpreter Bellerophon interpreter]]. The [[org.keymaerax.core.Provable Provables]] that
 * tactics produce can be extracted, for example, with [[org.keymaerax.btactics.TactixLibrary.proveBy()]].
 *
 * =Proof Styles=
 * KeYmaera X supports many different proof styles, including flexible combinations of the following styles:
 *
 *   1. [[org.keymaerax.core.Provable Explicit proof certificates]] directly program the proof rules from the core.
 *   1. [[org.keymaerax.btactics.TactixLibrary.andR Explicit proofs]] use tactics to describe a proof directly
 *      mentioning all or most proof steps.
 *   1. [[org.keymaerax.btactics.TactixLibrary.prop Proof by search]] relies mainly on proof search with occasional
 *      additional guidance.
 *   1. [[org.keymaerax.btactics.UnifyUSCalculus.useAt() Proof by pointing]] points out facts and where to use them.
 *   1. [[org.keymaerax.btactics.UnifyUSCalculus.CEat() Proof by congruence]] is based on equivalence or equality or
 *      implicational rewriting within a context.
 *   1. [[org.keymaerax.btactics.UnifyUSCalculus.chase() Proof by chase]] is based on chasing away operators at an
 *      indicated position.
 *
 * ===Explicit Proof Certificates===
 * The most explicit types of proofs can be constructed directly using the [[org.keymaerax.core.Provable]] certificates
 * in KeYmaera X's kernel without using any tactics. Also see [[org.keymaerax.core]].
 *
 * {{{
 *  import org.keymaerax.core._
 *  // explicit proof certificate construction of |- !!p() <-> p()
 *  val proof = (Provable.startProof(
 *    "!!p() <-> p()".asFormula)
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
 * Explicit proofs construct similarly explicit proof steps, just with explicit tactics from
 * [[org.keymaerax.btactics.TactixLibrary TactixLibrary]]: The only actual difference is the order of the branches,
 * which is fixed to be from left to right in [[org.keymaerax.bellerophon.BelleExpr.<() tactic branching]]. Tactics also
 * use more elegant signed integers to refer to antecedent positions (negative) or succedent positions (positive).
 * {{{
 * import TactixLibrary._
 * // Explicit proof tactic for |- !!p() <-> p()
 * val proof = TactixLibrary.proveBy("!!p() <-> p()".asFormula,
 *    equivR(1) & <(
 *      (notL(-1) &
 *        notR(2) &
 *        closeId)
 *      ,
 *      (notR(1) &
 *        notL(-2) &
 *        closeId)
 *      )
 *  )
 * }}}
 *
 * ===Proof by Search===
 * Proof by search primarily relies on proof search procedures to conduct a proof. That gives very short proofs but, of
 * course, they are not always entirely informative about how the proof worked. It is easiest to see in simple
 * situations where propositional logic proof search will find a proof but works well in more general situations, too.
 * {{{
 * import TactixLibrary._
 * // Proof by search of |- (p() & q()) & r() <-> p() & (q() & r())
 * val proof = TactixLibrary.proveBy("(p() & q()) & r() <-> p() & (q() & r())".asFormula,
 *    prop
 * )
 * }}}
 * Common tactics for proof by search include [[org.keymaerax.btactics.TactixLibrary.prop()]],
 * [[org.keymaerax.btactics.TactixLibrary.auto()]] and the like.
 *
 * ===Proof by Pointing===
 * Proof by pointing emphasizes the facts to use and is implicit about the details on how to use them exactly. Proof by
 * pointing works by pointing to a position in the sequent and using a given fact at that position. For example, for
 * proving
 *
 * ` __⟨v:=2*v+1;⟩v!=0__ <-> 2*v+1!=0 `
 *
 * it is enough to point to the highlighted position using the Ax.diamond axiom fact ` ![a;]!p(||) <-> __⟨a;⟩p(||)__ `
 * at the highlighted position to reduce the proof to a proof of
 *
 * ` !__[v:=2*v+1;]!(v!=0)__ <-> 2*v+1!=0 `
 *
 * which is, in turn, easy to prove by pointing to the highlighted position using the Ax.assignbAxiom axiom `
 * __[x:=t();]p(x)__ <-> p(t())` at the highlighted position to reduce the proof to
 *
 * ` __!!(2*v+1!=0)__ <-> 2*v+1!=0 `
 *
 * Finally, using double negation `__!!p()__ <-> p()` at the highlighted position yields the following
 *
 * ` __2*v+1!=0 <-> 2*v+1!=0__ `
 *
 * which easily proves by reflexivity `__p() <-> p()__`.
 *
 * Proof by pointing matches the highlighted position against the highlighted position in the fact and does what it
 * takes to use that knowledge. There are multiple variations of proof by pointing in
 * [[org.keymaerax.btactics.UnifyUSCalculus.useAt]] and [[org.keymaerax.btactics.UnifyUSCalculus.byUS]], which are also
 * imported into [[org.keymaerax.btactics.TactixLibrary]]. The above proof by pointing implements directly in KeYmaera
 * X:
 *
 * {{{
 * import TactixLibrary._
 * // Proof by pointing of  |- &lt;v:=2*v+1;&gt;v!=0 <-> 2*v+1!=0
 * val proof = TactixLibrary.proveBy("&lt;v:=2*v+1;&gt;q(v) <-> q(2*v+1)".asFormula,
 *   // use Ax.diamond axiom backwards at the indicated position on
 *   // |- __&lt;v:=2*v+1;&gt;q(v)__ <-> q(2*v+1)
 *   useExpansionAt(Ax.diamond)(1, 0::Nil) &
 *   // use Ax.assignbAxiom axiom forward at the indicated position on
 *   // |- !__[v:=2*v+1;]!q(v)__ <-> q(2*v+1)
 *   useAt(Ax.assignbAxiom(1, 0::0::Nil) &
 *   // use double negation at the indicated position on
 *   // |- __!!q(2*v+1)__ <-> q(2*v+1)
 *   useAt(Ax.doubleNegation)(1, 0::Nil) &
 *   // close by (an instance of) reflexivity |- p() <-> p()
 *   // |- q(2*v+1) <-> q(2*v+1)
 *   byUS(Ax.equivReflexive)
 * )
 * }}}
 * Another example is:
 * {{{
 * import TactixLibrary._
 * // Proof by pointing of  |- &lt;a;++b;&gt;p(x) <-> (&lt;a;&gt;p(x) | &lt;b;&gt;p(x))
 * val proof = TactixLibrary.proveBy("&lt;a;++b;&gt;p(x) <-> (&lt;a;&gt;p(x) | &lt;b;&gt;p(x))".asFormula,
 *   // use Ax.diamond axiom backwards at the indicated position on
 *   // |- __&lt;a;++b;&gt;p(x)__  <->  &lt;a;&gt;p(x) | &lt;b;&gt;p(x)
 *   useExpansionAt(Ax.diamond)(1, 0::Nil) &
 *   // use Ax.choiceb axiom forward at the indicated position on
 *   // |- !__[a;++b;]!p(x)__  <->  &lt;a;&gt;p(x) | &lt;b;&gt;p(x)
 *   useAt(Ax.choiceb)(1, 0::0::Nil) &
 *   // use Ax.diamond axiom forward at the indicated position on
 *   // |- !([a;]!p(x) & [b;]!p(x))  <->  __&lt;a;&gt;p(x)__ | &lt;b;&gt;p(x)
 *   useExpansionAt(Ax.diamond)(1, 1::0::Nil) &
 *   // use Ax.diamond axiom forward at the indicated position on
 *   // |- !([a;]!p(x) & [b;]!p(x))  <->  ![a;]!p(x) | __&lt;b;&gt;p(x)__
 *   useExpansionAt(Ax.diamond)(1, 1::1::Nil) &
 *   // use propositional logic to show
 *   // |- !([a;]!p(x) & [b;]!p(x))  <->  ![a;]!p(x) | ![b;]!p(x)
 *   prop
 * )
 * }}}
 * [[org.keymaerax.btactics.TactixLibrary.stepAt]] also uses proof by pointing but figures out the appropriate fact to
 * use on its own. Here's a similar proof:
 * {{{
 *  import TactixLibrary._
 *  // Proof by pointing with steps of  |- ⟨a++b⟩p(x) <-> (⟨a⟩p(x) | ⟨b⟩p(x))
 *  val proof = TactixLibrary.proveBy("<a;++b;>p(x) <-> (<a;>p(x) | <b;>p(x))".asFormula,
 *    // use Ax.diamond axiom backwards at the indicated position on
 *    // |- __⟨a++b⟩p(x)__  <->  ⟨a⟩p(x) | ⟨b⟩p(x)
 *    useExpansionAt(Ax.diamond)(1, 0::Nil) &
 *    // |- !__[a;++b;]!p(x)__  <->  ⟨a⟩p(x) | ⟨b⟩p(x)
 *    // step Ax.choiceb axiom forward at the indicated position
 *    stepAt(1, 0::0::Nil) &
 *    // |- __!([a;]!p(x) & [b;]!p(x))__  <-> ⟨a⟩p(x) | ⟨b⟩p(x)
 *    // step deMorgan forward at the indicated position
 *    stepAt(1, 0::Nil) &
 *    // |- __![a;]!p(x)__ | ![b;]!p(x)  <-> ⟨a⟩p(x) | ⟨b⟩p(x)
 *    // step Ax.diamond forward at the indicated position
 *    stepAt(1, 0::0::Nil) &
 *    // |- ⟨a⟩p(x) | __![b;]!p(x)__  <-> ⟨a⟩p(x) | ⟨b⟩p(x)
 *    // step Ax.diamond forward at the indicated position
 *    stepAt(1, 0::1::Nil) &
 *    // |- ⟨a⟩p(x) | ⟨b⟩p(x)  <-> ⟨a⟩p(x) | ⟨b⟩p(x)
 *    byUS(Ax.equivReflexive)
 *  )
 * }}}
 *
 * Likewise, for proving
 *
 * ` x>5 |- !([x:=x+1; ++ x:=0;]x>=6) | x<2 `
 *
 * it is enough to point to the highlighted position
 *
 * ` x>5 |- !(__[x:=x+1; ++ x:=0;]x>=6__) | x<2 `
 *
 * and using the Ax.choiceb axiom fact ` __[a;++b;]p(||)__ <-> [a;]p(||) & [b;]p(||) ` to reduce the proof to a proof of
 *
 * ` x>5 |- !([x:=x+1;]x>6 & [x:=0;]x>=6) | x<2 `
 *
 * which is, in turn, easy to prove by pointing to the assignments using Ax.assignbAxiom axioms and ultimately asking
 * propositional logic.
 *
 * More proofs by pointing are shown in [[org.keymaerax.btactics.Ax]] source code.
 *
 * ===Proof by Congruence===
 * [[org.keymaerax.btactics.UnifyUSCalculus.CEat() Proof by congruence]] is based on equivalence or equality or
 * implicational rewriting within a context. This proof style can make quite quick inferences leading to significant
 * progress using the CE, CQ, CT congruence proof rules or combinations thereof.
 * {{{
 *    import TactixLibrary._
 *    // |- x*(x+1)>=0 -> [y:=0;x:=__x^2+x__;]x>=y
 *    val proof = TactixLibrary.proveBy("x*(x+1)>=0 -> [y:=0;x:=x^2+x;]x>=y".asFormula,
 *      CEat(proveBy("x*(x+1)=x^2+x".asFormula, QE)) (1, 1::0::1::1::Nil) &
 *      // |- x*(x+1)>=0 -> [y:=0;x:=__x*(x+1)__;]x>=y by CE/CQ using x*(x+1)=x^2+x at the indicated position
 *      // step uses top-level operator [;]
 *      stepAt(1, 1::Nil) &
 *      // |- x*(x+1)>=0 -> [y:=0;][x:=x*(x+1);]x>=y
 *      // step uses top-level operator [:=]
 *      stepAt(1, 1::Nil) &
 *      // |- x*(x+1)>=0 -> [x:=x*(x+1);]x>=0
 *      // step uses top-level [:=]
 *      stepAt(1, 1::Nil) &
 *      // |- x*(x+1)>=0 -> x*(x+1)>=0
 *      prop
 *    )
 * }}}
 * Proof by congruence can also make use of a fact in multiple places at once by defining an appropriate context C:
 * {{{
 *   import TactixLibrary._
 *   val C = Context("x<5 & ⎵ -> [{x' = 5*x & ⎵}](⎵ & x>=1)".asFormula)
 *   // |- x<5 & __x^2<4__ -> [{x' = 5*x & __x^2<4__}](__x^2<4__ & x>=1)
 *   val proof = TactixLibrary.proveBy("x<5 & x^2<4 -> [{x' = 5*x & x^2<4}](x^2<4 & x>=1)".asFormula,
 *     CEat(proveBy("-2<x&x<2<->x^2<4".asFormula, QE), C) (1))
 *   )
 *   // |- x<5 & (__-2<x&x<2__) -> [{x' = 5*x & __-2<x&x<2__}]((__-2<x&x<2__) & x>=1) by CE
 *   println(proof.subgoals)
 * }}}
 *
 * ===Proof by Chase===
 * Proof by chase chases the expression at the indicated position forward until it is chased away or can't be chased
 * further without critical choices. The canonical examples use [[org.keymaerax.btactics.UnifyUSCalculus.chase()]] to
 * chase away differential forms:
 * {{{
 * import TactixLibrary._
 * val proof = TactixLibrary.proveBy("[{x'=22}](2*x+x*y>=5)'".asFormula,
 *  // chase the differential prime away in the postcondition
 *  chase(1, 1 :: Nil)
 *  // |- [{x'=22}]2*x'+(x'*y+x*y')>=0
 * )
 * // Remaining subgoals: |- [{x'=22}]2*x'+(x'*y+x*y')>=0
 * println(proof.subgoals)
 * }}}
 * {{{
 * import TactixLibrary._
 * val proof = TactixLibrary.proveBy("[{x'=22}](2*x+x*y>=5)' <-> [{x'=22}]2*x'+(x'*y+x*y')>=0".asFormula,
 *   // chase the differential prime away in the left postcondition
 *   chase(1, 0:: 1 :: Nil) &
 *   // |- [{x'=22}]2*x'+(x'*y+x*y')>=0 <-> [{x'=22}]2*x'+(x'*y+x*y')>=0
 *   byUS(Ax.equivReflexive)
 * )
 * }}}
 * Yet [[org.keymaerax.btactics.UnifyUSCalculus.chase()]] is also useful to chase away other operators, say, modalities:
 * {{{
 * import TactixLibrary._
 * // proof by chase of |- [?x>0;x:=x+1;x:=2*x; ++ ?x=0;x:=1;]x>=1
 * val proof = TactixLibrary.proveBy(
 *   "[?x>0;x:=x+1;x:=2*x; ++ ?x=0;x:=1;]x>=1".asFormula,
 *   // chase the box in the succedent away
 *   chase(1,Nil) &
 *   // |- (x>0->2*(x+1)>=1)&(x=0->1>=1)
 *   QE
 * )
 * }}}
 *
 * ==Additional Mechanisms==
 *
 *   - Tactic framework for Hilbert-style Forward Tactics: Tactics are functions `Provable=>Provable`
 *     - [[org.keymaerax.btactics.UnifyUSCalculus.ForwardTactic]]: Forward Hilbert-style tactics `Provable=>Provable`
 *     - [[org.keymaerax.btactics.UnifyUSCalculus.ForwardPositionTactic]]: Positional forward Hilbert-style tactics
 *       `Position=>(Provable=>Provable)`
 *     - [[org.keymaerax.btactics.UnifyUSCalculus]]: Forward Hilbert-style tactic combinators.
 *
 * @todo
 *   Expand descriptions
 * @see
 *   Andre Platzer.
 *   [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]].
 *   Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
 * @see
 *   [[org.keymaerax.btactics.TactixLibrary]]
 * @see
 *   [[org.keymaerax.btactics.HilbertCalculus]]
 * @see
 *   [[org.keymaerax.btactics.SequentCalculus]]
 * @see
 *   [[org.keymaerax.btactics.HybridProgramCalculus]]
 * @see
 *   [[org.keymaerax.btactics.DifferentialEquationCalculus]]
 * @see
 *   [[org.keymaerax.btactics.UnifyUSCalculus]]
 */
package object btactics {}
