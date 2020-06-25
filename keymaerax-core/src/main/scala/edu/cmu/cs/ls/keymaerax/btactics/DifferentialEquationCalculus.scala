/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.Position
import edu.cmu.cs.ls.keymaerax.macros.Tactic
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._

import scala.collection.immutable._

/**
  * Differential Equation Calculus for differential dynamic logic.
  * @author Andre Platzer
  * @author Stefan Mitsch
  * @see [[HilbertCalculus]]
  */
object DifferentialEquationCalculus extends DifferentialEquationCalculus

/**
  * Differential Equation Calculus for differential dynamic logic.
  * Basic axioms for differential equations are in [[HilbertCalculus]].
  *
  * Provides the elementary derived proof rules for differential equations from Figure 11.20 and Figure 12.9 in:
  * Andre Platzer. [[https://doi.org/10.1007/978-3-319-63588-0 Logical Foundations of Cyber-Physical Systems]]. Springer, 2018.
  * @author Andre Platzer
  * @author Stefan Mitsch
  * @see Andre Platzer. [[https://doi.org/10.1007/978-3-319-63588-0 Logical Foundations of Cyber-Physical Systems]]. Springer, 2018.
  * @see Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
  * @see Andre Platzer. [[https://doi.org/10.1109/LICS.2012.13 Logics of dynamical systems]]. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 13-24. IEEE 2012
  * @see Andre Platzer. [[https://doi.org/10.1109/LICS.2012.64 The complete proof theory of hybrid systems]]. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012
  * @see [[edu.cmu.cs.ls.keymaerax.core.AxiomBase]]
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.Ax]]
  * @todo @Tactic only partially implemented so far
  */
trait DifferentialEquationCalculus {

  /*******************************************************************
    * Differential Equation Proof Rules
    *******************************************************************/

  // differential equation elementary derived proof rules

  /** diffSolve: solve a differential equation `[x'=f]p(x)` to `\forall t>=0 [x:=solution(t)]p(x)`.
    * Similarly, `[x'=f(x)&q(x)]p(x)` turns to `\forall t>=0 (\forall 0<=s<=t q(solution(s)) -> [x:=solution(t)]p(x))`. */
  @Tactic(premises = "Γ |- ∀t≥0 (∀0≤s≤t q(sol(s)) → [x:=sol(t)]p(x)), Δ",
    conclusion = "Γ |- [x'=f(x)&q(x)]p(x), Δ", revealInternalSteps = true)
  lazy val solve: DependentPositionTactic = anon {(pos:Position) => AxiomaticODESolver.axiomaticSolve(instEnd = false)(pos)}

  /** diffSolve with evolution domain check at duration end: solve `[x'=f]p(x)` to `\forall t>=0 [x:=solution(t)]p(x)`.
    * Similarly, `[x'=f(x)&q(x)]p(x)` turns to `\forall t>=0 (q(solution(t)) -> [x:=solution(t)]p(x))`. */
  @Tactic(premises = "Γ |- ∀t≥0 (q(sol(t)) → [x:=sol(t)]p(x)), Δ",
    conclusion = "Γ |- [x'=f(x)&q(x)]p(x), Δ", revealInternalSteps = true)
  lazy val solveEnd: DependentPositionTactic = anon {(pos:Position) => AxiomaticODESolver.axiomaticSolve(instEnd = true)(pos) }


  /** DW: Differential Weakening uses evolution domain constraint so `[{x'=f(x)&q(x)}]p(x)` reduces to `\forall x (q(x)->p(x))`.
    * @note FV(post)/\BV(x'=f(x)) subseteq FV(q(x)) usually required to have a chance to succeed.
    * @see [[HilbertCalculus.DW]] */
  lazy val dW         : DependentPositionTactic = DifferentialTactics.diffWeaken

  /** Same as dW but preserves information about the initial conditions
    * @see [[dW]] */
  lazy val dWPlus     : DependentPositionTactic = DifferentialTactics.diffWeakenPlus

  /** DC: Differential Cut a new invariant, use old(x) to refer to initial values of variable x.
    * Use special function old(.) to introduce a discrete ghost for the starting value of a variable that can be
    * used in the evolution domain constraint.
    *
    * @example {{{
    *         x>0 |- [{x'=2&x>0}]x>=0     x>0 |- [{x'=2}]x>0
    *         -----------------------------------------------diffCut("x>0".asFormula)(1)
    *         x>0 |- [{x'=2}]x>=0
    * }}}
    * @example {{{
    *         x>0, x_0=x |- [{x'=2&x>=x_0}]x>=0     x>0, x_0=x |- [{x'=2}]x>=x_0
    *         -------------------------------------------------------------------diffCut("x>=old(x)".asFormula)(1)
    *         x>0 |- [{x'=2}]x>=0
    * }}}
    * @example {{{
    *         x>0, v>=0, x_0=x |- [{x'=v,v'=1&v>=0&x>=x_0}]x>=0
    *                x>0, v>=0 |- [{x'=v,v'=1}]v>=0
    *         x>0, v>=0, x_0=x |- [{x'=v,v'=1&v>=0}]x>=x_0
    *         --------------------------------------------------diffCut("v>=0".asFormula, "x>=old(x)".asFormula)(1)
    *                x>0, v>=0 |- [{x'=v,v'=1}]x>=0
    * }}}
    * @param R the formula that will be cut into the differential equation (in that order if it is a list).
    *          The formulas are typically shown to be differential invariants subsequently.
    *          They can use old(x) and old(y) etc. to refer to the initial values of x and y, respectively.
    * @note diffCut is often needed when FV(post) depend on BV(ode) that are not in FV(constraint).
    * @see[[HilbertCalculus.DC]]
    */
  def dC(R: Formula)       : DependentPositionTactic = DifferentialTactics.diffCut(R)
  @Tactic("Differential Cut", conclusion = "&Gamma; |- [{x′=f(x) & Q}]P, &Delta;",
    premises = "&Gamma; |- [{x′=f(x) & Q}]R, &Delta; ;; &Gamma; |- [{x′=f(x) & (Q∧R)}]P, &Delta;",
    revealInternalSteps = true)
  def dC(R: List[Formula]) : DependentPositionTactic = DifferentialTactics.diffCut(R)

  /** dI: Differential Invariant proves a formula to be an invariant of a differential equation (with the usual steps to prove it invariant).
    * (uses DI, DW, DE, QE)
    *
    * @param auto One of 'none, 'diffInd, 'full. Whether or not to automatically close and use DE, DW.
    *             'full: tries to close everything after diffInd rule (turning free variables to constants)
    *                    {{{
    *                        *
    *                      --------------------------
    *                      G |- [x'=f(x)&q(x)]p(x), D
    *                    }}}
    *             'none: behaves as using DI axiom per cheat sheet
    *                    {{{
    *                      G, q(x) |- p(x), D    G, q(x) |- [x'=f(x)&q(x)](p(x))', D
    *                      ---------------------------------------------------------
    *                                  G |- [x'=f(x)&q(x)]p(x), D
    *                    }}}
    *             'diffInd: behaves as dI rule per cheat sheet
    *                    {{{
    *                      G, q(x) |- p(x), D     q(x) |- [x':=f(x)]p'(x')    @note derive on (p(x))' already done
    *                      ----------------------------------------------
    *                                  G |- [x'=f(x)&q(x)]p(x), D
    *                    }}}
    * @example {{{
    *         *
    *    ---------------------diffInd('full)(1)
    *    x>=5 |- [{x'=2}]x>=5
    * }}}
    * @example {{{
    *    x>=5, true |- x>=5    true |- [{x':=2}]x'>=0
    *    --------------------------------------------diffInd('diffInd)(1)
    *    x>=5 |- [{x'=2}]x>=5
    * }}}
    * @example {{{
    *    x>=5, true |- x>=5    x>=5, true |- [{x'=2}](x>=5)'
    *    ---------------------------------------------------diffInd('none)(1)
    *    x>=5 |- [{x'=2}]x>=5
    * }}}
    * @example {{{
    *    x>=5 |- [x:=x+1;](true -> x>=5&2>=0)
    *    -------------------------------------diffInd('full)(1, 1::Nil)
    *    x>=5 |- [x:=x+1;][{x'=2}]x>=5
    * }}}
    * @example
    * {{{
    * proveBy("x^2>=2->[{x'=x^3}]x^2>=2".asFormula, implyR(1) &
    *   diffInd()(1) & QE
    * )
    * }}}
    * @incontext
    * @see [[HilbertCalculus.DI]]
    */
  def dI(auto: Symbol = 'full): DependentPositionTactic = DifferentialTactics.diffInd(auto)
//@todo@Tactic(premises = "Γ,Q |- [x':=f(x)](P)', Δ ;; Γ, Q |- P, Δ",
//    conclusion = "Γ |- [x'=f(x)&Q]p(x), Δ", revealInternalSteps = true)
  //@todo 'auto or 'cex
//  val dI: DependentPositionTactic = DifferentialTactics.diffInd('full)

  /** dG(ghost,r): Differential Ghost add auxiliary differential equations with extra variables
    * ghost of the form y'=a*y+b and the postcondition replaced by r, if provided.
    * {{{
    * G |- \exists y [x'=f(x),y'=g(x,y)&q(x)]r(x,y), D
    * ----------------------------------------------------------  dG using p(x) <-> \exists y. r(x,y) by QE
    * G |- [x'=f(x)&q(x)]p(x), D
    * }}}
    *
    * @note Uses QE to prove p(x) <-> \exists y. r(x,y)
    * @param ghost the extra differential equation for an extra variable y to ghost in of the form
    *              y'=a*y+b or y'=a*y or y'=b or y'=a*y-b
    * @param r the optional equivalent new postcondition to prove that can mention y; keeps p(x) if omitted.
    * @example
    * {{{
    * proveBy("x>0->[{x'=-x}]x>0".asFormula, implyR(1) &
    *   dG("{y'=(1/2)*y}".asDifferentialProgram, Some("x*y^2=1".asFormula))(1) &
    *     diffInd()(1, 0::Nil) & QE
    *   )
    * }}}
    * with optional instantiation of initial y
    * {{{
    * proveBy("x>0->[{x'=-x}]x>0".asFormula, implyR(1) &
    *   dG("{y'=(1/2)*y}".asDifferentialProgram, Some("x*y^2=1".asFormula))(1) &
    *     existsR("1/x^(1/2)".asFormula)(1) & diffInd()(1) & QE
    *   )
    * }}}
    * @see [[HilbertCalculus.DG]]
    */
//  @Tactic(premises = "Γ |- ∃y [x'=f(x),E&Q]P, Δ",
//    conclusion = "Γ |- [x'=f(x)&Q]P, Δ", revealInternalSteps = true, inputs = "E:differentialprogram")
  def dG(ghost: DifferentialProgram, r: Option[Formula]): DependentPositionTactic =
  anon {(pos:Position) => DifferentialTactics.dG(ghost, r)(pos)}


  // more DI/DC/DG variants


  /** DC+DI: Prove the given list of differential invariants in that order by DC+DI via [[dC]] followed by [[dI]]
    * Combines differential cut and differential induction. Use special function old(.) to introduce a ghost for the
    * starting value of a variable that can be used in the evolution domain constraint. Uses diffInd to prove that the
    * formulas are differential invariants. Fails if diffInd cannot prove invariants.
    *
    * @example {{{
    *         x>0 |- [{x'=2&x>0}]x>=0
    *         ------------------------diffInvariant("x>0".asFormula)(1)
    *         x>0 |- [{x'=2}]x>=0
    * }}}
    * @example {{{
    *         x>0, x_0=x |- [{x'=2&x>x_0}]x>=0
    *         ---------------------------------diffInvariant("x>old(x)".asFormula)(1)
    *                x>0 |- [{x'=2}]x>=0
    * }}}
    * @example {{{
    *         x>0, v>=0, x_0=x |- [{x'=v,v'=1 & v>=0&x>x_0}]x>=0
    *         ---------------------------------------------------diffInvariant("v>=0".asFormula, "x>old(x)".asFormula)(1)
    *                x>0, v>=0 |- [{x'=v,v'=1}]x>=0
    * }}}
    * @param invariants The differential invariants to cut in as evolution domain constraint.
    * @see [[dC]]
    * @see [[dI]]
    */
  def diffInvariant(invariants: Formula): DependentPositionTactic = DifferentialTactics.diffInvariant(List(invariants))
  def diffInvariant(invariants: List[Formula]): DependentPositionTactic = DifferentialTactics.diffInvariant(invariants)

  /** DIo: Open Differential Invariant proves an open formula to be an invariant of a differential equation (with the usual steps to prove it invariant)
    * openDiffInd: proves an inequality to be an invariant of a differential equation (by DIo, DW, DE, QE)
    *           For strict inequalities, it uses open diff ind (<,>)
    *
    * @example {{{
    *         *
    *    ---------------------openDiffInd(1)
    *    x^2>5 |- [{x'=x^3+x^4}]x^2>5
    * }}}
    * @example {{{
    *         *
    *    ---------------------openDiffInd(1)
    *    x^3>5 |- [{x'=x^3+x^4}]x^3>5
    * }}}
    * @example
    * {{{
    * proveBy("x^2>9->[{x'=x^4}]x^2>9".asFormula, implyR(1) &
    *   openDiffInd()(1)
    * )
    * }}}
    */
  def openDiffInd: DependentPositionTactic = DifferentialTactics.openDiffInd

  /** DV: Differential Variant proves a formula to become true at some point after a differential equation.
    *
    * @example {{{
    *         *
    *    ------------------------- DV(1)
    *    a()>0 |- <{x'=a()}>x>=b()
    * }}}
    */
  @deprecated
  def diffVar: DependentPositionTactic = DifferentialTactics.diffVar

  /** Refine top-level antecedent/succedent ODE domain constraint
    * G|- [x'=f(x)&R]P, D     G|- [x'=f(x)&Q]R, (D)?
    * ---------------------------------------------- dR
    * G|- [x'=f(x)&Q]P, D
    * @param formula the formula R to refine Q to
    * @param hide whether to keep the extra succedents (D) around (default true), which makes position management easier
    */
  def dR(formula: Formula, hide: Boolean=true): DependentPositionTactic = DifferentialTactics.diffRefine(formula,hide)

}
