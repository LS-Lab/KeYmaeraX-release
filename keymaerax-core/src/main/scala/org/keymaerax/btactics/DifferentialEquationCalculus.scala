/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon._
import org.keymaerax.btactics.TacticFactory._
import org.keymaerax.btactics.macros.{DisplayLevelAll, DisplayLevelBrowse, Tactic}
import org.keymaerax.core._
import org.keymaerax.infrastruct.Position

import scala.collection.immutable._
import scala.reflect.runtime.universe

/**
 * Differential Equation Calculus for differential dynamic logic.
 * @author
 *   Andre Platzer
 * @author
 *   Stefan Mitsch
 * @see
 *   [[HilbertCalculus]]
 */
object DifferentialEquationCalculus extends TacticProvider with DifferentialEquationCalculus {

  /** @inheritdoc */
  override def getInfo: (Class[_], universe.Type) =
    (DifferentialEquationCalculus.getClass, universe.typeOf[DifferentialEquationCalculus.type])
}

/**
 * Differential Equation Calculus for differential dynamic logic. Basic axioms for differential equations are in
 * [[HilbertCalculus]].
 *
 * Provides the elementary derived proof rules for differential equations from Figure 11.20 and Figure 12.9 in: Andre
 * Platzer. [[https://doi.org/10.1007/978-3-319-63588-0 Logical Foundations of Cyber-Physical Systems]]. Springer, 2018.
 * @author
 *   Andre Platzer
 * @author
 *   Stefan Mitsch
 * @see
 *   Andre Platzer. [[https://doi.org/10.1007/978-3-319-63588-0 Logical Foundations of Cyber-Physical Systems]].
 *   Springer, 2018.
 * @see
 *   Andre Platzer.
 *   [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]].
 *   Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
 * @see
 *   Andre Platzer. [[https://doi.org/10.1109/LICS.2012.13 Logics of dynamical systems]]. ACM/IEEE Symposium on Logic in
 *   Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 13-24. IEEE 2012
 * @see
 *   Andre Platzer. [[https://doi.org/10.1109/LICS.2012.64 The complete proof theory of hybrid systems]]. ACM/IEEE
 *   Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012
 * @see
 *   [[org.keymaerax.core.AxiomBase]]
 * @see
 *   [[org.keymaerax.btactics.Ax]]
 * @see
 *   [[TactixLibrary]]
 * @todo
 *   \@Tactic only partially implemented so far
 */
trait DifferentialEquationCalculus {

  /**
   * ***************************************************************** Differential Equation Proof Rules
   */

  // differential equation elementary derived proof rules

  /**
   * diffSolve: solve a differential equation `[x'=f]p(x)` to `\forall t>=0 [x:=solution(t)]p(x)`. Similarly,
   * `[x'=f(x)&q(x)]p(x)` turns to `\forall t>=0 (\forall 0<=s<=t q(solution(s)) -> [x:=solution(t)]p(x))`.
   */
  @Tactic(
    name = "solve",
    displayName = Some("[']"),
    displayNameLong = Some("Solution"),
    displayLevel = DisplayLevelAll,
    displayPremises = "Γ |- ∀t≥0 (∀0≤s≤t q(x(s))→[x:=x(t)]p(x)), Δ",
    displayConclusion = "Γ |- [x'=f(x)&q(x)]p(x), Δ",
    displayContextPremises = "Γ |- C( ∀t≥0 (∀0≤s≤t q(x(s))→[x:=x(t)]p(x)) ), Δ",
    displayContextConclusion = "Γ |- C( [x'=f(x)&q(x)]p(x) ), Δ",
    revealInternalSteps = true,
  )
  lazy val solve: DependentPositionTactic = anon { (pos: Position) =>
    AxiomaticODESolver.axiomaticSolve(instEnd = false)(pos)
  }

  /**
   * diffSolve with evolution domain check at duration end: solve `[x'=f]p(x)` to `\forall t>=0 [x:=solution(t)]p(x)`.
   * Similarly, `[x'=f(x)&q(x)]p(x)` turns to `\forall t>=0 (q(solution(t)) -> [x:=solution(t)]p(x))`.
   */
  @Tactic(
    name = "solveEnd",
    displayNameLong = Some("Solution with q(x) true at end"),
    displayLevel = DisplayLevelBrowse,
    displayPremises = "Γ |- ∀t≥0 (q(x(t))→[x:=x(t)]p(x)), Δ",
    displayConclusion = "Γ |- [x'=f(x)&q(x)]p(x), Δ",
    revealInternalSteps = true,
  )
  lazy val solveEnd: DependentPositionTactic = anon { (pos: Position) =>
    AxiomaticODESolver.axiomaticSolve(instEnd = true)(pos)
  }

  /**
   * DW: Differential Weakening uses evolution domain constraint so `[{x'=f(x)&q(x)}]p(x)` reduces to `\forall x
   * (q(x)->p(x))`.
   * @note
   *   FV(post)/\BV(x'=f(x)) subseteq FV(q(x)) usually required to have a chance to succeed.
   * @see
   *   [[HilbertCalculus.DW]]
   */
  lazy val dW: DependentPositionTactic = DifferentialTactics.diffWeaken

  /**
   * Same as dW but preserves information about the initial conditions
   * @see
   *   [[dW]]
   */
  lazy val dWPlus: DependentPositionTactic = DifferentialTactics.diffWeakenPlus

  /**
   * DC: Differential Cut a new invariant, use old(x) to refer to initial values of variable x. Use special function
   * old(.) to introduce a discrete ghost for the starting value of a variable that can be used in the evolution domain
   * constraint.
   * {{{
   * Use:                      Show:
   * G |- [x'=f(x)&Q&R]P, D    G |- [x'=f(x)&Q]R, D
   * ---------------------------------------------- dC(R)
   * G |- [x'=f(x)&Q]P, D
   * }}}
   * Also works in context, e.g.:
   * {{{
   * Use:                         Show:
   * G |- A->[x'=f(x)&Q&R]P, D    G |- A->[x'=f(x)&Q]R, D
   * ---------------------------------------------- dC(R)
   * G |- A->[x'=f(x)&Q]P, D
   * }}}
   *
   * @example
   *   {{{
   *   x>0 |- [{x'=2&x>0}]x>=0     x>0 |- [{x'=2}]x>0
   *   -----------------------------------------------dC("x>0".asFormula)(1)
   *   x>0 |- [{x'=2}]x>=0
   *   }}}
   * @example
   *   {{{
   *   x>0, x_0=x |- [{x'=2&x>=x_0}]x>=0     x>0, x_0=x |- [{x'=2}]x>=x_0
   *   -------------------------------------------------------------------dC("x>=old(x)".asFormula)(1)
   *   x>0 |- [{x'=2}]x>=0
   *   }}}
   * @example
   *   {{{
   *   x>0, v>=0, x_0=x |- [{x'=v,v'=1&v>=0&x>=x_0}]x>=0
   *          x>0, v>=0 |- [{x'=v,v'=1}]v>=0
   *   x>0, v>=0, x_0=x |- [{x'=v,v'=1&v>=0}]x>=x_0
   *   --------------------------------------------------dC("v>=0".asFormula, "x>=old(x)".asFormula)(1)
   *          x>0, v>=0 |- [{x'=v,v'=1}]x>=0
   *   }}}
   * @param R
   *   the formula that will be cut into the differential equation (in that order if it is a list). The formulas are
   *   typically shown to be differential invariants subsequently. They can use old(x) and old(y) etc. to refer to the
   *   initial values of x and y, respectively.
   * @note
   *   dC is often needed when FV(post) depend on BV(ode) that are not in FV(constraint).
   * @see
   *   [[HilbertCalculus.DC]]
   */
  def dC(R: Formula): DependentPositionWithAppliedInputTactic = dC(List(R))
  @Tactic(
    name = "dC",
    displayNameLong = Some("Differential Cut"),
    displayPremises = "Γ |- [x'=f(x) & Q∧R]P, Δ ;; Γ |- [x'=f(x) & Q]R, Δ",
    displayConclusion = "Γ |- [x'=f(x) & Q]P, Δ",
    displayContextPremises = "Γ |- C( [x'=f(x) & Q∧R]P ), Δ ;; Γ |- C( [x'=f(x) & Q]R ), Δ",
    displayContextConclusion = "Γ |- C( [x'=f(x) & Q]P ), Δ",
    inputGenerator = Some("pegasusCandidates"),
    revealInternalSteps = true,
  )
  def dC(R: List[Formula]): DependentPositionWithAppliedInputTactic = inputanon { (pos: Position) =>
    DifferentialTactics.diffCut(R)(pos)
  }

  /**
   * dIRule: Differential Invariant proves a formula to be an invariant of a differential equation. (uses DI, DW, DE).
   *
   * {{{
   * G, q(x) |- p(x), D     q(x) |- [x':=f(x)]p'(x')    @note derive on (p(x))' already done
   * ---------------------------------------------- dIRule
   *      G |- [x'=f(x)&q(x)]p(x), D
   * }}}
   * @example
   *   {{{
   *   x>=5, true |- x>=5    true |- [{x':=2}]x'>=0
   *   --------------------------------------------dIRule(1)
   *   x>=5 |- [{x'=2}]x>=5
   *   }}}
   * @incontext
   * @see
   *   [[HilbertCalculus.DI]]
   */
  @Tactic(
    name = "dIRule",
    displayNameLong = Some("Differential Invariant"),
    displayLevel = DisplayLevelAll,
    displayPremises = "Γ, Q |- P, Δ ;; Q |- [x':=f(x)](P)'",
    displayConclusion = "Γ |- [x'=f(x) & Q]P, Δ",
    displayContextPremises = "Γ |- C( Q→P∧[x':=f(x)](P)' ), Δ",
    displayContextConclusion = "Γ |- C( [x'=f(x) & Q]P ), Δ",
    revealInternalSteps = true,
  )
  def dIRule: DependentPositionTactic = DifferentialTactics.diffInd(Symbol("diffInd"))

  /**
   * dIClose: Differential Invariant proves a formula to be an invariant of a differential equation closing with the
   * usual steps to prove it invariant. (uses DI, DW, DE, QE). Tries to close everything after diffInd rule (turning
   * free variables to constants)
   * {{{
   *      *
   * -------------------------- dIClose
   * G |- [x'=f(x)&q(x)]p(x), D
   * }}}
   * @example
   *   {{{
   *        *
   *   ---------------------dIClose(1)
   *   x>=5 |- [{x'=2}]x>=5
   *   }}}
   * @example
   *   {{{
   *   x>=5 |- [x:=x+1;](true -> x>=5&2>=0)
   *   -------------------------------------dIClose(1, 1::Nil)
   *   x>=5 |- [x:=x+1;][{x'=2}]x>=5
   *   }}}
   * @incontext
   * @see
   *   [[HilbertCalculus.DI]]
   */
  @Tactic(
    name = "dIClose",
    displayNameLong = Some("Differential Invariant Auto-Close"),
    displayLevel = DisplayLevelAll,
    displayPremises = "*",
    displayConclusion = "Γ |- [x'=f(x) & Q]P, Δ",
    displayContextPremises = "Γ |- C( Q→P∧∀x(P')<sub>x'↦f(x)</sub> ), Δ",
    displayContextConclusion = "Γ |- C( [x'=f(x) & Q]P ), Δ",
    revealInternalSteps = true,
  )
  def dIClose: DependentPositionTactic = DifferentialTactics.diffInd(Symbol("cex"))

  /**
   * dI: Differential Invariant proves a formula to be an invariant of a differential equation (with the usual steps to
   * prove it invariant). (uses DI, DW, DE, QE)
   *
   * @param auto
   *   One of 'none, 'diffInd, 'full. Whether or not to automatically close and use DE, DW.
   *   - 'full: tries to close everything after diffInd rule (turning free variables to constants)
   *     {{{
   *       *
   *     --------------------------
   *     G |- [x'=f(x)&q(x)]p(x), D
   *     }}}
   *   - 'none: behaves as using DI axiom per cheat sheet
   *     {{{
   *     G, q(x) |- p(x), D    G, q(x) |- [x'=f(x)&q(x)](p(x))', D
   *     ---------------------------------------------------------
   *                 G |- [x'=f(x)&q(x)]p(x), D
   *     }}}
   *   - 'diffInd: behaves as dI rule per cheat sheet
   *     {{{
   *     G, q(x) |- p(x), D     q(x) |- [x':=f(x)]p'(x')    @note derive on (p(x))' already done
   *     ----------------------------------------------
   *                 G |- [x'=f(x)&q(x)]p(x), D
   *     }}}
   * @example
   *   {{{
   *        *
   *   ---------------------diffInd('full)(1)
   *   x>=5 |- [{x'=2}]x>=5
   *   }}}
   * @example
   *   {{{
   *   x>=5, true |- x>=5    true |- [{x':=2}]x'>=0
   *   --------------------------------------------diffInd('diffInd)(1)
   *   x>=5 |- [{x'=2}]x>=5
   *   }}}
   * @example
   *   {{{
   *   x>=5, true |- x>=5    x>=5, true |- [{x'=2}](x>=5)'
   *   ---------------------------------------------------diffInd('none)(1)
   *   x>=5 |- [{x'=2}]x>=5
   *   }}}
   * @example
   *   {{{
   *   x>=5 |- [x:=x+1;](true -> x>=5&2>=0)
   *   -------------------------------------diffInd('full)(1, 1::Nil)
   *   x>=5 |- [x:=x+1;][{x'=2}]x>=5
   *   }}}
   * @example
   *   {{{
   *   proveBy("x^2>=2->[{x'=x^3}]x^2>=2".asFormula, implyR(1) &
   *     diffInd()(1) & QE
   *   )
   *   }}}
   * @incontext
   * @see
   *   [[HilbertCalculus.DI]]
   */
  def dI(auto: Symbol = Symbol("full")): DependentPositionTactic = DifferentialTactics.diffInd(auto)

  @Tactic(
    name = "dI",
    displayNameLong = Some("Differential Invariant"),
    displayLevel = DisplayLevelAll,
    displayPremises = "Γ, Q |- P, Δ ;; Q |- [x':=f(x)](P)'", // todo: how to indicate closed premise?
    displayConclusion = "Γ |- [x'=f(x) & Q]P, Δ",
    displayContextPremises = "Γ |- C( Q→P∧∀x(P')<sub>x'↦f(x)</sub> ), Δ",
    displayContextConclusion = "Γ |- C( [x'=f(x) & Q]P ), Δ",
    revealInternalSteps = true,
  )
  def dIX: DependentPositionTactic = DifferentialTactics.diffInd(Symbol("cex"))

  /**
   * dG(ghost,r): Differential Ghost add auxiliary differential equations with extra variables ghost of the form
   * y'=a*y+b and the postcondition replaced by r, if provided.
   * {{{
   * G |- \exists y [x'=f(x),y'=g(x,y)&q(x)]r(x,y), D
   * ----------------------------------------------------------  dG using p(x) <-> \exists y. r(x,y) by QE
   * G |- [x'=f(x)&q(x)]p(x), D
   * }}}
   *
   * @note
   *   Uses QE to prove p(x) <-> \exists y. r(x,y)
   * @param ghost
   *   the extra differential equation for an extra variable y to ghost in of the form y'=a*y+b or y'=a*y or y'=b or
   *   y'=a*y-b
   * @param r
   *   the optional equivalent new postcondition to prove that can mention y; keeps p(x) if omitted.
   * @example
   *   {{{
   *   proveBy("x>0->[{x'=-x}]x>0".asFormula, implyR(1) &
   *     dG("{y'=(1/2)*y}".asDifferentialProgram, Some("x*y^2=1".asFormula))(1) &
   *       diffInd()(1, 0::Nil) & QE
   *     )
   *   }}}
   *   with optional instantiation of initial y
   *   {{{
   *   proveBy("x>0->[{x'=-x}]x>0".asFormula, implyR(1) &
   *     dG("{y'=(1/2)*y}".asDifferentialProgram, Some("x*y^2=1".asFormula))(1) &
   *       existsR("1/x^(1/2)".asFormula)(1) & diffInd()(1) & QE
   *     )
   *   }}}
   */
  @Tactic(
    name = "dG",
    displayNameLong = Some("Differential Ghost"),
    displayPremises = "Γ |- ∃y [x'=f(x),E & Q]G, Δ ;; G |- P",
    displayConclusion = "Γ |- [x'=f(x) & Q]P, Δ",
    displayContextPremises = "Γ |- C( ∃y [x'=f(x),E & Q]G ), Δ",
    displayContextConclusion = "Γ |- C( [x'=f(x) & Q]P ), Δ",
    revealInternalSteps = true,
    inputs = "E[y,x,y']:expression;; G[y]:option[formula]",
  )
  def dG(E: Expression, G: Option[Formula]): DependentPositionWithAppliedInputTactic = inputanon { (pos: Position) =>
    E match {
      case Equal(l: DifferentialSymbol, r) => DifferentialTactics.dG(AtomicODE(l, r), G)(pos)
      case dp: DifferentialProgram => DifferentialTactics.dG(dp, G)(pos)
      case ODESystem(dp, _) => DifferentialTactics.dG(dp, G)(pos)
      case _ => throw new IllegalArgumentException("Expected a differential program y′=f(y), but got " + E.prettyString)
    }
  }

  @Tactic(
    name = "dGold",
    displayName = Some("dG"),
    displayNameLong = Some("Differential Ghost"),
    displayPremises = "Γ |- ∃y [{x'=f(x),y′=a(x)*y+b(x) & Q}]P, Δ",
    displayConclusion = "Γ |- [{x'=f(x) & Q}]P, Δ",
    inputs = "y[y]:variable;;a(x):term;;b(x):term;;P[y]:option[formula]",
  )
  def dGold(y: Variable, t1: Term, t2: Term, p: Option[Formula]): DependentPositionWithAppliedInputTactic =
    TactixLibrary.dG(AtomicODE(DifferentialSymbol(y), Plus(Times(t1, y), t2)), p)

  // more DI/DC/DG variants

  /**
   * DC+DI: Prove the given list of differential invariants in that order by DC+DI via [[dC]] followed by [[dI]]
   * Combines differential cut and differential induction. Use special function old(.) to introduce a ghost for the
   * starting value of a variable that can be used in the evolution domain constraint. Uses diffInd to prove that the
   * formulas are differential invariants. Fails if diffInd cannot prove invariants.
   *
   * @example
   *   {{{
   *   x>0 |- [{x'=2&x>0}]x>=0
   *   ------------------------diffInvariant("x>0".asFormula)(1)
   *   x>0 |- [{x'=2}]x>=0
   *   }}}
   * @example
   *   {{{
   *   x>0, x_0=x |- [{x'=2&x>x_0}]x>=0
   *   ---------------------------------diffInvariant("x>old(x)".asFormula)(1)
   *          x>0 |- [{x'=2}]x>=0
   *   }}}
   * @example
   *   {{{
   *   x>0, v>=0, x_0=x |- [{x'=v,v'=1 & v>=0&x>x_0}]x>=0
   *   ---------------------------------------------------diffInvariant("v>=0".asFormula, "x>old(x)".asFormula)(1)
   *          x>0, v>=0 |- [{x'=v,v'=1}]x>=0
   *   }}}
   * @param invariants
   *   The differential invariants to cut in as evolution domain constraint.
   * @see
   *   [[dC]]
   * @see
   *   [[dI]]
   */
  // NB: Annotate diffInvariant(Formula) rather than DifferentialTactics.diffInvariant(List[Formula]) for compatibility
  @Tactic(
    name = "diffInvariant",
    displayNameLong = Some("Differential Cut + Auto Differential Invariant"),
    displayPremises = "Γ |- [x'=f(x) & Q∧R]P, Δ",
    displayConclusion = "Γ |- [x'=f(x) & Q]P, Δ",
    inputs = "R:formula",
    revealInternalSteps = true,
  )
  def diffInvariant(invariant: Formula): DependentPositionWithAppliedInputTactic = inputanon { (pos: Position) =>
    DifferentialTactics.diffInvariant(List(invariant))(pos)
  }
  def diffInvariant(invariants: List[Formula]): DependentPositionWithAppliedInputTactic = DifferentialTactics
    .diffInvariant(invariants)

  /**
   * DIo: Open Differential Invariant proves an open formula to be an invariant of a differential equation (with the
   * usual steps to prove it invariant) openDiffInd: proves an inequality to be an invariant of a differential equation
   * (by DIo, DW, DE, QE) For strict inequalities, it uses open diff ind (<,>)
   *
   * @example
   *   {{{
   *        *
   *   ---------------------openDiffInd(1)
   *   x^2>5 |- [{x'=x^3+x^4}]x^2>5
   *   }}}
   * @example
   *   {{{
   *        *
   *   ---------------------openDiffInd(1)
   *   x^3>5 |- [{x'=x^3+x^4}]x^3>5
   *   }}}
   * @example
   *   {{{
   *   proveBy("x^2>9->[{x'=x^4}]x^2>9".asFormula, implyR(1) &
   *     openDiffInd()(1)
   *   )
   *   }}}
   */
  def openDiffInd: DependentPositionTactic = DifferentialTactics.openDiffInd

  /**
   * Refine top-level antecedent/succedent ODE domain constraint
   * {{{
   * G|- [x'=f(x)&R]P, D     G|- [x'=f(x)&Q]R, (D)?
   * ---------------------------------------------- dR
   * G|- [x'=f(x)&Q]P, D
   * }}}
   * @param formula
   *   the formula R to refine Q to
   * @param hide
   *   whether to keep the extra succedents (D) around (default true), which makes position management easier
   */
  def dR(formula: Formula, hide: Boolean = true): DependentPositionTactic = DifferentialTactics
    .diffRefine(formula, hide)

}