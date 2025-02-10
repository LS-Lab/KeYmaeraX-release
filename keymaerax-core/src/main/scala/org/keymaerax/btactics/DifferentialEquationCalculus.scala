/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon.*
import org.keymaerax.btactics.TacticFactory.*
import org.keymaerax.btactics.macros.{
  DisplayLevel,
  ExpressionArg,
  FormulaArg,
  InputPositionTacticInfo,
  ListArg,
  OptionArg,
  PositionTacticInfo,
  TacticConstructor0,
  TacticConstructor1,
  TacticConstructor2,
  TacticConstructor4,
  TermArg,
  VariableArg,
}
import org.keymaerax.core.*
import org.keymaerax.core.btactics.annotations.Derivation
import org.keymaerax.infrastruct.Position

import scala.collection.immutable.*

/**
 * Differential Equation Calculus for differential dynamic logic. Basic axioms for differential equations are in
 * [[HilbertCalculus]].
 *
 * Provides the elementary derived proof rules for differential equations from Figure 11.20 and Figure 12.9 in
 * [[org.keymaerax.Bibliography.Platzer18]].
 *
 * @author
 *   Andre Platzer
 * @author
 *   Stefan Mitsch
 * @see
 *   [[org.keymaerax.Bibliography.Platzer18]]
 * @see
 *   [[org.keymaerax.Bibliography.JarPlatzer17]]
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
object DifferentialEquationCalculus {

  /**
   * ***************************************************************** Differential Equation Proof Rules
   */

  // differential equation elementary derived proof rules

  /**
   * diffSolve: solve a differential equation `[x'=f]p(x)` to `\forall t>=0 [x:=solution(t)]p(x)`. Similarly,
   * `[x'=f(x)&q(x)]p(x)` turns to `\forall t>=0 (\forall 0<=s<=t q(solution(s)) -> [x:=solution(t)]p(x))`.
   */
  lazy val solve: DependentPositionTactic = "solve".by { (pos: Position) =>
    AxiomaticODESolver.axiomaticSolve(instEnd = false)(pos)
  }

  @Derivation
  val solveInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "solve",
    displayName = Some("[']"),
    displayNameLong = Some("Solution"),
    displayLevel = DisplayLevel.All,
    displayPremises = "Γ |- ∀t≥0 (∀0≤s≤t q(x(s))→[x:=x(t)]p(x)), Δ",
    displayConclusion = "Γ |- [x'=f(x)&q(x)]p(x), Δ",
    displayContextPremises = "Γ |- C( ∀t≥0 (∀0≤s≤t q(x(s))→[x:=x(t)]p(x)) ), Δ",
    displayContextConclusion = "Γ |- C( [x'=f(x)&q(x)]p(x) ), Δ",
    revealInternalSteps = true,
    constructor = TacticConstructor0.create()(() => solve),
  )

  /**
   * diffSolve with evolution domain check at duration end: solve `[x'=f]p(x)` to `\forall t>=0 [x:=solution(t)]p(x)`.
   * Similarly, `[x'=f(x)&q(x)]p(x)` turns to `\forall t>=0 (q(solution(t)) -> [x:=solution(t)]p(x))`.
   */
  lazy val solveEnd: DependentPositionTactic = "solveEnd".by { (pos: Position) =>
    AxiomaticODESolver.axiomaticSolve(instEnd = true)(pos)
  }

  @Derivation
  val solveEndInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "solveEnd",
    displayNameLong = Some("Solution with q(x) true at end"),
    displayLevel = DisplayLevel.Browse,
    displayPremises = "Γ |- ∀t≥0 (q(x(t))→[x:=x(t)]p(x)), Δ",
    displayConclusion = "Γ |- [x'=f(x)&q(x)]p(x), Δ",
    revealInternalSteps = true,
    constructor = TacticConstructor0.create()(() => solveEnd),
  )

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

  def dC(R: List[Formula]): DependentPositionWithAppliedInputTactic = "dC"
    .byWithInputs(List(R), (pos: Position) => DifferentialTactics.diffCut(R)(pos))

  @Derivation
  val dCInfo: InputPositionTacticInfo = InputPositionTacticInfo.create(
    name = "dC",
    displayNameLong = Some("Differential Cut"),
    displayPremises = "Γ |- [x'=f(x) & Q∧R]P, Δ ;; Γ |- [x'=f(x) & Q]R, Δ",
    displayConclusion = "Γ |- [x'=f(x) & Q]P, Δ",
    displayContextPremises = "Γ |- C( [x'=f(x) & Q∧R]P ), Δ ;; Γ |- C( [x'=f(x) & Q]R ), Δ",
    displayContextConclusion = "Γ |- C( [x'=f(x) & Q]P ), Δ",
    revealInternalSteps = true,
    inputGenerator = Some("pegasusCandidates"),
    constructor = TacticConstructor1.create(ListArg(FormulaArg("R")))((R: List[Formula]) => dC(R)),
  )

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
  def dIRule: DependentPositionTactic = "dIRule".forward(DifferentialTactics.diffInd(Symbol("diffInd")))

  @Derivation
  val dIRuleInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "dIRule",
    displayNameLong = Some("Differential Invariant"),
    displayLevel = DisplayLevel.All,
    displayPremises = "Γ, Q |- P, Δ ;; Q |- [x':=f(x)](P)'",
    displayConclusion = "Γ |- [x'=f(x) & Q]P, Δ",
    displayContextPremises = "Γ |- C( Q→P∧[x':=f(x)](P)' ), Δ",
    displayContextConclusion = "Γ |- C( [x'=f(x) & Q]P ), Δ",
    revealInternalSteps = true,
    constructor = TacticConstructor0.create()(() => dIRule),
  )

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
  def dIClose: DependentPositionTactic = "dIClose".forward(DifferentialTactics.diffInd(Symbol("cex")))

  @Derivation
  val dICloseInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "dIClose",
    displayNameLong = Some("Differential Invariant Auto-Close"),
    displayLevel = DisplayLevel.All,
    displayPremises = "*",
    displayConclusion = "Γ |- [x'=f(x) & Q]P, Δ",
    displayContextPremises = "Γ |- C( Q→P∧∀x(P')<sub>x'↦f(x)</sub> ), Δ",
    displayContextConclusion = "Γ |- C( [x'=f(x) & Q]P ), Δ",
    revealInternalSteps = true,
    constructor = TacticConstructor0.create()(() => dIClose),
  )

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

  def dIX: DependentPositionTactic = "dI".forward(DifferentialTactics.diffInd(Symbol("cex")))

  @Derivation
  val dIXInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "dI",
    displayNameLong = Some("Differential Invariant"),
    displayLevel = DisplayLevel.All,
    displayPremises = "Γ, Q |- P, Δ ;; Q |- [x':=f(x)](P)'",
    displayConclusion = "Γ |- [x'=f(x) & Q]P, Δ",
    displayContextPremises = "Γ |- C( Q→P∧∀x(P')<sub>x'↦f(x)</sub> ), Δ",
    displayContextConclusion = "Γ |- C( [x'=f(x) & Q]P ), Δ",
    revealInternalSteps = true,
    constructor = TacticConstructor0.create()(() => dIX),
  )

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
  def dG(E: Expression, G: Option[Formula]): DependentPositionWithAppliedInputTactic = "dG".byWithInputs(
    List(E, G),
    (pos: Position) =>
      E match {
        case Equal(l: DifferentialSymbol, r) => DifferentialTactics.dG(AtomicODE(l, r), G)(pos)
        case dp: DifferentialProgram => DifferentialTactics.dG(dp, G)(pos)
        case ODESystem(dp, _) => DifferentialTactics.dG(dp, G)(pos)
        case _ =>
          throw new IllegalArgumentException("Expected a differential program y′=f(y), but got " + E.prettyString)
      },
  )

  @Derivation
  val dGInfo: InputPositionTacticInfo = InputPositionTacticInfo.create(
    name = "dG",
    displayNameLong = Some("Differential Ghost"),
    displayPremises = "Γ |- ∃y [x'=f(x),E & Q]G, Δ ;; G |- P",
    displayConclusion = "Γ |- [x'=f(x) & Q]P, Δ",
    displayContextPremises = "Γ |- C( ∃y [x'=f(x),E & Q]G ), Δ",
    displayContextConclusion = "Γ |- C( [x'=f(x) & Q]P ), Δ",
    revealInternalSteps = true,
    constructor = TacticConstructor2
      .create(ExpressionArg("E", List("y", "x", "y'")), OptionArg(FormulaArg("G", List("y"))))(dG),
  )

  def dGold(y: Variable, t1: Term, t2: Term, p: Option[Formula]): DependentPositionWithAppliedInputTactic = "dGold"
    .forward(dG(AtomicODE(DifferentialSymbol(y), Plus(Times(t1, y), t2)), p))

  @Derivation
  val dGoldInfo: InputPositionTacticInfo = InputPositionTacticInfo.create(
    name = "dGold",
    displayName = Some("dG"),
    displayNameLong = Some("Differential Ghost"),
    displayPremises = "Γ |- ∃y [{x'=f(x),y′=a(x)*y+b(x) & Q}]P, Δ",
    displayConclusion = "Γ |- [{x'=f(x) & Q}]P, Δ",
    constructor = TacticConstructor4
      .create(VariableArg("y", List("y")), TermArg("a(x)"), TermArg("b(x)"), OptionArg(FormulaArg("P", List("y"))))(
        dGold
      ),
  )

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
  def diffInvariant(invariant: Formula): DependentPositionWithAppliedInputTactic = "diffInvariant"
    .byWithInputs(List(invariant), (pos: Position) => DifferentialTactics.diffInvariant(List(invariant))(pos))

  @Derivation
  val diffInvariantInfo: InputPositionTacticInfo = InputPositionTacticInfo.create(
    name = "diffInvariant",
    displayNameLong = Some("Differential Cut + Auto Differential Invariant"),
    displayPremises = "Γ |- [x'=f(x) & Q∧R]P, Δ",
    displayConclusion = "Γ |- [x'=f(x) & Q]P, Δ",
    revealInternalSteps = true,
    constructor = TacticConstructor1.create(FormulaArg("R"))((invariant: Formula) => diffInvariant(invariant)),
  )

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
