/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon._
import org.keymaerax.btactics.Idioms.saturate
import org.keymaerax.btactics.macros.DerivationInfoAugmentors.ProvableInfoAugmentor
import org.keymaerax.btactics.macros.{DisplayLevel, Tactic}
import org.keymaerax.core._
import org.keymaerax.infrastruct.Augmentors._
import org.keymaerax.infrastruct.ExpressionTraversal.ExpressionTraversalFunction
import org.keymaerax.infrastruct._
import org.keymaerax.pt.ProvableSig

import scala.collection.immutable._
import scala.collection.mutable.ListBuffer
import scala.reflect.runtime.universe

/**
 * Hilbert Calculus for differential dynamic logic.
 * @author
 *   Andre Platzer
 * @author
 *   Stefan Mitsch
 * @see
 *   [[HilbertCalculus]]
 */
object HilbertCalculus extends TacticProvider with HilbertCalculus {

  /** @inheritdoc */
  override def getInfo: (Class[_], universe.Type) = (HilbertCalculus.getClass, universe.typeOf[HilbertCalculus.type])
}

/**
 * Hilbert Calculus for differential dynamic logic.
 *
 * Provides the axioms and axiomatic proof rules from Figure 2 and Figure 3 in: Andre Platzer.
 * [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]].
 * Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
 *
 * @author
 *   Andre Platzer
 * @author
 *   Stefan Mitsch
 * @see
 *   Andre Platzer.
 *   [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]].
 *   Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
 * @see
 *   Andre Platzer. [[https://doi.org/10.1007/978-3-319-63588-0 Logical Foundations of Cyber-Physical Systems]].
 *   Springer, 2018.
 * @see
 *   Andre Platzer.
 *   [[https://doi.org/10.1007/978-3-319-21401-6_32 A uniform substitution calculus for differential dynamic logic]]. In
 *   Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin,
 *   Germany, Proceedings, LNCS. Springer, 2015.
 *   [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic. arXiv 1503.01981]]
 * @see
 *   Andre Platzer. [[https://doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015.
 *   [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
 * @see
 *   Andre Platzer. [[https://doi.org/10.1109/LICS.2012.13 Logics of dynamical systems]]. ACM/IEEE Symposium on Logic in
 *   Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 13-24. IEEE 2012
 * @see
 *   Andre Platzer. [[https://doi.org/10.1109/LICS.2012.64 The complete proof theory of hybrid systems]]. ACM/IEEE
 *   Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012
 * @see
 *   [[HilbertCalculus.stepAt()]]
 * @see
 *   [[HilbertCalculus.derive()]]
 * @see
 *   [[org.keymaerax.core.AxiomBase]]
 * @see
 *   [[org.keymaerax.btactics.Ax]]
 * @see
 *   [[TactixLibrary]]
 * @Tactic
 *   completed
 */
trait HilbertCalculus extends UnifyUSCalculus {
  import TacticFactory._

  /**
   * True when insisting on internal useAt technology, false when more elaborate external tactic calls are used on
   * demand.
   */
  private[btactics] val INTERNAL = false

  /**
   * Make the canonical simplifying proof step at the indicated position except when a decision needs to be made (e.g.
   * invariants for loops or for differential equations). Using the canonical [[AxIndex]].
   * @author
   *   Andre Platzer
   * @note
   *   Efficient source-level indexing implementation.
   * @see
   *   [[AxIndex]]
   */
  @Tactic(name = "stepAt")
  val stepAt: DependentPositionTactic = UnifyUSCalculus.stepAt(AxIndex.axiomFor)
  // = UnifyUSCalculus.stepAt(AxIndex.axiomFor)
  // = anon {(pos:Position) => UnifyUSCalculus.stepAt(AxIndex.axiomFor)(pos)}

  //
  // axiomatic rules
  //

  /**
   * G: Gödel generalization rule reduces a proof of `&Gamma; |- [a]p(x), &Delta;` to proving the postcondition `|-
   * p(x)` in isolation.
   * {{{
   *     |- p(||)
   *   --------------- G
   *   G |- [a]p(||), D
   * }}}
   * This rule is a special case of rule [[monb]] with p(x)=True by [[boxTrue]].
   * @note
   *   Unsound for hybrid games
   * @see
   *   [[monb]] with p(x)=True
   * @see
   *   [[boxTrue]]
   */
  @Tactic(name = "G", displayPremises = "|- P", displayConclusion = "Γ |- [a]P, Δ")
  val G: DependentPositionTactic = anon { (pos: Position) => SequentCalculus.cohideR(pos) & DLBySubst.G }

  /**
   * allG: all generalization rule reduces a proof of `\forall x p(x) |- \forall x q(x)` to proving `p(x) |- q(x)` in
   * isolation.
   * {{{
   *      p(x) |- q(x)
   *   ---------------------------------
   *   \forall x p(x) |- \forall x q(x)
   * }}}
   * @see
   *   [[UnifyUSCalculus.CMon()]]
   */
  // @todo flexibilize via cohide2 first
  @Tactic(name = "monall", displayPremises = "P |- Q", displayConclusion = "∀x P |- ∀x Q")
  lazy val monall: BuiltInTactic = anon { US(Ax.monallrule.provable).result _ }

  /**
   * monb: Monotone `[a]p(x) |- [a]q(x)` reduces to proving `p(x) |- q(x)`.
   * {{{
   *      p(x) |- q(x)
   *   ------------------- M[.]
   *   [a]p(x) |- [a]q(x)
   * }}}
   * @see
   *   [[UnifyUSCalculus.CMon()]]
   */
  // @todo flexibilize via cohide2 first
  @Tactic(name = "monb", displayPremises = "P |- Q", displayConclusion = "[a]P |- [a]Q")
  lazy val monb: BuiltInTactic = anon { US(Ax.monbaxiom.provable).result _ }

  /**
   * mond: Monotone `⟨a⟩p(x) |- ⟨a⟩q(x)` reduces to proving `p(x) |- q(x)`.
   * {{{
   *      p(x) |- q(x)
   *   ------------------- M
   *   ⟨a⟩p(x) |- ⟨a⟩q(x)
   * }}}
   * @see
   *   [[UnifyUSCalculus.CMon()]]
   */
  // @todo flexibilize via cohide2 first
  @Tactic(name = "mond", displayPremises = "P |- Q", displayConclusion = "&langle;a&rangle;P |- &langle;a&rangle;Q")
  lazy val mond: BuiltInTactic = anon { US(Ax.mondrule.provable).result _ }

  //
  // axioms
  //

  //
  // box modality
  //

  /** diamond: <.> reduce double-negated box `![a]!p(x)` to a diamond `⟨a⟩p(x)`. */
  lazy val diamond: BuiltInPositionTactic = useAt(Ax.diamond)
  @Tactic(
    name = "diamondd",
    displayName = Some("<·>"),
    displayNameAscii = Some("<.>"),
    displayConclusion = "__&langle;a&rangle;P__ ↔ &not;[a]&not;P",
  )
  lazy val diamondd: BuiltInPositionTactic = HilbertCalculus.useAt(Ax.diamond, PosInExpr(1 :: Nil))

  /**
   * assignb: [:=] simplify assignment `[x:=f;]p(x)` by substitution `p(f)` or equation. Box assignment by substitution
   * assignment [v:=t();]p(v) <-> p(t()) (preferred), or by equality assignment [x:=f();]p(||) <-> \forall x (x=f() ->
   * p(||)) as a fallback. Universal quantifiers are skolemized if applied at top-level in the succedent; they remain
   * unhandled in the antecedent and in non-top-level context.
   * @example
   *   {{{
   *   |- 1>0
   *   --------------------assignb(1)
   *   |- [x:=1;]x>0
   *   }}}
   * @example
   *   {{{
   *          1>0 |-
   *   --------------------assignb(-1)
   *   [x:=1;]x>0 |-
   *   }}}
   * @example
   *   {{{
   *   x_0=1 |- [{x_0:=x_0+1;}*]x_0>0
   *   ----------------------------------assignb(1)
   *         |- [x:=1;][{x:=x+1;}*]x>0
   *   }}}
   * @example
   *   {{{
   *   \\forall x_0 (x_0=1 -> [{x_0:=x_0+1;}*]x_0>0) |-
   *   -------------------------------------------------assignb(-1)
   *                          [x:=1;][{x:=x+1;}*]x>0 |-
   *   }}}
   * @example
   *   {{{
   *   |- [y:=2;]\\forall x_0 (x_0=1 -> x_0=1 -> [{x_0:=x_0+1;}*]x_0>0)
   *   -----------------------------------------------------------------assignb(1, 1::Nil)
   *   |- [y:=2;][x:=1;][{x:=x+1;}*]x>0
   *   }}}
   * @see
   *   [[DLBySubst.assignEquality]]
   */
  @Tactic(
    name = "assignb",
    displayName = Some("[:=]"),
    revealInternalSteps = true,
    displayConclusion = "__[x:=e]p(x)__↔p(e)",
  )
  lazy val assignb: BuiltInPositionTactic = anon { (pr: ProvableSig, pos: Position) =>
    if (INTERNAL)
      try { useAt(Ax.assignbAxiom)(pos)(pr) }
      catch { case _: Throwable => useAt(Ax.selfassignb)(pos)(pr) }
    else
      try { useAt(Ax.assignbAxiom)(pos)(pr) }
      catch {
        case _: Throwable =>
          try { useAt(Ax.selfassignb)(pos)(pr) }
          catch { case _: Throwable => DLBySubst.assignEquality(pos)(pr) }
      }
  }

  /** randomb: [:*] simplify nondeterministic assignment `[x:=*;]p(x)` to a universal quantifier `\forall x p(x)` */
  lazy val randomb: BuiltInPositionTactic = useAt(Ax.randomb)

  /** testb: [?] simplifies test `[?q;]p` to an implication `q->p` */
  lazy val testb: BuiltInPositionTactic = useAt(Ax.testb)

  /** diffSolve: solve a differential equation `[x'=f]p(x)` to `\forall t>=0 [x:=solution(t)]p(x)` */
  // def diffSolve               : DependentPositionTactic = ???
  /** choiceb: [++] handles both cases of a nondeterministic choice `[a++b]p(x)` separately `[a]p(x) & [b]p(x)` */
  lazy val choiceb: BuiltInPositionTactic = useAt(Ax.choiceb)

  /** composeb: [;] handle both parts of a sequential composition `[a;b]p(x)` one at a time `[a][b]p(x)` */
  lazy val composeb: BuiltInPositionTactic = useAt(Ax.composeb)

  /** iterateb: [*] prove a property of a loop `[{a}*]p(x)` by unrolling it once `p(x) & [a][{a}*]p(x)` */
  lazy val iterateb: BuiltInPositionTactic = useAt(Ax.iterateb)

  /** dualb: [^d^] handle dual game `[{a}^d^]p(x)` by `![a]!p(x)` */
  lazy val dualb: BuiltInPositionTactic = useAt(Ax.dualb)

  //
  // diamond modality
  //

  /** box: [.] to reduce double-negated diamond `!⟨a⟩!p(x)` to a box `[a]p(x)`. */
  lazy val box: BuiltInPositionTactic = useAt(Ax.box)
  @Tactic(
    name = "boxd",
    displayName = Some("[·]"),
    displayNameAscii = Some("[.]"),
    displayConclusion = "__[a]P__ ↔ &not;&langle;a&rangle;&not;P",
  )
  lazy val boxd: BuiltInPositionTactic = HilbertCalculus.useAt(Ax.box, PosInExpr(1 :: Nil))

  /** assignd: <:=> simplify assignment `<x:=f;>p(x)` by substitution `p(f)` or equation */
  @Tactic(
    name = "assignd",
    displayName = Some("<:=>"),
    revealInternalSteps = true,
    displayConclusion = "__&langle;x:=e&rangle;p(x)__↔p(e)",
  )
  lazy val assignd: DependentPositionTactic = anon { (pos: Position) =>
    useAt(Ax.assigndAxiom)(pos) |! useAt(Ax.selfassignd)(pos) |! DLBySubst.assigndEquality(pos)
  }

  /** randomd: <:*> simplify nondeterministic assignment `<x:=*;>p(x)` to an existential quantifier `\exists x p(x)` */
  lazy val randomd: BuiltInPositionTactic = useAt(Ax.randomd)

  /** testd: <?> simplifies test `<?q;>p` to a conjunction `q&p` */
  lazy val testd: BuiltInPositionTactic = useAt(Ax.testd)

  /** diffSolve: solve a differential equation `<x'=f>p(x)` to `\exists t>=0 <x:=solution(t)>p(x)` */
  // def diffSolved              : DependentPositionTactic = ???
  /** choiced: <++> handles both cases of a nondeterministic choice `⟨a++b⟩p(x)` separately `⟨a⟩p(x) | ⟨b⟩p(x)` */
  lazy val choiced: BuiltInPositionTactic = useAt(Ax.choiced)

  /** composed: <;> handle both parts of a sequential composition `⟨a;b⟩p(x)` one at a time `⟨a⟩⟨b⟩p(x)` */
  lazy val composed: BuiltInPositionTactic = useAt(Ax.composed)

  /** iterated: <*> prove a property of a loop `⟨{a}*⟩p(x)` by unrolling it once `p(x) | ⟨a⟩⟨{a}*⟩p(x)` */
  lazy val iterated: BuiltInPositionTactic = useAt(Ax.iterated)

  /** duald: `<^d^>` handle dual game `⟨{a}^d^⟩p(x)` by `!⟨a⟩!p(x)` */
  lazy val duald: BuiltInPositionTactic = useAt(Ax.duald)

  lazy val assigndDual: BuiltInPositionTactic = HilbertCalculus.useAt(Ax.assignDual2)
  @Tactic(
    name = "assignbDual",
    displayName = Some("[:=]D"),
    displayConclusion = "&langle;x:=f();&rangle;P ↔ __[x:=f();]P__",
  )
  lazy val assignbDual: BuiltInPositionTactic = HilbertCalculus.useAt(Ax.assignDual2, PosInExpr(1 :: Nil))

//  /** I: prove a property of a loop by induction with the given loop invariant (hybrid systems) */
//  def I(invariant : Formula)  : PositionTactic = TacticLibrary.inductionT(Some(invariant))
//  def loop(invariant: Formula) = I(invariant)
  /**
   * K: modal modus ponens (hybrid systems)
   * @note
   *   Use with care since limited to hybrid systems. Use [[monb]] instead.
   * @see
   *   [[monb]]
   * @see
   *   [[mond]]
   */
  lazy val K: BuiltInPositionTactic = useAt(Ax.K)

  /**
   * V: vacuous box `[a]p()` will be discarded and replaced by `p()` provided program `a` does not change values of
   * postcondition `p()`.
   * @note
   *   Unsound for hybrid games
   */
  lazy val V: BuiltInPositionTactic = useAt(Ax.V)

  /**
   * VK: vacuous box `[a]p()` will be discarded and replaced by `p()` provided program `a` does not change values of
   * postcondition `p()` and provided `[a]true` proves, e.g., since `a` is a hybrid system.
   */
  lazy val VK: BuiltInPositionTactic = useAt(Ax.VK)

  //
  // differential equations
  //

  /**
   * DW: Differential Weakening to use evolution domain constraint `[{x'=f(x)&q(x)}]p(x)` reduces to
   * `[{x'=f(x)&q(x)}](q(x)->p(x))`.
   * {{{
   * G |- [x'=f(x)&Q](Q->P), D
   * ------------------------- DW(R)
   * G |- [x'=f(x)&Q]P, D
   * }}}
   * @incontext
   * @see
   *   [[DifferentialEquationCalculus.dW()]]
   */
  lazy val DW: BuiltInPositionTactic = useAt(Ax.DW)

  /**
   * DWd: Diamond Differential Weakening to use evolution domain constraint `<{x'=f(x)&q(x)}>p(x)` reduces to
   * `<{x'=f(x)&q(x)}>(q(x)&p(x))`
   */
  lazy val DWd: BuiltInPositionTactic = useAt(Ax.DWd)

  /**
   * DC: Differential Cut a new invariant for a differential equation `[{x'=f(x)&q(x)}]p(x)` reduces to
   * `[{x'=f(x)&q(x)&C(x)}]p(x)` with `[{x'=f(x)&q(x)}]C(x)`.
   * {{{
   * Use:                      Show:
   * G |- [x'=f(x)&Q&R]P, D    G |- [x'=f(x)&Q]R, D
   * ---------------------------------------------- DC(R)
   * G |- [x'=f(x)&Q]P, D
   * }}}
   * {{{
   * Use:                         Show:
   * G |- A->[x'=f(x)&Q&R]P, D    G |- A->[x'=f(x)&Q]R, D
   * ---------------------------------------------- dC(R)
   * G |- A->[x'=f(x)&Q]P, D
   * }}}
   * @incontext
   * @see
   *   [[DifferentialEquationCalculus.dC()]]
   */
  @Tactic(
    name = "DC",
    displayConclusion = "(__[x'=f(x)&Q]P__↔[x'=f(x)&Q∧R]P)←[x'=f(x)&Q]R",
    inputs = "R:formula",
    revealInternalSteps = true,
  )
  def DC(invariant: Formula): DependentPositionWithAppliedInputTactic = inputanon { (pos: Position) =>
    useAt(
      Ax.DC,
      (us: Option[Subst]) =>
        us.getOrElse(throw new UnsupportedTacticFeature("Unexpected missing substitution in DC")) ++
          RenUSubst(Seq((UnitPredicational("r", AnyArg), invariant))),
    )(pos) < (LabelBranch(BelleLabels.cutUse), LabelBranch(BelleLabels.cutShow))
  }

  /**
   * DCd: Diamond Differential Cut a new invariant for a differential equation `<{x'=f(x)&q(x)}>p(x)` reduces to
   * `<{x'=f(x)&q(x)&C(x)}>p(x)` with `[{x'=f(x)&q(x)}]C(x)`.
   */
  @Tactic(
    name = "DCd",
    displayConclusion = "(__<x'=f(x)&Q>P__↔<x'=f(x)&Q∧R>P)←[x'=f(x)&Q]R",
    inputs = "R:formula",
    revealInternalSteps = true,
  )
  def DCd(invariant: Formula): DependentPositionWithAppliedInputTactic = inputanon { (pos: Position) =>
    useAt(
      Ax.DCdaxiom,
      (us: Option[Subst]) =>
        us.getOrElse(throw new UnsupportedTacticFeature("Unexpected missing substitution in DCd")) ++
          RenUSubst(Seq((UnitPredicational("r", AnyArg), invariant))),
    )(pos) < (LabelBranch(BelleLabels.cutUse), LabelBranch(BelleLabels.cutShow))
  }

  /**
   * DE: Differential Effect exposes the effect of a differential equation `[x'=f(x)]p(x,x')` on its differential
   * symbols as `[x'=f(x)][x':=f(x)]p(x,x')` with its differential assignment `x':=f(x)`.
   * {{{
   *   G |- [{x'=f(||)&H(||)}][x':=f(||);]p(||), D
   *   -------------------------------------------
   *   G |- [{x'=f(||)&H(||)}]p(||), D
   * }}}
   *
   * @example
   *   {{{
   *   |- [{x'=1}][x':=1;]x>0
   *   -----------------------DE(1)
   *   |- [{x'=1}]x>0
   *   }}}
   * @example
   *   {{{
   *   |- [{x'=1, y'=x & x>0}][y':=x;][x':=1;]x>0
   *   -------------------------------------------DE(1)
   *   |- [{x'=1, y'=x & x>0}]x>0
   *   }}}
   * @incontext
   */
  lazy val DE: DependentPositionTactic = DifferentialTactics.DE

  /**
   * DI: Differential Invariants are used for proving a formula to be an invariant of a differential equation.
   * `[x'=f(x)&q(x)]p(x)` reduces to `q(x) -> p(x) & [x'=f(x)]p(x)'`.
   * @see
   *   [[DifferentialEquationCalculus.dI()]]
   */
  lazy val DI: BuiltInPositionTactic = useAt(Ax.DI)

  // @todo replace with a DG(DifferentialProgram) tactic instead to use said axiom.

  /** DGC: Differential ghost add auxiliary differential equation with extra constant g */
  private[btactics] def DGC(y: Variable, b: Term) = useAt(
    Ax.DGC,
    PosInExpr(0 :: Nil),
    (us: Option[Subst]) => {
      val singular = FormulaTools.singularities(b)
      insist(
        singular.isEmpty,
        "Possible singularities during DG(" + DifferentialSymbol(y) + "=" + b + ") will be rejected: " +
          singular.mkString(","),
      )
      us.getOrElse(throw new UnsupportedTacticFeature("Unexpected missing substitution in DG")) ++ RenUSubst(
        Seq((Variable("y_", None, Real), y), (UnitFunctional("b", Except(Variable("y_", None, Real) :: Nil), Real), b))
      )
    },
  )

  // @todo unclear
  private[btactics] def DGCa(y: Variable, b: Term) = useAt(
    Ax.DGCa,
    PosInExpr(0 :: Nil),
    (us: Option[Subst]) => {
      val singular = FormulaTools.singularities(b)
      insist(
        singular.isEmpty,
        "Possible singularities during DG(" + DifferentialSymbol(y) + "=" + b + ") will be rejected: " +
          singular.mkString(","),
      )
      us.getOrElse(throw new UnsupportedTacticFeature("Unexpected missing substitution in DG")) ++ RenUSubst(
        Seq((Variable("y_", None, Real), y), (UnitFunctional("b", Except(Variable("y_", None, Real) :: Nil), Real), b))
      )
    },
  )

  /** DGC: Differential ghost add auxiliary differential equation with extra constant g */
  private[btactics] def DGCd(y: Variable, b: Term) = useAt(
    Ax.DGCd,
    PosInExpr(0 :: Nil),
    (us: Option[Subst]) => {
      val singular = FormulaTools.singularities(b)
      insist(
        singular.isEmpty,
        "Possible singularities during DG(" + DifferentialSymbol(y) + "=" + b + ") will be rejected: " +
          singular.mkString(","),
      )
      us.getOrElse(throw new UnsupportedTacticFeature("Unexpected missing substitution in DGd")) ++ RenUSubst(
        Seq((Variable("y_", None, Real), y), (UnitFunctional("b", Except(Variable("y_", None, Real) :: Nil), Real), b))
      )
    },
  )
  private[btactics] def DGCde(y: Variable, b: Term) = useAt(
    Ax.DGCde,
    PosInExpr(0 :: Nil),
    (us: Option[Subst]) => {
      val singular = FormulaTools.singularities(b)
      insist(
        singular.isEmpty,
        "Possible singularities during DG(" + DifferentialSymbol(y) + "=" + b + ") will be rejected: " +
          singular.mkString(","),
      )
      us.getOrElse(throw new UnsupportedTacticFeature("Unexpected missing substitution in DGde")) ++ RenUSubst(
        Seq((Variable("y_", None, Real), y), (UnitFunctional("b", Except(Variable("y_", None, Real) :: Nil), Real), b))
      )
    },
  )

  //  /** DA: Differential Ghost add auxiliary differential equations with extra variables y'=a*y+b and replacement formula */
//  def DA(y:Variable, a:Term, b:Term, r:Formula) : PositionTactic = ODETactics.diffAuxiliariesRule(y,a,b,r)
  /**
   * DS: Differential Solution solves a simple differential equation `[x'=c&q(x)]p(x)` by reduction to `\forall t>=0
   * ((\forall 0<=s<=t q(x+c()*s) -> [x:=x+c()*t;]p(x))`
   */
  lazy val DS: BuiltInPositionTactic = useAt(Ax.DS)

  /** Dassignb: [':=] Substitute a differential assignment `[x':=f]p(x')` to `p(f)` */
  // @note potential incompleteness here should not ever matter
  lazy val Dassignb: BuiltInPositionTactic = useAt(Ax.Dassignb)

  /*
   * Derive by proof
   */

  /**
   * Derive the differential expression at the indicated position (Hilbert computation deriving the answer by proof) to
   * get rid of the differential operators.
   * @example
   *   When applied at 1::Nil, turns [{x'=22}](2*x+x*y>=5)' into [{x'=22}]2*x'+x'*y+x*y'>=0
   * @see
   *   [[UnifyUSCalculus.chase]]
   */
  @Tactic(name = "derive", displayName = Some("()'"), revealInternalSteps = false /* uninformative as useFor proof */ )
  lazy val derive: BuiltInPositionTactic = anon { (pr: ProvableSig, pos: Position) =>
    ProofRuleTactics.requireOneSubgoal(pr, "derive")

    val chaseNegations = anon { (provable: ProvableSig, pos: Position) =>
      ProofRuleTactics.requireOneSubgoal(provable, "derive.chaseNegations")
      provable.subgoals.head.sub(pos) match {
        case Some(post: Formula) =>
          val notPositions = ListBuffer.empty[PosInExpr]
          ExpressionTraversal.traverse(
            new ExpressionTraversalFunction() {
              override def preF(p: PosInExpr, e: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] =
                e match {
                  case Not(_) if !notPositions.exists(_.isPrefixOf(p)) => notPositions.append(p); Left(None)
                  case _ => Left(None)
                }
            },
            post,
          )
          notPositions.map(p => chase(pos ++ p)).foldLeft(provable)({ (pr, r) => pr(r.computeResult _, 0) })
        case _ => provable
      }
    }

    val deriveVars = anon { (provable: ProvableSig, pos: Position) =>
      ProofRuleTactics.requireOneSubgoal(provable, "derive.deriveVars")
      provable.subgoals.head.sub(pos) match {
        case Some(e: Expression) =>
          val dvarPositions = ListBuffer.empty[PosInExpr]
          ExpressionTraversal.traverseExpr(
            new ExpressionTraversalFunction() {
              override def preT(p: PosInExpr, t: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] =
                t match {
                  case Differential(_: Variable) => dvarPositions.append(p); Left(None)
                  case _ => Left(None)
                }
            },
            e,
          )
          dvarPositions.foldLeft(provable)({ case (pr, p) => pr(DifferentialTactics.Dvariable(pos ++ p), 0) })
        case _ => provable
      }
    }

    pr(saturate(chaseNegations(pos) andThen deepChase(pos)), 0)(deriveVars(pos), 0)
  }

  //
  // Additional
  //

  /** boxAnd: splits `[a](p&q)` into `[a]p & [a]q` */
  lazy val boxAnd: BuiltInPositionTactic = useAt(Ax.boxAnd)

  /** diamondOr: splits `⟨a⟩(p|q)` into `⟨a⟩p | ⟨a⟩q` */
  lazy val diamondOr: BuiltInPositionTactic = useAt(Ax.diamondOr)

  /** boxImpliesAnd: splits `[a](p->q&r)` into `[a](p->q) & [a](p->r)` */
  lazy val boxImpliesAnd: BuiltInPositionTactic = useAt(Ax.boxImpliesAnd)

  // def ind

  /** boxTrue: proves `[a]true` directly for hybrid systems `a` that are not hybrid games. */
  @Tactic(
    name = "boxTrue",
    displayName = Some("[]T"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__[a]⊤__ ↔ ⊤",
  )
  // @note: do not use in derived axioms, instead use useAt(Ax.boxTrueAxiom) to avoid circular dependencies!
  lazy val boxTrue: BuiltInPositionTactic = anon { (provable: ProvableSig, pos: Position) =>
    (provable(useAt(Ax.boxTrueTrue)(pos).computeResult _, 0)(
      if (pos.isSucc && pos.isTopLevel) SequentCalculus.closeT.result _ else skip.result _,
      0,
    ))
  }

  /*
   *  First-order logic
   */

  /** allV: vacuous `\forall x p()` will be discarded and replaced by p() provided x does not occur in p(). */
  lazy val allV: BuiltInPositionTactic = useAt(Ax.allV)

  /** existsV: vacuous `\exists x p()` will be discarded and replaced by p() provided x does not occur in p(). */
  lazy val existsV: BuiltInPositionTactic = useAt(Ax.existsV)

  /**
   * allDist: distribute `\forall x p(x) -> \forall x q(x)` by replacing it with `\forall x (p(x)->q(x))`.
   * @see
   *   [[allDistElim]]
   */
  lazy val allDist: BuiltInPositionTactic = useAt(Ax.allDist)

  /** allDistElim: distribute `\forall x P -> \forall x Q` by replacing it with `\forall x (P->Q)`. */
  lazy val allDistElim: BuiltInPositionTactic = useAt(Ax.allDistElim)

  /** existsE: show `\exists x P` by showing that it follows from `P`. */
  lazy val existsE: BuiltInPositionTactic = useAt(Ax.existse)

}

object Derive extends TacticProvider with Derive {

  /** @inheritdoc */
  override def getInfo: (Class[_], universe.Type) = (Derive.getClass, universe.typeOf[Derive.type])
}

/**
 * Derive: provides individual differential axioms bundled as [[HilbertCalculus.derive]].
 *
 * There is rarely a reason to use these separate axioms, since [[HilbertCalculus.derive]] already uses the appropriate
 * differential axiom as needed.
 * @see
 *   Figure 3 in Andre Platzer.
 *   [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]].
 *   Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
 * @see
 *   [[HilbertCalculus.derive]]
 */
trait Derive extends UnifyUSCalculus {
  import TacticFactory._

  /**
   * True when insisting on internal useAt technology, false when more elaborate external tactic calls are used on
   * demand.
   */
  private[btactics] val INTERNAL = false

  /** Dplus: +' derives a sum `(f(x)+g(x))' = (f(x))' + (g(x))'` */
  lazy val Dplus: BuiltInPositionTactic = useAt(Ax.Dplus)

  /** neg: -' derives unary negation `(-f(x))' = -(f(x)')` */
  lazy val Dneg: BuiltInPositionTactic = useAt(Ax.Dneg)

  /** Dminus: -' derives a difference `(f(x)-g(x))' = (f(x))' - (g(x))'` */
  lazy val Dminus: BuiltInPositionTactic = useAt(Ax.Dminus)

  /** Dtimes: *' derives a product `(f(x)*g(x))' = f(x)'*g(x) + f(x)*g(x)'` */
  lazy val Dtimes: BuiltInPositionTactic = useAt(Ax.Dtimes)

  /** Dquotient: /' derives a quotient `(f(x)/g(x))' = (f(x)'*g(x) - f(x)*g(x)') / (g(x)^2)` */
  lazy val Dquotient: BuiltInPositionTactic = useAt(Ax.Dquotient)

  /** Dpower: `^'` derives a power */
  lazy val Dpower: BuiltInPositionTactic = useAt(Ax.Dpower)

  /** Dcompose: o' derives a function composition by chain rule */
  // @todo not sure if useAt can handle this yet
  lazy val Dcompose: BuiltInPositionTactic = useAt(Ax.Dcompose)

  /** Dconst: c()' derives a constant `c()' = 0` */
  lazy val Dconst: BuiltInPositionTactic = useAt(Ax.Dconst)

  /**
   * Dvariable: x' derives a variable `(x)' = x'` Syntactically derives a differential of a variable to a differential
   * symbol.
   * {{{
   *   G |- x'=f, D
   *   --------------
   *   G |- (x)'=f, D
   * }}}
   *
   * @example
   *   {{{
   *   |- x'=1
   *   ----------Dvariable(1, 0::Nil)
   *   |- (x)'=1
   *   }}}
   * @example
   *   {{{
   *   |- [z':=1;]z'=1
   *   ------------------Dvariable(1, 1::0::Nil)
   *   |- [z':=1;](z)'=1
   *   }}}
   * @incontext
   */
  @Tactic(name = "Dvar", displayName = Some("(x)'"), displayLevel = DisplayLevel.Browse, displayConclusion = "(x)' = x")
  lazy val Dvar: DependentPositionTactic = anon { (pos: Position) =>
    (if (INTERNAL) useAt(Ax.DvarAxiom) else DifferentialTactics.Dvariable) (pos)
  }

  /** Dand: &' derives a conjunction `(p(x)&q(x))'` to obtain `p(x)' & q(x)'` */
  lazy val Dand: BuiltInPositionTactic = useAt(Ax.Dand)

  /** Dor: |' derives a disjunction `(p(x)|q(x))'` to obtain `p(x)' & q(x)'` */
  lazy val Dor: BuiltInPositionTactic = useAt(Ax.Dor)

  /** Dimply: ->' derives an implication `(p(x)->q(x))'` to obtain `(!p(x) | q(x))'` */
  lazy val Dimply: BuiltInPositionTactic = useAt(Ax.Dimply)

  /** Dequal: =' derives an equation `(f(x)=g(x))'` to obtain `f(x)'=g(x)'` */
  lazy val Dequal: BuiltInPositionTactic = useAt(Ax.Dequal)

  /** Dnotequal: !=' derives a disequation `(f(x)!=g(x))'` to obtain `f(x)'=g(x)'` */
  lazy val Dnotequal: BuiltInPositionTactic = useAt(Ax.Dnotequal)

  /** Dless: <' derives less-than `(f(x)⟨g(x))'` to obtain `f(x)'<=g(x)'` */
  lazy val Dless: BuiltInPositionTactic = useAt(Ax.Dless)

  /** Dlessequal: <=' derives a less-or-equal `(f(x)<=g(x))'` to obtain `f(x)'<=g(x)'` */
  lazy val Dlessequal: BuiltInPositionTactic = useAt(Ax.Dlessequal)

  /** Dgreater: >' derives greater-than `(f(x)>g(x))'` to obtain `f(x)'>=g(x)'` */
  lazy val Dgreater: BuiltInPositionTactic = useAt(Ax.Dgreater)

  /** Dgreaterequal: >=' derives a greater-or-equal `(f(x)>=g(x))'` to obtain `f(x)'>=g(x)'` */
  lazy val Dgreaterequal: BuiltInPositionTactic = useAt(Ax.Dgreaterequal)

  /** Dforall: \forall' derives an all quantifier `(\forall x p(x))'` to obtain `\forall x (p(x)')` */
  lazy val Dforall: BuiltInPositionTactic = useAt(Ax.Dforall)

  /** Dexists: \exists' derives an exists quantifier */
  lazy val Dexists: BuiltInPositionTactic = useAt(Ax.Dexists)
}
