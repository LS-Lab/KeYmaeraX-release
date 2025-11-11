/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon.{
  BuiltInRightTactic,
  BuiltInTactic,
  DependentPositionTactic,
  DependentPositionWithAppliedInputTactic,
  LastSucc,
  TacticAssertionError,
  TacticInapplicableFailure,
}
import org.keymaerax.btactics.Ax.*
import org.keymaerax.btactics.PropositionalTactics.prop
import org.keymaerax.btactics.RefinementCalculus.*
import org.keymaerax.btactics.SequentCalculus.{cutL, cutR}
import org.keymaerax.btactics.TacticFactory.{anon, TacticForNameFactory}
import org.keymaerax.btactics.TactixLibrary.proveBy
import org.keymaerax.btactics.UnifyUSCalculus.{skip, useAt}
import org.keymaerax.btactics.macros.{
  DisplayLevel,
  FormulaArg,
  PositionTacticInfo,
  TacticConstructor0,
  TacticConstructor1,
}
import org.keymaerax.core.*
import org.keymaerax.core.StaticSemantics.symbols
import org.keymaerax.core.btactics.annotations.Derivation
import org.keymaerax.infrastruct.Augmentors.{FormulaAugmentor, ProgramAugmentor, SequentAugmentor}
import org.keymaerax.infrastruct.FormulaTools.polarityAt
import org.keymaerax.infrastruct.PosInExpr.HereP
import org.keymaerax.infrastruct.{Context, PosInExpr, Position, SuccPosition}
import org.keymaerax.parser.StringConverter.StringToStringConverter
import org.keymaerax.pt.ProvableSig

object Refactor {

  lazy val congrAndL: ProvableSig = proveBy("(p() -> q()) -> (p() & r()) -> (q() & r())".asFormula, prop)

  lazy val congrAndR: ProvableSig = proveBy("(p() -> q()) -> (r() & p()) -> (r() & q())".asFormula, prop)

  lazy val congrOrL: ProvableSig = proveBy("(p() -> q()) -> (p() | r()) -> (q() | r())".asFormula, prop)

  lazy val congrOrR: ProvableSig = proveBy("(p() -> q()) -> (r() | p()) -> (r() | q())".asFormula, prop)

  lazy val congrImpL: ProvableSig = proveBy("(p() -> q()) -> (q() -> r()) -> (p() -> r())".asFormula, prop)

  lazy val congrImpR: ProvableSig = proveBy("(p() -> q()) -> (r() -> p()) -> (r() -> q())".asFormula, prop)

  lazy val congrRefL: ProvableSig = proveBy(
    "a{|^@|}; <= b{|^@|}; -> b{|^@|}; <= c{|^@|}; -> a{|^@|}; <= c{|^@|};".asFormula,
    refTrans("b{|^@|};".asProgram)(1, 1 :: 1 :: Nil) & prop,
  )

  lazy val congrRefR: ProvableSig = proveBy(
    "a{|^@|}; <= b{|^@|}; -> c{|^@|}; <= a{|^@|}; -> c{|^@|}; <= b{|^@|};".asFormula,
    refTrans("a{|^@|};".asProgram)(1, 1 :: 1 :: Nil) & prop,
  )

  /**
   * focus(pos) pushes a *top-level* refinement/implication down to the indicated position
   *
   * {{{
   *   G |- C'{a; <= b;}, D
   *   ----------------------
   *   G |- C{a;} <= C{b;}, D
   * }}}
   *
   * {{{
   *   G |- C'{p -> q}, D
   *   ----------------------
   *   G |- C{p} -> C{q}, D
   * }}}
   * The context `C` can represent an arbitrary program. The resulting context `C'` is computed from `C` and only keeps
   * binders, i.e. `C'` is built using `[a]_` and `\forall x,_`.
   *
   * @note
   *   `pos` can refer to the position of either side (e.g. `a` or `b`) in the sequent.
   * @note
   *   The position of the hole in `C'` is computable via [[focusPos]]
   */
  def focus: BuiltInRightTactic = "focus".by { (provable: ProvableSig, pos: SuccPosition) =>
    require(provable.subgoals.size == 1, "Sole subgoal expected, but got " + provable.prettyString)
    val sequent = provable.subgoals.head
    val inEqPos = pos.inExpr.child
    sequent(pos.top) match {
      case Refinement(a, b) =>
        val (ctxA, e) = a.at(inEqPos)
        val (ctxB, _) = b.at(inEqPos)
        val dot = e match {
          case _: Formula => DotFormula
          case _: Program => DotProgram
          case _ => throw new TacticInapplicableFailure("Expected formula or program, but got " + e)
        }
        require(ctxA == ctxB, "Same context expected, but got " + ctxA + " and " + ctxB)
        Predef.assert(ctxA.ctx == ctxB.ctx, "Same context formula expected, but got " + ctxA.ctx + " and " + ctxB.ctx)
        provable(focusP(ctxA, pos.topLevel, dot), 0)
      case Imply(p, q) =>
        val (ctxA, e) = p.at(inEqPos)
        val (ctxB, _) = q.at(inEqPos)
        val dot = e match {
          case _: Formula => DotFormula
          case _: Program => DotProgram
          case _ => throw new TacticInapplicableFailure("Expected formula or program, but got " + e)
        }
        require(ctxA == ctxB, "Same context expected, but got " + ctxA + " and " + ctxB)
        Predef.assert(ctxA.ctx == ctxB.ctx, "Same context formula expected, but got " + ctxA.ctx + " and " + ctxB.ctx)
        provable(focusF(ctxA, pos.topLevel, dot), 0)
      case f => throw new TacticInapplicableFailure("Expected refinement or implication, but got " + f)
    }
  }

  @Derivation
  val focusInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "focus",
    displayPremises = "C'(a<=b)",
    displayConclusion = "C{a}<=C{b}",
    constructor = TacticConstructor0.create()(() => focus),
  )

  private[btactics] def focusF(ctx: Context[Formula], pos: Position, dot: NamedSymbol): BuiltInTactic =
    anon { (provable: ProvableSig) =>
      ctx.ctx match {
        case DotFormula => provable
        case Not(c) => provable(useAt(converseImply)(pos), 0)(focusF(Context(c), pos, dot), 0)
        case And(c, p) if !symbols(p).contains(dot) =>
          provable(useAt(congrAndL, PosInExpr(1 :: Nil))(pos), 0)(focusF(Context(c), pos, dot), 0)
        case And(p, c) if !symbols(p).contains(dot) =>
          provable(useAt(congrAndR, PosInExpr(1 :: Nil))(pos), 0)(focusF(Context(c), pos, dot), 0)
        case Or(c, p) if !symbols(p).contains(dot) =>
          provable(useAt(congrOrL, PosInExpr(1 :: Nil))(pos), 0)(focusF(Context(c), pos, dot), 0)
        case Or(p, c) if !symbols(p).contains(dot) =>
          provable(useAt(congrOrR, PosInExpr(1 :: Nil))(pos), 0)(focusF(Context(c), pos, dot), 0)
        case Imply(c, p) if !symbols(p).contains(dot) =>
          provable(useAt(congrImpL, PosInExpr(1 :: Nil))(pos), 0)(focusF(Context(c), pos, dot), 0)
        case Imply(p, c) if !symbols(p).contains(dot) =>
          provable(useAt(congrImpR, PosInExpr(1 :: Nil))(pos), 0)(focusF(Context(c), pos, dot), 0)
        case Forall(_, c) =>
          provable(useAt(allDistElim)(pos), 0)(focusF(Context(c), pos ++ PosInExpr(0 :: Nil), dot), 0)
        case Exists(_, c) =>
          provable(useAt(existsDistElim)(pos), 0)(focusF(Context(c), pos ++ PosInExpr(0 :: Nil), dot), 0)
        case Box(c, p) if !symbols(p).contains(dot) => provable(useAt(refBox)(pos), 0)(focusP(Context(c), pos, dot), 0)
        case Box(a, c) if !symbols(a).contains(dot) =>
          provable(useAt(K)(pos), 0)(focusF(Context(c), pos ++ PosInExpr(1 :: Nil), dot), 0)
        case Diamond(c, p) if !symbols(p).contains(dot) =>
          provable(useAt(refDiamond)(pos), 0)(focusP(Context(c), pos, dot), 0)
        case Diamond(a, c) if !symbols(a).contains(dot) =>
          provable(useAt(Kd)(pos), 0)(focusF(Context(c), pos ++ PosInExpr(1 :: Nil), dot), 0)
        case Refinement(c, a) if !symbols(a).contains(dot) =>
          provable(useAt(congrRefL, PosInExpr(1 :: Nil))(pos), 0)(focusP(Context(c), pos, dot), 0)
        case Refinement(a, c) if !symbols(a).contains(dot) =>
          provable(useAt(congrRefR, PosInExpr(1 :: Nil))(pos), 0)(focusP(Context(c), pos, dot), 0)
        case Equiv(_, _) | ProgramEquivalence(_, _) =>
          throw new TacticInapplicableFailure("No monotone congruence for equivalence. Try `focusEq` instead.")
        case _: ComparisonFormula | PredOf(_, _) =>
          throw new TacticInapplicableFailure("Focus down to Terms not implemented.")
        case DifferentialFormula(_) | PredicationalOf(_, _) => throw new TacticInapplicableFailure("Not implemented.")
        case And(_, _) | Or(_, _) | Imply(_, _) | Box(_, _) | Diamond(_, _) | Refinement(_, _) =>
          throw new TacticAssertionError(
            s"Context should contain only one ${dot.getClass.getSimpleName}, but is ${ctx}"
          )
        case False | True | UnitPredicational(_, _) =>
          throw new TacticAssertionError(s"Proper contexts have dots somewhere ${ctx}")

      }
    }

  private[btactics] def focusP(ctx: Context[Program], pos: Position, dot: NamedSymbol): BuiltInTactic =
    anon { (provable: ProvableSig) =>
      ctx.ctx match {
        case DotProgram => provable
        case Test(c) => provable(useAt(refTest)(pos), 0)(focusF(Context(c), pos, dot), 0)
        case Choice(c, a) if !symbols(a).contains(dot) =>
          provable(useAt(congrChoiceL, PosInExpr(1 :: Nil))(pos), 0)(focusP(Context(c), pos, dot), 0)
        case Choice(a, c) if !symbols(a).contains(dot) =>
          provable(useAt(congrChoiceR, PosInExpr(1 :: Nil))(pos), 0)(focusP(Context(c), pos, dot), 0)
        case Compose(c, a) if !symbols(a).contains(dot) =>
          provable(useAt(congrSeqL, PosInExpr(1 :: Nil))(pos), 0)(focusP(Context(c), pos, dot), 0)
        case Compose(a, c) if !symbols(a).contains(dot) =>
          provable(useAt(congrSeqR, PosInExpr(1 :: Nil))(pos), 0)(
            focusP(Context(c), pos ++ PosInExpr(1 :: Nil), dot),
            0,
          )
        case Loop(c) => provable(useAt(refUnloop, PosInExpr(1 :: Nil))(pos), 0)(
            focusP(Context(c), pos ++ PosInExpr(1 :: Nil), dot),
            0,
          )
        case ODESystem(ode, c) if !symbols(ode).contains(dot) =>
          provable(useAt(congrODEDom, PosInExpr(1 :: Nil))(pos), 0)(
            focusF(Context(c), pos ++ PosInExpr(1 :: Nil), dot),
            0,
          )

        case Dual(_) => throw new TacticInapplicableFailure("Not implemented for games")
        case Assign(_, _) | ODESystem(_, _) =>
          throw new TacticInapplicableFailure("Focus down to Terms not implemented.")
        case Choice(_, _) | Compose(_, _) => throw new TacticAssertionError(
            s"Context should contain only one ${dot.getClass.getSimpleName}, but is ${ctx}"
          )
        case AssignAny(_) | ProgramConst(_, _) | SystemConst(_, _) =>
          throw new TacticAssertionError(s"Proper contexts have dots somewhere ${ctx}")
        case _: DifferentialProgram => throw new TacticAssertionError("Expected non-differential program context")
      }
    }

  /**
   * Computes the updated position after applying [[focus]] along with an unreliable expression of C'.
   * @note
   *   When focusing inside of loops or ODEs, the context of [[focusPos]] may use the wrong program.
   */
  def focusPos(e: Expression, pos: PosInExpr): (PosInExpr, Context[Formula]) = {
    if (pos == HereP) { (pos, Context(DotFormula)) }
    else {
      val (expr, rec) = e match {
        case f: Modal if pos.head == 1 => (f.child, Some(Context(Box(f.program, DotFormula)), 1))
        case f: Quantified => (f.child, Some(Context(Forall(f.vars, DotFormula)), 0))
        case Compose(a, b) if pos.head == 1 => (b, Some(Context(Box(a, DotFormula)), 1))
        case Loop(a) => (a, Some(Context(Box(Loop(a), DotFormula)), 1))
        case ODESystem(c, f) => (f, Some(Context(Box(ODESystem(c, f), DotFormula)), 1))
        // Base cases
        case f: Modal => (f.program, None)
        case f: BinaryCompositeFormula =>
          if (pos.head == 0) { (f.left, None) }
          else { (f.right, None) }
        case f: ProgramComparison =>
          if (pos.head == 0) { (f.left, None) }
          else { (f.right, None) }
        case f: UnaryCompositeFormula => (f.child, None)
        case a: BinaryCompositeProgram =>
          if (pos.head == 0) { (a.left, None) }
          else { (a.right, None) }
        case Test(p) => (p, None)
        case _: Term | _: ComparisonFormula | Dual(_) | _: DifferentialProgram | _: Function | _: NamedSymbol | True |
            False | Assign(_, _) | AssignAny(_) | PredOf(_, _) | PredicationalOf(_, _) => ???
      }
      rec match {
        case None => focusPos(expr, pos.child)
        case Some((ctxt, updatePos)) =>
          val (posRec, ctxtRec) = focusPos(expr, pos.child)
          (PosInExpr(updatePos :: Nil) ++ posRec, ctxt(ctxtRec))
      }
    }
  }

  /**
   * When pointing to the ODE, removes the right conjunction of the domain, i.e. from `x'=f(x) & p(x) & q(x)` to
   * `x'=f(x) & p(x)`. If the transformation is not trivially correct (e.g. right side diamond), creates an additional
   * subgoal for proving its correction.
   */
  def dropODEr: DependentPositionTactic = "dropODEr".by { (pos: Position, sequent: Sequent) =>
    val (ctx, e) = sequent.at(pos)
    e match {
      case a @ ODESystem(sys, And(left, right)) =>
        val pol = polarityAt(sequent(pos.top), pos.inExpr) * (if (pos.isSucc) 1 else -1)
        if (pol < 0) {
          // Easy case: follows by congruence
          useAt(proveBy("p() & q() -> p()".asFormula, prop), PosInExpr(0 :: Nil))(pos ++ PosInExpr(1 :: Nil))
        } else if (pol > 0) {
          val newF = ctx(ODESystem(sys, left))
          domainUpdateAux(newF)(pos)
        } else { throw new TacticInapplicableFailure(s"ODE is at unknown polarity") }
      case ODESystem(_, dom) => throw new TacticInapplicableFailure(s"Expected conjunction in domain, but got $dom")
      case _ => throw new TacticInapplicableFailure(s"Expected ODE systems, but got $e")
    }
  }

  @Derivation
  val dropODErInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "dropODEr",
    displayNameLong = Some("Drop ODE domain constraint"),
    displayPremises = "x'=f(x) & p(x) & q(x)",
    displayConclusion = "x'=f(x) & p(x)",
    displayLevel = DisplayLevel.Menu,
    constructor = TacticConstructor0.create()(() => dropODEr),
  )

  def introduceODE(f: Formula): DependentPositionWithAppliedInputTactic = "introduceODE".byWithInputs(
    List(f),
    (pos: Position, sequent: Sequent) => {
      val (ctx, e) = sequent.at(pos)
      e match {
        case a @ ODESystem(sys, dom) =>
          val pol = polarityAt(sequent(pos.top), pos.inExpr) * (if (pos.isSucc) 1 else -1)
          if (pol > 0) {
            // Easy case: follows by congruence
            useAt(proveBy(Imply(And(dom, f), dom), prop), PosInExpr(1 :: Nil))(pos ++ PosInExpr(1 :: Nil))
          } else if (pol < 0) {
            val newF = ctx(ODESystem(sys, And(dom, f)))
            domainUpdateAux(newF)(pos)
          } else { throw new TacticInapplicableFailure(s"ODE is at unknown polarity") }
        case _ => throw new TacticInapplicableFailure(s"Expected ODE systems, but got $e")
      }
    },
  )

  def domainUpdateAux(newF: Formula): DependentPositionTactic = anon { (pos: Position, sequent: Sequent) =>
    if (pos.isSucc) {
      // Box case
      val postFocusPosinExpr = focusPos(sequent(pos.top), pos.inExpr)._1
      val postFocusPos = pos.topLevel ++ postFocusPosinExpr
      cutR(newF)(pos.checkSucc) & Idioms.<(
        // Transformed goal
        skip,
        // Additional proof required (remains open)
        // Focus down to the proof that `p() -> p() & q()` locally
        focus(pos.topLevel ++ PosInExpr(1 :: Nil) ++ pos.inExpr) & useAt(refDomainAx)(postFocusPos) &
          // Closes easy case for left side of the conjunction by dW
          useAt(boxAnd)(postFocusPos) & useAt(DWbase)(postFocusPos ++ PosInExpr(0 :: Nil)) &
          useAt(trueAnd)(postFocusPos),
      )
    } else {
      // Diamond case
      // cutL creates a new succedent, so we use [[LastSucc]] compared to `pos.topLevel` in the case above
      val preFocusPosLoc = LastSucc(0, PosInExpr(0 :: Nil) ++ pos.inExpr)
      val postFocusPosinExpr = focusPos(sequent(pos.top), pos.inExpr)._1
      val postFocusPosLoc = LastSucc(0, postFocusPosinExpr)
      val posLocLeft = LastSucc(0, postFocusPosinExpr ++ 0)
      cutL(newF)(pos.checkAnte) & Idioms.<(
        // Transformed goal
        skip,
        // Additional proof required (remains open), same as above
        focus(preFocusPosLoc) & useAt(refDomainAx)(postFocusPosLoc) & useAt(boxAnd)(postFocusPosLoc) &
          useAt(DWbase)(posLocLeft) & useAt(trueAnd)(postFocusPosLoc),
      )
    }
  }

  @Derivation
  val introduceODEInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "introduceODE",
    displayNameLong = Some("Introduce ODE domain constraint"),
    displayPremises = "x'=f(x) & p(x)",
    displayConclusion = "x'=f(x) & p(x) & Q",
    displayLevel = DisplayLevel.Menu,
    constructor = TacticConstructor1.create(FormulaArg("Q"))(introduceODE),
  )

}
