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
import org.keymaerax.btactics.macros.{DerivedAxiomInfo, DisplayLevel, PositionTacticInfo, TacticConstructor0}
import org.keymaerax.core.*
import org.keymaerax.core.StaticSemantics.symbols
import org.keymaerax.core.btactics.annotations.Derivation
import org.keymaerax.infrastruct.Augmentors.{FormulaAugmentor, ProgramAugmentor, SequentAugmentor}
import org.keymaerax.infrastruct.FormulaTools.polarityAt
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
  def focusInfo: PositionTacticInfo = PositionTacticInfo.create(
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
}
