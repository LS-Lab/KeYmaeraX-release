package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms.?
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.bellerophon.{AntePosition, PosInExpr, Position, SuccPosition}
import Augmentors._
import StaticSemanticsTools._

import scala.collection.immutable._

/**
 * Implementation: Tactics to rewrite equalities and introduce abbreviations.
  *
 */
private object EqualityTactics {

  /**
   * Rewrites an equality exhaustively from right to left (i.e., replaces occurrences of left with right).
   * @note Base tactic for eqL2R and eqR2L.
   * @param name The name of the tactic.
   * @return The tactic.
   */
  private def exhaustiveEq(name: String): DependentPositionTactic = name by ((pos: Position, sequent: Sequent) => {
    require(pos.isAnte && pos.isTopLevel, "Equality must be top-level in antecedent")
    sequent.sub(pos) match {
      case Some(eq@Equal(lhs, rhs)) =>
        // prevent endless self rewriting (e.g., 0=0) -> compute dependencies first to figure out what to rewrite when
        require(!lhs.isInstanceOf[Number], "Rewriting numbers not supported")
        require(lhs != rhs, "LHS and RHS are not allowed to overlap")

        val occurrences = positionsOf(lhs, sequent).filter(p => p.isAnte != pos.isAnte || p.index0 != pos.index0).
          filter(p => boundAt(sequent(p.top), p.inExpr).intersect(StaticSemantics.freeVars(lhs)).isEmpty).map(_.top).toList

        if (occurrences.isEmpty) skip
        else occurrences.map(eqL2R(pos.checkAnte)(_)).reduce[BelleExpr](_&_)
    }
  })

  /** Computes the positions of term t in sequent s */
  private def positionsOf(t: Term, s: Sequent): Set[Position] = {
    val ante = s.ante.zipWithIndex.flatMap({ case (f, i) => positionsOf(t, f).map(p => AntePosition.base0(i, p)) })
    val succ = s.succ.zipWithIndex.flatMap({ case (f, i) => positionsOf(t, f).map(p => SuccPosition.base0(i, p)) })
    (ante ++ succ).toSet
  }

  /** Computes the positions of term t in formula fml */
  private def positionsOf(t: Term, fml: Formula): Set[PosInExpr] = {
    var positions: Set[PosInExpr] = Set.empty
    ExpressionTraversal.traverse(new ExpressionTraversal.ExpressionTraversalFunction {
      override def preT(p: PosInExpr, e: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = {
        if (e == t && !positions.exists(_.isPrefixOf(p))) positions += p
        Left(None)
      }
    }, fml)
    positions
  }

  /** @see [[TactixLibrary.eqL2R]] */
  def eqL2R(eqPos: Int): DependentPositionTactic = eqL2R(Position(eqPos).checkAnte)
  def eqL2R(eqPos: AntePosition): DependentPositionTactic = TacticFactory.anon ((pos:Position, sequent:Sequent) => {
    sequent.sub(eqPos) match {
      case Some(eq@Equal(lhs, rhs)) =>
        val (condEquiv@Imply(_, Equiv(_, repl)), dottedRepl) = sequent.sub(pos) match {
          case Some(f: Formula) =>
            (Imply(eq, Equiv(sequent(pos.top), sequent(pos.top).replaceAt(pos.inExpr, f.replaceFree(lhs, rhs)))),
              sequent(pos.top).replaceAt(pos.inExpr, f.replaceFree(lhs, DotTerm())))
          case Some(t: Term) if t == lhs =>
            (Imply(eq, Equiv(sequent(pos.top), sequent(pos.top).replaceAt(pos.inExpr, rhs))),
              sequent(pos.top).replaceAt(pos.inExpr, DotTerm()))
          case Some(t: Term) if t != lhs =>
            (Imply(eq, Equiv(sequent(pos.top), sequent(pos.top).replaceAt(pos.inExpr, t.replaceFree(lhs, rhs)))),
              sequent(pos.top).replaceAt(pos.inExpr, t.replaceFree(lhs, DotTerm())))
        }

        //@note "stupid" order of cuts, since otherwise original formula not unambiguous from result (e.g., x=0, 0*y=0 ambiguous: was original formula x*y=x or x*y=0 or 0*y=x?)
        val (equivifyCommute, closeWhere, inverseImply) = if (pos.isSucc) (equivifyR(pos.top) & commuteEquivR(pos.top), Fixed(pos), implyRi()(eqPos, pos)) else (equivifyR('Rlast), LastSucc(0), implyRi()(eqPos, SuccPosition.base0(sequent.succ.length-1)))
        cut(condEquiv) <(
          /* use */ (implyL('Llast) <(closeIdWith('Rlast), cutLR(repl)(pos) <(hide('Llast) partial, equivifyCommute & closeIdWith(closeWhere)) partial) partial) partial,
          /* show */ cohide('Rlast) & by("const formula congruence", RenUSubst(
            (FuncOf(Function("s", None, Unit, Real), Nothing), lhs) ::
            (FuncOf(Function("t", None, Unit, Real), Nothing), rhs) ::
            (PredOf(Function("ctxF_", None, Real, Bool), DotTerm()), dottedRepl) :: Nil))
          )
    }
  })

  /** @see [[TactixLibrary.eqR2L]] */
  def eqR2L(eqPos: Int): DependentPositionTactic = eqR2L(Position(eqPos).checkAnte)
  def eqR2L(eqPos: AntePosition): DependentPositionTactic = "eqR2L" by ((pos: Position, sequent: Sequent) => {
    require(eqPos.isTopLevel, "Equality must be at top level, but is " + pos)
    sequent.sub(eqPos) match {
      case Some(Equal(lhs, rhs)) =>
        useAt("= commute")(eqPos) & eqL2R(eqPos)(pos) & useAt("= commute")('L, Equal(rhs, lhs))
    }
  })

  /**
   * Rewrites free occurrences of the left-hand side of an equality into the right-hand side exhaustively.
   * @example{{{
   *    x=2, 2+y=7 |- 2+1<y, [x:=3;]x>0
   *    --------------------------------exhaustiveEqR2L(-1)
   *    x=2, x+y=7 |- x+1<y, [x:=3;]x>0
   * }}}
   * @return The tactic.
   */
  lazy val exhaustiveEqL2R: DependentPositionTactic = exhaustiveEq("allL2R")

  /* Rewrites equalities exhaustively with hiding, but only if left-hand side is an atom (variable or uninterpreted function) */
  def atomExhaustiveEqL2R: DependentPositionTactic = "atomAllL2R" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(fml@Equal(_: Variable, _)) => EqualityTactics.exhaustiveEqL2R(pos) & hideL(pos, fml)
    case Some(fml@Equal(FuncOf(Function(_, _, _, _, false), _), _)) => EqualityTactics.exhaustiveEqL2R(pos) & hideL(pos, fml)
  })

  /**
   * Rewrites free occurrences of the right-hand side of an equality into the left-hand side exhaustively.
   * @example{{{
   *    2=x, 2+y=7 |- 2+1<y, [x:=3;]x>0
   *    --------------------------------exhaustiveEqR2L(-1)
   *    2=x, x+y=7 |- x+1<y, [x:=3;]x>0
   * }}}
   * @return The tactic.
   */
  lazy val exhaustiveEqR2L: DependentPositionTactic = "allR2L" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(fml@Equal(lhs, rhs)) =>
      useAt("= commute")(pos, fml) & exhaustiveEq("allL2R")(pos, Equal(rhs, lhs)) & useAt("= commute")(pos, Equal(rhs, lhs))
  })


  /** @see [[TactixLibrary.abbrv()]] */
  def abbrv(abbrvV: Variable): DependentPositionTactic = "abbrv" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(t: Term) => abbrv(t, Some(abbrvV))
    case Some(e) => throw new BelleThrowable("Expected a term at position " + pos + ", but got " + e)
    case _ => throw new BelleThrowable("Position " + pos + " is undefined in sequent " + sequent)
  })

  /**
   * Abbreviates a term `t` to a variable everywhere, except in places where some free variable of `t` is bound.
    *
    * @example{{{
   *   max_0 = max(c,d) |- a+b <= max_0+e
   *   ----------------------------------------abbrv("max(c,d)".asTerm)
   *                    |- a+b <= max(c, d) + e
   * }}}
    * @example { { {
    * *   e = max(c,d), e <= 7 |- [c:=2;]max(c, d) >= 2
    * *   ---------------------------------------------abbrv("max(c,d)".asTerm, Some("e".asVariable))
    * *         max(c, d) <= 7 |- [c:=2;]max(c, d) >= 2
    * * }}}
   * @param abbrvV The abbreviation. If None, the tactic picks a name based on the top-level operator of the term.
   * @return The tactic.
   */
  def abbrv(t: Term, abbrvV: Option[Variable] = None): InputTactic = new InputTactic("abbrv",
      abbrvV match { case Some(v) => t::v::Nil case None => t::Nil }) {
    def computeExpr(): BelleExpr = new SingleGoalDependentTactic(name) {
      def computeExpr(sequent: Sequent): BelleExpr = {
        require(abbrvV.isEmpty ||
          !(sequent.ante.flatMap(StaticSemantics.signature)
            ++ sequent.succ.flatMap(StaticSemantics.signature)).contains(abbrvV.get),
          "Abbreviation must be fresh in sequent")
        val v = abbrvV match {
          case Some(vv) => vv
          case None => t match {
            case FuncOf(Function(n, _, _, sort,_), _) => Variable(n, TacticHelper.freshIndexInSequent(n, sequent), sort)
            case BaseVariable(n, _, sort) => Variable(n, TacticHelper.freshIndexInSequent(n, sequent), sort)
            case _ => Variable("x", TacticHelper.freshIndexInSequent("x", sequent), t.sort)
          }
        }

        cut(Exists(v :: Nil, Equal(v, t))) <(
          /* use */ existsL('Llast) & exhaustiveEqR2L('Llast),
          /* show */ cohide('Rlast) & existsR(t)(1) & byUS("= reflexive")
        )
      }
    }
  }

  /**
    * Abbreviates a term to a variable at a position.
    * @example{{{
    *   |- [x:=2;]\exists z (z=min(x,y) & z<=2)
    *   ---------------------------------------abbrvAt("min(x,y)".asTerm, Some("z".asVariable)(1,1::Nil)
    *   |- [x:=2;]min(x,y) <= 2
    * }}}
    * @param abbrvV The abbreviation. If None, the tactic picks a name based on the top-level operator of the term.
    * @return The tactic.
    */
  def abbrvAt(t: Term, abbrvV: Option[Variable] = None): DependentPositionWithAppliedInputTactic = "abbrvAt" byWithInputs(
    abbrvV match { case Some(v) => t::v::Nil case None => t::Nil }, (pos: Position, sequent: Sequent) => {
      val inFml = sequent.sub(pos) match {
        case Some(p: Formula) => p
        case Some(t: Term) => throw BelleTacticFailure("Position " + pos + " expected to point to a formula, but points to term " + t.prettyString)
        case _ => throw BelleIllFormedError("Position " + pos + " does not point to an expression")
      }
      require(abbrvV.isEmpty ||
        !sequent.sub(pos).map(StaticSemantics.signature).contains(abbrvV.get),
        "Abbreviation must be fresh at position")
      val v = abbrvV match {
        case Some(vv) => vv
        case None => t match {
          case FuncOf(Function(n, _, _, sort,_), _) => Variable(n, TacticHelper.freshIndexInSequent(n, sequent), sort)
          case BaseVariable(n, _, sort) => Variable(n, TacticHelper.freshIndexInSequent(n, sequent), sort)
          case _ => Variable("x", TacticHelper.freshIndexInSequent("x", sequent), t.sort)
        }
      }

      val polarity = FormulaTools.polarityAt(sequent(pos.top), pos.inExpr) * (if (pos.isSucc) 1 else -1)

      val cutFml =
        if (polarity >= 0) /* positive and unknown polarity */ Forall(v :: Nil, Imply(Equal(v, t), inFml.replaceFree(t, v)))
        else Exists(v :: Nil, And(Equal(v, t), inFml.replaceFree(t, v)))

      val cohidePos = if (pos.isAnte) cohide('Rlast) else cohide(pos.top)

      cutAt(cutFml)(pos) <(
        /* use */ skip,
        /* show */ cohidePos & CMon(pos.inExpr) & implyR(1) &
        (if (polarity >= 0) allL(t)(-1) & implyL(-1) <(cohide(2) & byUS(DerivedAxioms.equalReflex), closeId)
         else existsR(t)(1) & andR(1) <(cohide(1) & byUS(DerivedAxioms.equalReflex), closeId)) &
        done
      )
  })

  /**
   * Expands an absolute value function.
   * @example{{{
   *    x>=0&abs_0=x | x<0&abs_0=-x |- abs_0=5
   *    ---------------------------------------abs(1, 0::Nil)
   *                                |- abs(x)=5
   * }}}
   * @return The tactic.
   */
  def abs: DependentPositionTactic = "absExp" by ((pos: Position, sequent: Sequent) => sequent.at(pos) match {
    case (ctx, abs@FuncOf(Function(fn, None, Real, Real, true), t)) if fn == "abs" =>
      if (StaticSemantics.boundVars(ctx.ctx).intersect(StaticSemantics.freeVars(t)).isEmpty) {
        val freshAbsIdx = TacticHelper.freshIndexInSequent(fn, sequent)
        val absVar = Variable(fn, freshAbsIdx)
        abbrv(abs, Some(absVar)) &
          useAt("= commute")('L, Equal(absVar, abs)) &
          useAt(fn)('L, Equal(abs, absVar))
      } else {
        absAt(pos)
      }
  })
  /** Expands abs only at a specific position (also works in contexts that bind the argument of abs). */
  def absAt: DependentPositionTactic = "ANON" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(abs@FuncOf(Function(fn, None, Real, Real, true), _)) if fn == "abs" =>
      val freshAbsIdx = TacticHelper.freshIndexInSequent(fn, sequent)
      val absVar = Variable(fn, freshAbsIdx)

      val parentPos = parentFormulaPos(pos, sequent)

      abbrvAt(abs, Some(absVar))(parentFormulaPos(pos, sequent)) &
        (if (parentPos.isTopLevel && parentPos.isSucc) {
          allR(parentPos) & implyR(parentPos) &
          useAt("= commute")('Llast, Equal(absVar, abs)) &
          useAt(fn)('Llast, Equal(abs, absVar))
        } else if (parentPos.isTopLevel && parentPos.isAnte) {
          existsL(parentPos) & andL(parentPos) &
          useAt("= commute")('L, Equal(absVar, abs)) &
          useAt(fn)('L, Equal(abs, absVar))
        } else {
          val inContextEqPos = pos.topLevel ++ (pos.inExpr.parent ++ PosInExpr(0 :: 0 :: Nil))
          useAt(DerivedAxioms.equalCommute)(inContextEqPos) & useAt(fn)(inContextEqPos)
        }
        )
  })

  /**
   * Expands min/max function.
   * @example{{{
   *    x>=y&max_0=x | x<y&max_0=y  |- max_0=5
   *    ------------------------------------------max(1, 0::Nil)
   *                                |- max(x,y)=5
   * }}}
   * @return The tactic.
   */
  def minmax: DependentPositionTactic = "minmax" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(minmax@FuncOf(Function(fn, None, Tuple(Real, Real), Real, true), Pair(f, g))) if fn == "min" || fn == "max" =>
      val freshMinMaxIdx = TacticHelper.freshIndexInSequent(fn, sequent)
      val minmaxVar = Variable(fn, freshMinMaxIdx)

      abbrv(minmax, Some(minmaxVar)) &
        useAt("= commute")('L, Equal(minmaxVar, minmax)) &
        useAt(fn)('L, Equal(minmax, minmaxVar))
  })
  /** Expands min/max only at a specific position (also works in contexts that bind some of the arguments). */
  def minmaxAt: DependentPositionTactic = "ANON" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(minmax@FuncOf(Function(fn, None, Tuple(Real, Real), Real, true), Pair(f, g))) if fn == "min" || fn == "max" =>
      val freshMinMaxIdx = TacticHelper.freshIndexInSequent(fn, sequent)
      val minmaxVar = Variable(fn, freshMinMaxIdx)

      val parentPos = parentFormulaPos(pos, sequent)

      abbrvAt(minmax, Some(minmaxVar))(parentFormulaPos(pos, sequent)) &
        (if (parentPos.isTopLevel && parentPos.isSucc) {
          allR(parentPos) & implyR(parentPos) &
          useAt("= commute")('Llast, Equal(minmaxVar, minmax)) &
          useAt(fn)('Llast, Equal(minmax, minmaxVar))
        } else if (parentPos.isTopLevel && parentPos.isAnte) {
          existsL(parentPos) & andL(parentPos) &
          useAt("= commute")('L, Equal(minmaxVar, minmax)) &
          useAt(fn)('L, Equal(minmax, minmaxVar))
        } else {
          val inContextEqPos = pos.topLevel ++ (pos.inExpr.parent ++ PosInExpr(0 :: 0 :: Nil))
          useAt(DerivedAxioms.equalCommute)(inContextEqPos) & useAt(fn)(inContextEqPos)
        }
        )
  })

  /** Expands all special functions (abs/min/max). */
  def expandAll: BelleExpr = "expandAll" by ((s: Sequent) => {
    val allTopPos = s.ante.indices.map(i => AntePos(i)) ++ s.succ.indices.map(i => SuccPos(i))
    val tactics = allTopPos.flatMap(p =>
      Idioms.mapSubpositions(p, s, {
        case (FuncOf(Function("abs", _, _, _, true), _), pos: Position) => Some(?(abs(pos)))
        case (FuncOf(Function("min", _, _, _, true), _), pos: Position) => Some(?(minmax(pos)))
        case (FuncOf(Function("max", _, _, _, true), _), pos: Position) => Some(?(minmax(pos)))
        case _ => None
      })
    )
    tactics.reduceOption(_ & _).getOrElse(skip)
  })

  private def parentFormulaPos(pos: Position, seq: Sequent): Position =
    if (pos.isTopLevel) pos
    else seq.sub(pos) match {
      case Some(_: Formula) => pos
      case Some(_) => pos.topLevel ++ pos.inExpr.parent
    }
}
