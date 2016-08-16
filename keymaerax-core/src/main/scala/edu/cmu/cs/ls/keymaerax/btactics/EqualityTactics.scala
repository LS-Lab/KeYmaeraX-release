package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.bellerophon.{AntePosition, PosInExpr, Position, SuccPosition}
import Augmentors._
import StaticSemanticsTools._

import scala.collection.immutable._
import scala.language.postfixOps

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
  private def exhaustiveEq(name: String): DependentPositionTactic = name by ((pos, sequent) => {
    require(pos.isAnte && pos.isTopLevel, "Equality must be top-level in antecedent")
    sequent.sub(pos) match {
      case Some(eq@Equal(lhs, rhs)) =>
        // prevent endless self rewriting (e.g., 0=0) -> compute dependencies first to figure out what to rewrite when
        require(!lhs.isInstanceOf[Number] && lhs != rhs, "LHS and RHS are not allowed to overlap")

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

  /**
   * Rewrites a formula according to an equality appearing in the antecedent.
   * @example{{{
   *    x=0 |- 0*y=0, x+1>0
   *    ---------------------eqL2R(-1)(1)
   *    x=0 |- x*y=0, x+1>0
   * }}}
   * @param eqPos The position of the equality. If it points to a formula, it rewrites all occurrences of left in that formula.
   *              If it points to a specific term, then only this term is rewritten.
   * @return The tactic.
   */
  def eqL2R(eqPos: Int): DependentPositionTactic = eqL2R(Position(eqPos).checkAnte)
  def eqL2R(eqPos: AntePosition): DependentPositionTactic = TacticFactory.anon ((pos:Position, sequent:Sequent) => {
    sequent.sub(eqPos) match {
      case Some(eq@Equal(lhs, rhs)) =>
        val (condEquiv@Imply(_, Equiv(_, repl)), dottedRepl) = sequent.sub(pos) match {
          case Some(f: Formula) =>
            (Imply(eq, Equiv(sequent(pos.top), sequent(pos.top).replaceAt(pos.inExpr, f.replaceFree(lhs, rhs)).asInstanceOf[Formula])),
              sequent(pos.top).replaceAt(pos.inExpr, f.replaceFree(lhs, DotTerm)))
          case Some(t: Term) if t == lhs =>
            (Imply(eq, Equiv(sequent(pos.top), sequent(pos.top).replaceAt(pos.inExpr, rhs).asInstanceOf[Formula])),
              sequent(pos.top).replaceAt(pos.inExpr, DotTerm))
          case Some(t: Term) if t != lhs =>
            (Imply(eq, Equiv(sequent(pos.top), sequent(pos.top).replaceAt(pos.inExpr, t.replaceFree(lhs, rhs)).asInstanceOf[Formula])),
              sequent(pos.top).replaceAt(pos.inExpr, t.replaceFree(lhs, DotTerm)))
        }

        //@note "stupid" order of cuts, since otherwise original formula not unambiguous from result (e.g., x=0, 0*y=0 ambiguous: was original formula x*y=x or x*y=0 or 0*y=x?)
        val (equivifyCommute, closeWhere, inverseImply) = if (pos.isSucc) (equivifyR(pos.top) & commuteEquivR(pos.top), Fixed(pos), implyRi(eqPos.top, pos.checkSucc.top)) else (equivifyR('Rlast), LastSucc(0), implyRi(eqPos.top, SuccPos(sequent.succ.length-1)))
        cut(condEquiv) <(
          /* use */ (implyL('Llast) <(closeIdWith('Rlast), cutLR(repl)(pos) <(hide('Llast) partial, equivifyCommute & closeIdWith(closeWhere)) partial) partial) partial,
          /* show */ cohide('Rlast) & by("const formula congruence", RenUSubst(
            (FuncOf(Function("s", None, Unit, Real), Nothing), lhs) ::
            (FuncOf(Function("t", None, Unit, Real), Nothing), rhs) ::
            (PredOf(Function("ctxF_", None, Real, Bool), DotTerm), dottedRepl) :: Nil))
          )
    }
  })

  /**
   * Rewrites a formula according to an equality appearing in the antecedent.
   * @example{{{
   *    0=x |- 0*y=0, x+1>0
   *    ---------------------eqR2L(-1)(1)
   *    0=x |- x*y=0, x+1>0
   * }}}
   * @param eqPos The position of the equality.
   * @return The tactic.
   */
  def eqR2L(eqPos: Int): DependentPositionTactic = eqR2L(Position(eqPos).checkAnte)
  def eqR2L(eqPos: AntePosition): DependentPositionTactic = "eqR2L" by ((pos, sequent) => {
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

  /**
   * Rewrites free occurrences of the right-hand side of an equality into the left-hand side exhaustively.
   * @example{{{
   *    2=x, 2+y=7 |- 2+1<y, [x:=3;]x>0
   *    --------------------------------exhaustiveEqR2L(-1)
   *    2=x, x+y=7 |- x+1<y, [x:=3;]x>0
   * }}}
   * @return The tactic.
   */
  lazy val exhaustiveEqR2L: DependentPositionTactic = "allL2R" by ((pos, sequent) => sequent.sub(pos) match {
    case Some(fml@Equal(lhs, rhs)) =>
      useAt("= commute")(pos, fml) & exhaustiveEq("allL2R")(pos, Equal(rhs, lhs)) & useAt("= commute")(pos, Equal(rhs, lhs))
  })


  /**
   * Abbreviates a term at a position to a variable.
   * @example{{{
   *   maxcd = max(c,d) |- a+b <= maxcd+e
   *   ----------------------------------------abbrv(Variable("maxcd"))(1, 1::0::Nil)
   *                    |- a+b <= max(c, d) + e
   * }}}
   * @param abbrvV The abbreviation.
   * @return The tactic.
   */
  def abbrv(abbrvV: Variable): DependentPositionTactic = "abbrv" by ((pos, sequent) => sequent.sub(pos) match {
    case Some(t: Term) => abbrv(t, Some(abbrvV))
    case Some(e) => throw new BelleError("Expected a term at position " + pos + ", but got " + e)
    case _ => throw new BelleError("Position " + pos + " is undefined in sequent " + sequent)
  })

  /**
   * Abbreviates a term to a variable.
   * @example{{{
   *   max_0 = max(c,d) |- a+b <= max_0+e
   *   ----------------------------------------abbrv("max(c,d)".asTerm)
   *                    |- a+b <= max(c, d) + e
   * }}}
   * @param abbrvV The abbreviation. If None, the tactic picks a name based on the top-level operator of the term.
   * @return The tactic.
   */
  def abbrv(t: Term, abbrvV: Option[Variable] = None): DependentTactic = new SingleGoalDependentTactic("abbrv") {
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
          /* use */ (existsL('Llast) & exhaustiveEqR2L('Llast)) partial,
          /* show */ cohide('Rlast) & existsR(t)(1) & byUS("= reflexive")
        )
    }
  }

  /**
   * Expands an absolute value function.
   * @example{{{
   *    x>=0&abs_0=x | x<0&abs_0=-x |- abs_0=5
   *    ---------------------------------------abs(1, 0::Nil)
   *                                |- abs(x)=5
   * }}}
   * @return The tactic.
   */
  def abs: DependentPositionTactic = "abs" by ((pos, sequent) => sequent.sub(pos) match {
    case Some(abs@FuncOf(Function(fn, None, Real, Real, true), _)) if fn == "abs" =>
      val freshAbsIdx = TacticHelper.freshIndexInSequent(fn, sequent)
      val absVar = Variable(fn, freshAbsIdx)

      abbrv(abs, Some(absVar)) &
        useAt("= commute")('L, Equal(absVar, abs)) &
        useAt(fn)('L, Equal(abs, absVar))
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
  def minmax: DependentPositionTactic = "min/max" by ((pos, sequent) => sequent.sub(pos) match {
    case Some(minmax@FuncOf(Function(fn, None, Tuple(Real, Real), Real, true), Pair(f, g))) if fn == "min" || fn == "max" =>
      val freshMinMaxIdx = TacticHelper.freshIndexInSequent(fn, sequent)
      val minmaxVar = Variable(fn, freshMinMaxIdx)

      abbrv(minmax, Some(minmaxVar)) &
        useAt("= commute")('L, Equal(minmaxVar, minmax)) &
        useAt(fn)('L, Equal(minmax, minmaxVar))
  })
}
