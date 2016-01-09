package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.bellerophon.{AntePosition, PosInExpr, Position, SuccPosition}
import Augmentors._
import StaticSemanticsTools._

import scala.language.postfixOps

/**
 * Tactics to rewrite equalities and introduce abbreviations.
 */
object EqualityTactics {

  /**
   * Rewrites a formula according to an equivalence appearing in the antecedent.
   * @note Uses propositional tactics instead of builtin rules.
   * @example{{{
   *   x>0 <-> y>0 |- y>0 | y<=0, x>0->z=1
   *   ------------------------------------equivRewriting(-1)(1)
   *   x>0 <-> y>0 |- x>0 | y<=0, x>0->z=1
   * }}}
   * @param eqPos The position where the equivalence appears in the antecedent.
   * @return The tactic.
   */
  def equivRewriting(eqPos: Int): DependentPositionTactic = equivRewriting(Position.convertPos(eqPos).asInstanceOf[AntePosition])
  def equivRewriting(eqPos: AntePosition): DependentPositionTactic = new DependentPositionTactic("Equivalence Rewriting") {
    override def factory(pos: Position): DependentTactic = new DependentTactic(name) {
      override def computeExpr(v: BelleValue): BelleExpr = v match {
        case BelleProvable(provable, _) =>
          require(eqPos.isTopLevel, "Equivalence to rewrite must occur in top-level position in antecedent")
          val sequent = provable.subgoals.head
          sequent.sub(eqPos) match {
            case Some(Equiv(a, b)) if a == sequent(pos) && !pos.isAnte =>
              equivL(eqPos) <(
                andL(eqPos) & closeId,
                (andL(eqPos) & ProofRuleTactics.hide(pos) & notL('Llast) & ProofRuleTactics.hide('Llast)) partial
              )
            case Some(Equiv(a, b)) if a == sequent(pos) && pos.isAnte =>
              equivL(eqPos) <(
                (andL(eqPos) &
                  (if (pos.index0 < eqPos.index0) ProofRuleTactics.hide(AntePosition(sequent.ante.length)) & ProofRuleTactics.hide(pos)
                  else ProofRuleTactics.hide(AntePosition(sequent.ante.length)) & ProofRuleTactics.hide(pos.advanceIndex(-1)))) partial,
                andL(eqPos) & notL('Llast) & notL('Llast) & closeId
              )
            case Some(Equiv(a, b)) if b == sequent(pos) && !pos.isAnte =>
              equivL(eqPos) <(
                andL(eqPos) & closeId,
                (andL(eqPos) & ProofRuleTactics.hide(pos) & notL(eqPos) & ProofRuleTactics.hide(eqPos)) partial
              )
            case Some(Equiv(a, b)) if b == sequent(pos) && pos.isAnte =>
              equivL(eqPos) <(
                (andL(eqPos) &
                  (if (pos.index0 < eqPos.index0) ProofRuleTactics.hide(AntePosition(sequent.ante.length + 1)) & ProofRuleTactics.hide(pos)
                  else ProofRuleTactics.hide(AntePosition(sequent.ante.length + 1)) & ProofRuleTactics.hide(pos.advanceIndex(-1)))) partial,
                andL(eqPos) & notL('Llast) & notL('Llast) & closeId
              )
          }
      }
    }
  }

  /**
   * Rewrites an equality exhaustively from right to left (i.e., replaces occurrences of left with right).
   * @note Base tactic for eqL2R and eqR2L.
   * @param name The name of the tactic.
   * @return The tactic.
   */
  private def exhaustiveEq(name: String): DependentPositionTactic = new DependentPositionTactic(name) {
    override def factory(pos: Position): DependentTactic = new DependentTactic(name) {
      override def computeExpr(v: BelleValue): BelleExpr = v match {
        case BelleProvable(provable, _) =>
          require(pos.isAnte && pos.isTopLevel, "Equality must be top-level in antecedent")
          val sequent = provable.subgoals.head
          sequent.sub(pos) match {
            case Some(eq@Equal(lhs, rhs)) =>
              // prevent endless self rewriting (e.g., 0=0) -> compute dependencies first to figure out what to rewrite when
              require(!lhs.isInstanceOf[Number] && lhs != rhs, "LHS and RHS are not allowed to overlap")

              val occurrences = positionsOf(lhs, sequent).filter(p => p.isAnte != pos.isAnte || p.index0 != pos.index0).
                filter(p => boundAt(sequent(p.top), p.inExpr).intersect(StaticSemantics.freeVars(lhs)).isEmpty)

              if (occurrences.isEmpty) {
                ident
              } else {
                eqL2R(pos)(occurrences.head.top) &
                  ?(exhaustiveEq(name)('L, eq))
              }
          }
      }
    }

    private def positionsOf(t: Term, s: Sequent): Set[Position] = {
      val ante = s.ante.zipWithIndex.flatMap({ case (f, i) => positionsOf(t, f).map(p => AntePosition.base0(i, p)) })
      val succ = s.succ.zipWithIndex.flatMap({ case (f, i) => positionsOf(t, f).map(p => SuccPosition.base0(i, p)) })
      (ante ++ succ).toSet
    }

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
  }

  /**
   * Rewrites a formula according to an equality appearing in the antecedent.
   * @example{{{
   *    x=0 |- 0*y=0, x+1>0
   *    ---------------------eqL2R(-1)(1)
   *    x=0 |- x*y=0, x+1>0
   * }}}
   * @param eqPos The position of the equality.
   * @return The tactic.
   */
  def eqL2R(eqPos: Int): DependentPositionTactic = eqL2R(Position.convertPos(eqPos))
  def eqL2R(eqPos: Position): DependentPositionTactic = new DependentPositionTactic("eqL2R") {
    override def factory(pos: Position): DependentTactic = new DependentTactic(name) {
      override def computeExpr(v: BelleValue): BelleExpr = v match {
        case BelleProvable(provable, _) =>
          val sequent = provable.subgoals.head
          sequent.sub(eqPos) match {
            case Some(eq@Equal(lhs, rhs)) =>
              val condEquiv = sequent.sub(pos) match {
                case Some(f: Formula) => Imply(eq, Equiv(f, SubstitutionHelper.replaceFree(f)(lhs, rhs)))
                case _ => throw new BelleError("Provable " + provable + " at position " + pos + " must be a formula")
              }
              cut(condEquiv) <(
                //@note could say equivRewriting('Llast) ??
                /* use */ (implyL('Llast) <(closeId, equivRewriting(AntePosition(sequent.ante.length + 1))(pos) partial)) partial,
                /* show */ cohide('Rlast) & byUS("const formula congruence")
                )
          }

      }
    }
  }

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
  def eqR2L(eqPos: Int): DependentPositionTactic = eqR2L(Position.convertPos(eqPos))
  def eqR2L(eqPos: Position): DependentPositionTactic = new DependentPositionTactic("eqR2L") {
    override def factory(pos: Position): DependentTactic = new DependentTactic(name) {
      override def computeExpr(v: BelleValue): BelleExpr = v match {
        case BelleProvable(provable, _) =>
          require(provable.subgoals.size == 1, "Exactly 1 subgoal expected, but got " + provable.subgoals.size)
          require(eqPos.isTopLevel, "Equality must be at top level, but is " + pos)
          val Equal(lhs, rhs) = provable.subgoals.head(eqPos)
          //@note need to search since eqL2R may alter the position of the equality
          useAt("= commute")(eqPos) & eqL2R(eqPos)(pos) &
            useAt("= commute")('L, Equal(rhs, lhs))
      }
    }
  }

  /**
   * Rewrites free occurrences of the left-hand side of an equality into the right-hand side exhaustively.
   * @example{{{
   *    x=2, 2+y=7 |- 2+1<y, [x:=3;]x>0
   *    --------------------------------exhaustiveEqR2L(-1)
   *    x=2, x+y=7 |- x+1<y, [x:=3;]x>0
   * }}}
   * @return The tactic.
   */
  lazy val exhaustiveEqL2R: DependentPositionTactic = exhaustiveEq("Find Left and Replace Left with Right")

  /**
   * Rewrites free occurrences of the right-hand side of an equality into the left-hand side exhaustively.
   * @example{{{
   *    2=x, 2+y=7 |- 2+1<y, [x:=3;]x>0
   *    --------------------------------exhaustiveEqR2L(-1)
   *    2=x, x+y=7 |- x+1<y, [x:=3;]x>0
   * }}}
   * @return The tactic.
   */
  lazy val exhaustiveEqR2L: DependentPositionTactic = new DependentPositionTactic("Find Right and Replace Right with Left") {
    override def factory(pos: Position): DependentTactic = new DependentTactic(name) {
      override def computeExpr(v: BelleValue): BelleExpr = v match {
        case BelleProvable(provable, _) =>
          require(provable.subgoals.size == 1, "Exactly 1 subgoal expected, but got " + provable.subgoals.size)
          require(pos.isTopLevel, "Equality must be at top level, but is " + pos)
          val Equal(lhs, rhs) = provable.subgoals.head(pos)
          //@note need to search since exhaustiveEq may alter the position of the equality
          useAt("= commute")(pos) & exhaustiveEq(name)(pos) &
            useAt("= commute")('L, Equal(rhs, lhs))
      }
    }
  }

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
  def abbrv(abbrvV: Variable): DependentPositionTactic = new DependentPositionTactic("abbrv") {
    override def factory(pos: Position): DependentTactic = new DependentTactic(name) {
      override def computeExpr(v: BelleValue): BelleExpr = v match {
        case BelleProvable(provable, _) =>
          val sequent = provable.subgoals.head
          sequent.sub(pos) match {
            case Some(t: Term) => abbrv(t, Some(abbrvV))
            case Some(e) => throw new BelleError("Expected a term at position " + pos + ", but got " + e)
            case _ => throw new BelleError("Position " + pos + " is undefined in sequent " + sequent)
          }

      }
    }
  }

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
            case FuncOf(Function(n, _, _, sort), _) => Variable(n, TacticHelper.freshIndexInSequent(n, sequent), sort)
            case Variable(n, _, sort) => Variable(n, TacticHelper.freshIndexInSequent(n, sequent), sort)
            case _ => Variable("x", TacticHelper.freshIndexInSequent("x", sequent), t.sort)
          }
        }

        cut(Exists(v :: Nil, Equal(v, t))) <(
          /* use */ (existsL('Llast) & exhaustiveEqR2L('Llast)) partial,
//          @note cannot use existsR because Unification match doesn't get it right yet
//          /* show */ cohide('Rlast) & existsR(t)(1) & byUS("= reflexive")
          /* show */ cohide('Rlast) & cut(Equiv(Exists(v :: Nil, Equal(v, t)), Equal(t, t))) <(
            /* use */ equivRewriting(-1)(1) & byUS("= reflexive"),
            /* show */ equivR('Rlast) <(
              closeId,
              FOQuantifierTactics.existsGeneralize(v, PosInExpr(0::Nil)::Nil)(-1) & closeId
            )
          )
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
  def abs: DependentPositionTactic = new DependentPositionTactic("abs") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = sequent.sub(pos) match {
        case Some(abs@FuncOf(Function(fn, None, Real, Real), _)) if fn == "abs" =>
          val freshAbsIdx = TacticHelper.freshIndexInSequent(fn, sequent)
          val absVar = Variable(fn, freshAbsIdx)

          abbrv(abs, Some(absVar)) &
            useAt("= commute")('L, Equal(absVar, abs)) &
            useAt(fn)('L, Equal(abs, absVar))
      }
    }
  }

  /**
   * Expands min/max function.
   * @example{{{
   *    x>=y&max_0=x | x<y&max_0=y  |- max_0=5
   *    ------------------------------------------max(1, 0::Nil)
   *                                |- max(x,y)=5
   * }}}
   * @return The tactic.
   */
  def minmax: DependentPositionTactic = new DependentPositionTactic("min/max") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = sequent.sub(pos) match {
        case Some(minmax@FuncOf(Function(fn, None, Tuple(Real, Real), Real), Pair(f, g))) if fn == "min" || fn == "max" =>
          val freshMinMaxIdx = TacticHelper.freshIndexInSequent(fn, sequent)
          val minmaxVar = Variable(fn, freshMinMaxIdx)

          abbrv(minmax, Some(minmaxVar)) &
            useAt("= commute")('L, Equal(minmaxVar, minmax)) &
            useAt(fn)('L, Equal(minmax, minmaxVar))
      }
    }
  }
}
