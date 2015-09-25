/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tactics

import ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.ArithmeticTacticsImpl.EqualReflexiveT
import edu.cmu.cs.ls.keymaerax.tactics.FormulaConverter._
import edu.cmu.cs.ls.keymaerax.tactics.ContextTactics.replaceInContext
import edu.cmu.cs.ls.keymaerax.tactics.FOQuantifierTacticsImpl.{instantiateT, skolemizeT}
import edu.cmu.cs.ls.keymaerax.tactics.PropositionalTacticsImpl.{cutT, EquivLeftT}
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl.{lastSucc,locateAnte}
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.TacticHelper
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.{ConstructionTactic, PositionTactic, Tactic, NilPT, NilT}
import PropositionalTacticsImpl._
import BranchLabels._
import SearchTacticsImpl.{lastAnte,onBranch}
import edu.cmu.cs.ls.keymaerax.tactics.AxiomTactic.{uncoverConditionalAxiomT,uncoverConditionalTermAxiomT,axiomLookupBaseT}
import TacticLibrary.TacticHelper.getTerm
import edu.cmu.cs.ls.keymaerax.tools.Tool

import scala.collection.immutable.Set

/**
 * Implementation of equality rewriting.
 */
object EqualityRewritingImpl {
  /**
   * Returns a new tactic for rewriting a formula in the succedent according to an equivalence appearing in the
   * antecedent. Uses propositional tactics instead of builtin rules.
   * @param eqPos The position where the equivalence appears in the antecedent.
   * @param p The position where to rewrite in the succedent.
   * @return The newly created tactic.
   */
  def equivRewriting(eqPos: Position, p: Position): Tactic =
    new ConstructionTactic("Equivalence Rewriting") {
    override def applicable(node: ProofNode): Boolean = eqPos.isAnte && eqPos.isTopLevel && p.isTopLevel &&
      (node.sequent(eqPos) match {
        case Equiv(_, _) => true
        case _ => false
    })

    def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(eqPos) match {
      case Equiv(a, b) if a == node.sequent(p) && !p.isAnte =>
        Some(EquivLeftT(eqPos) & onBranch(
          (equivLeftLbl, AndLeftT(eqPos) & AxiomCloseT),
          (equivRightLbl, AndLeftT(eqPos) & hideT(p) & NotLeftT(AntePos(node.sequent.ante.length)) & hideT(AntePos(node.sequent.ante.length - 1)))
        ))
      case Equiv(a, b) if a == node.sequent(p) && p.isAnte =>
        Some(EquivLeftT(eqPos) & onBranch(
          (equivLeftLbl, AndLeftT(eqPos) &
            (if (p.index < eqPos.index) hideT(AntePosition(node.sequent.ante.length - 1)) & hideT(p)
             else hideT(AntePosition(node.sequent.ante.length - 1)) & hideT(AntePosition(p.index - 1)))),
          (equivRightLbl, AndLeftT(eqPos) & lastAnte(NotLeftT) & lastAnte(NotLeftT) & AxiomCloseT)
        ))
      case Equiv(a, b) if b == node.sequent(p) && !p.isAnte =>
        Some(EquivLeftT(eqPos) & onBranch(
          (equivLeftLbl, AndLeftT(eqPos) & AxiomCloseT),
          (equivRightLbl, AndLeftT(eqPos) & hideT(p) & NotLeftT(eqPos) & hideT(eqPos))
        ))
      case Equiv(a, b) if b == node.sequent(p) && p.isAnte =>
        Some(EquivLeftT(eqPos) & onBranch(
          (equivLeftLbl, AndLeftT(eqPos) &
            (if (p.index < eqPos.index) hideT(AntePosition(node.sequent.ante.length)) & hideT(p)
             else hideT(AntePosition(node.sequent.ante.length)) & hideT(AntePosition(p.index - 1)))),
          (equivRightLbl, AndLeftT(eqPos) & lastAnte(NotLeftT) & lastAnte(NotLeftT) & AxiomCloseT)
        ))
      case _ => None
    }
  }

  def constFormulaCongruenceT(eqPos: Position, left: Boolean, exhaustive: Boolean = true): PositionTactic = new PositionTactic("const formula congruence") {
    override def applies(s: Sequent, p: Position): Boolean = eqPos.isAnte && eqPos.isTopLevel && (s(eqPos) match {
      case Equal(lhs, rhs) if !exhaustive &&  left => getTerm(s, p) == lhs
      case Equal(lhs, rhs) if !exhaustive && !left => getTerm(s, p) == rhs
      case Equal(lhs, rhs) if  exhaustive => true
      case _ => false
    })

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(eqPos) match {
        case Equal(lhs, rhs) =>
          if (exhaustive) {
            def axiomInstance(f: Formula): Formula = {
              val cond = node.sequent(eqPos)
              if (left) Imply(cond, Equiv(node.sequent(p), SubstitutionHelper.replaceFree(node.sequent(p))(lhs, rhs)))
              else      Imply(cond, Equiv(node.sequent(p), SubstitutionHelper.replaceFree(node.sequent(p))(rhs, lhs)))
            }
            Some(uncoverConditionalAxiomT("const formula congruence", axiomInstance, _ => constFormulaCongruenceCondT,
              _ => constFormulaCongruenceBaseT(left, p.inExpr, exhaustive))(p))
          } else {
            def axiomInstance(t: Term): Formula = {
              val cond = node.sequent(eqPos)
              if (exhaustive && left) Imply(cond, Equiv(node.sequent(p), SubstitutionHelper.replaceFree(node.sequent(p))(lhs, rhs)))
              if (exhaustive && !left) Imply(cond, Equiv(node.sequent(p), SubstitutionHelper.replaceFree(node.sequent(p))(rhs, lhs)))
              else Imply(cond, replaceInContext(node.sequent(p), node.sequent(eqPos), p.inExpr))
            }
            Some(uncoverConditionalTermAxiomT("const formula congruence", axiomInstance, _ => constFormulaCongruenceCondT,
              _ => constFormulaCongruenceBaseT(left, p.inExpr, exhaustive))(p))
          }
      }
    }
  }
  /** Shows condition in const formula congruence */
  private def constFormulaCongruenceCondT: PositionTactic = new PositionTactic("const formula congruence cond") {
    override def applies(s: Sequent, p: Position): Boolean = true
    override def apply(p: Position): Tactic = AxiomCloseT
  }
  /** Base tactic for const formula congruence */
  private def constFormulaCongruenceBaseT(isLeft: Boolean, where: PosInExpr, exhaustive: Boolean): PositionTactic = new PositionTactic("const formula congruence base") {
    override def applies(s: Sequent, p: Position): Boolean = true

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        def subst(fml: Formula): List[SubstitutionPair] = fml match {
          case Imply(Equal(s, t), Equiv(lhs, rhs)) =>
            val aS = FuncOf(Function("s", None, Unit, Real), Nothing)
            val aT = FuncOf(Function("t", None, Unit, Real), Nothing)
            val aCtx = PredOf(Function("ctxF_", None, Real, Bool), DotTerm)

            if (exhaustive) {
              val substF = if (isLeft) lhs else rhs
              SubstitutionPair(aS, s) :: SubstitutionPair(aT, t) ::
                SubstitutionPair(aCtx, SubstitutionHelper.replaceFree(substF)(if (isLeft) s else t, DotTerm)) :: Nil
            } else {
              // does not check whether substituting is admissible! use with caution, tactic will result in substitution clashes
              val ctx = if (isLeft) lhs.replaceAt(s, where, DotTerm) else rhs.replaceAt(t, where, DotTerm)
              SubstitutionPair(aS, s) :: SubstitutionPair(aT, t) :: SubstitutionPair(aCtx, ctx) :: Nil
            }
        }
        Some(axiomLookupBaseT("const formula congruence", subst, _ => NilPT, (f, ax) => ax)(p))
      }
    }
  }

  /**
   * Creates a new tactic to rewrite an equality.
   * @param name The name of the tactic.
   * @param left If true: rewrite right to left; if false: rewrite left to right
   * @param exhaustive Indicates whether to rewrite exhaustively.
   * @return The new tactic.
   */
  private def eqPos(name: String, left: Boolean, exhaustive: Boolean): PositionTactic = new PositionTactic(name) {
    import scala.language.postfixOps
    override def applies(s: Sequent, p: Position): Boolean = p.isAnte && (s(p) match {
      case Equal(lhs, rhs) =>
        val what = if (left) lhs else rhs
        val repl = if (left) rhs else lhs
        // prevent endless self rewriting (e.g., 0=0) -> compute dependencies first to figure out what to rewrite when
        !what.isInstanceOf[Number] && what != repl &&
        StaticSemantics.symbols(what).intersect(StaticSemantics.symbols(repl)).isEmpty &&
          positionsOf(what, s).exists(pos => (pos.isAnte != p.isAnte || pos.index != p.index) &&
            StaticSemanticsTools.boundAt(s(pos), pos.inExpr).intersect(StaticSemantics.freeVars(what)).isEmpty)
      case _ => false
    })

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
        case eq@Equal(lhs, rhs) =>
          val what = if (left) lhs else rhs
          val repl = if (left) rhs else lhs
          assert(!what.isInstanceOf[Number] && what != repl)
          // positions are not stable, so we need to search over and over again (we even need to search eqPos, since it
          // may shift)
          val occurrences = positionsOf(what, node.sequent).filter(pos => pos.isAnte != p.isAnte || pos.index != p.index).
            filter(pos => StaticSemanticsTools.boundAt(node.sequent(pos), pos.inExpr).intersect(StaticSemantics.freeVars(what)).isEmpty)
          if (exhaustive) {
            Some(constFormulaCongruenceT(p, left=left, exhaustive=false)(occurrences.head) &
              (locateAnte(eqPos(name, left, exhaustive), _ == eq) | NilT))
          } else {
            Some(constFormulaCongruenceT(p, left=left, exhaustive=false)(occurrences.head))
          }
      }
    }

    def positionsOf(t: Term, fml: Formula): Set[PosInExpr] = {
      var positions: Set[PosInExpr] = Set.empty
      ExpressionTraversal.traverse(new ExpressionTraversalFunction {
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
          if (e == t && !positions.exists(_.isPrefixOf(p))) positions += p
          Left(None)
        }
      }, fml)
      positions
    }

    def positionsOf(t: Term, s: Sequent): Set[Position] = {
      val ante = s.ante.zipWithIndex.flatMap({ case (f, i) => positionsOf(t, f).map(p => AntePosition(i, p)) })
      val succ = s.succ.zipWithIndex.flatMap({ case (f, i) => positionsOf(t, f).map(p => SuccPosition(i, p)) })
      (ante ++ succ).toSet
    }
  }

  /**
   * Creates a new tactic to rewrite occurrences of the left-hand side of an equality into the right-hand side.
   * @param exhaustive True: apply exhaustively; false: apply only once at the first occurrence found.
   * @return The new tactic.
   */
  def eqLeft(exhaustive: Boolean): PositionTactic = eqPos("Find Left and Apply Right to Left", left=true, exhaustive=exhaustive)
  /**
   * Creates a new tactic to rewrite occurrences of the right-hand side of an equality into the left-hand side.
   * @param exhaustive True: apply exhaustively; false: apply only once at the first occurrence found.
   * @return The new tactic.
   */
  def eqRight(exhaustive: Boolean): PositionTactic = eqPos("Find Right and Apply Left to Right", left=false, exhaustive=exhaustive)

  /**
   * Abbreviates a term at a position to a variable.
   * @example{{{
   *   maxcd = max(c,d) |- a+b <= maxcd+e
   *   ----------------------------------------abbrv(Variable("maxcd"))(SuccPosition(0).second.first)
   *                    |- a+b <= max(c, d) + e
   * }}}
   * @param abbrvV The abbreviation.
   * @return The tactic.
   */
  def abbrv(abbrvV: Variable): PositionTactic = new PositionTactic("abbrv") {
    override def applies(s: Sequent, p: Position): Boolean = getTerm(s, p) != null // just to test that there is no exception

    override def apply(p: Position): Tactic = new ConstructionTactic("abbrv") {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val t = getTerm(node.sequent, p)
        Some(abbrv(t, Some(abbrvV)))
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
  def abbrv(t: Term, abbrvV: Option[Variable] = None): Tactic = new ConstructionTactic("abbrv") {
    override def applicable(node: ProofNode): Boolean = abbrvV match {
      case Some(v) => !TacticHelper.names(node.sequent).contains(v)
      case None => true
    }

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
      val v = abbrvV match {
        case Some(vv) => vv
        case None => t match {
          case FuncOf(Function(n, _, _, sort), _) => Variable(n, TacticHelper.freshIndexInSequent(n, node.sequent), sort)
          case Variable(n, _, sort) => Variable(n, TacticHelper.freshIndexInSequent(n, node.sequent), sort)
          case _ => Variable(t.kind.toString, TacticHelper.freshIndexInSequent(t.kind.toString, node.sequent), t.sort)
        }
      }
      Some(cutT(Some(Exists(v :: Nil, Equal(v, t)))) & onBranch(
        (cutShowLbl, lastSucc(cohideT) &
          //@note cannot use instantiateT, because during \exists generalize we don't know which part of z=z we should generalize
          cutT(Some(Equiv(Exists(v :: Nil, Equal(v, t)), Equal(t, t)))) & onBranch(
          (cutShowLbl, lastSucc(EquivRightT) & onBranch(
            (equivLeftLbl, AxiomCloseT),
            (equivRightLbl, FOQuantifierTacticsImpl.existentialGenPosT(v, HereP.first :: Nil)(AntePosition(0)) & AxiomCloseT)
          )),
          (cutUseLbl, equivRewriting(AntePosition(0), SuccPosition(0)) & EqualReflexiveT(SuccPosition(0)))
        )),
        (cutUseLbl, lastAnte(skolemizeT) & lastAnte(eqRight(exhaustive = true)))
      ))
    }
  }

}
