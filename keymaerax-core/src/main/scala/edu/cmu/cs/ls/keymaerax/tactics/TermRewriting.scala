package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.EqualityRewritingImpl._
import edu.cmu.cs.ls.keymaerax.tactics.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.SyntacticDerivationInContext.ApplicableAtTerm
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.TacticHelper
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.{ConstructionTactic, PositionTactic, Tactic}
import edu.cmu.cs.ls.keymaerax.tools.Tool

/**
 * Created by nfulton on 9/11/15.
 */
object TermRewriting {
  def replaceSubterm(f: Formula, p: PosInExpr, replacementTerm: Term => Term) = {
    val traversalFunction = new ExpressionTraversalFunction {
      override def preT(tPos: PosInExpr, t: Term) =
        if(tPos == p) Right(replacementTerm(t))
        else Left(None)
    }
    ExpressionTraversal.traverse(traversalFunction, f)
  }

  /**
   * Rewrites f{t} to f{replacementTerm(t)} assuming that t=s is a tautology of FOLR.
   * @param replacementTerm the term that replaces f@termPosition.
   * @param applicabilityPredicate The applicability function on terms
   * @param equivT A proof that f <-> f{replacementTerm}
   * @return Tactic that produces one open goal: f, but with replacementTerm in position termPosition
   */
  def rewriteTerm(applicabilityPredicate: Term => Boolean, replacementTerm: Term => Term, equivT: Tactic, name : String) : PositionTactic =
    new PositionTactic(s"rewriteTerm ($name)") with ApplicableAtTerm {
      override def apply(p: Position): Tactic = new ConstructionTactic("Construct" + name) {
        override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
          val formula: Formula = node.sequent(p.topLevel)
          val newFormula : Formula = replaceSubterm(formula, p.inExpr, replacementTerm).get
          val equivalence = Equiv(node.sequent(p.topLevel), newFormula)

          val assumptionPos = AntePos(node.sequent.ante.length)
          val cutPos = SuccPos(node.sequent.succ.length)
          val tactic : Tactic = PropositionalTacticsImpl.cutT(Some(equivalence)) & onBranch(
            (BranchLabels.cutShowLbl,
              PropositionalTacticsImpl.cohideT(cutPos) &
              AxiomaticRuleTactics.equationCongruenceT(p.inExpr) &
              equivT
            ),
            (BranchLabels.cutUseLbl, equivRewriting(assumptionPos, SuccPos(0)))
          )

          Some(tactic)
        }
        override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
      }

      override def applies(s: Sequent, p: Position): Boolean =
        TacticHelper.getTerm(s(p.topLevel), p.inExpr) match {
          case Some(term) => applies(term)
          case None => false
        }

      override def applies(t: Term): Boolean = applicabilityPredicate(t)
    }

  /** just a wrapper around rewriteTerm */
  def apply(applicabilityPredicate: Term => Boolean, replacementTerm: Term => Term, equivT: Tactic, name : String) =
    rewriteTerm(applicabilityPredicate, replacementTerm, equivT, name)
}
