package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction, TraverseToPosition}
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.AxiomaticRuleTactics._
import edu.cmu.cs.ls.keymaera.tactics.Tactics.{ConstructionTactic, Tactic}
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.cutT
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.TacticHelper.getFormula

/**
 * Created by smitsch on 3/20/15.
 * @author Stefan Mitsch
 */
object ContextTactics {

  /**
   * Creates a new tactic to uncover an equivalence inside context, and execute a base tactic on that uncovered formula.
   * @param baseF The base formula to uncover.
   * @param baseT The base tactic to execute on the base formula once uncovering is completed.
   * @return The newly created tactic.
   */
  def showEquivInContext(baseF: Formula, baseT: Tactic): Tactic = new ConstructionTactic("Show Equivalence in Context") {
    override def applicable(node : ProofNode): Boolean = node.sequent.ante.isEmpty && node.sequent.succ.length == 1 &&
      (node.sequent.succ(0) match {
        case eq@Equiv(_, _) => eq == baseF || congruenceT.applicable(node)
        case _ => false
      })

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
      if (node.sequent.succ(0) == baseF) Some(baseT)
      else Some(congruenceT & showEquivInContext(baseF, baseT))
  }

  /**
   * Creates a tactic to cut in an equivalence p<->q in context, i.e., C[p] <-> C[q]. Expects either the left-hand side
   * of the equivalence to be present or the right-hand side to be present at position ctx.
   * @param f The desired equivalence.
   * @param ctx Points to the position in the context.
   * @return The newly created tactic.
   */
  def cutEquivInContext(f: Formula, ctx: Position): Tactic = cutEquivInContext(_ => f, ctx)
  def cutEquivInContext(g: ProofNode => Formula, ctx: Position): Tactic = new ConstructionTactic("Cut in Context") {
    def applicable(pn: ProofNode): Boolean = g(pn) match {
      case Equiv(lhs, rhs) => val f = getFormula(pn.sequent, ctx); f == lhs || f == rhs
      case _ => false
    }

    override def constructTactic(tool: Tool, p: ProofNode): Option[Tactic] = g(p) match {
      case Equiv(lhs, rhs) if getFormula(p.sequent, ctx) == lhs =>
        val lhsInCtx = p.sequent(ctx.topLevel)
        val rhsInCtx = ExpressionTraversal.traverse(TraverseToPosition(ctx.inExpr, new ExpressionTraversalFunction {
          override def preF(pos: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] =
            if (f == lhs) Right(rhs)
            else Left(Some(ExpressionTraversal.stop))
        }), lhsInCtx) match {
          case Some(f) => f
          case None => throw new IllegalArgumentException(s"Did not find $lhs at position $ctx")
        }
        val equivInCtx = Equiv(lhsInCtx, rhsInCtx)
        Some(cutT(Some(equivInCtx)))
      case Equiv(lhs, rhs) if getFormula(p.sequent, ctx) == rhs =>
        val rhsInCtx = p.sequent(ctx.topLevel)
        val lhsInCtx = ExpressionTraversal.traverse(TraverseToPosition(ctx.inExpr, new ExpressionTraversalFunction {
          override def preF(pos: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] =
            if (f == rhs) Right(lhs)
            else Left(Some(ExpressionTraversal.stop))
        }), rhsInCtx) match {
          case Some(f) => f
          case None => throw new IllegalArgumentException(s"Did not find $rhs at position $ctx")
        }
        val equivInCtx = Equiv(lhsInCtx, rhsInCtx)
        Some(cutT(Some(equivInCtx)))
    }
  }
}
