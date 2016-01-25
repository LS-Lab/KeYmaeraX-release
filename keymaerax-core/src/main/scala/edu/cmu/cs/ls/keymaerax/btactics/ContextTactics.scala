package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{DependentPositionTactic, PosInExpr, BelleExpr, Position}
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal.{TraverseToPosition, ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import Augmentors._
import edu.cmu.cs.ls.keymaerax.tools.Tool

/**
  * Created by bbohrer on 1/24/16.
  */
object ContextTactics {
  /**
    * Creates a tactic to cut in an implication p->q in context, i.e., C[p] -> C[q]. Expects the right-hand side
    * of the implication to be present at position ctx.
    * @param f The desired implication.
    * @param ctx Points to the position in the context.
    * @return The newly created tactic.
    */
  def cutImplyInContext(f: Formula, ctx: Position): BelleExpr = cutImplyInContext(_ => f, ctx)
  def cutImplyInContext(g: Sequent => Formula, ctx: Position): BelleExpr = "Cut in Context" by ((p, sequent) =>
      sequent.at(p)._1.ctx match {
      case Imply(lhs, rhs) if sequent.at(ctx) == lhs =>
        require(sequent.at(ctx) == lhs || sequent.at(ctx) == rhs)
        val lhsInCtx = sequent.at(ctx.topLevel)._1.ctx
        val rhsInCtx = ExpressionTraversal.traverse(TraverseToPosition(ctx.inExpr, new ExpressionTraversalFunction {
          override def preF(pos: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] =
            if (f == lhs) Right(rhs)
            else Left(Some(ExpressionTraversal.stop))
        }), lhsInCtx) match {
          case Some(f) => f
          case None => throw new IllegalArgumentException(s"Did not find $lhs at position $ctx")
        }
        val implyInCtx = Imply(lhsInCtx, rhsInCtx)
        SequentCalculus.cut(implyInCtx)
      case Imply(lhs, rhs) if sequent.at(ctx) == rhs =>
        require(sequent.at(ctx) == lhs || sequent.at(ctx) == rhs)
        val rhsInCtx = sequent.at(ctx.topLevel)._1.ctx
        val lhsInCtx = ExpressionTraversal.traverse(TraverseToPosition(ctx.inExpr, new ExpressionTraversalFunction {
          override def preF(pos: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] =
            if (f == rhs) Right(lhs)
            else Left(Some(ExpressionTraversal.stop))
        }), rhsInCtx) match {
          case Some(f) => f
          case None => throw new IllegalArgumentException(s"Did not find $rhs at position $ctx")
        }
        val implyInCtx = Imply(lhsInCtx, rhsInCtx)
        SequentCalculus.cut(implyInCtx)
    })

  /**
    * Creates a tactic to cut in an equality f = g or equivalence f <-> g in context, i.e., C[f] <-> C[g]. Expects either
    * the left-hand side or the right-hand side of the equality/equivalence to be present at position ctx.
    * @param f The desired equality/equivalence.
    * @param ctx Points to the position in the context.
    * @return The newly created tactic.
    */
  def cutInContext(f: Formula, ctx: Position): DependentPositionTactic = cutInContext(_ => f, ctx)
  def cutInContext(g: Sequent => Formula, ctx: Position): DependentPositionTactic = "Cut in Context" by ((p:Position, sequent:Sequent) => {
      ProofRuleTactics.cut(replaceInContext(sequent.at(ctx)._1.ctx, g(sequent), ctx.inExpr))
  })


  /**
    * Replaces either the left-hand side or the right-hand side of eq at position where in formula fml, and returns an
    * equivalence of both formulas.
    * @param fml The formula to replace in.
    * @param eq The equality/equivalence (depending on occurrence in fml, either replaces left with right or vice versa)
    * @param where Where to replace in fml.
    * @return If lhs replaced by rhs: equivalence fml <-> fml after the replacement;
    *         if rhs replaced by lhs: equivalence fml after the replacement <-> fml.
    */
  def replaceInContext(fml: Formula, eq: Formula, where: PosInExpr): Formula = eq match {
    case Equal(lhs, rhs) if fml.at(where) == lhs => Equiv(fml, fml.replaceAt(where, rhs).asInstanceOf[Formula])
    case Equal(lhs, rhs) if fml.at(where) == rhs => Equiv(fml.replaceAt(where, lhs).asInstanceOf[Formula], fml)
    case Equiv(lhs, rhs) if fml.at(where) == lhs => Equiv(fml, fml.replaceAt(where, rhs).asInstanceOf[Formula])
    case Equiv(lhs, rhs) if fml.at(where) == rhs => Equiv(fml.replaceAt(where, lhs).asInstanceOf[Formula], fml)
    //For the power derive rule.
    case Imply(cond, Equal(lhs, rhs)) if fml.at(where) == lhs => {
      // We have [ctx] f(lhs) and want [ctx] cond -> f(lhs) = f(rhs), where f is some formula.
      val (f, fPos, lhsPos) = findSmallestSubformulaContaining(fml, where)
      val newFormula = Imply(cond, f.replaceAt(lhsPos, rhs).asInstanceOf[Formula])
      Equiv(fml, fml.replaceAt(fPos, newFormula).asInstanceOf[Formula])
    }
  }

  /**
    * Example: Consider arguments a+b = 0 -> a=0|b=0, 0::0::0, i.e. the position of a in fml.
    * Then the return value should be:
    *      a+b = 0       - smallest subformula containing a
    *      0             - location of a+b=0 within fml
    *      0 :: 0        - location of a within a+b=0
    *
    * @author Nathan Fulton
    * @param fml A formula
    * @param where A position in the formula
    * @return A 3-tuple containing:
    *          The smallest subformula containing the term/formula at where.
    *          The position of the first return value in fml.
    *          The position of where within the smallest subformula.
    */
  private def findSmallestSubformulaContaining(fml : Formula, where : PosInExpr, recPos : PosInExpr = PosInExpr()) : (Formula, PosInExpr, PosInExpr) = {
    val nextLargestPos = PosInExpr(where.pos.dropRight(1))
    val posOfWhereInSubformula = PosInExpr(recPos.pos :+ where.pos.last)

    //None means that we must have found a term or program rather than a subformula, so we recurse.
    fml.at(nextLargestPos) match {
      case (ctx,f) => (ctx.ctx, nextLargestPos, posOfWhereInSubformula)
    }
  }

}
