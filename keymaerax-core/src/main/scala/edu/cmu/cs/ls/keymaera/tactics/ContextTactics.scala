package edu.cmu.cs.ls.keymaera.tactics

import ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction, TraverseToPosition}
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.core.StaticSemantics.signature
import edu.cmu.cs.ls.keymaera.tactics.AlphaConversionHelper.replaceBound
import edu.cmu.cs.ls.keymaera.tactics.AxiomaticRuleTactics._
import edu.cmu.cs.ls.keymaera.tactics.FOQuantifierTacticsImpl.{skolemizeT,instantiateT}
import edu.cmu.cs.ls.keymaera.tactics.FormulaConverter._
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl.{AxiomCloseT,ImplyRightT,ImplyLeftT,NotRightT,NotLeftT,
  AndLeftT,AndRightT}
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl.{lastSucc,lastAnte}
import edu.cmu.cs.ls.keymaera.tactics.Tactics.{PositionTactic, ConstructionTactic, Tactic, stopT}
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.{cutT,debugT,alphaRenamingT}
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.TacticHelper.{getFormula,freshNamedSymbol,getTerm}
import edu.cmu.cs.ls.keymaera.tools.Tool


/**
 * Created by smitsch on 3/20/15.
 * @author Stefan Mitsch
 */
object ContextTactics {

  def peelT(counterPart: Position, inCtx: PosInExpr, baseT: PositionTactic): PositionTactic = new PositionTactic("Peel") {
    override def applies(s: Sequent, p: Position): Boolean =
      s(p).extractContext(inCtx)._1 == s(counterPart).extractContext(inCtx)._1

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val c1 = node.sequent(p).extractContext(inCtx)
        val c2 = node.sequent(counterPart).extractContext(inCtx)
        assert(c1._1 == c2._1, "Ensured by applies to never happen")
        Some(peelT(c1._1.ctx, c1._2, c2._2, counterPart, baseT)(p))
      }
    }
  }

  def peelT(context: Formula, f: Expression, g: Expression, counterPart: Position, baseT: PositionTactic): PositionTactic = new PositionTactic("Peel") {
    override def applies(s: Sequent, p: Position): Boolean = true

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        // TODO use once uniform substitution of CDotFormula is fixed
        //        assert(context.instantiateContext(f) == node.sequent(p), s"Context $context with formula $f, which is\n   ${context.instantiateContext(f)}\n not found at position $p\n   ${node.sequent(p)}")
        //        assert(context.instantiateContext(g) == node.sequent(counterPart), s"Context $context with formula $g, which is\n   ${context.instantiateContext(g)}\n not found at position $counterPart\n   ${node.sequent(counterPart)}")
        if (!signature(context).contains(DotFormula) && !signature(context).contains(DotTerm))
          Some(AxiomCloseT | debugT(s"Unexpected peeling result: ${node.sequent} did not close by axiom") & stopT)
        else context match {
          case DotFormula => Some(debugT(s"Finished peeling, now calling base tactic ${baseT.name}") & baseT(p))
          case Not(phi) => Some(NotLeftT(counterPart) & NotRightT(p) & lastSucc(peelT(phi, f, g, AntePosition(node.sequent.ante.length - 1), baseT)))
          case And(lhs, rhs) => Some(AndLeftT(counterPart) & AndRightT(p) &&(
            peelT(lhs, f, g, counterPart, baseT)(p),
            peelT(rhs, f, g, AntePosition(node.sequent.ante.length), baseT)(p)))
          case Imply(lhs, rhs) => Some(ImplyRightT(p) & ImplyLeftT(counterPart) && (
            // both left-hand sides move in the last position on the other side of the turn stile
            lastSucc(peelT(lhs, f, g, AntePosition(node.sequent.ante.length), baseT)),
            // ImplyLeftT moves right-hand side into last ante position
            peelT(rhs, f, g, AntePosition(node.sequent.ante.length), baseT)(p)))
          case Forall(vars, phi) =>
            // HACK guess skolem name
            val (v, newV) = vars.head match { case v: Variable => (v, freshNamedSymbol(v, node.sequent)) }
            val newF = f match { case fml: Formula => replaceBound(fml)(v, newV) case _ => f }
            val newG = g match { case fml: Formula => replaceBound(fml)(v, newV) case _ => g }
            Some(skolemizeT(p) & alphaRenamingT(v.name, v.index, newV.name, newV.index)(counterPart) &
              // alpha renaming changes the position from counterPart to last ante
              lastAnte(instantiateT(newV, newV)) &
              peelT(phi, newF, newG, AntePosition(node.sequent.ante.length - 1), baseT)(p))
          case Exists(vars, phi) =>
            // HACK guess skolem name
            val (v, newV) = vars.head match { case v: Variable => (v, freshNamedSymbol(v, node.sequent)) }
            val newF = f match { case fml: Formula => replaceBound(fml)(v, newV) case _ => f }
            val newG = g match { case fml: Formula => replaceBound(fml)(v, newV) case _ => g }
            Some(skolemizeT(counterPart) & alphaRenamingT(v.name, v.index, newV.name, newV.index)(p) &
              // alpha renaming changes the position from p to last succ
              lastSucc(instantiateT(newV, newV)) &
              peelT(phi, newF, newG, AntePosition(node.sequent.ante.length - 1), baseT)(p))
        }
      }
    }
  }

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
    case Equal(lhs, rhs) if fml.termAt(where) == lhs => Equiv(fml, fml.replaceAt(lhs, where, rhs))
    case Equal(lhs, rhs) if fml.termAt(where) == rhs => Equiv(fml.replaceAt(rhs, where, lhs), fml)
    case Equiv(lhs, rhs) if fml.subFormulaAt(where) == Some(lhs) => Equiv(fml, fml.replaceAt(lhs, where, rhs))
    case Equiv(lhs, rhs) if fml.subFormulaAt(where) == Some(rhs) => Equiv(fml.replaceAt(rhs, where, lhs), fml)
    //For the power derive rule.
    case Imply(cond, Equal(lhs, rhs)) if fml.termAt(where) == lhs => {
      // We have [ctx] f(lhs) and want [ctx] cond -> f(lhs) = f(rhs), where f is some formula.
      val (f, fPos, lhsPos) = findSmallestSubformulaContaining(fml, where)
//      val fPos = PosInExpr(where.pos.dropRight(1))
//
//      val f: Formula = fml.subFormulaAt(fPos).getOrElse(
//        throw new Exception("Could not find a subformula at position " + fPos.pos.mkString("::") + " in " + fml.prettyString())
//      )
      val newFormula = Imply(cond, f.replaceAt(lhs, lhsPos, rhs))
      Equiv(fml, fml.replaceAt(f, fPos, newFormula))
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
    fml.subFormulaAt(nextLargestPos) match {
      case Some(f) => (f, nextLargestPos, posOfWhereInSubformula)
      case None    => findSmallestSubformulaContaining(fml, nextLargestPos, posOfWhereInSubformula)
    }
  }

  /**
   * Creates a tactic to cut in an equality f = g or equivalence f <-> g in context, i.e., C[f] <-> C[g]. Expects either
   * the left-hand side or the right-hand side of the equality/equivalence to be present at position ctx.
   * @param f The desired equality/equivalence.
   * @param ctx Points to the position in the context.
   * @return The newly created tactic.
   */
  def cutInContext(f: Formula, ctx: Position): Tactic = cutInContext(_ => f, ctx)
  def cutInContext(g: ProofNode => Formula, ctx: Position): Tactic = new ConstructionTactic("Cut in Context") {
    def applicable(pn: ProofNode): Boolean = g(pn) match {
      case Equal(lhs, rhs) => val t = getTerm(pn.sequent, ctx); t == lhs || t == rhs
      case Equiv(lhs, rhs) => val f = getFormula(pn.sequent, ctx); f == lhs || f == rhs
      case Imply(cond, Equal(lhs, rhs)) => val t = getTerm(pn.sequent, ctx); t == lhs || t == rhs
      case _ => false
    }

    override def constructTactic(tool: Tool, p: ProofNode): Option[Tactic] =
      Some(cutT(Some(replaceInContext(p.sequent(ctx), g(p), ctx.inExpr))))
  }

  /**
   * Creates a tactic to cut in an implication p->q in context, i.e., C[p] -> C[q]. Expects the right-hand side
   * of the implication to be present at position ctx.
   * @param f The desired implication.
   * @param ctx Points to the position in the context.
   * @return The newly created tactic.
   */
  def cutImplyInContext(f: Formula, ctx: Position): Tactic = cutImplyInContext(_ => f, ctx)
  def cutImplyInContext(g: ProofNode => Formula, ctx: Position): Tactic = new ConstructionTactic("Cut in Context") {
    def applicable(pn: ProofNode): Boolean = g(pn) match {
      case Imply(_, Equiv(lhs, rhs)) => getFormula(pn.sequent, ctx) == lhs || getFormula(pn.sequent, ctx) == rhs
      case Imply(lhs, rhs) => getFormula(pn.sequent, ctx) == lhs || getFormula(pn.sequent, ctx) == rhs
      case _ => false
    }

    override def constructTactic(tool: Tool, p: ProofNode): Option[Tactic] = g(p) match {
      case Imply(lhs, rhs) if getFormula(p.sequent, ctx) == lhs =>
        val lhsInCtx = p.sequent(ctx.topLevel)
        val rhsInCtx = ExpressionTraversal.traverse(TraverseToPosition(ctx.inExpr, new ExpressionTraversalFunction {
          override def preF(pos: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] =
            if (f == lhs) Right(rhs)
            else Left(Some(ExpressionTraversal.stop))
        }), lhsInCtx) match {
          case Some(f) => f
          case None => throw new IllegalArgumentException(s"Did not find $lhs at position $ctx")
        }
        val implyInCtx = Imply(lhsInCtx, rhsInCtx)
        Some(cutT(Some(implyInCtx)))
      case Imply(lhs, rhs) if getFormula(p.sequent, ctx) == rhs =>
        val rhsInCtx = p.sequent(ctx.topLevel)
        val lhsInCtx = ExpressionTraversal.traverse(TraverseToPosition(ctx.inExpr, new ExpressionTraversalFunction {
          override def preF(pos: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] =
            if (f == rhs) Right(lhs)
            else Left(Some(ExpressionTraversal.stop))
        }), rhsInCtx) match {
          case Some(f) => f
          case None => throw new IllegalArgumentException(s"Did not find $rhs at position $ctx")
        }
        val implyInCtx = Imply(lhsInCtx, rhsInCtx)
        Some(cutT(Some(implyInCtx)))
    }
  }
}
