package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{TraverseToPosition, StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.Tactics.{PositionTactic, ApplyRule, Tactic}

/**
 * Implementation of equality rewriting.
 */
object EqualityRewritingImpl {
  // exhaustive equality rewriting
  // check variable disjointness between left and right side
  protected[tactics] def isEquality(s: Sequent, p: Position, checkDisjointness: Boolean = false): Boolean = {
    import Helper.names
    p.isAnte && p.inExpr == HereP && (s.ante(p.getIndex) match {
      case Equals(_, a, b) => if (checkDisjointness) names(a).intersect(names(b)).isEmpty else true
      case ProgramEquals(a, b) => /*if (checkDisjointness) variables(a).intersect(variables(b)).isEmpty else*/ true
      case Equiv(a, b) => /*if (checkDisjointness) variables(a).intersect(variables(b)).isEmpty else*/ true
      case _ => false
    })
  }

  private def equalityApplicable(left: Boolean, eqPos: Position, p: Position, s: Sequent): Boolean = {
    import Helper.names
    var applicable = false
    val (blacklist, f) = s.ante(eqPos.getIndex) match {
      case Equals(_, a, b) => val search = if(left) a else b
        (names(a) ++ names(b),
          new ExpressionTraversalFunction {
            override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
              if (e == search) applicable = true
              Left(Some(new StopTraversal {}))
            }
          })
      case ProgramEquals(a, b) => val search = if(left) a else b
        (names(a) ++ names(b),
          new ExpressionTraversalFunction {
            override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = {
              if (e == search) applicable = true
              Left(Some(new StopTraversal {}))
            }
          })
      case Equiv(a, b) => val search = if(left) a else b
        (names(a) ++ names(b),
          new ExpressionTraversalFunction {
            override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
              if (e == search) applicable = true
              Left(Some(new StopTraversal {}))
            }
          })
      case _ => throw new IllegalArgumentException("Equality Rewriting not applicable")
    }
    val trav = TraverseToPosition(p.inExpr, f, blacklist)
    val form = (if (p.isAnte) s.ante else s.succ)(p.getIndex)
    ExpressionTraversal.traverse(trav, form)
    applicable
  }

  protected[tactics] def equalityRewriting(eqPos: Position, p: Position, checkDisjoint: Boolean = true): Tactic = new ApplyRule(new EqualityRewriting(eqPos, p)) {
    override def applicable(node: ProofNode): Boolean = {
      val res = isEquality(node.sequent, eqPos, checkDisjoint) && (equalityApplicable(true, eqPos, p, node.sequent) || equalityApplicable(false, eqPos, p, node.sequent))
      res
    }
  }

  protected[tactics] def equalityRewritingRight(eqPos: Position): PositionTactic = new PositionTactic("Equality Rewriting Right") {

    override def applies(s: Sequent, p: Position): Boolean = isEquality(s, eqPos, true) && equalityApplicable(false, eqPos, p, s)

    override def apply(p: Position): Tactic = equalityRewriting(eqPos, p)
  }

  protected[tactics] def equalityRewritingLeft(eqPos: Position): PositionTactic = new PositionTactic("Equality Rewriting Left") {

    override def applies(s: Sequent, p: Position): Boolean = isEquality(s, eqPos, true) && equalityApplicable(true, eqPos, p, s)

    override def apply(p: Position): Tactic = equalityRewriting(eqPos, p)
  }
}
