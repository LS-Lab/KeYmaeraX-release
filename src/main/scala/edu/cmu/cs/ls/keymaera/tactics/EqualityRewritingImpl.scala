package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{TraverseToPosition, StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.Tactics.{ConstructionTactic, PositionTactic, ApplyRule, Tactic}

import scala.collection.immutable.Set

/**
 * Implementation of equality rewriting.
 */
object EqualityRewritingImpl {
  // exhaustive equality rewriting
  // check variable disjointness between left and right side
  protected[tactics] def isEquality(s: Sequent, p: Position, checkDisjointness: Boolean = false): Boolean = {
    import BindingAssessment.allNames
    p.isAnte && p.inExpr == HereP && (s.ante(p.getIndex) match {
      case Equals(_, a, b) => if (checkDisjointness) allNames(a).intersect(allNames(b)).isEmpty else true
      case ProgramEquals(a, b) => /*if (checkDisjointness) variables(a).intersect(variables(b)).isEmpty else*/ true
      case Equiv(a, b) => /*if (checkDisjointness) variables(a).intersect(variables(b)).isEmpty else*/ true
      case _ => false
    })
  }

  private def equalityApplicable(left: Boolean, eqPos: Position, p: Position, s: Sequent): Boolean = {
    import BindingAssessment.allNames
    var applicable = false
    val (blacklist, f) = s.ante(eqPos.getIndex) match {
      case Equals(_, a, b) => val search = if(left) a else b
        (allNames(a) ++ allNames(b),
          new ExpressionTraversalFunction {
            override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
              if (e == search) applicable = true
              Left(Some(new StopTraversal {}))
            }
          })
      case ProgramEquals(a, b) => val search = if(left) a else b
        (allNames(a) ++ allNames(b),
          new ExpressionTraversalFunction {
            override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = {
              if (e == search) applicable = true
              Left(Some(new StopTraversal {}))
            }
          })
      case Equiv(a, b) => val search = if(left) a else b
        (allNames(a) ++ allNames(b),
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
      val res = isEquality(node.sequent, eqPos, checkDisjoint) && (equalityApplicable(left = true, eqPos, p, node.sequent) || equalityApplicable(left = false, eqPos, p, node.sequent))
      res
    }
  }

  protected[tactics] def equalityRewritingRight(eqPos: Position): PositionTactic = new PositionTactic("Equality Rewriting Right") {

    override def applies(s: Sequent, p: Position): Boolean = isEquality(s, eqPos, checkDisjointness =  true) && equalityApplicable(left = false, eqPos, p, s)

    override def apply(p: Position): Tactic = equalityRewriting(eqPos, p)
  }

  protected[tactics] def equalityRewritingLeft(eqPos: Position): PositionTactic = new PositionTactic("Equality Rewriting Left") {

    override def applies(s: Sequent, p: Position): Boolean = isEquality(s, eqPos, checkDisjointness = true) && equalityApplicable(left = true, eqPos, p, s)

    override def apply(p: Position): Tactic = equalityRewriting(eqPos, p)
  }


  protected[tactics] def eqRewritePos(left: Boolean, eqPos: Position): Tactic = new ConstructionTactic("Apply Equality Left") {
    require(eqPos.isAnte && eqPos.inExpr == HereP, "Equalities for rewriting have to be in the antecedent")

    override def applicable(node: ProofNode): Boolean = eqPos.isAnte && eqPos.isTopLevel && (node.sequent(eqPos) match {
      case Equals(_, _, _) => findPosInExpr(left, node.sequent, eqPos).isDefined
      case ProgramEquals(_, _) => findPosInExpr(left, node.sequent, eqPos).isDefined
      case Equiv(_, _) => findPosInExpr(left, node.sequent, eqPos).isDefined
      case _ => false
    })

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
      import PropositionalTacticsImpl.hideT
      findPosInExpr(left, node.sequent, eqPos) match {
        case Some(p) =>
          val t = equalityRewriting(eqPos, p)
          val hide = hideT(p.topLevel)
          Some(t & hide)
        case None => None
      }
    }
  }

  protected[tactics] def eqLeft(exhaustive: Boolean): PositionTactic = new PositionTactic("Find Equality and Apply Right to Left") {
    import scala.language.postfixOps
    override def applies(s: Sequent, p: Position): Boolean = p.isAnte && isEquality(s, p, checkDisjointness = true) && findPosInExpr(left = true, s, p).isDefined

    override def apply(p: Position): Tactic = if(exhaustive) eqRewritePos(left = true, p)* else eqRewritePos(left = true, p)
  }

  protected[tactics] def eqRight(exhaustive: Boolean): PositionTactic = new PositionTactic("Find Equality and Apply Left to Right") {
    import scala.language.postfixOps
    override def applies(s: Sequent, p: Position): Boolean = p.isAnte && isEquality(s, p, checkDisjointness = true) && findPosInExpr(left = false, s, p).isDefined

    override def apply(p: Position): Tactic = if(exhaustive) eqRewritePos(left = false, p)* else eqRewritePos(left = false, p)
  }

  private def findPosInExpr(s: Sequent, blacklist: Set[NamedSymbol], search: Expr, ignore: Position): Option[Position] =
    findPosInExpr(s, blacklist, search == _, Some(ignore))

  private def findPosInExpr(s: Sequent, blacklist: Set[NamedSymbol], test: (Expr => Boolean), filterPos: Option[Position]): Option[Position] = {
    var posInExpr: PosInExpr = null
    val f = new ExpressionTraversalFunction {
      val stop = new StopTraversal {}

      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = if (test(e)) {
        posInExpr = p
        Left(Some(stop))
      } else {
        e match {
          case Forall(v, phi) if blacklist.map(v.contains).foldLeft(false)(_ || _) => Left(Some(stop))
          case Exists(v, phi) if blacklist.map(v.contains).foldLeft(false)(_ || _) => Left(Some(stop))
          case BoxModality(a, c) if blacklist.map(a.writes.contains).foldLeft(false)(_ || _) => Left(Some(stop))
          case DiamondModality(a, c) if blacklist.map(a.writes.contains).foldLeft(false)(_ || _) => Left(Some(stop))
          case _ => Left(None)
        }
      }

      override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = if (test(e)) {
        posInExpr = p
        Left(Some(stop))
      } else Left(None)

      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
        if (test(e)) {
          posInExpr = p
          Left(Some(stop))
        } else Left(None)
      }


      override def preG(p: PosInExpr, e: ModalOp): Either[Option[StopTraversal], ModalOp] = if (test(e)) {
        posInExpr = p
        Left(Some(stop))
      } else Left(None)

    }
    val ignore = filterPos match {
      case Some(p) => p
      case None => null
    }
    for(i <- 0 until s.ante.length) {
      if(ignore == null || !ignore.isAnte || ignore.getIndex != i) {
        ExpressionTraversal.traverse(f, s.ante(i))
        if (posInExpr != null) {
          return Some(AntePosition(i, posInExpr))
        }
      }
    }
    for(i <- 0 until s.succ.length) {
      if(ignore == null || ignore.isAnte || ignore.getIndex != i) {
        ExpressionTraversal.traverse(f, s.succ(i))
        if (posInExpr != null) {
          return Some(SuccPosition(i, posInExpr))
        }
      }
    }
    None
  }

  private def findPosInExpr(left: Boolean, s: Sequent, eqPos: Position): Option[Position] = {
    val eq = s.ante(eqPos.getIndex)
    val blacklist = BindingAssessment.allNames(eq)
    val search: Expr = eq match {
      case Equals(_, a, b) => if(left) a else b
      case ProgramEquals(a, b) => if(left) a else b
      case Equiv(a, b) => if(left) a else b
      case _ => throw new IllegalArgumentException("Equality Rewriting does not work for " + eq)
    }
    findPosInExpr(s, blacklist, search, eqPos)
  }
}
