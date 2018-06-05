/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaerax.btactics.TacticIndex.{Branches, TacticRecursors}
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.core._

import scala.annotation.switch

/**
 * Tactic indexing data structures for canonical proof strategies.
 * @author Stefan Mitsch
 * @see [[edu.cmu.cs.ls.keymaerax.btactics.AxiomInfo]]
 */
object TacticIndex {
  /** A list of things to do on a branch */
  type Branch = List[PositionLocator]

  /** Branch recursors (parent tactics may branch). */
  type Branches = List[Branch]

  /**
    * Recursors list resulting siblings for subsequent chase (every recursor is itself
    * a list, since tactics may branch).
    */
  type TacticRecursors = List[(Sequent, Position) => Branches]

  lazy val default: TacticIndex = new DefaultTacticIndex

  val allLStutter: DependentPositionTactic = TactixLibrary.useAt(DerivedAxioms.forallStutter)
  val existsRStutter: DependentPositionTactic = TactixLibrary.useAt(DerivedAxioms.existsStutter)
}

trait TacticIndex {
  def tacticRecursors(tactic: BelleExpr): TacticRecursors
  def tacticFor(expr: Expression, restrictTo: List[AtPosition[_ <: BelleExpr]]): (Option[AtPosition[_ <: BelleExpr]], Option[AtPosition[_ <: BelleExpr]])
  def tacticsFor(expr: Expression): (List[AtPosition[_ <: BelleExpr]], List[AtPosition[_ <: BelleExpr]])
}

class DefaultTacticIndex extends TacticIndex {

  private def one(pos: PositionLocator): Branches = (pos :: Nil) :: Nil

  /**
   * Return tactic index with list of recursors on other sibling, i.e., for chasing after the tactic is applied.
   */
  def tacticRecursors(tactic: BelleExpr): TacticRecursors = (tactic: @switch) match {
    //@note expected formulas are used to fall back to search
    case TactixLibrary.notL =>
      ((s: Sequent, p: Position) => one(Fixed(SuccPosition.base0(s.succ.length), child(s(p.top))))) :: Nil
    case TactixLibrary.andL =>
      ((s: Sequent, p: Position) => one(Fixed(AntePosition.base0(s.ante.length), right(s(p.top))))) ::
      ((s: Sequent, p: Position) => one(Fixed(AntePosition.base0(s.ante.length-1), left(s(p.top))))) :: Nil
    case TactixLibrary.orL =>
      ((s: Sequent, p: Position) => (new Fixed(p, left(s(p.top)))::Nil)::(new Fixed(p, right(s(p.top)))::Nil)::Nil) :: Nil
    case TactixLibrary.implyL =>
      ((s: Sequent, p: Position) =>
        (Fixed(SuccPosition.base0(s.succ.length), left(s(p.top)))::Nil)::
        (new Fixed(p, right(s(p.top)))::Nil)::Nil) :: Nil
    case TactixLibrary.equivL =>
      ((s: Sequent, p: Position) =>
        (new Fixed(p, Some(And(left(s(p.top)).get, right(s(p.top)).get)))::Nil)::
        (new Fixed(p, Some(And(Not(left(s(p.top)).get), Not(right(s(p.top)).get))))::Nil)::Nil) :: Nil
    case TactixLibrary.notR =>
      ((s: Sequent, p: Position) => one(Fixed(AntePosition.base0(s.ante.length), child(s(p.top))))) :: Nil
    case TactixLibrary.implyR =>
      ((s: Sequent, p: Position) => one(Fixed(AntePosition.base0(s.ante.length), left(s(p.top))))) ::
      ((s: Sequent, p: Position) => one(Fixed(SuccPosition.base0(s.succ.length-1), right(s(p.top))))) :: Nil
    case TactixLibrary.orR =>
      ((s: Sequent, p: Position) => one(Fixed(SuccPosition.base0(s.succ.length), right(s(p.top))))) ::
      ((s: Sequent, p: Position) => one(Fixed(SuccPosition.base0(s.succ.length-1), left(s(p.top))))) :: Nil
    case TactixLibrary.andR =>
      ((s: Sequent, p: Position) => (new Fixed(p, left(s(p.top)))::Nil)::(new Fixed(p, right(s(p.top)))::Nil)::Nil) :: Nil
    case TactixLibrary.equivR =>
      ((s: Sequent, p: Position) =>
        (Fixed(AntePosition.base0(s.ante.length), left(s(p.top)))::Fixed(SuccPosition.base0(s.succ.length-1), right(s(p.top)))::Nil)::
        (Fixed(AntePosition.base0(s.ante.length), right(s(p.top)))::Fixed(SuccPosition.base0(s.succ.length-1), left(s(p.top)))::Nil)::Nil) :: Nil
    case TactixLibrary.step => ((_: Sequent, p: Position) => one(new Fixed(p))) :: Nil
    case TactixLibrary.allR => ((s: Sequent, p: Position) => one(new Fixed(p, child(s(p.top))))) :: Nil
    case TacticIndex.allLStutter => ((s: Sequent, p: Position) => {
      //@note skip ahead to programs
      var (childPos, c) = (PosInExpr(0::Nil), child(s(p.top)))
      ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preF(p: PosInExpr, e: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = e match {
          case _: Modal => childPos = p; c = Some(e); Left(Some(ExpressionTraversal.stop))
          case _ => Left(None)
        }
      }, s(p.top))
      one(new Fixed(p ++ childPos, c))
    }) :: Nil
    case TactixLibrary.existsL => ((s: Sequent, p: Position) => one(new Fixed(p, child(s(p.top))))) :: Nil
    case TacticIndex.existsRStutter => ((s: Sequent, p: Position) => {
      //@note skip ahead to programs
      var (childPos, c) = (PosInExpr(0::Nil), child(s(p.top)))
      ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preF(p: PosInExpr, e: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = e match {
          case _: Modal => childPos = p; c = Some(e); Left(Some(ExpressionTraversal.stop))
          case _ => Left(None)
        }
      }, s(p.top))
      one(new Fixed(p ++ childPos, c))
    }) :: Nil
    case TactixLibrary.ODE => ((_: Sequent, p: Position) => one(new Fixed(p))) :: Nil
    case TactixLibrary.`solve` => ((_: Sequent, p: Position) => one(new Fixed(p))) :: Nil
    // default position: stop searching
    case _ => Nil
  }

  private def child(fml: Formula) = fml match {
    case f: UnaryCompositeFormula => Some(f.child)
    case Box(_, p) => Some(p)
    case Diamond(_, p) => Some(p)
    case Forall(_, p) => Some(p)
    case Exists(_, p) => Some(p)
  }
  private def left(fml: Formula) = fml match { case f: BinaryCompositeFormula => Some(f.left) }
  private def right(fml: Formula) = fml match { case f: BinaryCompositeFormula => Some(f.right) }

  // lookup canonical axioms for an expression (index)

  /** Give the first canonical (derived) axiom name or tactic name that simplifies the expression `expr`. */
  def tacticFor(expr: Expression, restrictTo: List[AtPosition[_ <: BelleExpr]]): (Option[AtPosition[_ <: BelleExpr]], Option[AtPosition[_ <: BelleExpr]]) = {
    val tactics = tacticsFor(expr)
    (tactics._1.intersect(restrictTo).headOption, tactics._2.intersect(restrictTo).headOption)
  }

  /** Return ordered list of all canonical tactic names that simplifies the expression `expr` (ante, succ). */
  def tacticsFor(expr: Expression): (List[AtPosition[_ <: BelleExpr]], List[AtPosition[_ <: BelleExpr]]) = {
    if (expr.kind == TermKind) expr match {
      case _ => (Nil, Nil)
    } else expr match {
      case Box(a, _) if !a.isInstanceOf[ODESystem] && !a.isInstanceOf[Loop] => (TactixLibrary.step::Nil, TactixLibrary.step::Nil)
      case Box(a, _) if a.isInstanceOf[ODESystem] => (TactixLibrary.solve::Nil, TactixLibrary.ODE::Nil)
      case Diamond(a, _) if !a.isInstanceOf[ODESystem] && !a.isInstanceOf[Loop] => (TactixLibrary.step::Nil, TactixLibrary.step::Nil)
      case Diamond(a, _) if a.isInstanceOf[ODESystem] => (TactixLibrary.solve::Nil, TactixLibrary.solve::Nil)
      case Forall(_, _) => (TacticIndex.allLStutter::Nil, TactixLibrary.allR::Nil)
      case Exists(_, _) => (TactixLibrary.existsL::Nil, TacticIndex.existsRStutter::Nil)
      case Not(_) => (TactixLibrary.notL::Nil, TactixLibrary.notR::Nil)
      case And(_, _) => (TactixLibrary.andL::Nil, TactixLibrary.andR::Nil)
      case Or(_, _) => (TactixLibrary.orL::Nil, TactixLibrary.orR::Nil)
      case Imply(_, _) => (TactixLibrary.implyL::Nil, TactixLibrary.implyR::Nil)
      case Equiv(_, _) => (TactixLibrary.equivL::Nil, TactixLibrary.equivR::Nil)
      case True => (Nil, ProofRuleTactics.closeTrue::Nil)
      case False => (ProofRuleTactics.closeFalse::Nil, Nil)
      case _ => (Nil, Nil)
    }
  }

}
