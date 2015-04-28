package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.FormulaConverter._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._
import edu.cmu.cs.ls.keymaera.tactics.SyntacticDerivationInContext._
import edu.cmu.cs.ls.keymaera.tools.Tool

/**
 * Breaking stuff up.
 * Created by nfulton on 2/14/15.
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
object SyntacticDerivativeTermAxiomsInContext {

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // The top-level tactic implementations.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  def SyntacticDerivativeInContextT = new PositionTactic("Top-level tactic for contextual syntactic derivation of terms.") {
    def tactics : List[PositionTactic] =
      ConstantDerivativeT ::
      PowerDerivativeT ::
      NegativeDerivativeT ::
      SubtractDerivativeT ::
      AddDerivativeT ::
      MultiplyDerivativeT ::
      DivideDerivativeT :: Nil

    def applicableTactic(s : Sequent, p : Position) = {
      val l = tactics.filter(_.applies(s,p))
      if(l.length > 0) Some(l.last) else None
    }

    //@todo this is wrong b/c what if we're applying in ^A -> [pi;](^^x > 0)' where ^^ is the term pos and ^ the formula pos?
    //@todo still not quite right I think.
    override def applies(s: Sequent, p: Position): Boolean = applicableTactic(s,p) match {
      case Some(_) =>
        //make sure that we're actually within a box context!
        SyntacticDerivationInContext.formulaContainsModality(s(p)).isDefined
      case None => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = applicableTactic(node.sequent, p) match {
        case Some(pt) => Some(pt(p))
        case None => None
      }
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Term positional helpers.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  def smallestFormulaContainingTerm(f : Formula, pos : PosInExpr) : (Formula, PosInExpr) = {
    f.subFormulaAt(pos) match {
      case Some(formula) => (formula, pos) //base case.
      case None => smallestFormulaContainingTerm(f, PosInExpr(pos.pos.init))
    }
  }
}
