package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._
import edu.cmu.cs.ls.keymaera.tactics.SyntacticDerivationInContext._

/**
 * Breaking stuff up.
 * Created by nfulton on 2/14/15.
 */
object SyntacticDerivativeTermAxiomsInContext {

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // The top-level tactic implementations.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  def SyntacticDerivativeInContextT = new PositionTactic("Top-level tactic for contextual syntactic derivation of terms.") {
    def tactics : List[PositionTactic] =
      ConstantDerivativeT ::
      PowerDerivativeT ::
      SubtractDerivativeT ::
      AddDerivativeT ::
      NegativeDerivativeT ::
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

  def getFormula(f : Formula, pos : PosInExpr) : Option[Formula] = {
    var formula : Option[Formula] = None
    val fn = new ExpressionTraversalFunction {
      override def preF(p : PosInExpr, f:Formula) = {if(p == pos) {
        formula = Some(f)
        Left(Some(ExpressionTraversal.stop))
      } else {
        Left(None)
      }}
    }
    ExpressionTraversal.traverse(fn, f)
    formula
  }

  def getTerm(f : Formula, pos : PosInExpr) : Option[Term] = {
    var term : Option[Term] = None
    val fn = new ExpressionTraversalFunction {
      override def preT(pos : PosInExpr, t:Term) = {term = Some(t); Left(Some(ExpressionTraversal.stop))}
    }
    ExpressionTraversal.traverse(fn, f)
    term
  }

  def smallestFormulaContainingTerm(f : Formula, pos : PosInExpr) : (Formula, PosInExpr) = {
    getFormula(f, pos) match {
      case Some(formula) => (formula, pos) //base case.
      case None => smallestFormulaContainingTerm(f, PosInExpr(pos.pos.init))
    }
  }

  def getTermAtPosition(f : Formula, pos : PosInExpr) : Option[Term] = {
    var retVal : Option[Term] = None
    val fn = new ExpressionTraversalFunction() {
      override def preT(p : PosInExpr, t : Term) = {
        if(pos.equals(p)) {
          retVal = Some(t)
          Left(Some(ExpressionTraversal.stop))
        }
        else {
          Left(None)
        }
      }
    }
    ExpressionTraversal.traverse(fn, f)
    retVal
  }

}
