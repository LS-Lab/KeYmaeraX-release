package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{TraverseToPosition, StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.TacticHelper._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl._

/**
 * This file contains the contextual term  context tactics.
 * Created by nfulton on 2/14/15.
 */
object SyntacticDerivativeTermAxiomsInContext {
  import edu.cmu.cs.ls.keymaera.tactics.SyntacticDerivationAxiomTactics._

  ///////////////1///////////////////////////////////////////////////////////////////////////////////////////////////////
  // Section 3: Term axioms in context. This should be used for the master rewrites.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


  import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._


  def SubtractDerivativeInContextT = new PositionTactic("Subtract Derivative in context") {
    val theTactic = SubtractDerivativeT
    override def applies(s: Sequent, p: Position): Boolean = {
      getTermAtPosition(s(p), p.inExpr) match {
        case Some(term) => theTactic.applies(term)
        case None => false
      }
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool : Tool, node : ProofNode): Option[Tactic] = getTermAtPosition(node.sequent(p), p.inExpr) match {
        case Some(term) => term match {
          case Derivative(dSort, Subtract(stSort, s, t)) => {
            val replacement = Subtract(dSort, Derivative(stSort, s), Derivative(stSort, t))
            val contextTactic = new TermAxiomInContextTactic("The actual term axiom in context tactic for " + this.name, term, replacement, SubtractDerivativeT)
            val positionOfFormula = if(p.isAnte) {
              AntePosition(p.index)
            }
            else {
              SuccPosition(p.index)
            }

            Some(
              contextTactic(positionOfFormula)
            )
          }
          case _ => None
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  private def getTermAtPosition(f : Formula, pos : PosInExpr) : Option[Term] = {
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

  class TermAxiomInContextTactic(name : String, termToFind : Term, replacementTerm : Term, termTactic : TermAxiomTactic)
    extends ContextualizeKnowledgeTactic(name) //replaced with PropositionalInContextTactic.
  {
    override def applies(f: Formula): Boolean = findApplicablePositionForTermAxiom(f, termTactic) match {
      case Some(_) => true
      case None => false
    }

    override def constructInstanceAndSubst(f: Formula): Option[(Formula, Option[Tactic])] = {
      val replacementPositionOption = findApplicablePositionForTermAxiom(f, termTactic)

      replacementPositionOption match {
        case Some((replacementPosition, _)) => Some(replaceTerm(f, replacementTerm, replacementPosition), None)
        case None => None
      }
    }

    override def apply(pos : Position) = {
      def theBranchTactic : Tactic = sequentToImplication &
        kModalModusPonensT(pos) &
        boxDerivativeAssignT(pos) & //will it always be a box assign?
        implyToEquiv(pos) &
        locateTerm(termTactic) &
        EquivRightT(pos) & onBranch(
          (BranchLabels.equivLeftLbl, closeT),
          (BranchLabels.equivRightLbl, closeT)
        )

      def knowledgeContinuationTactic : Tactic = SearchTacticsImpl.onBranch(
        (BranchLabels.knowledgeSubclassContinue, locateSucc(EquivRightT) & onBranch(
          (BranchLabels.equivLeftLbl, theBranchTactic),
          (BranchLabels.equivRightLbl, theBranchTactic)
        )),
        ("additional obligation", locateSucc(ImplyRightT) & locateTerm(termTactic) & AxiomCloseT)
      )

      super.apply(pos) & knowledgeContinuationTactic

    }

    /**
     * @todo check this implementation.
     * @param original The original expression
     * @param replacement The term to insert at position p
     * @param p The position in the expression to replace.
     * @return A new expression identical to original except at position p.
     */
    private def replaceTerm(original : Formula, replacement : Term, p : PosInExpr) : Formula = {
      val fn = new ExpressionTraversalFunction {
        override def preT(posInExpr : PosInExpr, term : Term) = if(posInExpr.equals(p)) Right(replacement) else Right(term)
      }
      ExpressionTraversal.traverse(fn, original).get
    }
  }

  /**
   * Converts the last two formulas in a sequent into an implication. So to show f |- g, you can now just show |- f -> g.
   * This is useful for proof rules which only apply the implications.
   */
  def sequentToImplication : Tactic = (new PositionTactic("Convert sequent to identical implication.") {
    override def applies(s: Sequent, p: Position): Boolean = true

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val originalAntePos = AntePosition(node.sequent.ante.length - 1)
        val originalSuccPos = SuccPosition(node.sequent.succ.length - 1)
        val cutF = Imply(node.sequent(originalAntePos), node.sequent(originalSuccPos))
        val useCutPos = AntePosition(node.sequent.ante.length)

        Some(cutT(Some(cutF)) & onBranch(
          (BranchLabels.cutShowLbl, hideT(originalAntePos) & hideT(originalSuccPos)),
          (BranchLabels.cutUseLbl, (ImplyLeftT(useCutPos) & (closeT, closeT)))
        ))
      }

      override def applicable(node: ProofNode): Boolean = true

    }
  })(SuccPosition(0))

  /*
   * After running this you will have two results. The first is the ????? should only be one?
   */
  def implyToEquiv : PositionTactic = new PositionTactic("Translate implication to equivalence") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case Imply(_,_) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val (left,right) = node.sequent(p) match {
          case Imply(l,r) => (l,r)
          case _ => ???
        }
        val cutF = Equiv(left,right)

        val newAntePos = AntePosition(node.sequent.ante.length)
        Some(
          cutT(Some(cutF)) & onBranch(
            (BranchLabels.cutShowLbl, hideT(p)),
            (BranchLabels.cutUseLbl, locateAnte(EquivLeftT) & onBranch(
              (BranchLabels.equivLeftLbl, locateAnte(AndLeftT) & locateSucc(ImplyRightT) & AxiomCloseT ~ debugT("Should have closed!")),
              (BranchLabels.equivRightLbl, AndLeftT(newAntePos) & (locateAnte(NotLeftT) *) & locateSucc(ImplyRightT) & AxiomCloseT ~ debugT("Should have closed!"))
            ))
          )
        )


      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

}
