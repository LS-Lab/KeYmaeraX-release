package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{TraverseToPosition, StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaera.tactics.SyntacticDerivationInContext._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.TacticHelper._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl._

/**
 * Breaking stuff up.
 * Created by nfulton on 2/14/15.
 */
object SyntacticDerivativeTermAxiomsInContext {
  import edu.cmu.cs.ls.keymaera.tactics.SyntacticDerivationInContext._

  ///////////////1///////////////////////////////////////////////////////////////////////////////////////////////////////
  // Section 3: Term axioms in context. This should be used for the master rewrites.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


  import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // The top-level tactic implementations.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  def ConstantFnDerivativeInContextT = new PositionTactic("Constant Function Symbol Derivative in context") {
    val theTactic = ConstantFnDerivativeT

    override def applies(s: Sequent, p: Position): Boolean = {
      getTermAtPosition(s(p), p.inExpr) match {
        case Some(term) => theTactic.applies(term)
        case None => false
      }
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool : Tool, node : ProofNode): Option[Tactic] = getTermAtPosition(node.sequent(p), p.inExpr) match {
        case Some(term) => term match {
          case Derivative(dSort, s@Apply(Function(_, _, Unit, sSort), Nothing)) => {
            val replacement = Number(0)
            val contextTactic = new TermTacticInContextTactic("The actual term axiom in context tactic for " + this.name, term, replacement, theTactic)

            Some(contextTactic(p))
          }
          case _ => None
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  def NegativeDerivativeInContextT = new PositionTactic("Negative Derivative in context") {
    val theTactic = NegativeDerivativeT 

    override def applies(s: Sequent, p: Position): Boolean = {
      getTermAtPosition(s(p), p.inExpr) match {
        case Some(term) => theTactic.applies(term)
        case None => false
      }
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool : Tool, node : ProofNode): Option[Tactic] = getTermAtPosition(node.sequent(p), p.inExpr) match {
        case Some(term) => term match {
          case Derivative(dSort, Neg(sSort, s)) => {
            val ds = Derivative(sSort, s)
            val replacement = Neg(sSort, ds)
            val contextTactic = new TermTacticInContextTactic("The actual term axiom in context tactic for " + this.name, term, replacement, theTactic)

            Some(contextTactic(p))
          }
          case _ => None
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  def DivideDerivativeInContextT = new PositionTactic("Divide Derivative in context") {
    val theTactic = DivideDerivativeT

    override def applies(s: Sequent, p: Position): Boolean = {
      getTermAtPosition(s(p), p.inExpr) match {
        case Some(term) => theTactic.applies(term)
        case None => false
      }
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool : Tool, node : ProofNode): Option[Tactic] = getTermAtPosition(node.sequent(p), p.inExpr) match {
        case Some(term) => term match {
          case Derivative(dSort, Divide(stSort, s, t)) => {
            val ds = Derivative(stSort, s)
            val dt = Derivative(stSort, t)
            val replacement = Divide(dSort,  Subtract(stSort, Multiply(stSort, ds, t), Multiply(stSort, s, dt)), Exp(stSort, t, Number(2)))
            val contextTactic = new TermTacticInContextTactic("The actual term axiom in context tactic for " + this.name, term, replacement, theTactic)

            Some(contextTactic(p))
          }
          case _ => None
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  def MultiplyDerivativeInContextT = new PositionTactic("Multiply Derivative in context") {
    val theTactic = MultiplyDerivativeT

    override def applies(s: Sequent, p: Position): Boolean = {
      getTermAtPosition(s(p), p.inExpr) match {
        case Some(term) => theTactic.applies(term)
        case None => false
      }
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool : Tool, node : ProofNode): Option[Tactic] = getTermAtPosition(node.sequent(p), p.inExpr) match {
        case Some(term) => term match {
          case Derivative(dSort, Multiply(stSort, s, t)) => {
            val ds = Derivative(stSort, s)
            val dt = Derivative(stSort, t)
            val replacement = Add(dSort,  Multiply(stSort, ds, t), Multiply(stSort, s, dt))
            val contextTactic = new TermTacticInContextTactic("The actual term axiom in context tactic for " + this.name, term, replacement, theTactic)

            Some(contextTactic(p))
          }
          case _ => None
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  def AddDerivativeInContextT = new PositionTactic("Add Derivative in context") {
    val theTactic = AddDerivativeT

    override def applies(s: Sequent, p: Position): Boolean = {
      getTermAtPosition(s(p), p.inExpr) match {
        case Some(term) => theTactic.applies(term)
        case None => false
      }
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool : Tool, node : ProofNode): Option[Tactic] = getTermAtPosition(node.sequent(p), p.inExpr) match {
        case Some(term) => term match {
          case Derivative(dSort, Add(stSort, s, t)) => {
            val replacement = Add(dSort, Derivative(stSort, s), Derivative(stSort, t))
            val contextTactic = new TermTacticInContextTactic("The actual term axiom in context tactic for " + this.name, term, replacement, theTactic)

            Some(contextTactic(p))
          }
          case _ => None
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

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
            val contextTactic = new TermTacticInContextTactic("The actual term axiom in context tactic for " + this.name, term, replacement, theTactic)

            Some(contextTactic(p))
          }
          case _ => None
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }


  def SyntacticDerivativeInContextT = new PositionTactic("Top-level tactic for contextual syntactic derivation of terms.") {
    def tactics : List[PositionTactic] = SyntacticDerivativeProofRulesInContext.ConstantDerivativeInContext ::
      SyntacticDerivativeProofRulesInContext.MonomialDerivativeInContext :: SubtractDerivativeInContextT ::
      AddDerivativeInContextT :: NegativeDerivativeInContextT :: MultiplyDerivativeInContextT ::
      DivideDerivativeInContextT :: ConstantFnDerivativeInContextT :: Nil

    def applicableTactic(s : Sequent, p : Position) = {
      val l = tactics.filter(_.applies(s,p))
      if(l.length > 0) Some(l.last) else None
    }

    //@todo this is wrong b/c what if we're applying in ^A -> [pi;](^^x > 0)' where ^^ is the term pos and ^ the formula pos?
    //@todo still not quite right I think.
    override def applies(s: Sequent, p: Position): Boolean = applicableTactic(s,p) match {
      case Some(_) => {
        //make sure that we're actually within a box context!
        SyntacticDerivationInContext.formulaContainsModality(s(p)).isDefined
      }
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
  // Implementation of term-level rewrites.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /**
   *
   * @param name The name of the tactic.
   * @param termToFind The term that will be replaced
   * @param replacementTerm The term which will replace termToFind
   * @param termTactic A tactic stating that termToFind <-> replacementTerm
   */
  class TermTacticInContextTactic(name : String, termToFind : Term, replacementTerm : Term, termTactic : TermAxiomTactic)
    extends ContextualizeKnowledgeForTermTactic(name) //replaced with PropositionalInContextTactic.
  {
    override def constructInstanceAndSubst(f: Formula): Option[(Formula, Option[Tactic])] = {
      val replacementPositionOption = findApplicablePositionForTermAxiom(f, termTactic)

      replacementPositionOption match {
        case Some((replacementPosition, _)) =>
          val (smallest, _) = smallestFormulaContainingTerm(f, replacementPosition)
          val desiredResult = replaceTerm(replacementTerm, termToFind, smallest)
          Some(desiredResult, None)
        case None => None
      }
    }

    override def apply(pos : Position) = {
      def knowledgeContinuationTactic : Tactic = SearchTacticsImpl.onBranch(
        (BranchLabels.knowledgeSubclassContinue, locateSucc(EquivRightT) & onBranch(
          (BranchLabels.equivLeftLbl, locateTerm(termTactic, inAnte = Some(true)) & AxiomCloseT),
          (BranchLabels.equivRightLbl, locateTerm(termTactic, inAnte = Some(false)) & AxiomCloseT)
        )),
        ("additional obligation", (locateSucc(ImplyRightT) & locateTerm(termTactic)) ~ AxiomCloseT)
      )

      super.apply(pos) & knowledgeContinuationTactic
    }
  }

  /**
   * Be very careful re-using this for other purposes...
   */
  abstract class ContextualizeKnowledgeForTermTactic(name: String) extends PositionTactic(name) {
    override def applies(s: Sequent, p: Position): Boolean = getTerm(s(p), p.inExpr) match {
      case Some(_) => true
      case _ => false
    }

    /**
     * This method constructs the desired result before the renaming.
     *
     * @param f the formula that should be rewritten
     * @return Desired result before executing the renaming
     */
    def constructInstanceAndSubst(f: Formula): Option[(Formula, Option[Tactic])]

    //@TODO Add contract that applies()=>\result fine
    override def apply(pos: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        import TacticLibrary.{abstractionT,skolemizeT,cutT,equalityRewriting}

        constructInstanceAndSubst(node.sequent(pos)) match {
          case Some((desiredResult, renameTactic)) =>
            val (f, fPos) = smallestFormulaContainingTerm(node.sequent(pos), pos.inExpr)

            val fInContext = TacticHelper.getFormula(node.sequent, pos.topLevel)
            val desiredResultInContext = replaceFormula(desiredResult, f, fInContext)

            val forKAxiomInstance = Imply(desiredResultInContext, fInContext)
            val axiomInstance = Equiv(f, desiredResult)

            val axiomInstPos = AntePosition(node.sequent.ante.length)

            val axiomApplyTactic = assertPT(forKAxiomInstance, s"$getClass A.1")(axiomInstPos) &
              ImplyLeftT(axiomInstPos) && (
              hideT(SuccPosition(0)) /* desired result remains */,
              AxiomCloseT ~ TacticLibrary.debugT("axiomclose failed here.")&assertT(0,0)
              )

            val cont = renameTactic match {
              case Some(t) => assertT(0, 1) & t
              case None => NilT
            }

            val axiomPos = SuccPosition(node.sequent.succ.length)

            val axiomInstanceTactic = (assertPT(forKAxiomInstance, s"$getClass A.2") & cohideT)(axiomPos) & (assertT(0,1) &
              assertT(forKAxiomInstance, SuccPosition(0)) & kModalModusPonensT(SuccPosition(0)) &
              abstractionT(SuccPosition(0)) & hideT(SuccPosition(0)) & skolemizeT(SuccPosition(0)) &
              assertT(0, 1) & cutT(Some(axiomInstance)) & debugT(s"ready for term rewriting at $fPos") &
              onBranch((cutUseLbl,
                (equalityRewriting(AntePosition(0), SuccPosition(0, fPos)) & debugT("term rewriting result") & ((assertPT(axiomInstance, s"$getClass A.3")&hideT)(AntePosition(0)) & hideT(pos.topLevel)) & ImplyRightT(pos.topLevel) & AxiomCloseT) ~
                  (hideT(axiomInstPos) & LabelBranch("additional obligation"))), //for term stuff.
                (cutShowLbl,
                  hideT(SuccPosition(0)) & cont & LabelBranch(BranchLabels.knowledgeSubclassContinue))))

            Some(cutT(Some(forKAxiomInstance)) & onBranch((cutUseLbl, axiomApplyTactic), (cutShowLbl, axiomInstanceTactic)))
          case None => None
        }
      }
    }

  }


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Some tactics which could be generally useful, and it might make sense to move into the TacticsLibrary.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

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


  /**
   * @todo check this implementation.
   * @param original The original expression
   * @param termToReplace The position to replace.
   * @param replacement The term to insert at position p
   * @return [replacement / termToReplace] original
   */
  def replaceTerm(replacement : Term, termToReplace : Term, original : Formula) : Formula = {
    val fn = new ExpressionTraversalFunction {
      override def preT(posInExpr : PosInExpr, term : Term) = if(term.equals(termToReplace)) Right(replacement) else Left(None)
    }
    ExpressionTraversal.traverse(fn, original).get
  }

  def replaceFormula(replacement : Formula, f : Formula, original : Formula) : Formula = {
    val fn = new ExpressionTraversalFunction {
      override def preF(posInExpr : PosInExpr, formula : Formula) = {
        if(f.equals(formula)) {
          Right(replacement)
        } else {
          Left(None)
        }
      }
    }
    ExpressionTraversal.traverse(fn, original).get
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Term positional helpers.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  def getFormula(f : Formula, pos : PosInExpr) : Option[Formula] = {
    var formula : Option[Formula] = None;
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
    var term : Option[Term] = None;
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
