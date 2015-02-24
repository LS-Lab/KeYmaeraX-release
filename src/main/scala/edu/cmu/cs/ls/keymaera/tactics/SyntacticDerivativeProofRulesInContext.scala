package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.SyntacticDerivationInContext._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._

/**
 * Created by nfulton on 2/23/15.
 */
object SyntacticDerivativeProofRulesInContext {
  import SyntacticDerivativeTermAxiomsInContext._
  import TacticLibrary._

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Proof rule implementations.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  def MonomialDerivativeInContext = new PositionTactic("Monomial Derivative in context") {
    val theTactic : PositionTactic with ApplicableAtTerm = MonomialDerivativeT

    override def applies(s: Sequent, p: Position): Boolean = {
      getTermAtPosition(s(p), p.inExpr) match {
        case Some(term) => theTactic.applies(term)
        case None => false
      }
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool : Tool, node : ProofNode): Option[Tactic] = getTermAtPosition(node.sequent(p), p.inExpr) match {
        case Some(term) => term match {
          case Derivative(dSort, Exp(eSort, x:Variable, Number(nSort, n))) => {
            val replacement = Multiply(eSort, Number(nSort, n), Exp(eSort, x, Number(nSort, n - 1)))
            val contextTactic = new TermTacticInContextTactic("The actual term axiom in context tactic for " + this.name, term, replacement, equivTactic(theTactic))
            Some(contextTactic(p))
          }
          case _ => None
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  def ConstantDerivativeInContext = new PositionTactic("Monomial Derivative in context") {
    val theTactic : PositionTactic with ApplicableAtTerm = ConstantDerivativeT

    override def applies(s: Sequent, p: Position): Boolean = {
      getTermAtPosition(s(p), p.inExpr) match {
        case Some(term) => theTactic.applies(term)
        case None => false
      }
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool : Tool, node : ProofNode): Option[Tactic] = getTermAtPosition(node.sequent(p), p.inExpr) match {
        case Some(term) => term match {
          case Derivative(dSort, Number(nsort, n)) => {
            val replacement = Number(nsort, 0)
            val contextTactic = new TermTacticInContextTactic("The actual term axiom in context tactic for " + this.name, term, replacement, equivTactic(theTactic))
            Some(contextTactic(p))
          }
          case _ => None
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  private def equivTactic(prt : PositionTactic with ApplicableAtTerm) : PositionTactic with ApplicableAtTerm = new PositionTactic("Prove equiv using " + prt.name) with ApplicableAtTerm {
    override def applies(t : Term) = prt.applies(t)

    override def applies(s: Sequent, p: Position): Boolean = getTermAtPosition(s(p), p.inExpr) match {
      case Some(x) => prt.applies(x)
      case _ => false
    }

    override def apply(p: Position): Tactic = debugT("This needs to close with a single term rewrite and axiom close.") & SearchTacticsImpl.locateTerm(prt) & debugT("here...") & AxiomCloseT
  }



  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  //Copy-pasted, in case changes are necessary:

  /**
   *
   * @param name The name of the tactic.
   * @param termToFind The term that will be replaced
   * @param replacementTerm The term which will replace termToFind
   * @param termTactic A tactic stating that termToFind <-> replacementTerm
   */
  class TermTacticInContextTactic(name : String, termToFind : Term, replacementTerm : Term, termTactic : PositionTactic with ApplicableAtTerm)
    extends ContextualizeKnowledgeForTermTactic(name) //replaced with PropositionalInContextTactic.
  {
    override def constructInstanceAndSubst(f: Formula): Option[(Formula, Option[Tactic])] = {
      val replacementPositionOption = findApplicablePositionForTermAxiom(f, termTactic)

      replacementPositionOption match {
        case Some((replacementPosition, _)) => {
          val (smallest, _) = smallestFormulaContainingTerm(f, replacementPosition)
          val desiredResult = replaceTerm(replacementTerm, termToFind, smallest)
          Some(desiredResult, None)
        }
        case None => None
      }
    }

    override def apply(pos : Position) = {
      def knowledgeContinuationTactic : Tactic = debugT("Trying to close something in context based on a term equivalence tactic.") & SearchTacticsImpl.onBranch(
        (BranchLabels.knowledgeSubclassContinue, locateSucc(EquivRightT) & onBranch(
          (BranchLabels.equivLeftLbl, locateTerm(termTactic) & AxiomCloseT),
          (BranchLabels.equivRightLbl, locateTerm(termTactic) & AxiomCloseT)
        )),
        ("additional obligation", locateSucc(ImplyRightT) & locateTerm(termTactic) & AxiomCloseT)
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
              assertT(forKAxiomInstance, SuccPosition(0))  & kModalModusPonensT(SuccPosition(0)) &
              abstractionT(SuccPosition(0)) & hideT(SuccPosition(0)) & skolemizeT(SuccPosition(0)) &
              assertT(0, 1) & cutT(Some(axiomInstance)) & debugT("Did the equiv I just cut in make sense??") &
              onBranch((cutUseLbl, debugT(s"Ready for equality rewriting at $fPos") &
                (equalityRewriting(AntePosition(0), SuccPosition(0, fPos)) & hideT(AntePosition(0)) &
                  hideT(pos.topLevel) & ImplyRightT(pos.topLevel) & AxiomCloseT) ~
                  (hideT(AntePosition(0)) & LabelBranch("additional obligation"))), //for term stuff.
                (cutShowLbl,
                  hideT(SuccPosition(0)) & cont & LabelBranch(BranchLabels.knowledgeSubclassContinue))))

            Some(cutT(Some(forKAxiomInstance)) & onBranch((cutUseLbl, axiomApplyTactic), (cutShowLbl, axiomInstanceTactic)))
          case None => None
        }
      }
    }

  }
}
