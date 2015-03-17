package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.AxiomaticRuleTactics._
import edu.cmu.cs.ls.keymaera.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.SyntacticDerivationInContext._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._

/**
 * Created by nfulton on 2/23/15.
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
object SyntacticDerivativeProofRulesInContext {
  import SyntacticDerivativeTermAxiomsInContext._
  import TacticLibrary._

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Proof rule implementations.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  def PowerDerivativeInContext = new PositionTactic("Power Derivative in context") {
    val theTactic : PositionTactic with ApplicableAtTerm = PowerDerivativeT

    override def applies(s: Sequent, p: Position): Boolean = {
      getTermAtPosition(s(p), p.inExpr) match {
        case Some(term) => theTactic.applies(term)
        case None => false
      }
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool : Tool, node : ProofNode): Option[Tactic] = getTermAtPosition(node.sequent(p), p.inExpr) match {
        case Some(term) => term match {
          case Derivative(dSort, Exp(eSort, x, c@Number(nSort, n))) if n != BigDecimal(0) =>
            val replacement = Multiply(eSort, Multiply(eSort, Number(nSort, n), Exp(eSort, x, Subtract(nSort, c, Number(1)))), Derivative(dSort, x))
            val contextTactic = new TermTacticInContextTactic("The actual term axiom in context tactic for " + this.name, term, replacement, theTactic)
            Some(contextTactic(p))
          case Derivative(dSort, Exp(eSort, x, Number(nSort, n))) if n == BigDecimal(0) =>
            Some(errorT(s"Exponent 0 not allowed, but $n == 0") & stopT)
          case _ => None
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  def ConstantDerivativeInContext = new PositionTactic("Constant Derivative in context") {
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
            val contextTactic = new TermTacticInContextTactic("The actual term axiom in context tactic for " + this.name, term, replacement, theTactic)
            Some(contextTactic(p))
          }
          case _ => None
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
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
      import scala.language.postfixOps
      def knowledgeContinuationTactic : Tactic = debugT("Trying to close something in context based on a term equivalence tactic.") & SearchTacticsImpl.onBranch(
        (BranchLabels.knowledgeSubclassContinue, locateSucc(EquivRightT) &
          ((locateTerm(termTactic, inAnte = true) | locateTerm(termTactic, inAnte = false))*) &
          (AxiomCloseT | debugT(s"${getClass.getCanonicalName}: Should never happen using ${termTactic.name}") & stopT)),
        ("additional obligation", debugT("Ever called?") & locateSucc(ImplyRightT) & locateTerm(termTactic, inAnte = false) &
          (AxiomCloseT | debugT("Should never happen") & stopT))
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
            val (f, _) = smallestFormulaContainingTerm(node.sequent(pos), pos.inExpr)

            val fInContext = TacticHelper.getFormula(node.sequent, pos.topLevel)
            val desiredResultInContext = replaceFormula(desiredResult, f, fInContext)

            val congruenceAxiomInstance = Equiv(fInContext, desiredResultInContext)
            val axiomInstance = Equiv(f, desiredResult)

            val axiomInstPos = AntePosition(node.sequent.ante.length)

            val axiomApplyTactic = assertPT(congruenceAxiomInstance, s"$getClass A.1")(axiomInstPos) &
              EquivLeftT(axiomInstPos) & onBranch(
                (equivLeftLbl, AndLeftT(axiomInstPos) & AxiomCloseT),
                (equivRightLbl, hideT(pos.topLevel) & AndLeftT(axiomInstPos) & hideT(axiomInstPos) & NotLeftT(axiomInstPos))
              )

            val cont = renameTactic match {
              case Some(t) => assertT(0, 1) & t
              case None => NilT
            }

            val axiomPos = SuccPosition(node.sequent.succ.length)

            val axiomInstanceTactic =
              (assertPT(congruenceAxiomInstance, s"$getClass A.2") & cohideT)(axiomPos) & assertT(0,1) &
                (boxCongruenceT*) & assertT(0,1) & cutT(Some(axiomInstance)) & onBranch(
                (cutUseLbl, assertPT(axiomInstance, s"$getClass A.3")(AntePosition(0)) & (
                  ((AxiomCloseT | locateAnte(Propositional) | locateSucc(Propositional))*) |
                    debugT(s"$getClass: axiom close failed unexpectedly") & stopT)),
                (cutShowLbl, hideT(SuccPosition(0)) & cont & LabelBranch(BranchLabels.knowledgeSubclassContinue))
              )
            Some(cutT(Some(congruenceAxiomInstance)) & onBranch((cutUseLbl, axiomApplyTactic), (cutShowLbl, axiomInstanceTactic)))
          case None => None
        }
      }
    }

  }
}
