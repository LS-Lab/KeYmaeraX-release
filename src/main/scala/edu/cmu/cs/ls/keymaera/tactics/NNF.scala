package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._

/**
* Rewrites formulas into negation normal form using DeMorgan's laws and double negation elimination.
* Created by nfulton on 2/11/15.
*/
object NNFRewrite {
  def apply(p : Position) = NegationNormalFormT(p)

  def NegationNormalFormT : PositionTactic = new PositionTactic("NNF") {
    override def applies(s: Sequent, p: Position): Boolean = ???

    override def apply(p: Position): Tactic = ???
  }

  /*
   * Obligation: Show [pi;](f <-> g) |- [pi;]f
   * Have: Transformation from |- f to |- g
   * Strategy: Apply monotonicity and then break up the implication, creating two obligations:
   *    f |- g, g
   *      Run the tactic at the final position and then do an axiom close on the antecedent and the final position.
   *    g |- g, f
   *      Axiom close on the antecedent and the original succedent position.
   */
  def useDerivationInContext(proofOfValidity : Tactic) : Position = ???

  /*
   * Have: !(!f)
   * Wnat: f
   */
  def DoubleNegationEliminationT : PositionTactic = new PositionTactic("Double Negation Elimination") {
    override def applies(s: Sequent, p: Position): Boolean = formulaAtPosition(s,p) match {
      case Some(Not(Not(f))) => true
      case _ => false
    }

    override def apply(doubleNegatedPos: Position): Tactic = new ConstructionTactic("Double Negation Elimination") {

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        //First construct an equality.
        val nnf = formulaAtPosition(node.sequent, doubleNegatedPos).getOrElse(throw new Exception("Tactic is not applicable here."))
        val f = nnf match {
          case Not(Not(x)) => x
          case _ => throw new Exception("Tactic is not applicable here.")
        }
        val equiv = Equiv(nnf, f)

        //The succedent position of the cut-in formula
        val cutAsObligationPos = SuccPosition(node.sequent.succ.length)
        val cutAsAssumptionPos = AntePosition(node.sequent.ante.length)

        def equalityRewrite = {
          new ApplyRule(new EqualityRewriting(cutAsAssumptionPos, doubleNegatedPos)) {
            override def applicable(node: ProofNode): Boolean = applies(node.sequent, doubleNegatedPos)
          }
        }

        val topLevelPositionContainingDoubleNegation = if(doubleNegatedPos.isAnte) {
          AntePosition(doubleNegatedPos.index)
        }
        else {
          SuccPosition(doubleNegatedPos.index)
        }

        Some(
          PropositionalTacticsImpl.cutT(Some(equiv)) & onBranch(
            (BranchLabels.cutShowLbl, proofOfDoubleNegElim(cutAsObligationPos)),
            (BranchLabels.cutUseLbl, debugT("DNEV equality rewrite") & equalityRewrite & hideT(topLevelPositionContainingDoubleNegation) & hideT(cutAsAssumptionPos))
          )
        )
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, doubleNegatedPos)
    }
  }

  def proofOfDoubleNegElim = new PositionTactic("Double Negation Elimination Validity (DNEV) proof") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case Equiv(Not(Not(x)), y) => x.equals(y)
      case _ => false
    }

    override def apply(initialEquivPosition: Position): Tactic = new ConstructionTactic("DNEV") {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        def leftTactic = {
          val succNoNegPos = SuccPosition(node.sequent.succ.length - 1)
          val doubleNegPos = AntePosition(node.sequent.ante.length)
          val singleNegPos = SuccPosition(node.sequent.succ.length) // f replaces init, so this was also the initial pos.
          val anteNoNegPos = doubleNegPos
          NotLeftT(doubleNegPos) & NotRightT(singleNegPos) & AxiomCloseT(anteNoNegPos, succNoNegPos)
        }

        def rightTactic = {
          val anteNoNegPos = AntePosition(node.sequent.ante.length)
          val succDoubleNegPos = SuccPosition(node.sequent.succ.length -1)
          val anteSingleNegPos = AntePosition(node.sequent.ante.length + 1)
          val succNoNegPos = succDoubleNegPos
          NotRightT(succDoubleNegPos) & NotLeftT(anteSingleNegPos) & AxiomCloseT(anteNoNegPos, succNoNegPos)
        }

        Some(
          debugT("DNEV begin") ~ EquivRightT(initialEquivPosition) & onBranch(
            (BranchLabels.equivLeftLbl, debugT("DNEV left") & leftTactic & debugT("DNEV left complete")),
            (BranchLabels.equivRightLbl, debugT("DNEV right") & rightTactic & debugT("DNEV right Complete"))
          )
        )
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, initialEquivPosition)
    }
  }
}
