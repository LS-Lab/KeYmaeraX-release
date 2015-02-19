package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.ContextualizeKnowledgeTactic
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.TacticHelper._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl.onBranch

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

  ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // !(f ^ g) <-> !f | !g
  ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  def proofOfDeMorganConjunction = new PositionTactic("DeMorgan - Conjunction") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case Equiv(Not(And(l,r)), Or(Not(l2), Not(r2))) => {
        l.equals(l2) && r.equals(r2) && !p.isAnte
      }
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
        case Equiv(Not(And(l1, r1)), Or(Not(l2), Not(r2))) => {
          assert(p.isAnte == false) //The proof starts with an equivright.
          assert(l1.equals(l2) && r1.equals(r2)) //justifies:
          val f = l1
          val g = r1

          val newAntePos = AntePosition(node.sequent.ante.length)
          def newerAntePos = AntePosition(node.sequent.ante.length + 1)
          val newSuccPos = SuccPosition(node.sequent.succ.length)

          Some(
            EquivRightT(p) && onBranch(
              (BranchLabels.equivLeftLbl, NotLeftT(newAntePos) & AndRightT(newSuccPos) & OrRightT(p) & ((locate(NotRightT) *) & AxiomCloseT )),
              (BranchLabels.equivRightLbl, NotRightT(p) & AndLeftT(newerAntePos) & OrLeftT(newAntePos) & (NotLeftT(newAntePos) & AxiomCloseT))
            )
          )
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  def rewriteNegConjunct = new PositionTactic("Rewrite conjunction") {
    override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
      case Not(And(_,_)) => true
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val original = getFormula(node.sequent, p)

        val replacement = original match {
          case Not(And(l,r)) => Or(Not(l), Not(r))
          case _ => ???
        }

        Some(
          rewriteEquiv(original, replacement, proofOfDeMorganConjunction)(p)
        )
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // !(f | g) <-> !f & !g
  ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  def proofOfDeMorganDisjunction = new PositionTactic("DeMorgan - Disjunction") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case Equiv(Not(Or(l,r)), And(Not(l2), Not(r2))) => {
        l.equals(l2) && r.equals(r2) && !p.isAnte
      }
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
        case Equiv(Not(Or(l1, r1)), And(Not(l2), Not(r2))) => {
          assert(p.isAnte == false) //The proof starts with an equivright.
          assert(l1.equals(l2) && r1.equals(r2)) //justifies:
          val f = l1
          val g = r1

          val newAntePos = AntePosition(node.sequent.ante.length)
          val orAntePos = AntePosition(node.sequent.ante.length + 2)
          val newSuccPos = SuccPosition(node.sequent.succ.length)


          Some(
            EquivRightT(p) && onBranch(
              (BranchLabels.equivLeftLbl, NotLeftT(newAntePos) & AndRightT(p) & ( NotRightT(p) & OrRightT(p) & AxiomCloseT)),
              (BranchLabels.equivRightLbl, AndLeftT(newAntePos) & NotRightT(p) & OrLeftT(orAntePos) & (NotLeftT(newAntePos) & NotLeftT(newAntePos) & AxiomCloseT))
            )
          )
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  def rewriteNegDisjunct = new PositionTactic("Rewrite disjunction") {
    override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
      case Not(Or(_,_)) => true
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val original = getFormula(node.sequent, p)

        val replacement = original match {
          case Not(Or(l,r)) => And(Not(l), Not(r))
          case _ => ???
        }

        Some(
          rewriteEquiv(original, replacement, proofOfDeMorganDisjunction)(p)
        )
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Double negation elimination
  ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  def DoubleNegationElimination(position : Position) : Tactic = ((new TacticInContextT(ValidityOfDoubleNegationEliminationT(position)) {
    override def applies(f: Formula) = f match {
      case Not(Not(_)) => true
      case _ => false
    }

    override def constructInstanceAndSubst(f: Formula): Option[(Formula, Option[Tactic])] = f match {
      case Not(Not(phi)) => Some(phi, None)
      case _ => None
    }
  })(position) ~ SearchTacticsImpl.locateSucc(ImplyRightT) ~ AxiomCloseT)

  /*
   * Have: !(!f)
   * Want: f
   */
  def ValidityOfDoubleNegationEliminationT : PositionTactic = new PositionTactic("Double Negation Elimination") {
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
          NotRightT(succDoubleNegPos) & NotLeftT(anteSingleNegPos) &  AxiomCloseT(anteNoNegPos, succNoNegPos)
        }

        Some(
          debugT("DNEV begin") ~ EquivRightT(initialEquivPosition) ~ (onBranch(
            (BranchLabels.equivLeftLbl, debugT("DNEV left") ~ leftTactic ~ debugT("DNEV left complete")),
            (BranchLabels.equivRightLbl, debugT("DNEV right") ~ rightTactic ~ debugT("DNEV right Complete"))
          ))
        )
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, initialEquivPosition)
    }
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Context helper.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  abstract class TacticInContextT(tactic : Tactic)
    extends ContextualizeKnowledgeTactic("In Context: " + tactic.name) {
    def applies(f: Formula): Boolean
    override def applies(s: Sequent, p: Position): Boolean = applies(getFormula(s, p))

    override def apply(pos: Position): Tactic = super.apply(pos) &
      onBranch("knowledge subclass continue", tactic)
  }

  def rewriteEquiv(original : Formula, replacement : Formula, proofOfEquiv : PositionTactic) : PositionTactic = new PositionTactic("Rewrite for " + proofOfEquiv.name) {
    override def applies(s: Sequent, p: Position): Boolean = formulaAtPosition(s,p) match {
      case Some(formula) => formula.equals(original)
      case _ => false
    }

    override def apply(targetPosition: Position): Tactic = new ConstructionTactic(this.name) {

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        //First construct an equality.
        val equiv = Equiv(original, replacement)

        //The succedent position of the cut-in formula
        val cutAsObligationPos = SuccPosition(node.sequent.succ.length)
        val cutAsAssumptionPos = AntePosition(node.sequent.ante.length)

        def equalityRewrite = {
          new ApplyRule(new EqualityRewriting(cutAsAssumptionPos, targetPosition)) {
            override def applicable(node: ProofNode): Boolean = applies(node.sequent, targetPosition)
          }
        }

        val topLevelPositionContainingOriginalFormula = targetPosition.topLevel

        Some(
          PropositionalTacticsImpl.cutT(Some(equiv)) & onBranch(
            (BranchLabels.cutShowLbl, proofOfEquiv(cutAsObligationPos)),
            (BranchLabels.cutUseLbl, equalityRewrite & hideT(topLevelPositionContainingOriginalFormula) & hideT(cutAsAssumptionPos)) //@todo I think I have to run the continuation here or something.
          )
        //@todo
        )
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, targetPosition)
    }
  }
}
