package edu.cmu.cs.ls.keymaera.tactics

import ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.AxiomaticRuleTactics.equivalenceCongruenceT
import edu.cmu.cs.ls.keymaera.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaera.tactics.ContextTactics.cutInContext
import edu.cmu.cs.ls.keymaera.tactics.EqualityRewritingImpl.equivRewriting
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl.cohideT
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl.lastSucc
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.TacticHelper._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl.onBranch
import edu.cmu.cs.ls.keymaera.tools.Tool

/**
* Rewrites formulas into negation normal form using DeMorgan's laws and double negation elimination.
 * Each of the rewrites has two definitions. The first is a proof that the associated equivalence between formulas is
 * valid, and the second is a rewrite of some formula containing a subformula with the RHS of the associated equivalence.
 * Doing things in context is handled by the master tactics @todo
* Created by nfulton on 2/11/15.
*/
object NNFRewrite {
  def apply(p : Position) : Tactic = NegationNormalFormT(p)

  def NegationNormalFormT : PositionTactic = new PositionTactic("Negation Normal Form for Propositional Formula") {
    override def applies(s: Sequent, p: Position): Boolean = {
      val fn = new ExpressionTraversalFunction {
        var foundNegatedFormula = false
        override def preF(p : PosInExpr, f : Formula) = {
          f match {
            case Not(x) => if(!x.isInstanceOf[NamedSymbol]) { println("Found a negatated formula: " + f); foundNegatedFormula = true; Left(Some(ExpressionTraversal.stop)) } else Left(None)
            case _ => Left(None)
          }
        }
      }

      ExpressionTraversal.traverse(fn, s(p))
      fn.foundNegatedFormula
    }

    //@todo example of pt 5 desirability...
    override def apply(p: Position): Tactic = {
      import scala.language.postfixOps
      import ArithmeticTacticsImpl._
      def l : PositionTactic => Tactic = SearchTacticsImpl.locateSubposition(p)
      def nl: PositionTactic => Tactic = SearchTacticsImpl.locateSubposition(p, { case Not(_) => true case _ => false})
      ((debugT("Before an iteration of the NNF rewrite:") &
        (l(rewriteImplicationToDisjunction) | l(rewriteNegConjunct) |
         l(rewriteNegDisjunct) | l(rewriteDoubleNegationEliminationT)))*) ~ (
        (debugT("Binary relation negation") &
          (nl(NegateGreaterEqualsT)
            | nl(NegateGreaterThanT)
            | nl(NegateEqualsT)
            | nl(NegateNotEqualsT)
            | nl(NegateLessThanT)
            | nl(NegateLessEqualsT)
            ))*) ~ NilT /* so that we don't fail this tactic if none of the negation stuff applies */

    }
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Implication
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  def implicationToDisjunctionEquiv = new PositionTactic("Prove the classical definition of implication.") {
    override def applies(s: Sequent, p: Position): Boolean = getFormula(s,p) match {
      case Equiv(Imply(p,q), Or(Not(p2), q2)) => p.equals(p2) && q.equals(q2)
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val newAntePos = AntePosition(node.sequent.ante.length)
        val newSuccPos = SuccPosition(node.sequent.succ.length)

        def rightT = ImplyRightT(p) & OrLeftT(newAntePos) & (NotLeftT(newAntePos) & AxiomCloseT, AxiomCloseT)

        def leftT = ImplyLeftT(newAntePos) && (OrRightT(p) ~ NotRightT(newSuccPos) & AxiomCloseT, OrRightT(p) & AxiomCloseT)

        Some(
          EquivRightT(p) & onBranch(
            (BranchLabels.equivLeftLbl, leftT),
            (BranchLabels.equivRightLbl, rightT)
          )
        )
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  def rewriteImplicationToDisjunction = new PositionTactic("Rewrite implication") {
    override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
      case Imply(l,r) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val original = getFormula(node.sequent, p)

        val replacement = original match {
          case Imply(p, q) => Or(Not(p), q)
          case _ => ???
        }

        Some(
          rewriteEquiv(original, replacement, implicationToDisjunctionEquiv)(p)
        )
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
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
          assert(!p.isAnte) //The proof starts with an equivright.
          assert(l1.equals(l2) && r1.equals(r2)) //justifies:
          val f = l1
          val g = r1

          val newAntePos = AntePosition(node.sequent.ante.length)
          def newerAntePos = AntePosition(node.sequent.ante.length + 1)
          val newSuccPos = SuccPosition(node.sequent.succ.length)
          val lastSuccPos = SuccPosition(node.sequent.succ.length + 1)


          Some(
            EquivRightT(p) && onBranch(
              (BranchLabels.equivLeftLbl, NotLeftT(newAntePos) & AndRightT(newSuccPos) && (OrRightT(p) & NotRightT(newSuccPos) & AxiomCloseT, OrRightT(p)& NotRightT(lastSuccPos) & AxiomCloseT)),
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
      case _ => false
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
          assert(!p.isAnte) //The proof starts with an equivright.
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
      case _ => false
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

  /*
   * Have: !(!f)
   * Want: f
   */
  def rewriteDoubleNegationEliminationT : PositionTactic = new PositionTactic("Double Negation Elimination") {
    override def applies(s: Sequent, p: Position): Boolean = formulaAtPosition(s,p) match {
      case Some(Not(Not(f))) => true
      case _ => false
    }

    override def apply(doubleNegatedPos: Position): Tactic = new ConstructionTactic("Double Negation Elimination") {

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val original = formulaAtPosition(node.sequent, doubleNegatedPos).getOrElse(throw new Exception("Tactic is not applicable here."))
        val replacement = original match {
          case Not(Not(x)) => x
          case _ => throw new Exception("Tactic is not applicable here.")
        }
        Some(rewriteEquiv(original, replacement, proofOfDoubleNegElim)(doubleNegatedPos))
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
          debugT("DNEV begin") ~ EquivRightT(initialEquivPosition) ~ onBranch(
            (BranchLabels.equivLeftLbl, debugT("DNEV left") ~ leftTactic ~ debugT("DNEV left complete")),
            (BranchLabels.equivRightLbl, debugT("DNEV right") ~ rightTactic ~ debugT("DNEV right Complete"))
          )
        )
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, initialEquivPosition)
    }
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Context helper.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  def rewriteEquiv(original : Formula, replacement : Formula, proofOfEquiv : PositionTactic): PositionTactic = new PositionTactic("Rewrite for " + proofOfEquiv.name) {
    override def applies(s: Sequent, p: Position): Boolean = formulaAtPosition(s,p) match {
      case Some(formula) => formula.equals(original)
      case _ => false
    }

    override def apply(targetPosition: Position): Tactic = new ConstructionTactic(this.name) {

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        //First construct an equality.
        val equiv = Equiv(original, replacement)
        Some(cutInContext(equiv, targetPosition) & onBranch(
          (cutShowLbl, lastSucc(cohideT) & equivalenceCongruenceT(targetPosition.inExpr) &
            assertT(0,1) & lastSucc(assertPT(equiv)) & lastSucc(proofOfEquiv)),
          (cutUseLbl, equivRewriting(AntePosition(node.sequent.ante.length), targetPosition.topLevel)))
        )
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, targetPosition)
    }
  }
}
