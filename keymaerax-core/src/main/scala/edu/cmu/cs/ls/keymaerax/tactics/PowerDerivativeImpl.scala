/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.AxiomaticRuleTactics._
import edu.cmu.cs.ls.keymaerax.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaerax.tactics.EqualityRewritingImpl._
import edu.cmu.cs.ls.keymaerax.tactics.PropositionalTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.SyntacticDerivationInContext.ApplicableAtTerm
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.AxiomCloseT
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.hideT
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.EquivLeftT
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.EquivRightT
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.ImplyLeftT
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.ImplyRightT
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.TacticHelper._
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.cutT
import edu.cmu.cs.ls.keymaerax.tactics.Tactics._
import edu.cmu.cs.ls.keymaerax.tools.Tool


/**
 * Created by nfulton on 5/9/15.
 * @author Nathan Fulton
 */
object PowerDerivativeImpl {
  private val axiom = Axiom.axioms("^' derive power")

  /**
   *
   * @return The formula after a single application of the syntactic derivation axiom for powers.
   */
  def PowerDerivativeT = new PositionTactic("^' derive power") with ApplicableAtTerm {

    override def applies(t: Term): Boolean = t match {
      case Differential(Power(_, exp)) => exp != Number(0)
      case _ => false
    }
    override def applies(s: Sequent, p: Position): Boolean = applies(getTerm(s, p))

    override def apply(p: Position): Tactic = new ConstructionTactic("Construct " + name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        //The position of f(term) in [pi;]g(f(term)), where g might be some even larger formula.
        //I.e., the smallest subformula containing term.
        val formulaCtxPos = SyntacticDerivationInContext.findParentFormulaPos(node.sequent(p), p.inExpr)

        val term = getTerm(node.sequent, p)
        //Construct the tactic.
        term match {
          case Differential(Power(base, power)) => {
            Some(
              debugT("Starting complicated new ^' tactic") &
                ContextTactics.cutInContext(Equal(term, differentiatedTerm(base, power)), p) & onBranch(
                (cutShowLbl, proveInContext(term, base, power, formulaCtxPos)),
                (cutUseLbl, equivRewriting(AntePosition(node.sequent.ante.length), p.topLevel))
              ))
          }
          case _ => None
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  /**
   * Proves [pi;] f((base^power^)') <-> f(syntactic derivative of (base^power^)')
   * @param diffTerm The original differential term. Probably (base^power^)'
   * @param base The base of diffTerm
   * @param power the power of diffTerm
   * @param formulaCtxPos The position of the smallest subformula containing diffTerm..
   * @return Closed proof
   */
  private def proveInContext(diffTerm: Term, base: Term, power: Term, formulaCtxPos: PosInExpr) : Tactic = {
    assert(diffTerm == Differential(Power(base, power)),
      "Expected diffTerm to be (base^power)' -- not sure if this is going to work out.")

    lastSucc(cohideT) & // hide original problem.
      equivalenceCongruenceT(formulaCtxPos) & // hide box
      assertT(0,1) &
      PropositionalTacticsImpl.cutT(Some(NotEqual(power, Number(0)))) &
      onBranch(
        (BranchLabels.cutShowLbl, lastSucc(cohideT) & arithmeticT ~ errorT("c!=0 failed")),
        (BranchLabels.cutUseLbl, {
          cutT(Some( Equal(diffTerm, differentiatedTerm(base, power)) )) &
          onBranch(
            (BranchLabels.cutShowLbl, {
              debugT("show =") &
                hideT(SuccPos(0)) &
                cutT(Some(Imply(NotEqual(power, Number(0)), Equal(diffTerm, differentiatedTerm(base, power))))) &
                onBranch(
                  (BranchLabels.cutShowLbl,
                    lastSucc(cohideT) &
                    introduceInstance(diffTerm, base, power) &
                    onBranch(
                      (yield_proveAxiomInstance, AxiomCloseT)
                    ) ~
                    errorT("Expected close")
                  ),
                  (BranchLabels.cutUseLbl,
                    lastAnte(ImplyLeftT) && (
                      AxiomCloseT ~ errorT("Expected close."),
                      AxiomCloseT ~ errorT("Expected close.")
                      )
                  )
                ) ~
                debugT("Expected close")
            }),
            (BranchLabels.cutUseLbl, {
              EquationCongruenceCorollary(diffTerm, differentiatedTerm(base, power)) ~
                errorT("Expected EquationCongruenceCorollary to close.")
            })
          )
        })
      ) ~ errorT("Expected full proof.")
  }


  private def differentiatedTerm(base: Term, power: Term) : Term =
    Times(Times(power, Power(base, Minus(power, Number(1)))), Differential(base))

  private def axiomInstance(originalTerm: Term, base: Term, power: Term): Formula = {
    assert(originalTerm == Differential(Power(base, power)), "Original term did not have expected form.")
    val right = differentiatedTerm(base, power)
    Imply(NotEqual(power, Number(0)), Equal(originalTerm, right))
  }

  private def uniformSubstitution(base: Term, power: Term) = {
    val aF = FuncOf(Function("f", None, base.sort, base.sort), Anything)
    val aC = FuncOf(Function("c", None, Unit, Real), Nothing)
    new SubstitutionPair(aF, base) :: new SubstitutionPair(aC, power) :: Nil
  }


  /**
   * The original derive power rule states c!=0 -> (t^c^)' = t^c-1^*t'
   * This tactic proves that this axiom hods at:
   *    t = base
   *    c = power
   *    originalDifferentialTerm = (base^power^)'
   * @param diffTerm Should equal (base^power^)'
   * @param base Value to instantiate the base position.
   * @param power Value to instantiate the power position.
   * @return A new sequent identical to the current one, but with the axiomInstance in the last antecedent position.
   *         Completely closes the left cut branch.
   *         The final goal is emitted with the label "yield_proveAxiomInstance"
   */
  private def introduceInstance(diffTerm: Term, base : Term, power : Term) = {
    val instance = axiomInstance(diffTerm, base, power) // power != 0 -> (base^power)' = base^(power-1)*base'
    val subst = uniformSubstitution(base, power)

    cutT(Some(instance))  &
      onBranch(
        (BranchLabels.cutShowLbl, {
          lastSucc(cohideT) &
            uniformSubstT(subst, Map(instance -> axiom)) &
            lastSucc(assertPT(axiom)) & assertT(0, 1) &
            AxiomTactic.axiomT("^' derive power")
        }),
        (BranchLabels.cutUseLbl, LabelBranch(yield_proveAxiomInstance))
      )
  }

  /**
   * Label for output of proveAxiomInstance
   * @see proveAxiomInstance
   */
  private val yield_proveAxiomInstance : String = "yield_proveAxiomInstance"

  /**
   * Assuming:
   *    a and b are terms
   *    c -> (a = b) is provable by the power derive axiom.
   *    a occurs at position posInExpr in f(a), and similarly for b and f(b).
   * This tactic proves:
   *    c, a=b |- f(a) <-> f(b)
   *
   * @author Nathan Fulton
   * @return Closed proof.
   */
  private def EquationCongruenceCorollary(a: Term, b: Term) =
  new ConstructionTactic("Corollary of Equation Congruence (elide valid premise in implication)") {
    override def applicable(node: ProofNode): Boolean = {
      val s = node.sequent
      s.ante.length == 2 &&
        s.succ.length == 1 &&
        (s.succ.last match {
          case Equiv(phi, psi) => true
          case _ => false
        })
    }

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
      val (phi, psi) = node.sequent.succ(0) match {
        case Equiv(phi, psi) => (phi, psi)
        case _ => throw new IllegalArgumentException(".applicable should not have been true.")
      }

      Some(
        locateForCongruenceRewriting(a, b, EqualityRewritingImpl.constFormulaCongruenceT(AntePos(1), true, false))(SuccPos(0)) &
        debugT("Successfully applied congruence rewriting in power derivative tactic.") &
        lastSucc(EquivRightT) &
        onBranch(
          (BranchLabels.equivLeftLbl, AxiomCloseT ~ errorT("should have closed")),
          (BranchLabels.equivRightLbl, AxiomCloseT ~ errorT("should have closed"))
        )
      )
    }
  }
}


