package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.AxiomaticRuleTactics._
import edu.cmu.cs.ls.keymaera.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaera.tactics.EqualityRewritingImpl._
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.SyntacticDerivationInContext.ApplicableAtTerm
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.AxiomCloseT
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.hideT
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.EquivLeftT
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.EquivRightT
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.ImplyLeftT
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.ImplyRightT
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.TacticHelper._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.cutT
import edu.cmu.cs.ls.keymaera.tactics.Tactics._
import edu.cmu.cs.ls.keymaera.tools.Tool


/**
 * Created by nfulton on 5/9/15.
 * @author Nathan Fulton
 */
object PowerDerivativeImpl {
  private val axiom = Axiom.axioms("^' derive power")

  /**
   *
   * @return The formula after a single syntactic derivation the power at the position.
   */
  def PowerDerivativeT = new PositionTactic("^' derive power") with ApplicableAtTerm {

    override def applies(t: Term): Boolean = t match {
      case Differential(Power(_, exp)) => true
      case _ => false
    }
    override def applies(s: Sequent, p: Position): Boolean = applies(getTerm(s, p))

    override def apply(p: Position): Tactic = new ConstructionTactic("Construct " + name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        //@todo explain what this is?
        val formulaCtxPos = SyntacticDerivationInContext.findParentFormulaPos(node.sequent(p), p.inExpr)

        val term = getTerm(node.sequent, p)
        //Construct the tactic.
        term match {
          case Differential(Power(lhs, rhs)) => {
            Some(
              debugT("Starting complicated new ^' tactic") &
                ContextTactics.cutInContext(axiomInstance(term, lhs, rhs), p) & onBranch(
                (cutShowLbl, proveInContext(term, lhs, rhs, formulaCtxPos, p)),
                (cutUseLbl, equivRewriting(AntePosition(node.sequent.ante.length), p.topLevel))
              ))
          }
          case _ => None
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  private def proveInContext(diffTerm: Term, base: Term, power: Term, formulaCtxPos: PosInExpr, p : Position) : Tactic = {
    //Remove the head because it's referring to a boxed formula and will always be 1.
    //Then add a 0 because we're always interested in the differential term which we keep on the left of the equiv.
    //@todo remove this.
    val positionOfPowerTermWithinEquivalence : PosInExpr = PosInExpr(0 +: p.inExpr.pos.tail)

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
              introduceInstance(diffTerm, base, power) &
              onBranch(
                (yield_proveAxiomInstance, ( lastAnte(ImplyLeftT) && (AxiomCloseT, AxiomCloseT)) ~ errorT("Expected closed"))
              ) ~ errorT("expected closed")
            }),
            (BranchLabels.cutUseLbl, {
              EquationCongruenceCorollary(positionOfPowerTermWithinEquivalence)
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
          uniformSubstT(subst, Map(instance -> axiom)) & //Do we need to hide stuff here?
            AxiomTactic.axiomT("^' derive power") &
            lastAnte(assertPT(axiom)) &
            lastSucc(assertPT(axiom)) &
            AxiomCloseT
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
   *    c -> (a = b) is provable by quantifier elimination
   *    a occurs at position posInExpr in f(a), and similarly for b and f(b).
   * This tactic proves:
   *    c, a=b |- f(a) <-> ( c -> f(b) )
   * By first proving a key lemma (elidePremiseOccurringInAntecedent) that removes the assumed premise in the right hand side:
   *    c, a=b |- (f(a) <-> (c -> f(b)) IFF f(a) <-> f(b).
   *
   * @author Nathan Fulton
   * @param posInExpr the position in f where we can apply the CQ rule (see comment above.)
   * @return Closed proof.
   */
  private def EquationCongruenceCorollary(posInExpr : PosInExpr) = new ConstructionTactic("Corollary of Equation Congruence (elide valid premise in implication)") {
    override def applicable(node: ProofNode): Boolean = {
      val s = node.sequent
      s.ante.length == 2 &&
        s.succ.length == 1 &&
        (s.succ.last match {
          case Equiv(phi, Imply(c, psi)) => c == s.ante(0)
          case _ => false
        })
    }

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
      val cRight            = node.sequent.ante(0)
      val (phi, cLeft, psi) = node.sequent.succ(0) match {
        case Equiv(phi, Imply(c2, psi)) => (phi, c2, psi)
        case _ => throw new IllegalArgumentException(".applicable should not have been true.")
      }
      assert(cLeft == cRight)

      val lemma = Equiv(Equiv(phi, Imply(cLeft, psi)), Equiv(phi, psi))

      //@todo a tactic that does: "This formula has the form f(a) <-> f(b) for a given a,b and some f. Please find the position of a for me."
      Some(
          cutT(Some(lemma)) &
          onBranch(
            (BranchLabels.cutShowLbl, debugT("showing lemma (f(a) <-> (c -> f(b)) IFF f(a) <-> f(b)") & hideT(SuccPos(0)) & elidePremiseOccurringInAntecedent ~ errorT("End of show.")),
            (BranchLabels.cutUseLbl,
              debugT("using lemma") &
              equivRewriting(AntePos(2), SuccPos(0)) &
              debugAtT("Is the position correct?")(SuccPosition(0, posInExpr)) &
              EqualityRewritingImpl.constFormulaCongruenceT(AntePos(1), true, false)(SuccPosition(0, posInExpr)) &
              lastSucc(EquivRightT) &
              onBranch(
                (BranchLabels.equivLeftLbl, AxiomCloseT ~ errorT("should have closed")),
                (BranchLabels.equivRightLbl, AxiomCloseT ~ errorT("should have closed"))
              )
            )
          )
      )
    }

      /**
       * Lemma: c, a=b |- (f(a) <-> (c -> f(b)) IFF f(a) <-> f(b).
       * Apologies for the unaligned parens -- it's an IntelliJ bug.
       */
    def elidePremiseOccurringInAntecedent : Tactic = {
      assertT(2, 1) &
      lastSucc(EquivRightT) &
      onBranch(
        (BranchLabels.equivLeftLbl,
          lastSucc(EquivRightT) &
          onBranch(
            (BranchLabels.equivLeftLbl,
                equivRewriting(AntePos(2), AntePos(3)) & // rewrite c -> f(i) to f(a)
                lastAnte(ImplyLeftT) & AxiomCloseT ~ errorT("Should've closed by Ax Close") // both branches close immediately
            ),
            (BranchLabels.equivRightLbl,
              equivRewriting(AntePos(2), SuccPos(0)) & // rewrite f(a) in succ to c -> f(i)
                lastSucc(ImplyRightT) &
                AxiomCloseT ~ debugT("Should've closed.")

            )
          )
        ),
        (BranchLabels.equivRightLbl,
          lastSucc(EquivRightT) &
          onBranch(
            (BranchLabels.equivLeftLbl,
              equivRewriting(AntePos(2), AntePos(3)) &
                lastSucc(ImplyRightT) &
                AxiomCloseT ~ debugT("Should've closed.")
              ),
            (BranchLabels.equivRightLbl,
              equivRewriting(AntePos(2), SuccPos(0)) &
              lastAnte(ImplyLeftT) && (
                AxiomCloseT ~ errorT("Should've closed by now."),
                AxiomCloseT ~ errorT("Should've closed by now.")
              )
            )
          )
        )
      )
    }
  }
}


