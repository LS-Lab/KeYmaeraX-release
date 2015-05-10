package edu.cmu.cs.ls.keymaera.tactics

import java.lang.Number

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.AxiomaticRuleTactics._
import edu.cmu.cs.ls.keymaera.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaera.tactics.EqualityRewritingImpl._
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.SyntacticDerivationInContext.ApplicableAtTerm
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.AxiomCloseT
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.EquivLeftT
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.EquivRightT
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.ImplyLeftT
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.ImplyRightT
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.TacticHelper._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.cutT
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.hideT
import edu.cmu.cs.ls.keymaera.tactics.Tactics._
import edu.cmu.cs.ls.keymaera.tools.Tool

/**
 * Created by nfulton on 5/9/15.
 * @author Nathan Fulton
 */
object PowerDerivativeImpl {

  /**
   * maps 
   * @return
   */
  def PowerDerivativeT = new PositionTactic("^' derive power") with ApplicableAtTerm {
    val axiom = Axiom.axioms("^' derive power")

    override def applies(t: Term): Boolean = t match {
      case Differential(Power(_, exp)) => exp != Number(0)
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = applies(getTerm(s, p))

    override def apply(p: Position): Tactic = new ConstructionTactic("Construct " + name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        //Positions
        val formulaCtxPos = SyntacticDerivationInContext.findParentFormulaPos(node.sequent(p), p.inExpr)

        //Terms and formulas
        val term = getTerm(node.sequent, p)

        //Construct the tactic.
        term match {
          case Differential(Power(lhs, rhs)) => {
            require(rhs != Number(0), "not power 0")
            val right = Times(Times(rhs, Power(lhs, Minus(rhs, Number(1)))), Differential(lhs))
            val axiomInstance = Imply(NotEqual(rhs, Number(0)), Equal(term, right))

            val errOnOpen = assertT(_=>false, "Failed to close")

            val aF = FuncOf(Function("f", None, lhs.sort, lhs.sort), Anything)
            val aC = FuncOf(Function("c", None, Unit, Real), Nothing)

            val subst = new SubstitutionPair(aF, lhs) :: new SubstitutionPair(aC, rhs) :: Nil

            //Show that an instance of the axiom is true by uniform substitution.
            def proveByAxiom = {
              val cNonZero = NotEqual(rhs, Number(0))

              def proveByUsubst = //helper tactic for proveEquivalence
                assertT(1,2) &
                  cutT(Some(axiomInstance)) &
                  onBranch(
                    (BranchLabels.cutShowLbl,
                      hideT(SuccPos(0)) &
                        hideT(SuccPos(0)) &
                        uniformSubstT(subst, Map(axiomInstance -> axiom)) &
                        AxiomTactic.axiomT("^' derive power") &
                        assertT(2,1) &
                        lastAnte(assertPT(axiom)) &
                        lastSucc(assertPT(axiom)) &
                        AxiomCloseT),
                    (BranchLabels.cutUseLbl,
                      (lastAnte(ImplyLeftT) &&
                        (
                          (AxiomCloseT ~ errorT("Expected close")),
                          (AxiomCloseT ~ errorT("user -- left over"))
                          )
                        ) ~
                        errorT("Expected proof to close.")
                      )
                  )

              val theEquality = Equal(term, right)
              //Computes the location of the position for writing relative to the top-level equivalence.
              val runCQ : Tactic = {
                //                assert(getTerm(node.sequent, p) equals term, "Position should point to term equal to rewrite target.")
                //                assert(node.sequent.succ.length == 1, "Succedent should have only one formula.")
                //                assert(node.sequent.succ(0).isInstanceOf[Equiv], "Succedent formula should be an equivalence, but it was " + node.sequent.succ(0))

                // The position of the selected term within the equivalence.
                val posWithinEquiv = PosInExpr(p.inExpr.pos.tail)

                debugT("About to try equation congruence (CQ)") &
                  AxiomaticRuleTactics.equationCongruenceT(posWithinEquiv, PosInExpr(1 +: posWithinEquiv.pos)) //?
              }


              /**
               * This is a lemmo for proveEquivalence.
               * A proof that c |- ( f(a) <-> (c->f(i)) ) <-> ( f(a) <-> f(i) )
               * Let phi == f(a) <-> (c->f(i))
               * @todo Should we have some way of associating images with proofs?
               */
              def elideValidImplication : Tactic = {
                assertT(1, 1) &
                  lastSucc(EquivRightT) & onBranch(
                  (BranchLabels.equivLeftLbl,
                    lastSucc(EquivLeftT) & onBranch(
                      (BranchLabels.equivLeftLbl,
                        equivRewriting(AntePos(1), AntePos(0)) & // rewrite c -> f(i) to f(a)
                          lastAnte(ImplyLeftT) & AxiomCloseT ~ errorT("Should've closed by now") // both branches close immediately
                        ),
                      (BranchLabels.equivRightLbl,
                        equivRewriting(AntePos(1), SuccPos(0)) & // rewrite f(a) in succ to c -> f(i)
                          lastSucc(ImplyRightT) &
                          AxiomCloseT
                        )
                    )
                    ),
                  (BranchLabels.equivRightLbl,
                    lastSucc(EquivRightT) & onBranch(
                      (BranchLabels.equivLeftLbl,
                        equivRewriting(AntePos(1), AntePos(0)) &
                          lastSucc(ImplyRightT) &
                          AxiomCloseT
                        ),
                      (BranchLabels.equivRightLbl,
                        lastAnte(ImplyRightT) && (
                          AxiomCloseT,
                          (equivRewriting(AntePos(1), AntePos(0)) & AxiomCloseT ~ errorT("Should've closed by now."))
                          )
                        )
                    )
                    )
                )
              }

              def proof : Tactic = {
                assertT(1,1)
              }

              def proveEquivalence =
                cutT(Some( Equal(term, right) )) &
                  onBranch(
                    (BranchLabels.cutShowLbl, proveByUsubst ~ errOnOpen),
                    (BranchLabels.cutUseLbl,
                      debugT("here")
                      )
                  )

              lastSucc(cohideT) & // hide original problem.
                equivalenceCongruenceT(formulaCtxPos) &
                assertT(0,1) &
                PropositionalTacticsImpl.cutT(Some(cNonZero)) &
                onBranch(
                  (BranchLabels.cutShowLbl, lastSucc(cohideT) & arithmeticT),
                  (BranchLabels.cutUseLbl, proveEquivalence)
                ) ~ errorT("Expected full proof.")
            }


            Some(
              debugT("Starting complicated new ^' tactic") &
                ContextTactics.cutInContext(axiomInstance, p) & debugT("Cut Successful") & onBranch(
                (cutShowLbl, proveByAxiom),
                (cutUseLbl, equivRewriting(AntePosition(node.sequent.ante.length), p.topLevel))
              ))

          }
          case _ => None
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }

  }
}


