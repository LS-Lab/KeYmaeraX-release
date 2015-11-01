package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core
import edu.cmu.cs.ls.keymaerax.core.{Provable, QETool}

/**
 * Tactics that execute and use the output of tools.
 * Also contains tactics for pre-processing sequents.
 * @author Nathan Fulton
 */
object ToolTactics {
  /** Performs QE and fails if the goal isn't closed. */
  def fullQE(implicit qeTool: QETool) = Idioms.NamedTactic(
    qeTool.getClass.getSimpleName + " QE",
    toSingleFormula & qeSuccedentHd & ProofRuleTactics.CloseTrue
  )

  /** Performs QE and allows the goal to be reduced to something that isn't necessarily true.
    * @note You probably want to use fullQE most of the time, because partialQE will destroy the structure of the sequent
    */
  def partialQE(implicit qeTool: QETool) = Idioms.NamedTactic(
    qeTool.getClass.getSimpleName + " QE",
    toSingleFormula & qeSuccedentHd & (ProofRuleTactics.CloseTrue | Idioms.IdentT)
  )

  /**
   * Converts a sequent into a single formula. @todo unimplemented!
   * Example:
   * {{{
   *   A, B |- S, T, U
   * }}}
   * is converted into:
   * {{{
   *   (A ^ B) -> (S \/ T \/ U)
   * }}}
   */
  private def toSingleFormula  = new BuiltInTactic("toSingleFormula") {
    override def result(provable: Provable): Provable = {
      assert(provable.subgoals.length == 1, "Should have at most one subgoal")
      provable //@todo unimplemented!
    } ensuring(r => r.subgoals.length == 1 && r.subgoals(0).ante.length == 0 && r.subgoals(0).succ.length == 1)
  }

  /** Performs Quantifier Elimination on a provable containing a single formula with a single succedent. */
  private def qeSuccedentHd(implicit qeTool : QETool) = new DependentTactic("QE") {
    override def computeExpr(v: BelleValue): BelleExpr  = {
      val provable = v match {
        case BelleProvable(provable) => provable
      }
      assert(provable.subgoals.length == 1, "Provable should have at most one subgoal.")
      assert(provable.subgoals(0).ante.length == 0 && provable.subgoals(0).succ.length == 1,
        "Provable's subgoal should have only a single succedent.")

      //Extract the formula to pass to QE.
      val formulaToProve = provable.subgoals(0).succ(0)

      //Run QE and extract the resulting provable and equivalence
      val qeFact = core.RCF.proveArithmetic(qeTool, formulaToProve).fact
      val qeEquivalence : core.Equiv =
        qeFact.conclusion.succ(0).asInstanceOf[core.Equiv]

      ProofRuleTactics.Cut(qeEquivalence) < (
        Idioms.by(qeFact),
        ??? //@todo this needs CQ or CE, depending on the shape of the qeEquivalence. But these are axioms?
      )
    }
  }
}
