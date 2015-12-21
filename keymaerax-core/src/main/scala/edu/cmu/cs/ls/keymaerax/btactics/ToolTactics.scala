package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.SuccPosition

import scala.language.postfixOps

/**
 * Tactics that execute and use the output of tools.
 * Also contains tactics for pre-processing sequents.
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
object ToolTactics {
  /** Performs QE and fails if the goal isn't closed. */
  def fullQE(order: List[NamedSymbol] = Nil)(implicit qeTool: QETool): BelleExpr = {
    require(qeTool != null, "No QE tool available. Use implicit parameter 'qeTool' to provide an instance (e.g., use withMathematica in unit tests)")
    Idioms.NamedTactic(qeTool.getClass.getSimpleName + " QE",
      toSingleFormula & FOQuantifierTactics.universalClosure(order)(1) & qeSuccedentHd(qeTool) & DebuggingTactics.assertProved
  )}
  def fullQE(implicit qeTool: QETool): BelleExpr = fullQE()

  /** Performs QE and allows the goal to be reduced to something that isn't necessarily true.
    * @note You probably want to use fullQE most of the time, because partialQE will destroy the structure of the sequent
    */
  def partialQE(implicit qeTool: QETool) = {
    require(qeTool != null, "No QE tool available. Use implicit parameter 'qeTool' to provide an instance (e.g., use withMathematica in unit tests)")
    Idioms.NamedTactic(qeTool.getClass.getSimpleName + " QE",
      toSingleFormula & qeSuccedentHd(qeTool)
    )
  }

  /**
   * Converts a sequent into a single formula.
   * Example:
   * {{{
   *   A, B |- S, T, U
   * }}}
   * is converted into:
   * {{{
   *   (A ^ B) -> (S \/ T \/ U)
   * }}}
   */
  private lazy val toSingleFormula: DependentTactic  = new SingleGoalDependentTactic("toSingleFormula") {
    override def computeExpr(sequent: Sequent): BelleExpr = {
      val ante = (sequent.ante ++ (True::True::Nil)).reduce(And)
      val succ = (sequent.succ ++ (False::False::Nil)).reduce(Or)
      cut(Imply(ante, succ)) <(
        /* use */ implyL('Llast) <(
          hideR(1)*sequent.succ.size  & (andR(1) <((close | skip) partial, close))*(sequent.ante.size+1),
          hideL(-1)*sequent.ante.size & (orL(-1) <((close | skip) partial, close))*(sequent.succ.size+1)),
        /* show */ cohide('Rlast) partial
        )
    }
  }

  /** Performs Quantifier Elimination on a provable containing a single formula with a single succedent. */
  private def qeSuccedentHd(qeTool : QETool) = new SingleGoalDependentTactic("QE") {
    override def computeExpr(sequent: Sequent): BelleExpr  = {
      assert(sequent.ante.isEmpty && sequent.succ.length == 1, "Provable's subgoal should have only a single succedent.")

      //Run QE and extract the resulting provable and equivalence
      val qeFact = core.RCF.proveArithmetic(qeTool, sequent.succ.head).fact
      val Equiv(_, result) = qeFact.conclusion.succ.head

      ProofRuleTactics.cutLR(result)(SuccPosition(0)) <(
        (close | skip) partial,
        equivifyR(1) & commuteEquivR(1) & by(qeFact)
      )
    }
  }
}
