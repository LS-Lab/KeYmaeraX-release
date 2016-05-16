/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, DependentTactic, PartialTactic}
import edu.cmu.cs.ls.keymaerax.core._

/**
  * Tactics for simplifying arithmetic sub-goals.
  *
  * @author Nathan Fulton
  */
object ArithmeticSimplification {
  //region Tactics

  val isArithmetic = TactixLibrary.assertT((s:Sequent) => isFOLR(s),
    "Expected a sequent corresponding to a formula of first-order real arithemtic, but found non-arithmetic formulas in the sequent.")

  /** Simplifies arithmetic by removing formulas that are **definitely** irrelevant to the current sub-goal.
    * This tactic should necessarily retain validity. */
  lazy val conserviatvelySimplifyArith = ???

  /** Simplifies arithmetic by removing formulas that are **probably** irrelevant to the current sub-goal.
    * Does not necessarily retain validity. */
  lazy val aggressivelySimplifyArith = new DependentTactic("aggressivelySimplifyArith") {
    override def computeExpr(p: Provable) = {
      assert(p.subgoals.length == 1, s"${this.name} is only relevant to Provables with one subgoal; found ${p.subgoals.length} subgoals")

      //Build up a tactic that hides all non-relevant antecedent positions.
      PartialTactic(
        isArithmetic &
        relevantAntePositions(p.subgoals(0)).foldLeft[BelleExpr](Idioms.nil)((e, nextIndex) => e & SequentCalculus.hideL(nextIndex))
      )
    }
  }

  //endregion

  //region Relevancy predicate and helper methods

  /** Returns only relevant antecedent positions.
    * @note This is factored out of tacitc implementations because relevancy might depend upon the entire antecedent,
    *       not just the point-wise relationships that can be implemented in terms of the type of [[isRelevant]]. */
  private def relevantAntePositions(s : Sequent): IndexedSeq[AntePos] = {
    val relevant = isRelevant(s.succ)(_)
    s.ante.zipWithIndex.filter(p => !relevant(p._1)).map(x => AntePos(x._2)) //@todo +1?
  }

  /** Returns true if fml is relevant to any of the formulas in goals. */
  private def isRelevant(goals: Seq[Formula])(fml: Formula) = {
    assert(isFOLR(fml), s"Antecendent formulas passed to isRelevant should be formulas of first-order real arithmetic; ${fml} is not.")
    goals.foreach(goal => assert(isFOLR(goal), s"All formulas in the succedent of a goal passed to isRelevant should be formulas of first-order real arithmetic; ${goal} is not."))

    val symbolsInFmls = goals.foldLeft(Set[NamedSymbol]())((symbols, nextFml) => symbols ++ TacticHelper.symbols(nextFml))
    TacticHelper.symbols(fml).intersect(symbolsInFmls).nonEmpty
  }

  /** Returns true if fml is a first-order formula of real arithmetic. */
  private def isFOLR(fml: Formula): Boolean = {
    val noPrograms = fml match {
      case Box(_, _) => false
      case Diamond(_, _) => false
      case x:AtomicFormula => true
      case x:ComparisonFormula => true
      case x:UnaryCompositeFormula => isFOLR(x.child)
      case x:BinaryCompositeFormula => isFOLR(x.left) && isFOLR(x.right)
      case x:Quantified => isFOLR(x.child)
    }

    val noPrimes = TacticHelper.symbols(fml).find(_ match {
      case x : DifferentialSymbol => true
      case _ => false
    }).isEmpty

    noPrograms && noPrimes
  }

  private def isFOLR(s: Sequent): Boolean = s.ante.forall(isFOLR) && s.succ.forall(isFOLR)

  //endregion
}
