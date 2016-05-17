/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
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

  /** Simplifies arithmetic by removing all formulas (both antecedent and succedent) that mention any of the
    * irrelevant names. */
  def hideFactsAbout(irrelevant: String*): BelleExpr = "hideIrrelevant" by ((sequent: Sequent) => {
    val irrelevantSet = irrelevant.map(_.asNamedSymbol).toSet
    val hideAnte = sequent.ante.zipWithIndex.filter(p => StaticSemantics.symbols(p._1).intersect(irrelevantSet).nonEmpty).
      sortWith((l,r) => l._2 <= r._2).reverse.map {
      case (fml, idx) => hideL(-(idx+1), fml)
    }.foldLeft[BelleExpr](skip)((composite, atom) => composite & atom)
    val hideSucc = sequent.succ.zipWithIndex.filter(p => StaticSemantics.symbols(p._1).intersect(irrelevantSet).nonEmpty).
      sortWith((l,r) => l._2 <= r._2).reverse.map {
      case (fml, idx) => hideR(idx+1, fml)
    }.foldLeft[BelleExpr](skip)((composite, atom) => composite & atom)
    hideAnte & hideSucc
  })

  /** Transforms the formula at position by replacing all free occurrences of what with to.
    */
  def replaceTransform(what: Term, to: Term): DependentPositionTactic = "replaceTransform" by ((pos: Position, sequent: Sequent) => {
    cutLR(sequent(pos.top).replaceFree(what, to))(pos) <(
      skip,
      implyR('Rlast) & sequent.succ.indices.map(i => hideR(i+1)).reverse.foldLeft(skip)((a, b) => a & b) & QE
      )
  })

  //endregion

  //region Relevancy predicate and helper methods

  /** Returns only relevant antecedent positions.
    *
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
