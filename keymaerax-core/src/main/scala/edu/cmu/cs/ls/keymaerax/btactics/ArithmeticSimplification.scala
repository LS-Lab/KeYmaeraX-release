/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, DependentTactic, PartialTactic}
import edu.cmu.cs.ls.keymaerax.core._

import scala.annotation.tailrec

/**
  * Tactics for simplifying arithmetic sub-goals.
  *
  * @author Nathan Fulton
  */
object ArithmeticSimplification {
  //region Tactics

  val isArithmetic = TactixLibrary.assertT((s:Sequent) => isFOLR(s),
    "Expected a sequent corresponding to a formula of first-order real arithemtic, but found non-arithmetic formulas in the sequent.")

  /** Simplifies arithmetic by removing formulas that are **probably** irrelevant to the current sub-goal.
    * Does not necessarily retain validity??? */
  lazy val smartHide = new DependentTactic("smartHide") {
    override def computeExpr(p: Provable) = {
      assert(p.subgoals.length == 1, s"${this.name} is only relevant to Provables with one subgoal; found ${p.subgoals.length} subgoals")

      //Build up a tactic that hides all non-relevant antecedent positions.
      PartialTactic(
        isArithmetic &
        irrelevantAntePositions(p.subgoals(0)).foldLeft[BelleExpr](Idioms.nil)((e, nextIndex) => e & SequentCalculus.hideL(nextIndex))
      )
    }
  }

//  /** Cleans up silly pieces like E^1, 2-1, etc. */
//  lazy val cleanup = new DependentTactic("cleanup") {
//    override def computeExpr(p: Provable) = ???
//  }

//  def abbreviate(equality: Formula) = new AppliedDependentTactic("abbreviate") {
//
//  }

  //endregion

  //region Relevancy predicate and helper methods

  /** Returns only relevant antecedent positions. */
  private def irrelevantAntePositions(s : Sequent): Seq[AntePos] = {
    val theFilter : (Seq[(Formula, Int)], Set[NamedSymbol]) => Seq[(Formula, Int)] = transitiveRelevance //    relevantFormulas(s.ante.zipWithIndex, symbols(s.succ))
    val relevantIndexedFormulas = theFilter(s.ante.zipWithIndex, symbols(s.succ))
    val complementOfRelevantFormulas = s.ante.zipWithIndex.filter(x => !relevantIndexedFormulas.contains(x))
    complementOfRelevantFormulas.map(x => AntePos(x._2))
  }



  /**
    * Returns all formulas that transitively mention relevantSymbols.
    * For example, if fmls = (
    *   (x>=y , 0)
    *   (y>=z , 5)
    *   (z>=12 , 6)
    * )
    * and relevantSymbols = {x}, then transitiveRelevance(fmls) = fmls because:
    *    AntePos(0) mentions x \in {x}      ==> transitiveRelevance(0::5::6, {x,y})
    *    AntePos(5) mentions y \in {x,y}    ==> transitiveRelevance(0::5::6, {x,y,z})
    *    AntePos(6) mentions z \in {x,y,z}  ==> recursion terminates now or after one more step because all variables already occur in relevantSymbols.
    */
  @tailrec
  private def transitiveRelevance(fmls: Seq[(Formula, Int)], relevantSymbols: Set[NamedSymbol]) : Seq[(Formula, Int)] = {
    val relevantFmls = relevantFormulas(fmls, relevantSymbols)
    val newlyRelevantSymbols = symbols(relevantFmls.map(_._1)) -- relevantSymbols

    if(newlyRelevantSymbols.size == 0) relevantFmls
    else transitiveRelevance(fmls, relevantSymbols ++ newlyRelevantSymbols) //sic: recurse on [[indexedFmls]], not [[relevantFmls]], because some of the previously irrelevant formulas might now be relevant.
  }

  /** Returns all formulas that mention a relevantSymbol, together with that formula's position in the original sequence. */
  private def relevantFormulas(indexedFmls: Seq[(Formula, Int)], relevantSymbols: Set[NamedSymbol]) : Seq[(Formula, Int)] = {
    indexedFmls.filter(p => TacticHelper.symbols(p._1).intersect(relevantSymbols).nonEmpty)
  }

  /** Returns the union of all symbols mentioned in fmls. */
  private def symbols(fmls: Seq[Formula]) =
    fmls.foldLeft(Set[NamedSymbol]())((symbols, nextFml) => symbols ++ TacticHelper.symbols(nextFml))

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
