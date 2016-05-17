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

      //Should already be sorted highest-to-lowest, but check just in case.
      val toHide = irrelevantAntePositions(p.subgoals(0)).sortBy(x => x.index0).reverse

      //Build up a tactic that hides all non-relevant antecedent positions.
      PartialTactic(
        isArithmetic &
          DebuggingTactics.debug(s"Hiding positions ${toHide.mkString(",")}") &
          toHide.foldLeft[BelleExpr](Idioms.nil)((e, nextPosition) => e & SequentCalculus.hideL(nextPosition))
      )
    }
  }

  /** Simplifies arithmetic by removing all formulas (both antecedent and succedent) that mention any of the
    * irrelevant names.
    * @author Stefan Mistch
    * @note Same as smartHide except does both the succedent and the antecedent, and assumes that a list of irrelevant names is already available.
    */
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
    * @author Stefan Mitsch
    */
  def replaceTransform(what: Term, to: Term): DependentPositionTactic = "replaceTransform" by ((pos: Position, sequent: Sequent) => {
    cutLR(sequent(pos.top).replaceFree(what, to))(pos) <(
      skip,
      if (pos.isAnte) implyR('Rlast) & sequent.succ.indices.map(i => hideR(i+1)).reverse.foldLeft(skip)((a, b) => a & b) & QE
      else implyR(pos) & sequent.succ.indices.dropRight(1).map(i => hideR(i+1)).reverse.foldLeft(skip)((a, b) => a & b) & QE
      )
  })

//  def abbreviate(f:Formula) = new AppliedDependentTactic("abbreviate") {
//
//  }

//Unimplemented because this is low priority for the FM paper I think.
//  /** Cleans up silly pieces of arithmetic to make things easier to read:
//    *     t^1 -> t,
//    *     t^0 -> 1,
//    *     1*t -> t
//    *     t*1 -> t
//    *     0*t -> 0
//    *     t*0 -> t
//    *     ... (additive identities, etc.)
//    *     N.M -> Number(N.M) for N,M Numbers and . \in +,-,*,/
//    */
//  lazy val cleanup = new DependentTactic("cleanupArithmetic") {
//    import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
//    /** Equational axioms that will be re-written left-to-right using the CT proof rule. */
//    private val axioms = Set(
//      ("oneExponent", "t^1=t".asFormula),
//      ("zeroExponent", "t^0=1".asFormula),
//      ("multIdRight", "t*1=t".asFormula),
//      ("multIdLeft", "1*t=t".asFormula),
//      ("multUnitRight", "t*0=0".asFormula),
//      ("multUnitLeft", "0*t=0".asFormula)
//    )
//
//    override def computeExpr(p: Provable) = {
//      ??? //@todo first prove each of the axioms using suppose/show or similar, then write a tactic that CT's the cirst occurance of an LHS.
//    }
//  }

  //endregion

  //region Relevancy predicate and helper methods

  /** Returns only relevant antecedent positions. */
  private def irrelevantAntePositions(s : Sequent): Seq[AntePosition] = {
    val theFilter: (Seq[(Formula, Int)], Set[NamedSymbol]) => Seq[(Formula, Int)] = transitiveRelevance //    relevantFormulas(s.ante.zipWithIndex, symbols(s.succ))
    val relevantIndexedFormulas = theFilter(s.ante.zipWithIndex, symbols(s.succ))
    val complementOfRelevantFormulas = s.ante.zipWithIndex.filter(x => !relevantIndexedFormulas.contains(x))
    //Sort highest-to-lowest so that we don't end up hiding the wrong stuff.
    val result = complementOfRelevantFormulas.map(x => x._2).sorted.reverse.map(zeroIdx => AntePosition(zeroIdx + 1))
    result
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