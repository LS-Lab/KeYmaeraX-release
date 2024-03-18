/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics.arithmetic.signanalysis

import edu.cmu.cs.ls.keymaerax.core._

import scala.annotation.tailrec

/**
 * Tactics for simplifying arithmetic by analysing the signs of variables in formulas.
 *
 * @author
 *   Stefan Mitsch
 */
object SignAnalysis {

  type Signs = Map[Term, Map[Sign.Sign, Set[AntePos]]]

  /** Computes the signs of symbols in the sequent as known from the antecedent */
  def computeSigns(s: Sequent): Signs = {
    var signs = seedSigns(s)
    var prev = signs
    do {
      prev = signs
      signs = pushDownSigns(aggregateSigns(signs))
    } while (prev != signs)
    prev
  }

  /** Compute a sign seed from the antecedent of a sequent */
  def seedSigns(s: Sequent): Signs = {
    val signs: Map[AntePos, Map[Term, Sign.Sign]] = s
      .ante
      .zipWithIndex
      .filter(p => p._1.isInstanceOf[ComparisonFormula])
      .map(p => (normalize(p._1.asInstanceOf[ComparisonFormula]), p._2))
      .map {
        case (NotEqual(l, Number(r)), i) => assert(r == 0); AntePos(i) -> Map(l -> Sign.Unknown)
        case (Equal(l, Number(r)), i) => assert(r == 0); AntePos(i) -> Map(l -> Sign.Pos0)
        case (GreaterEqual(Neg(l), Number(r)), i) => assert(r == 0); AntePos(i) -> Map(l -> Sign.Neg0)
        case (GreaterEqual(l, Number(r)), i) => assert(r == 0); AntePos(i) -> Map(l -> Sign.Pos0)
        case (Greater(Neg(l), Number(r)), i) => assert(r == 0); AntePos(i) -> Map(l -> Sign.Neg0)
        case (Greater(l, Number(r)), i) => assert(r == 0); AntePos(i) -> Map(l -> Sign.Pos0)
        case e => throw new IllegalArgumentException(
            "Right-hand side of " + e._1.prettyString + " is not a number where a number is expected"
          )
      }
      .toMap

    val formulaSigns: List[Signs] = signs
      .map(p => {
        val pushedSigns = p._2.map(q => p._1 -> Sign.pushDown(q._1, Set(q._2)))
        pushedSigns.flatMap(q => q._2.map(r => r._1 -> r._2.map(_ -> Set(q._1)).toMap))
      })
      .toList
    val aggregate = formulaSigns
      .reduceLeftOption((acc, e) =>
        acc ++ e.map { case (k, v) =>
          k ->
            (acc.getOrElse(k, Map()) ++
              v.map { case (l, u) => l -> (u ++ acc.getOrElse(k, Map()).getOrElse(l, Set())) })
        }
      )
      .getOrElse(Map.empty)
    aggregate.map(p =>
      p._1 ->
        (if (p._2.size > 1 && p._2.contains(Sign.Unknown)) p._2.view.filterKeys(_ != Sign.Unknown).toMap else p._2)
    )
  } ensures
    (r =>
      r.forall(p => p._2.keySet.size == 1 || !p._2.keySet.contains(Sign.Unknown))
    ) // either unambiguous one of (+,-,?) or contradiction (+-)

  /** Aggregates sign bottom up in terms */
  @tailrec
  def aggregateSigns(signs: Signs): Signs = {
    val (facts, unknown) = signs.partition(!_._2.keySet.contains(Sign.Unknown))
    assert(unknown.forall(_._2.keySet.size == 1), "Unknown signs are not known")
    val aggregate = facts ++
      unknown.map(p => p._1 -> p._2.map(q => Sign.sign(p._1)(facts.map(p => p._1 -> p._2.keySet.head)) -> q._2))
    if (aggregate != signs) aggregateSigns(aggregate) else aggregate
  }

  /** Pushes signs of terms down into subterms */
  @tailrec
  def pushDownSigns(signs: Signs): Signs = {
    val (facts, unknown) = signs.partition(!_._2.keySet.contains(Sign.Unknown))
    assert(unknown.forall(_._2.keySet.size == 1), "Unknown signs are not known")
    val pushedFacts = facts.flatMap(p => {
      val pushed = Sign.pushDown(p._1, p._2.keySet)(facts.map(p => p._1 -> p._2.keySet))
      // compute positions where the sign info was found
      // pushed.map(q => q._1 -> q._2.map(r => r -> (facts.getOrElse(q._1, Map()).getOrElse(r, Set()) ++ p._2.getOrElse(r, unknown.getOrElse(q._1, Map()).getOrElse(r, Set())))).toMap)
      pushed.map { case (t, ss) =>
        t ->
          ss.map(s =>
              s -> facts.getOrElse(t, Map()).getOrElse(s, unknown.getOrElse(t, Map()).getOrElse(Sign.Unknown, Set()))
            )
            .toMap
      }
    })
    val aggregate = unknown ++ pushedFacts
    if (aggregate != signs) pushDownSigns(aggregate) else aggregate
  }

  /** Compute wanted bounds for variables from the succedent of a sequent */
  def bounds[T <: SeqPos](
      fmls: IndexedSeq[Formula],
      signs: Map[Term, Map[Sign.Sign, Set[AntePos]]],
      posFactory: Int => T,
  ): Map[T, Map[Term, Map[Bound.Bound, Set[AntePos]]]] = {
    val bounds = fmls
      .zipWithIndex
      .filter(p => p._1.isInstanceOf[ComparisonFormula])
      .map(p => (normalize(p._1.asInstanceOf[ComparisonFormula]), p._2))
      .map {
        case (NotEqual(l, Number(r)), i) => assert(r == 0); posFactory(i) -> Map(l -> Bound.Unknown)
        case (Equal(l, Number(r)), i) => assert(r == 0); posFactory(i) -> Map(l -> Bound.Exact)
        case (GreaterEqual(Neg(l), Number(r)), i) => assert(r == 0); posFactory(i) -> Map(l -> Bound.Upper)
        case (GreaterEqual(l, Number(r)), i) => assert(r == 0); posFactory(i) -> Map(l -> Bound.Lower)
        case (Greater(Neg(l), Number(r)), i) => assert(r == 0); posFactory(i) -> Map(l -> Bound.Upper)
        case (Greater(l, Number(r)), i) => assert(r == 0); posFactory(i) -> Map(l -> Bound.Lower)
        case e => throw new IllegalArgumentException(
            "Right-hand side of " + e._1.prettyString + " is not a number where a number is expected"
          )
      }
      .toMap
    bounds.map(p => (p._1, p._2.flatMap(p => Bound.pushDown(p._1, Map(p._2 -> Set()))(signs))))
  }

  /** Computes a list of candidates for hiding, based on inconsistent signs (bounds w.r.t. 0) */
//  def signInconsistencyHideCandidates(s: Sequent): List[SeqPos] = {
//    val signs = computeSigns(s)
//  }

  /** Computes a list of candidates for hiding, based on bounds. */
  def boundHideCandidates(s: Sequent): List[SeqPos] = {
    val signs = computeSigns(s)
    val anteBounds = bounds(s.ante, Map(), AntePos)
    val succBounds = bounds(s.succ, signs, SuccPos)
    val protect = succBounds.values.flatMap(_.values.flatMap(_.values.flatten)).toSet
    anteBounds
      .filter { case (pos, _) => !protect.contains(pos) }
      .filter { case (_, ab) => !boundsAreConsistent(ab, succBounds.values.toList) }
      .keys
      .toList
  }

  /**
   * Computes a list of candidates for hiding, based on inconsistent signs (might be too eager, i.e., filter x<=0 & x>=0
   * as inconsistent)
   */
  def signHideCandidates(s: Sequent): List[SeqPos] = {
    // hide everything that is consistent, hoping for a contradiction in the remaining inconsistent positions
    val consistentPos = computeSigns(s).filter(_._2.keySet.size <= 1).flatMap(_._2.values.flatten).toSet.toList
    s.ante.indices.map(AntePos).filter(consistentPos.contains).toList ++ s.succ.indices.map(SuccPos)
  }

  /** Computes whether the bounds that we have are consistent with what we want. */
  private def boundsAreConsistent(
      have: Map[Term, Map[Bound.Bound, Set[AntePos]]],
      want: List[Map[Term, Map[Bound.Bound, Set[AntePos]]]],
  ): Boolean = {
    !have.exists { case (k, v) =>
      want.forall(w =>
        w.get(k) match {
          case Some(wb) =>
            v.keySet.exists(hb => (hb == Bound.Upper || hb == Bound.Lower) && wb.keySet.contains(Bound.converse(hb)))
          case None => false
        }
      )
    }
  }

  /** Normalizes <, <=, =, >=, > into >, >=, = with right-hand side 0 */
  private def normalize(c: ComparisonFormula): ComparisonFormula = {
    c match {
      case Less(l, r) => normalize(Greater(r, l))
      case LessEqual(l, r) => normalize(GreaterEqual(r, l))
      case Equal(_, Number(i)) if i == 0 => c
      case Equal(l @ Number(i), r) if i == 0 => normalize(Equal(r, l))
      case Equal(l, r) => Equal(Minus(l, r), Number(0))
      case NotEqual(l @ Number(i), r) if i == 0 => normalize(NotEqual(r, l))
      case NotEqual(l, r) => NotEqual(Minus(l, r), Number(0))
      case GreaterEqual(_, Number(i)) if i == 0 => c
      case GreaterEqual(Number(i), Neg(r)) if i == 0 => GreaterEqual(r, Number(0))
      case GreaterEqual(Number(i), r) if i == 0 => GreaterEqual(Neg(r), Number(0))
      case GreaterEqual(l, r) => GreaterEqual(Minus(l, r), Number(0))
      case Greater(_, Number(i)) if i == 0 => c
      case Greater(Number(i), Neg(r)) if i == 0 => Greater(r, Number(0))
      case Greater(Number(i), r) if i == 0 => Greater(Neg(r), Number(0))
      case Greater(l, r) => Greater(Minus(l, r), Number(0))
    }
  } ensures
    (r =>
      r match {
        case NotEqual(_, Number(i)) => i == 0
        case Equal(_, Number(i)) => i == 0
        case GreaterEqual(_, Number(i)) => i == 0
        case Greater(_, Number(i)) => i == 0
      }
    )

}
