/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics.arithmetic.signanalysis

import org.keymaerax.core._

import scala.annotation.nowarn
import scala.collection.immutable._

/**
 * Directionality arithmetic.
 *
 * @author
 *   Stefan Mitsch
 */
object Bound extends Enumeration {
  type Bound = Value
  val Lower, Exact, Upper, Unknown = Value

  def converse(b: Bound): Bound = b match {
    case Lower => Upper
    case Exact => Exact
    case Upper => Lower
    case _ => Unknown
  }

  def plus(l: Bound, r: Bound): Bound = (l, r) match {
    case (Upper, Upper) => Upper
    case (Lower, Lower) => Lower
    case _ => Unknown
  }

  def minus(l: Bound, r: Bound): Bound = (l, r) match {
    case (Upper, Lower) => Upper
    case (Lower, Upper) => Lower
    case _ => Unknown
  }

  def times(l: Bound, r: Bound): Bound = plus(l, r)

  def divide(l: Bound, r: Bound): Bound = minus(l, r)

  def power(l: Bound, r: Int): Bound = Unknown

  @nowarn("msg=Exhaustivity analysis reached max recursion depth") @nowarn("msg=match may not be exhaustive")
  def bound(term: Term)(implicit atoms: Map[Term, Bound] = Map()): Bound = atoms.getOrElse(
    term,
    term match {
      case xp: DifferentialSymbol => Unknown
      case x: Variable => Unknown
      case n: Number => Exact
      case f: FuncOf => Unknown
      case org.keymaerax.core.Neg(e) => converse(bound(e))
      case Plus(l, r) => plus(bound(l), bound(r))
      case Minus(l, r) => minus(bound(l), bound(r))
      case Times(l, r) => times(bound(l), bound(r))
      case Divide(l, r) => divide(bound(l), bound(r))
      case Power(l, Number(r)) => power(bound(l), r.intValue) // @note only works for small exponents
    },
  )

  @nowarn("msg=Exhaustivity analysis reached max recursion depth") @nowarn("msg=match may not be exhaustive")
  def pushDown(term: Term, bound: Map[Bound, Set[AntePos]])(implicit
      signs: Map[Term, Map[Sign.Sign, Set[AntePos]]] = Map()
  ): Map[Term, Map[Bound, Set[AntePos]]] = term match {
    case x: Variable => Map(x -> bound)
    case f: FuncOf => Map(f -> bound)
    case n: Number => Map(n -> Map(Exact -> Set()))
    case Neg(t) => pushDown(t, bound.map(b => converse(b._1) -> b._2))
    case Plus(l, r) => combine(pushDown(l, bound), pushDown(r, bound))
    case Minus(l, r) => combine(pushDown(l, bound), pushDown(r, bound.map(b => converse(b._1) -> b._2)))
    case Times(l, r) if bound.keySet == Set(Exact) => combine(pushDown(l, bound), pushDown(r, bound))
    case Times(l, r) if bound.keySet != Set(Exact) =>
      def timesBounds(b: Bound, s: Map[Sign.Sign, Set[AntePos]]): (Map[Bound, Set[AntePos]], Map[Bound, Set[AntePos]]) =
        (b, s.head) match {
          case (Upper, (Sign.Pos0, pos)) => (Map(Upper -> pos), Map(Upper -> pos))
          case (Upper, (Sign.Neg0, pos)) => (Map(Lower -> pos), Map(Lower -> pos))
          case (Lower, (Sign.Pos0, pos)) => (Map(Upper -> pos), Map(Lower -> pos))
          case (Lower, (Sign.Neg0, pos)) => (Map(Lower -> pos), Map(Upper -> pos))
          case _ => (Map(Unknown -> Set()), Map(Unknown -> Set()))
        }

      val leftSign = signs.getOrElse(l, Map(Sign.Unknown -> Set[AntePos]()))
      val rightSign = signs.getOrElse(r, Map(Sign.Unknown -> Set[AntePos]()))

      val (wantLeft, wantRight) =
        if (bound.size == 1 && leftSign.size == 1 && rightSign.size == 1) {
          timesBounds(bound.head._1, leftSign) match {
            case (lb, _) if lb.keySet.contains(Unknown) => timesBounds(bound.head._1, rightSign)
            case res => res
          }
        } else (Map[Bound, Set[AntePos]](Unknown -> Set()), Map[Bound, Set[AntePos]](Unknown -> Set()))
      combine(pushDown(l, wantLeft), pushDown(r, wantRight)) // )
    case Divide(l @ Number(n), r) if n == 1 =>
      combine(pushDown(l, Map(Exact -> Set())), pushDown(r, bound.map(b => converse(b._1) -> b._2)))
    case Divide(l, r) => pushDown(Times(l, Divide(Number(1), r)), bound)
    case Power(l, _) => pushDown(l, Map(Unknown -> Set()))
  }

  private def combine(
      l: Map[Term, Map[Bound, Set[AntePos]]],
      r: Map[Term, Map[Bound, Set[AntePos]]],
  ): Map[Term, Map[Bound, Set[AntePos]]] = l ++ r.map { case (k, v) =>
    k -> {
      val bounds = v ++ l.getOrElse(k, List())
      if (bounds.size > 1) {
        val filtered = bounds.filter(_._1 != Unknown)
        if (filtered.size > 1) Map(Unknown -> Set[AntePos]()) else filtered
      } else bounds
    }
  }
}
