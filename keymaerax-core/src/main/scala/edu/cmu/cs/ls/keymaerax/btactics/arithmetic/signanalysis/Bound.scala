/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics.arithmetic.signanalysis

import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.immutable._

/** Directionality arithmetic.
  * @author Stefan Mitsch
  */
object Bound extends Enumeration {
  type Bound = Value
  val Lower, Exact, Upper, Unknown = Value

  def converse(b: Bound): Bound = b match {
    case Lower => Upper
    case Exact => Exact
    case Upper => Lower
  }

  def pushDown(term: Term, seed: Bound): Map[NamedSymbol, Bound] = term match {
    case x: Variable => Map(x -> seed)
    case FuncOf(f, _) => Map(f -> seed)
    case Number(_) => Map()
    case Neg(t) => pushDown(t, converse(seed))
    case Plus(l, r) => combine(pushDown(l, seed), pushDown(r, seed))
    case Minus(l, r) => combine(pushDown(l, seed), pushDown(r, converse(seed)))
    case Times(l, r) => combine(pushDown(l, seed), pushDown(r, seed))
    case Divide(l, r) => combine(pushDown(l, seed), pushDown(r, converse(seed)))
    case Power(l, _) => pushDown(l, Unknown)
  }

  private def combine(l: Map[NamedSymbol, Bound], r: Map[NamedSymbol, Bound]): Map[NamedSymbol, Bound] = l ++ r
}
