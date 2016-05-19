/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics.arithmetic.signanalysis

import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.immutable.Map

/** Sign arithmetic.
  *
  * @author Stefan Mitsch
  */
object Sign extends Enumeration {
  type Sign = Value
  val Neg0, Pos0, Unknown = Value

  def plusConverse(s: Sign): Sign = s match {
    case Neg0 => Pos0
    case Pos0 => Neg0
    case _ => Unknown
  }

  def timesConverse(s: Sign): Sign = s match {
    case Neg0 => Unknown
    case Pos0 => Pos0
    case _ => Unknown
  }

  def plus(l: Sign, r: Sign): Sign = (l,r) match {
    case (Neg0,Neg0) => Neg0
    case (Pos0,Pos0) => Pos0
    case _ => Unknown
  }

  def minus(l: Sign, r: Sign): Sign = plus(l, plusConverse(r))

  def times(l: Sign, r: Sign): Sign = (l,r) match {
    case (Neg0,Neg0) => Pos0
    case (Neg0,Pos0) => Neg0
    case (Pos0,Neg0) => Neg0
    case (Pos0,Pos0) => Pos0
    case _ => Unknown
  }

  def divide(l: Sign, r: Sign): Sign = times(l, r)

  def power(l: Sign, r: Int): Sign = l match {
    case Neg0 if r%2 != 0 => Neg0
    case Pos0             => Pos0
    case _    if r%2 == 0 => Pos0
    case _    if r%2 != 0 => Unknown
  }

  def num(n: Number): Sign = if (n.value >= 0) Pos0 else /* n.value <= 0 */ Neg0

  def sign(term: Term)(implicit atoms: Map[Term, Sign] = Map()): Sign = atoms.getOrElse(term, term match {
    case x: Variable => Unknown
    case xp: DifferentialSymbol => Unknown
    case n: Number => num(n)
    case f: FuncOf => Unknown
    case edu.cmu.cs.ls.keymaerax.core.Neg(e)       => plusConverse(sign(e))
    case Plus(l, r)   => plus(sign(l), sign(r))
    case Minus(l, r)  => minus(sign(l), sign(r))
    case Times(l, r)  => times(sign(l), sign(r))
    case Divide(l, r) => divide(sign(l), sign(r))
    case Power(l, Number(r))  => power(sign(l), r.intValue()) //@note only works for small exponents
  })

  def pushDown(term: Term, parent: Set[Sign])(implicit atoms: Map[Term, Set[Sign]] = Map()): Map[Term, Set[Sign]] =
    if (parent.contains(Unknown) && atoms.contains(term)) pushDown(term, atoms.get(term).get)
    else term match {
      case x: Variable => Map(x -> parent)
      case f: FuncOf => Map(f -> parent)
      case n@Number(i) if i >= 0 => Map(n -> Set(Pos0))
      case n@Number(i) if i <= 0 => Map(n -> Set(Neg0))
      case edu.cmu.cs.ls.keymaerax.core.Neg(t) => combine(Map(term -> parent), pushDown(t, parent.map(timesConverse)))
      case Plus(l, r) =>
        val left = pushDown(l, Set(Unknown))
        val right = pushDown(r, Set(Unknown))
        (parent.toList, left(l).toList, right(r).toList) match {
          case (Pos0::Nil, Neg0::Nil, _) => combine(Map(term -> parent), combine(left, pushDown(r, Set(Pos0))))
          case (Pos0::Nil, _, Neg0::Nil) => combine(Map(term -> parent), combine(pushDown(l, Set(Pos0)), right))
          case (Neg0::Nil, Pos0::Nil, _) => combine(Map(term -> parent), combine(left, pushDown(r, Set(Neg0))))
          case (Neg0::Nil, _, Pos0::Nil) => combine(Map(term -> parent), combine(pushDown(l, Set(Neg0)), right))
          case _ => combine(Map(term -> parent), combine(left, right))
        }
      case Minus(l, r) => //pushDown(Plus(l, Neg(r)), parent) //@note cannot use, otherwise lookup on parent operator fails
        val right = pushDown(r, Set(Unknown))
        (parent.toList, right(r).toList) match {
          case (Pos0::Nil, Pos0::Nil) => combine(Map(term -> parent), combine(pushDown(l, Set(Pos0)), right))
          case _ => combine(Map(term -> parent), combine(pushDown(l, Set(Unknown)), right))
        }
      case Times(l, r) =>
        val left = pushDown(l, Set(Unknown))
        val right = pushDown(r, Set(Unknown))
        (parent.toList, left(l).toList, right(r).toList) match {
          case (Pos0::Nil, Pos0::Nil, _) => combine(Map(term -> parent), combine(left, pushDown(r, Set(Pos0))))
          case (Pos0::Nil, Neg0::Nil, _) => combine(Map(term -> parent), combine(left, pushDown(r, Set(Neg0))))
          case (Pos0::Nil, _, Pos0::Nil) => combine(Map(term -> parent), combine(pushDown(l, Set(Pos0)), right))
          case (Pos0::Nil, _, Neg0::Nil) => combine(Map(term -> parent), combine(pushDown(l, Set(Neg0)), right))
          case (Neg0::Nil, Pos0::Nil, _) => combine(Map(term -> parent), combine(left, pushDown(r, Set(Neg0))))
          case (Neg0::Nil, Neg0::Nil, _) => combine(Map(term -> parent), combine(left, pushDown(r, Set(Pos0))))
          case (Neg0::Nil, _, Pos0::Nil) => combine(Map(term -> parent), combine(pushDown(l, Set(Neg0)), right))
          case (Neg0::Nil, _, Neg0::Nil) => combine(Map(term -> parent), combine(pushDown(l, Set(Pos0)), right))
          case _ => combine(Map(term -> parent), combine(left, right))
        }
      case Divide(l, r) => //pushDown(Times(l, r), parent) //@note cannot use, otherwise lookup on parent operator fails
        val left = pushDown(l, Set(Unknown))
        val right = pushDown(r, Set(Unknown))
        (parent.toList, left(l).toList, right(r).toList) match {
          case (Pos0::Nil, Pos0::Nil, _) => combine(Map(term -> parent), combine(left, pushDown(r, Set(Pos0))))
          case (Pos0::Nil, Neg0::Nil, _) => combine(Map(term -> parent), combine(left, pushDown(r, Set(Neg0))))
          case (Pos0::Nil, _, Pos0::Nil) => combine(Map(term -> parent), combine(pushDown(l, Set(Pos0)), right))
          case (Pos0::Nil, _, Neg0::Nil) => combine(Map(term -> parent), combine(pushDown(l, Set(Neg0)), right))
          case (Neg0::Nil, Pos0::Nil, _) => combine(Map(term -> parent), combine(left, pushDown(r, Set(Neg0))))
          case (Neg0::Nil, Neg0::Nil, _) => combine(Map(term -> parent), combine(left, pushDown(r, Set(Pos0))))
          case (Neg0::Nil, _, Pos0::Nil) => combine(Map(term -> parent), combine(pushDown(l, Set(Neg0)), right))
          case (Neg0::Nil, _, Neg0::Nil) => combine(Map(term -> parent), combine(pushDown(l, Set(Pos0)), right))
          case _ => combine(Map(term -> parent), combine(left, right))
        }
      case Power(l, Number(r)) if r%2 == 0 => combine(Map(term -> Set(Pos0)), pushDown(l, Set(Unknown)))
      case Power(l, Number(r)) if r%2 != 0 => combine(Map(term -> parent), pushDown(l, parent))
      case Power(l, _) => combine(Map(term -> parent), pushDown(l, Set(Unknown)))
    }

  private def combine(l: Map[Term, Set[Sign]], r: Map[Term, Set[Sign]]): Map[Term, Set[Sign]] =
    l ++ r.map { case (k,v) => k -> (v ++ l.getOrElse(k, List())) }


}