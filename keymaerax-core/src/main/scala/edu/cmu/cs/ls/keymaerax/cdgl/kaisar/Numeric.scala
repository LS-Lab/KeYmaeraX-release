/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Numeric types for strategy evaluation
 * @author
 *   Brandon Bohrer
 */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import java.math.RoundingMode

/** Trait for different arithmetic representations supported for system execution */
trait Numeric[T, Truth] {
  this: T =>
  def +(rhs: T): T
  def -(rhs: T): T
  def *(rhs: T): T
  def /(rhs: T): T
  def pow(num: Int, denom: Int): T
  def max(rhs: T): T
  def min(rhs: T): T
  def abs: T
  def <(rhs: T): Truth
  def <=(rhs: T): Truth
  def >(rhs: T): Truth
  def >=(rhs: T): Truth
  def eq(rhs: T): Truth
  def diseq(rhs: T): Truth
  def unary_- : T
  def intApprox: Int
}

trait NumberFactory[Truth, N <: Numeric[N, Truth]] {
  type T = N
  val number: (Rational => T)
}

object RatFactory extends NumberFactory[Boolean, RatNum] {
  override type T = RatNum
  override val number: (Rational => RatNum) = RatNum
}

object RatIntFactory extends NumberFactory[Ternary, RatIntNum] {
  override type T = RatIntNum
  override val number: (Rational => RatIntNum) = (rat => RatIntNum(rat, rat))
}

case class TernaryNumber[number <: Numeric[number, Boolean]](num: number)
    extends Numeric[TernaryNumber[number], Ternary] {
  override def +(rhs: TernaryNumber[number]): TernaryNumber[number] = TernaryNumber(num + rhs.num)
  override def -(rhs: TernaryNumber[number]): TernaryNumber[number] = TernaryNumber(num - rhs.num)
  override def *(rhs: TernaryNumber[number]): TernaryNumber[number] = TernaryNumber(num * rhs.num)
  override def /(rhs: TernaryNumber[number]): TernaryNumber[number] = TernaryNumber(num / rhs.num)
  override def pow(n: Int, denom: Int): TernaryNumber[number] = TernaryNumber(num.pow(n, denom))
  override def max(rhs: TernaryNumber[number]): TernaryNumber[number] = TernaryNumber(num.max(rhs.num))
  override def min(rhs: TernaryNumber[number]): TernaryNumber[number] = TernaryNumber(num.min(rhs.num))
  override def abs: TernaryNumber[number] = TernaryNumber(num.abs)

  override def <(rhs: TernaryNumber[number]): Ternary = if (num < rhs.num) KnownTrue() else KnownFalse()
  override def <=(rhs: TernaryNumber[number]): Ternary = if (num <= rhs.num) KnownTrue() else KnownFalse()
  override def >(rhs: TernaryNumber[number]): Ternary = if (num > rhs.num) KnownTrue() else KnownFalse()
  override def >=(rhs: TernaryNumber[number]): Ternary = if (num >= rhs.num) KnownTrue() else KnownFalse()
  override def eq(rhs: TernaryNumber[number]): Ternary = if (num.eq(rhs.num)) KnownTrue() else KnownFalse()
  override def diseq(rhs: TernaryNumber[number]): Ternary = if (num.diseq(rhs.num)) KnownTrue() else KnownFalse()
  override def unary_- : TernaryNumber[number] = TernaryNumber(-num)
  override def intApprox: Int = num.intApprox
}

case class UnknowingFactory[N <: Numeric[N, Boolean]](val factory: NumberFactory[Boolean, N])
    extends NumberFactory[Ternary, TernaryNumber[N]] {
  override type T = TernaryNumber[N]
  override val number: (Rational => T) = (rat => TernaryNumber(factory.number(rat)))
}

sealed trait Ternary {
  def unary_! : Ternary = this match {
    case KnownTrue() => KnownFalse()
    case KnownFalse() => KnownTrue()
    case Unknown() => Unknown()
  }
  def ||(other: Ternary): Ternary = (this, other) match {
    case (KnownTrue(), _) | (_, KnownTrue()) => KnownTrue()
    case (Unknown(), _) | (_, Unknown()) => Unknown()
    case _ => KnownFalse()
  }
  def &&(other: Ternary): Ternary = (this, other) match {
    case (KnownFalse(), _) | (_, KnownFalse()) => KnownFalse()
    case (Unknown(), _) | (_, Unknown()) => Unknown()
    case _ => KnownTrue()
  }
  def iff(other: Ternary): Ternary = (this, other, this == other) match {
    case (_, _, true) => KnownTrue()
    case (KnownTrue(), KnownFalse(), _) | (KnownFalse(), KnownTrue(), _) => KnownFalse()
    case _ => Unknown()
  }
}
case class KnownTrue() extends Ternary
case class KnownFalse() extends Ternary
case class Unknown() extends Ternary

/** Single rational number. */
case class RatNum(n: Rational) extends Numeric[RatNum, Boolean] {
  override def +(rhs: RatNum): RatNum = RatNum(n + rhs.n)
  override def -(rhs: RatNum): RatNum = RatNum(n - rhs.n)
  override def *(rhs: RatNum): RatNum = RatNum(n * rhs.n)
  override def /(rhs: RatNum): RatNum = RatNum(n / rhs.n)

  override def pow(num: Int, denom: Int): RatNum = {
    if (denom == 1) RatNum(n.pow(num))
    else if (denom == 0) throw NoValueException(msg = "Division by zero")
    else {
      // val (pos, numAbs) = if (num >= 0 == denom >= 0) (true, num) else (false, -num)
      val x = n.ratPow(num, denom)
      // val alg = n.toAlgebraic.nroot(denom).pow(numAbs)
      val frac = x // if(pos) x else 1 / x
      RatNum(Rational(frac.toBigDecimal(Play.ROUNDING_SCALE, RoundingMode.DOWN)))
    }
  }

  override def max(rhs: RatNum): RatNum = RatNum(n.max(rhs.n))
  override def min(rhs: RatNum): RatNum = RatNum(n.min(rhs.n))
  override def abs: RatNum = RatNum(n.abs)
  override def <(rhs: RatNum): Boolean = n < rhs.n
  override def <=(rhs: RatNum): Boolean = n <= rhs.n
  override def >(rhs: RatNum): Boolean = n > rhs.n
  override def >=(rhs: RatNum): Boolean = n >= rhs.n
  override def unary_- : RatNum = RatNum(-n)
  override def eq(other: RatNum): Boolean = (n == other.n)
  override def diseq(other: RatNum): Boolean = (n != other.n)
  override def intApprox: Int = n.toInt
}

/** Interval of rational numbers. */
case class RatIntNum(l: Rational, u: Rational) extends Numeric[RatIntNum, Ternary] {
  override def +(rhs: RatIntNum): RatIntNum = RatIntNum(l + rhs.l, u + rhs.u)
  override def -(rhs: RatIntNum): RatIntNum = RatIntNum(l - rhs.u, u - rhs.l)
  override def *(rhs: RatIntNum): RatIntNum = {
    val (p1, p2, p3, p4) = (l * rhs.l, u * rhs.l, l * rhs.u, u * rhs.u)
    val lo = p1.min(p2).min(p3).min(p4)
    val hi = p1.max(p2).max(p3).max(p4)
    RatIntNum(lo, hi)
  }
  override def /(rhs: RatIntNum): RatIntNum = {
    // Division by zero
    val (lo, hi) =
      if (rhs.l <= Rational(0, 1) && Rational(0, 1) <= rhs.u) throw NoValueException(msg = "Division by zero")
      else if (Rational(0, 1) <= rhs.l) { // top half
        if (l <= Rational(0, 1) && Rational(0, 1) <= u) { // top-center
          ((Rational(0, 1)).min(l / rhs.l), (Rational(0, 1)).max(u / rhs.l))
        } else if (u < Rational(0, 1)) { // top-left
          (l / rhs.l, u / rhs.u)
        } else { // top-right
          (l / rhs.u, u / rhs.l)
        }
      } else { // bottom half
        if (l <= Rational(0, 1) && Rational(0, 1) <= u) { // bottom-center
          ((u / rhs.u).min(Rational(0, 1)), (l / rhs.u).max(Rational(0, 1)))
        } else if (u < Rational(0, 1)) { // bottom-left
          (u / rhs.l, l / rhs.u)
        } else { // bottom-right
          (u / rhs.u, l / rhs.l)
        }
      }
    RatIntNum(lo, hi)
  }

  def natPow(k: Int): RatIntNum = {
    if (k == 0) RatIntNum(Rational(1), Rational(1))
    else {
      val (pos, abs) = if (k > 0) (true, k) else (false, -k)
      def mults(i: Int): RatIntNum = if (i == 1) this else this * mults(i - 1)
      val mag = mults(abs)
      if (pos) mag else -mag
    }
  }

  // @TODO: Check general-case correctness
  override def pow(num: Int, denom: Int): RatIntNum = {
    if (denom == 1) natPow(num)
    else if (denom == 0) throw NoValueException(msg = "Rational power with denominator zero")
    else {
      val (pos, numAbs) = if (num >= 0 == denom >= 0) (true, num) else (false, -num)
      val algL = l.ratPow(numAbs, denom)
      val algU = u.ratPow(numAbs, denom)
      val (fracL, fracU) = if (pos) (algL, algU) else (Rational(1) / algL, Rational(1) / algU)
      val (lo, hi) = if (fracL <= fracU) (fracL, fracU) else (fracU, fracL)
      RatIntNum(
        Rational(lo.toBigDecimal(Play.ROUNDING_SCALE, RoundingMode.DOWN)),
        Rational(hi.toBigDecimal(Play.ROUNDING_SCALE, RoundingMode.UP)),
      )
    }
  }
  override def max(rhs: RatIntNum): RatIntNum = RatIntNum(l.max(rhs.l), u.max(rhs.u))
  override def min(rhs: RatIntNum): RatIntNum = RatIntNum(l.min(rhs.l), u.min(rhs.u))
  override def abs: RatIntNum = {
    val aL = l.abs
    val aU = u.abs
    val lo = if (l <= Rational(0, 1) && u >= Rational(0, 1)) Rational(0, 1) else aL.min(aU)
    val hi = aL.max(aU)
    RatIntNum(lo, hi)
  }
  override def <(rhs: RatIntNum): Ternary = if (u < rhs.l) KnownTrue() else if (l >= rhs.u) KnownFalse() else Unknown()
  override def <=(rhs: RatIntNum): Ternary = if (u <= rhs.l) KnownTrue() else if (l > rhs.u) KnownFalse() else Unknown()
  override def >(rhs: RatIntNum): Ternary = if (rhs.u < l) KnownTrue() else if (rhs.l >= u) KnownFalse() else Unknown()
  override def >=(rhs: RatIntNum): Ternary = if (rhs.u <= l) KnownTrue() else if (rhs.l > u) KnownFalse() else Unknown()
  override def eq(rhs: RatIntNum): Ternary =
    if (l == u && rhs.l == rhs.u && l == rhs.l) KnownTrue()
    else if ((l <= rhs.l && rhs.l <= u) || (l <= rhs.u && rhs.u <= u)) Unknown()
    else KnownFalse()
  override def diseq(rhs: RatIntNum): Ternary =
    if (l == u && rhs.l == rhs.u && l == rhs.l) KnownFalse()
    else if ((l <= rhs.l && rhs.l <= u) || (l <= rhs.u && rhs.u <= u)) Unknown()
    else KnownTrue()
  override def unary_- : RatIntNum = RatIntNum(-u, -l)
  override def intApprox: Int = (l.toInt + u.toInt) / 2
}
