/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * Numeric types for strategy evaluation
  * @author Brandon Bohrer
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import spire.math.{Algebraic, Rational}

import java.math.RoundingMode

/** Trait for different arithmetic representations supported for system execution */
trait Numeric[T, Truth] { this: T =>
  def +(rhs : T) : T
  def -(rhs : T) : T
  def *(rhs : T) : T
  def /(rhs : T) : T
  def pow(num: Int, denom: Int): T
  def max(rhs: T): T
  def min(rhs: T): T
  def abs: T
  def <(rhs: T): Truth
  def <=(rhs: T): Truth
  def >(rhs: T): Truth
  def >=(rhs: T): Truth
  def unary_- : T
}

sealed trait Ternary
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
    else if (denom == 0) throw NoValueException()
    else {
      val (pos, numAbs) = if (num >= 0 == denom >= 0) (true, num) else (false, -num)
      val alg = n.toAlgebraic.nroot(denom).pow(numAbs)
      val frac = if(pos) alg else Algebraic(1) / alg
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
}

/** Interval of rational numbers. */
case class RatIntNum(l: Rational, u: Rational) extends Numeric[RatIntNum, Ternary] {
  override def +(rhs: RatIntNum): RatIntNum = RatIntNum(l + rhs.l,  u + rhs.u)
  override def -(rhs: RatIntNum): RatIntNum = RatIntNum(l - rhs.u, u - rhs.l)
  override def *(rhs: RatIntNum): RatIntNum = {
    val (p1, p2, p3, p4) = (l*rhs.l, u*rhs.l, l*rhs.u, u*rhs.u)
    val lo = p1.min(p2).min(p3).min(p4)
    val hi = p1.max(p2).max(p3).max(p4)
    RatIntNum(lo, hi)
  }
  override def /(rhs: RatIntNum): RatIntNum = {
    // Division by zero
    val (lo, hi) =
    if(rhs.l <= 0 && 0 <= rhs.u)
      throw NoValueException()
    else if (0 <= rhs.l) { // top half
      if (l <= 0 && 0 <= u) { // top-center
        (Rational(0).min(l / rhs.l), Rational(0).max(u / rhs.l))
      } else if (u < 0) { // top-left
        (l / rhs.l, u / rhs.u)
      } else { // top-right
        (l / rhs.u, u / rhs.l)
      }
    } else { // bottom half
      if (l <= 0 && 0 <= u) { // bottom-center
        ((u / rhs.u).min(0), (l / rhs.u).max(0))
      } else if (u < 0) { // bottom-left
        (u / rhs.l, l / rhs.u)
      } else { // bottom-right
        (u / rhs.u, l / rhs.l)
      }
    }
    RatIntNum(lo, hi)
  }

  def natPow(k: Int): RatIntNum = {
    if (k == 0) RatIntNum(1, 1)
    else {
      val (pos, abs) = if (k > 0) (true, k) else (false, -k)
      def mults(i: Int): RatIntNum = if(i == 1) this else this * mults(i - 1)
      val mag = mults(abs)
      if (pos) mag else -mag
    }
  }

  // @TODO: Check general-case correctness
  override def pow(num: Int, denom: Int): RatIntNum = {
    if (denom == 1) natPow(num)
    else if (denom == 0) throw NoValueException()
    else {
      val (pos, numAbs) = if (num >= 0 == denom >= 0) (true, num) else (false, -num)
      val algL = l.toAlgebraic.nroot(denom).pow(numAbs)
      val algU = u.toAlgebraic.nroot(denom).pow(numAbs)
      val (fracL, fracU) = if(pos) (algL, algU) else (Algebraic(1) / algL, Algebraic(1) / algU)
      val (lo, hi) = if (fracL <= fracU) (fracL, fracU) else (fracU, fracL)
      RatIntNum(Rational(lo.toBigDecimal(Play.ROUNDING_SCALE, RoundingMode.DOWN)), Rational(hi.toBigDecimal(Play.ROUNDING_SCALE, RoundingMode.UP)))
    }
  }
  override def max(rhs: RatIntNum): RatIntNum = RatIntNum(l.max(rhs.l), u.max(rhs.u))
  override def min(rhs: RatIntNum): RatIntNum = RatIntNum(l.min(rhs.l), u.min(rhs.u))
  override def abs: RatIntNum = {
    val aL = l.abs
    val aU = u.abs
    val lo = if(l <= 0 && u >= 0) Rational(0) else aL.min(aU)
    val hi = aL.max(aU)
    RatIntNum(lo, hi)
  }
  override def <(rhs: RatIntNum): Ternary =
    if (u < rhs.l) KnownTrue()
    else if (l >= rhs.u) KnownFalse()
    else Unknown()
  override def <=(rhs: RatIntNum): Ternary =
    if (u <= rhs.l) KnownTrue()
    else if (l > rhs.u) KnownFalse()
    else Unknown()
  override def >(rhs: RatIntNum): Ternary =
    if (rhs.u < l) KnownTrue()
    else if (rhs.l >= u) KnownFalse()
    else Unknown()
  override def >=(rhs: RatIntNum): Ternary =
    if (rhs.u <= l) KnownTrue()
    else if (rhs.l > u) KnownFalse()
    else Unknown()
  override def unary_- : RatIntNum = RatIntNum(-u, -l)
}

