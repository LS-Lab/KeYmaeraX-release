/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Concrete number arithmetic.
 * @author
 *   Fabian Immler
 * @note
 *   Code Review: 2020-02-14
 */
package edu.cmu.cs.ls.keymaerax.tools.qe

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.InterpretedSymbols._
import edu.cmu.cs.ls.keymaerax.tools.Tool

/**
 * Proves quantifier- and variable-free arithmetic formulas by exact arithmetic evaluation using
 * [[java.math.BigDecimal]]. Ground term evaluation for formulas with concrete number arithmetic.
 * @author
 *   Fabian Immler
 * @note
 *   Java's BigDecimal is clearer and has less indirection than Scala's BigDecimal.
 */
object BigDecimalQETool extends Tool with QETool {

  /** @inheritdoc */
  override val name: String = "BigDecimalQETool"

  private def unableToEvaluate(e: Expression) = name + " unable to evaluate " + e

  /**
   * Returns [[Some]] [[Int]] if the argument [[java.math.BigDecimal]] can be represented as an integer or [[None]]
   * otherwise
   */
  private def getIntOption(d: java.math.BigDecimal): Option[Int] =
    try { Some(d.intValueExact) }
    catch { case _: ArithmeticException => None }

  /**
   * Evaluate a [[Term]] in exact [[java.math.BigDecimal]] arithmetic.
   *
   * @return
   *   the [[java.math.BigDecimal]] equal to the input term
   * @throws IllegalArgumentException
   *   if exact evaluation is not possible, e.g., for Variables or non-exact division
   * @see
   *   the documentation of [[java.math.BigDecimal]], in particular the paragraph mentioning
   *   [[java.math.MathContext.UNLIMITED]]:
   *   - Arithmetic methods which take a [[java.math.MathContext.UNLIMITED]] or no [[java.math.MathContext]] object are
   *     exact.
   *   - If the result of division cannot be represented exactly, an [[ArithmeticException]] is thrown.
   * @note
   *   We use [[java.math.BigDecimal]] instead of [[scala.math.BigDecimal]] in order to avoid one layer of indirection
   *   and therefore reduce the trusted code base. Moreover [[java.math.BigDecimal]] is more explicit about rounding
   *   modes and precision.
   */
  def eval(t: Term): java.math.BigDecimal = t match {
    case Number(a) => a.bigDecimal
    case Plus(a, b) => eval(a).add(eval(b))
    case Minus(a, b) => eval(a).subtract(eval(b))
    case Times(a, b) => eval(a).multiply(eval(b))
    case Neg(a) => eval(a).negate
    case Power(a, b) =>
      val (x, y) = (eval(a), eval(b))
      val i = getIntOption(y).getOrElse(throw new IllegalArgumentException(unableToEvaluate(t)))
      // x ^ i for positive integer i
      if (i >= 1) x.pow(i)
      // x ^ 0 = 0 for x != 0
      else if (x.compareTo(java.math.BigDecimal.ZERO) != 0 && i == 0)
        /** @note [[x.compareTo]] respects different representations of 0 */
        java.math.BigDecimal.ONE
      // 10 ^ i for negative exponents i
      else if (x.compareTo(java.math.BigDecimal.TEN) == 0)
        /** @note [[x.compareTo]] respects different representations of 0 */
        java.math.BigDecimal.ONE.scaleByPowerOfTen(i)
      else throw new IllegalArgumentException(unableToEvaluate(t))
    case FuncOf(f, Pair(a, b)) =>
      if (f == minF) eval(a).min(eval(b))
      else if (f == maxF) eval(a).max(eval(b))
      else throw new IllegalArgumentException(unableToEvaluate(t))
    case FuncOf(f, x) => if (f == absF) eval(x).abs else throw new IllegalArgumentException(unableToEvaluate(t))
    case Divide(a, b) =>
      val dividend = eval(a)
      val divisor = eval(b)
      try {

        /**
         * @note
         *   divide throws an [[ArithmeticException]] if the exact quotient does not have a terminating decimal
         *   expansion
         */
        val quotient = dividend.divide(divisor)
        // assert correctness of the exact result
        assert(quotient.multiply(divisor).compareTo(dividend) == 0)
        quotient
      } catch { case _: ArithmeticException => throw new IllegalArgumentException(unableToEvaluate(t)) }
    case _ => throw new IllegalArgumentException(unableToEvaluate(t))
  }

  /**
   * Evaluate a [[Formula]] by evaluating its terms in exact [[java.math.BigDecimal]] arithmetic.
   *
   * @return
   *   the truth value of the input formula or
   * @throws [[IllegalArgumentException]]
   *   if terms cannot be evaluated in exact arithmetic or if Formula is not a Boolean combination of numeric
   *   comparisons.
   */
  def eval(fml: Formula): Boolean = fml match {
    case LessEqual(s, t) => eval(s).compareTo(eval(t)) <= 0
    case GreaterEqual(s, t) => eval(s).compareTo(eval(t)) >= 0
    case Less(s, t) => eval(s).compareTo(eval(t)) < 0
    case Greater(s, t) => eval(s).compareTo(eval(t)) > 0
    case Equal(s, t) => eval(s).compareTo(eval(t)) == 0
    case NotEqual(s, t) => eval(s).compareTo(eval(t)) != 0
    case And(f, g) =>
      val a = eval(f)
      val b = eval(g)
      // @note avoid short-circuit evaluation to ensure input formula is a Boolean combination of numeric comparisons
      a && b
    case Or(f, g) =>
      val a = eval(f)
      val b = eval(g)
      // @note avoid short-circuit evaluation to ensure input formula is a Boolean combination of numeric comparisons
      a || b
    case Imply(f, g) =>
      val a = eval(f)
      val b = eval(g)
      // @note avoid short-circuit evaluation to ensure input formula is a Boolean combination of numeric comparisons
      !a || b
    case Equiv(f, g) => if (eval(f)) eval(g) else /* !eval(f) */ !eval(g)
    case Not(f) => !eval(f)
    case True => true
    case False => false
    case _ => throw new IllegalArgumentException(unableToEvaluate(fml))
  }

  /** @inheritdoc */
  override def quantifierElimination(formula: Formula): Formula = if (eval(formula)) True else False

  /** @inheritdoc */
  final override def restart(): Unit = {}

  /** @inheritdoc */
  final override def shutdown(): Unit = {}

  /** @inheritdoc */
  override def cancel(): Boolean = true

  /** @inheritdoc */
  override def isInitialized: Boolean = true
}
