/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * @note Code Review: 2016-08-02
  */

package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.tools.MathematicaConversion.MExpr
import KMComparator._
import edu.cmu.cs.ls.keymaerax.core.{Function, Real, Tuple}

/**
  * Mathematica conversion stuff.
  *
  * @author Stefan Mitsch
  */

object MathematicaConversion {
  type MExpr = com.wolfram.jlink.Expr
  type KExpr = edu.cmu.cs.ls.keymaerax.core.Expression

  /** Reads a result from a mathematica expression `e` using the specified conversion, and safely disposes `e`.
    * @ensures e has been freed and should not ever be used again.
    */
  def importResult[T](e: MExpr, conversion: MExpr => T): T = try { conversion(e) } finally { e.dispose() }

  /** Interpreted symbols. */
  val interpretedSymbols: Map[Function, MExpr] = Map(
    Function("abs", None, Real, Real, interpreted=true) -> new MExpr(com.wolfram.jlink.Expr.SYMBOL, "Abs"),
    Function("max", None, Tuple(Real, Real), Real, interpreted=true) -> new MExpr(com.wolfram.jlink.Expr.SYMBOL, "Max"),
    Function("min", None, Tuple(Real, Real), Real, interpreted=true) -> new MExpr(com.wolfram.jlink.Expr.SYMBOL, "Min")
  )
}

/**
  * Converts Mathematica -> KeYmaera
  * @tparam T usually Expression, but also other target types for non-soundness-critical conversions.
  */
trait M2KConverter[T] extends (MExpr => T) {
  /** Convert mathematica expression `e` to `T` with rountrip contracts. */
  def apply(e: MExpr): T = convert(e) ensuring(r => k2m.convert(r) === e,
    "Roundtrip conversion is identity." +
      "\nMathematica expression:   " + e.toString + "\t@[" + e.args.map(_.head()).mkString(", ") + "]" +
      "\nConverted to KeYmaera X:  " + convert(e) + "\t@" + convert(e).getClass.getSimpleName +
      "\nRoundtrip to Mathematica: " + k2m.convert(convert(e)).toString + "\t@[" + k2m.convert(convert(e)).args.map(_.head()).mkString(", ") + "]")

  /** Converse conversion for contracts
    * @ensures k2m(this(e)) == e
    */
  def k2m: K2MConverter[T]

  /** Convert without contract checking */
  private[tools] def convert(e: MExpr): T

  /** Interpreted symbols. */
  def interpretedSymbols: Map[MExpr, Function] = MathematicaConversion.interpretedSymbols.map(_.swap)
}

/**
  * Converts KeYmaera -> Mathematica
  * @tparam T usually Expression, but also other source types for non-soundness-critical conversions.
  */
trait K2MConverter[T] extends (T => MExpr) {
  /** Convert expression `e` to Mathematica with rountrip contracts. */
  def apply(e: T): MExpr = convert(e) ensuring(r => m2k.convert(r) == e,
    "Roundtrip conversion is identity." +
    "\nKeYmaera X expression    " + e + "\t@" + e.getClass.getSimpleName +
    "\nConverted to Mathematica " + convert(e).toString +
    "\nRoundtrip to KeYmaera X  " + m2k.convert(convert(e)) + "\t@" + m2k.convert(convert(e)).getClass.getSimpleName)

  /** Converse conversion for contractcs
    * @ensures m2k(this(e)) == e
    */
  def m2k: M2KConverter[T]

  /** Convert without contract checking */
  private[tools] def convert(e: T): MExpr

  /** Interpreted symbols. */
  def interpretedSymbols: Map[Function, MExpr] = MathematicaConversion.interpretedSymbols
}

/** Implicit conversion from Mathematica expressions to comparator. */
object KMComparator {
  /**
    * Whether e is thing or starts with head thing.
    * @return true if ``e" and ``thing" are .equals-related.
    */
  def hasHead(e: MExpr, thing: MExpr) = e.equals(thing) || e.head().equals(thing)

  import scala.language.implicitConversions
  implicit def MExprToKMComparator(e: MExpr): KMComparator = new KMComparator(e)
}

/** Compares Mathematica expressions for equality (handles conversion differences). */
class KMComparator(val l: MExpr) {
  import KMComparator.hasHead

  /** Non-commutative comparison of Mathematica expressions for equality modulo Mathematica's implicit conversions.
    * Triple equality === is a new recursive definition based on double equality == of heads and recursing on arguments
    * plus special handling of rational etc.
    */
  def ===(r: MExpr): Boolean =
    // traverse MExpr and forward to MExpr.== for atomic MExpr, use === for arguments
    (l.head() == r.head() && l.args().length == r.args().length && l.args().zip(r.args()).forall({ case (la, ra) => la === ra })) ||
    // or special comparison
    (if (hasHead(l, MathematicaSymbols.INEQUALITY)) inequalityEquals(l, r)
    else if (hasHead(r, MathematicaSymbols.INEQUALITY)) inequalityEquals(r, l)
    else if (hasHead(l, MathematicaSymbols.RATIONAL)) rationalEquals(l, r)
    else if (hasHead(r, MathematicaSymbols.RATIONAL)) rationalEquals(r, l)
    else if (hasHead(l, MathematicaSymbols.PLUS)) naryEquals(l, r, MathematicaSymbols.PLUS)
    else if (hasHead(l, MathematicaSymbols.MULT)) naryEquals(l, r, MathematicaSymbols.MULT)
    else if (hasHead(l, MathematicaSymbols.AND)) naryEquals(l, r, MathematicaSymbols.AND)
    else if (hasHead(l, MathematicaSymbols.OR)) naryEquals(l, r, MathematicaSymbols.OR)
    else false)

  private def inequalityEquals(l: MExpr, r: MExpr): Boolean = {
    def checkInequality(l: Array[MExpr], r: MExpr): Boolean = hasHead(r, l(1)) && r.args.length == 2 && r.args().head === l(0) && r.args().last === l(2)
    def checkInequalities(l: Array[MExpr], r: MExpr): Boolean = {
      require(l.length % 2 == 1 && r.args().length % 2 == 0, "Expected pairs of expressions separated by operators")
      if (l.length <= 3) checkInequality(l, r)
      // And[c[a,b], ...] == {a c b ... }
      else hasHead(r, MathematicaSymbols.AND) && checkInequality(l, r.args().head) && checkInequalities(l.tail.tail, r.args().last)
    }
    checkInequalities(l.args(), r)
  }

  private def rationalEquals(l: MExpr, r: MExpr): Boolean = {
    assert(hasHead(l, MathematicaSymbols.RATIONAL) || hasHead(l, MathematicaSymbols.DIV), "already checked for rational-like heads")
    hasHead(r, MathematicaSymbols.DIV) && l.args().length == 2 && r.args().length == 2 &&
      l.args().head === r.args().head && l.args().last === r.args().last
  }

  /** equality modulo some limited form of associativity that Mathematica implicitly converts into n-ary operators */
  private def naryEquals(l: MExpr, r: MExpr, expectedHead: MExpr): Boolean = {
    // Op[Op[a,b], c] === Op[a,b,c]
    def checkBinary(l: MExpr, r: MExpr, i: Int): Boolean = {
      (l.head() === r.head() && l.args().length == 2 && l.args().last === r.args().reverse(i) &&
        (if (hasHead(l.args().head, expectedHead)) checkBinary(l.args().head, r, i+1)
         else l.args().head === r.args().reverse(i+1))) ||
      // List of Ands: first argument could be an Inequality, don't recurse
      (i == r.args().length-1 && l === r.args().reverse(i))
    }
    checkBinary(l, r, 0)
  }
}
