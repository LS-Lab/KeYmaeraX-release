/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * @note Code Review: 2016-08-02
  */

package edu.cmu.cs.ls.keymaerax.tools.qe

import edu.cmu.cs.ls.keymaerax.core.{ApplicationOf, BinaryCompositeFormula, BinaryCompositeTerm, ComparisonFormula, Divide, Ensures, Number, Quantified, UnaryCompositeFormula, UnaryCompositeTerm}
import edu.cmu.cs.ls.keymaerax.tools.qe.KMComparator._
import edu.cmu.cs.ls.keymaerax.tools.qe.MKComparator._
import edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaConversion.MExpr

import scala.annotation.tailrec

/**
  * Mathematica conversion support to check results for having failed/being aborted, and safely importing
  * Mathematica expressions into KeYmaera X.
  * @see [[M2KConverter]] for converting Mathematica -> KeYmaera X
  * @see [[K2MConverter]] for converting KeYmaera X  -> Mathematica
  *
  * @author Stefan Mitsch
  */
object MathematicaConversion {
  type MExpr = com.wolfram.jlink.Expr
  type KExpr = edu.cmu.cs.ls.keymaerax.core.Expression

  /** Reads a result from a mathematica expression `e` using the specified conversion, and safely disposes `e`.
    * @ensures e has been freed and should not ever be used again.
    */
  def disposeAfter[T](e: MExpr, conversion: MExpr => T): T = try { conversion(e) } finally { e.dispose() }

  /**
   * Check if a Mathematica expression has been aborted.
   *
   * @param e The expression to test.
   * @return `true` if the expression has aborted or timed out,
   *         `false` otherwise.
   */
  def isAborted(e: MExpr): Boolean =
    (e == MathematicaOpSpec.abort.op) ||
    (e == MathematicaOpSpec.aborted.op)

  /**
   * Check if a Mathematica expression failed.
   *
   * @param e The expression to test.
   * @return `true` if the expression has failed,
   *         `false` otherwise.
   */
  def isFailed(e: MExpr): Boolean =
    (e == MathematicaOpSpec.failed.op)

  /**
   * Check if a Mathematica expression timed out.
   *
   * @param e The expression to test.
   * @return `true` if the expression has timed out,
   *         `false` otherwise.
   */
  def isTimedOut(e: MExpr): Boolean =
    (e == MathematicaOpSpec.timedOut.op)

  /**
   * Check if a Mathematica expression is an exception.
   *
   * @param e The expression to test.
   * @return `true` if the expression is an exception,
   *         `false` otherwise.
   */
  def isException(e: MExpr): Boolean =
    (e == MathematicaOpSpec.exception.op)
}

/**
  * Converts Mathematica -> KeYmaera X.
  * @tparam T usually Expression, but also other target types for non-soundness-critical conversions.
  */
trait M2KConverter[T] extends (MExpr => T) {
  /** Convert mathematica expression `e` to `T` with rountrip contracts. */
  def apply(e: MExpr): T = convert(e) ensures(r => k2m.convert(r) === e,
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

}

/**
  * Converts KeYmaera X -> Mathematica.
  * @tparam T usually Expression, but also other source types for non-soundness-critical conversions.
  */
trait K2MConverter[T] extends (T => MExpr) {
  /** Convert expression `e` to Mathematica with rountrip contracts. */
  def apply(e: T): MExpr = convert(e) ensures(r => m2k.convert(r) === e,
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
}

/** Implicit conversion from Mathematica expressions to comparator. */
object KMComparator {
  /**
    * Whether e is thing or starts with head thing.
    * @return true if ``e" and ``thing" are .equals-related.
    */
  def hasHead(e: MExpr, thing: MExpr): Boolean = e == thing || e.head == thing

  import scala.language.implicitConversions
  implicit def MExprToKMComparator(e: MExpr): KMComparator = new KMComparator(e)
}

/** Compares Mathematica expressions for equality (handles conversion differences, since Mathematica silently
  * converts some expressions, e.g. division 2/5 into rational 2/5). */
class KMComparator(val l: MExpr) {

  /** Non-commutative comparison of Mathematica expressions for equality modulo Mathematica's implicit conversions.
    * Triple equality === is a new recursive definition based on double equality == of heads and recursing on arguments
    * plus special handling of rational etc.
    */
  def ===(r: MExpr): Boolean =
    // traverse MExpr and forward to MExpr.== for atomic MExpr, use === for arguments
    (l.head() == r.head() && l.args().length == r.args().length && l.args().zip(r.args()).forall({ case (la, ra) => la === ra })) ||
    // or special comparison
    (if (MathematicaOpSpec.inequality.applies(l)) inequalityEquals(l, r)
    else if (MathematicaOpSpec.inequality.applies(r)) inequalityEquals(r, l)
    else if (MathematicaOpSpec.rational.applies(l)) rationalEquals(l, r)
    else if (MathematicaOpSpec.rational.applies(r)) rationalEquals(r, l)
    else if (MathematicaOpSpec.plus.applies(l)) naryEquals(l, r, MathematicaOpSpec.plus.op)
    else if (MathematicaOpSpec.times.applies(l)) naryEquals(l, r, MathematicaOpSpec.times.op)
    else if (MathematicaOpSpec.and.applies(l)) naryEquals(l, r, MathematicaOpSpec.and.op)
    else if (MathematicaOpSpec.or.applies(l)) naryEquals(l, r, MathematicaOpSpec.or.op)
    else false)

  private def inequalityEquals(l: MExpr, r: MExpr): Boolean = {
    def checkInequality(l: Array[MExpr], r: MExpr): Boolean =
      hasHead(r, l(1)) && r.args.length == 2 && r.args().head === l(0) && r.args().last === l(2)
    @tailrec
    def checkInequalities(l: Array[MExpr], r: MExpr): Boolean = {
      require(l.length % 2 == 1 && r.args().length % 2 == 0, "Expected pairs of expressions separated by operators")
      if (l.length <= 3) checkInequality(l, r)
      // And[c[a,b], ...] == {a c b ... }
      else MathematicaOpSpec.and.applies(r) && checkInequality(l, r.args().head) && checkInequalities(l.tail.tail, r.args().last)
    }
    checkInequalities(l.args(), r)
  }

  private def rationalEquals(l: MExpr, r: MExpr): Boolean = {
    assert(MathematicaOpSpec.rational.applies(l), "already checked for rational head")
    (MathematicaOpSpec.rational.applies(r) && l.args().length == 2 && r.args().length == 2 &&
      l.args().head === r.args().head && l.args().last === r.args().last) ||
    //@note may happen with runUnchecked, but not if KeYmaeraToMathematica conversion is used
    (r.realQ() &&
      BigDecimal(l.args().head.asLong) / BigDecimal(l.args().last.asLong) == BigDecimal(r.asDouble()))
  }

  /** equality modulo some limited form of associativity that Mathematica implicitly converts into n-ary operators */
  private def naryEquals(l: MExpr, r: MExpr, expectedHead: MExpr): Boolean = {
    // Op[Op[a,b], c] === Op[a,b,c]
    def flattenBinaryL(e: MExpr): List[MExpr] = {
      if (e.head() == expectedHead) flattenBinaryL(e.args().head) :+ e.args()(1)
      else List(e)
    }
    // Op[a, Op[b,c]] === Op[a,b,c]
    def flattenBinaryR(e: MExpr): List[MExpr] = {
      if (e.head() == expectedHead) e.args().head +: flattenBinaryR(e.args()(1))
      else List(e)
    }

    val lf = flattenBinaryL(l)
    if (lf.size == r.args().length) lf.zip(r.args()).forall({ case (r, l) => r === l})
    else {
      val rf = flattenBinaryR(l)
      if (rf.size == r.args().length) rf.zip(r.args()).forall({ case (r, l) => r === l})
      else false
    }
  }
}

/** Implicit conversion from KeYmaera expressions to comparator. */
object MKComparator {
  import scala.language.implicitConversions
  implicit def TToMKComparator[T](e: T): MKComparator[T] = new MKComparator[T](e)
}

class MKComparator[T](val l: T) {
  def ===(r: T): Boolean = (l, r) match {
    case (lf: UnaryCompositeFormula, rf: UnaryCompositeFormula) if lf.getClass == rf.getClass => lf.child === rf.child
    case (lf: BinaryCompositeFormula, rf: BinaryCompositeFormula) if lf.getClass == rf.getClass => lf.left === rf.left && lf.right === rf.right
    case (lf: ComparisonFormula, rf: ComparisonFormula) if lf.getClass == rf.getClass => lf.left === rf.left && lf.right === rf.right
    case (lt: UnaryCompositeTerm, rt: UnaryCompositeTerm) if lt.getClass == rt.getClass => lt.child === rt.child
    case (lt: BinaryCompositeTerm, rt: BinaryCompositeTerm) if lt.getClass == rt.getClass => lt.left === rt.left && lt.right === rt.right
    case (lq: Quantified, rq: Quantified) if lq.getClass == rq.getClass => lq.vars == rq.vars && lq.child === rq.child
    case (lf: ApplicationOf, rf: ApplicationOf) if lf.func == rf.func => lf.child === rf.child
    case (Number(lv), Divide(Number(rn), Number(rd))) => lv == rn/rd
    case (Divide(Number(ln), Number(ld)), Number(rv)) => ln/ld == rv
    case _ => l == r
  }
}
