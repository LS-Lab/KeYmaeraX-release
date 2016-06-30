/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.tools.MathematicaConversion.MExpr
import KMComparator._

/**
  * Conversion types.
  *
  * @author Stefan Mitsch
  */

object MathematicaConversion {
  type MExpr = com.wolfram.jlink.Expr
  type KExpr = edu.cmu.cs.ls.keymaerax.core.Expression

  /** Reads a result from e using the specified conversion, disposes e. */
  def safeResult[T](e: MExpr, conversion: MExpr => T): T = try { conversion(e) } finally { e.dispose() }
}

/**
  * Converts Mathematica -> KeYmaera
  */
trait M2KConverter[T] extends (MExpr => T) {
  /** Converse conversion for contracts */
  def k2m: K2MConverter[T]

  /** Convert without contract checking */
  def convert(e: MExpr): T
}

trait BaseM2KConverter[T] extends M2KConverter[T] {
  def apply(e: MExpr): T = convert(e) ensuring(r => k2m.convert(r) === e, "Roundtrip conversion is identity." +
    "\nMathematica expression:   " + e.toString + "\t@[" + e.args.map(_.head()).mkString(", ") + "]" +
    "\nConverted to KeYmaera X:  " + convert(e) + "\t@" + convert(e).getClass.getSimpleName +
    "\nRoundtrip to Mathematica: " + k2m.convert(convert(e)).toString + "\t@[" + k2m.convert(convert(e)).args.map(_.head()).mkString(", ") + "]")
}

/**
  * Converts KeYmaera -> Mathematica
  */
trait K2MConverter[T] extends (T => MExpr) {
  /** Converse conversion for contractcs */
  def m2k: M2KConverter[T]

  /** Convert without contract checking */
  def convert(e: T): MExpr
}

trait BaseK2MConverter[T] extends K2MConverter[T] {
  def apply(e: T): MExpr = convert(e) ensuring(r => m2k.convert(r) == e, "Roundtrip conversion is identity." +
    "\nKeYmaera X expression    " + e + "\t@" + e.getClass.getSimpleName +
    "\nConverted to Mathematica " + convert(e).toString +
    "\nRoundtrip to KeYmaera X  " + m2k.convert(convert(e)) + "\t@" + m2k.convert(convert(e)).getClass.getSimpleName)
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

  /** Equality of Mathematica expressions */
  def ===(r: MExpr): Boolean = l == r || (
    if (hasHead(l, MathematicaSymbols.INEQUALITY)) {
      def checkInequality(l: Array[MExpr], r: MExpr): Boolean = hasHead(r, l(1)) && r.args.length == 2 && r.args().head == l(0) && r.args().last == l(2)
      def checkInequalities(l: Array[MExpr], r: MExpr): Boolean = {
        require(l.length % 2 == 1 && r.args().length % 2 == 0, "Expected pairs of expressions separated by operators")
        if (l.length <= 3) checkInequality(l, r)
        // And[c[a,b], ...] == {a c b ... }
        else hasHead(r, MathematicaSymbols.AND) && checkInequality(l, r.args().head) && checkInequalities(l.tail.tail, r.args().last)
      }
      checkInequalities(l.args(), r)
    } else if (hasHead(r, MathematicaSymbols.INEQUALITY)) {
      new KMComparator(r).===(l)
    } else false)
}
