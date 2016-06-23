/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.tools.MathematicaConversion.MExpr

/**
  * Conversion types.
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
  def apply(e: MExpr): T = convert(e) ensuring(r => k2m.convert(r) == e, "Roundtrip conversion is identity." +
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
