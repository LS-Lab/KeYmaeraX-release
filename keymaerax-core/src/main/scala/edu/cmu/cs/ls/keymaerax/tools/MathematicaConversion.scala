/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.tools.MathematicaConversion.{KExpr, MExpr}

/**
  * Conversion types.
  * @author Stefan Mitsch
  */

object MathematicaConversion {
  type MExpr = com.wolfram.jlink.Expr
  type KExpr = edu.cmu.cs.ls.keymaerax.core.Expression
}

/**
  * Converts Mathematica -> KeYmaera
  */
trait M2KConverter extends (MExpr => KExpr) {
  /** Converse conversion for contracts */
  def k2m: K2MConverter

  /** Convert without contract checking */
  def convert(e: MExpr): KExpr
}

trait BaseM2KConverter extends M2KConverter {
  def apply(e: MExpr): KExpr = convert(e) ensuring(r => k2m.convert(r) == e, "Roundtrip conversion is identity." +
    "\nMathematica expression:   " + e.toString + "\t@[" + e.args.map(_.head()).mkString(", ") + "]" +
    "\nConverted to KeYmaera X:  " + convert(e).prettyString + "\t@" + convert(e).getClass.getSimpleName +
    "\nRoundtrip to Mathematica: " + k2m.convert(convert(e)).toString + "\t@[" + k2m.convert(convert(e)).args.map(_.head()).mkString(", ") + "]")
}

/**
  * Converts KeYmaera -> Mathematica
  */
trait K2MConverter extends (KExpr => MExpr) {
  /** Converse conversion for contractcs */
  def m2k: M2KConverter

  /** Convert without contract checking */
  def convert(e: KExpr): MExpr
}

trait BaseK2MConverter extends K2MConverter {
  def apply(e: KExpr): MExpr = convert(e) ensuring(r => m2k.convert(r) == e, "Roundtrip conversion is identity." +
    "\nKeYmaera X expression    " + e.prettyString + "\t@" + e.getClass.getSimpleName +
    "\nConverted to Mathematica " + convert(e).toString +
    "\nRoundtrip to KeYmaera X  " + m2k.convert(convert(e)).prettyString + "\t@" + m2k.convert(convert(e)).getClass.getSimpleName)
}
