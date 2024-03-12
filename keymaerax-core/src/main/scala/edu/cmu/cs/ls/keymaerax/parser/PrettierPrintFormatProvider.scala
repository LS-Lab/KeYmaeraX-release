/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.Expression

/** Uses the [[KeYmaeraXPrettierPrinter]] to provide formatting for expression `e` fitting into `margin`. */
case class PrettierPrintFormatProvider(e: Expression, margin: Int)
    extends PrettyPrintFormatProvider(new KeYmaeraXPrettierPrinter(margin)(e), s => s) {
  override def print(next: String): String =
    try { super.print(next) }
    catch { case _: Throwable => next }
}
