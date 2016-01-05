/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.Expression
import edu.cmu.cs.ls.keymaerax.tactics.PosInExpr

/**
  * User-interface pretty printer for KeYmaera X syntax.
  * @author Andre Platzer
  */
class UIKeYmaeraXPrettyPrinter extends KeYmaeraXWeightedPrettyPrinter {
  private val HTML_OPEN = "$#@@"
  private val HTML_CLOSE = "@@#$"

  override def apply(expr: Expression): String = (stringify(expr)
    .replaceAllLiterally("<", "&lt;")
    .replaceAllLiterally(">", "&gt;")
    .replaceAllLiterally(HTML_OPEN, "<")
    .replaceAllLiterally(HTML_CLOSE, ">")
    )

  protected override def emit(q: PosInExpr, s: String): String =
    HTML_OPEN + "term id=\"" + q.pos.mkString(".") + "\"" + HTML_CLOSE + s + HTML_OPEN + "term" + HTML_CLOSE
}
