/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.core.{Expression, Sequent}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXWeightedPrettyPrinter
import edu.cmu.cs.ls.keymaerax.tactics.PosInExpr

object UIKeYmaeraXPrettyPrinter {
  /** UIKeYmaeraXPrettyPrinter(topId) is a UI pretty printer for sequent-formula with identifier topId */
  def apply(topId: String): Expression=>String = new UIKeYmaeraXPrettyPrinter(topId)
}

/**
  * User-interface pretty printer for KeYmaera X syntax.
  * @author Andre Platzer
  */
class UIKeYmaeraXPrettyPrinter(val topId: String) extends KeYmaeraXWeightedPrettyPrinter {
  private val HTML_OPEN = "$#@@$"
  private val HTML_CLOSE = "$@@#$"

  override def apply(expr: Expression): String = (stringify(expr)
    .replaceAllLiterally("<", "&lt;")
    .replaceAllLiterally(">", "&gt;")
    .replaceAllLiterally(HTML_OPEN, "<")
    .replaceAllLiterally(HTML_CLOSE, ">")
    )

  protected override def emit(q: PosInExpr, s: String): String =
    wrap(topId + "/" + q.pos.mkString("."), s)

//  private def wrap(id: String, content: String): String =
//    HTML_OPEN + "term id=\"" + id + "\"" + HTML_CLOSE + content + HTML_OPEN + "/term" + HTML_CLOSE

  private def wrap(id: String, content: String): String =
  s"""$$#@@$$span class="hl" id="$id"
    | onmouseover="$$(event.target).addClass('hlhover');"
    | onmouseout="$$(event.target).removeClass('hlhover');"
    | ng-click="formulaClick('$id', $$event)"
    | ng-right-click="formulaRightClick('$id', $$event)"
    | ng-repeat="formulaId in ['$id']"
    | uib-popover-template="'templates/axiomPopoverTemplate.html'"
    | popover-is-open="tacticPopover.isOpen('$id')"
    | popover-append-to-body="true"
    | popover-placement="bottom"$$@@#$$$content$$#@@$$/span$$@@#$$
  """.stripMargin


  //@todo
  override def apply(seq: Sequent): String = ???

  override def parser = throw new UnsupportedOperationException("UIKeYmaeraXPrettyPrinter.parser is undefined since not parsing HTML")
  override def fullPrinter: (Expression => String) = throw new UnsupportedOperationException("UIKeYmaeraXPrettyPrinter.fullPrinter not implemented yet")
}
