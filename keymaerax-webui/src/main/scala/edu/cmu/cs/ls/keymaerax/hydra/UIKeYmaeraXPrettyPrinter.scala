/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXWeightedPrettyPrinter, Parser, PrettyPrinter}
import edu.cmu.cs.ls.keymaerax.bellerophon.PosInExpr

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

//  override val parser = new Parser() {
//    def apply(input: String): Expression = throw new UnsupportedOperationException("UIKeYmaeraXPrettyPrinter.parser is undefined since not parsing HTML")
//    val termParser: (String => Term) = s => throw new UnsupportedOperationException("UIKeYmaeraXPrettyPrinter.parser is undefined since not parsing HTML")
//    val formulaParser: (String => Formula) = s => throw new UnsupportedOperationException("UIKeYmaeraXPrettyPrinter.parser is undefined since not parsing HTML")
//    val programParser: (String => Program) = s => throw new UnsupportedOperationException("UIKeYmaeraXPrettyPrinter.parser is undefined since not parsing HTML")
//    val differentialProgramParser: (String => DifferentialProgram) = s => throw new UnsupportedOperationException("UIKeYmaeraXPrettyPrinter.parser is undefined since not parsing HTML")
//    val printer: PrettyPrinter = UIKeYmaeraXPrettyPrinter.this
//  }
  override val fullPrinter: (Expression => String) = (e:Expression) => throw new UnsupportedOperationException("UIKeYmaeraXPrettyPrinter.fullPrinter not implemented yet")
}
