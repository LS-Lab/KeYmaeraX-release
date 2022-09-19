/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.responses.proofs

import edu.cmu.cs.ls.keymaerax.core.{Expression, NamedSymbol, SystemConst}
import edu.cmu.cs.ls.keymaerax.hydra.Response
import spray.json.{JsArray, JsBoolean, JsObject, JsString, JsValue}

case class ApplicableDefinitionsResponse(defs: List[(NamedSymbol, Expression, Option[Expression], Boolean)]) extends Response {
  /** Transforms name `n`, its expression `ne`, and its replacement `re`. */
  private def getDefJson(n: NamedSymbol, ne: Expression, re: Option[Expression], isEditable: Boolean): JsValue = {
    JsObject(
      "symbol" -> JsString(n match {
        case SystemConst(n, _) => n
        case _ => n.prettyString
      }),
      "definition" -> JsObject(
        "what" -> JsString(ne match {
          case SystemConst(n, _) => n
          case _ => ne.prettyString
        }),
        "repl" -> JsString(re.map(_.prettyString).getOrElse("")),
        "editable" -> JsBoolean(isEditable),
        "assumptionsCart" -> JsBoolean(n.name.startsWith("A_"))
      )
    )
  }

  def getJson: JsValue = JsArray(defs.map(d => getDefJson(d._1, d._2, d._3, d._4)):_*)
}
