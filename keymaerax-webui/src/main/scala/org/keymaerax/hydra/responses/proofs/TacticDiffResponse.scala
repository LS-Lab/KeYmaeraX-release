/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.responses.proofs

import org.keymaerax.bellerophon.TacticDiff
import org.keymaerax.bellerophon.parser.BellePrettyPrinter
import org.keymaerax.hydra.Response
import spray.json.{JsArray, JsObject, JsString, JsValue}

class TacticDiffResponse(diff: TacticDiff.Diff) extends Response {
  def getJson: JsValue = JsObject(
    "context" -> JsString(BellePrettyPrinter(diff._1.t)),
    "replOld" -> JsArray(
      diff
        ._2
        .map({ case (dot, repl) =>
          JsObject("dot" -> JsString(BellePrettyPrinter(dot)), "repl" -> JsString(BellePrettyPrinter(repl)))
        })
        .toVector
    ),
    "replNew" -> JsArray(
      diff
        ._3
        .map({ case (dot, repl) =>
          JsObject("dot" -> JsString(BellePrettyPrinter(dot)), "repl" -> JsString(BellePrettyPrinter(repl)))
        })
        .toVector
    ),
  )
}
