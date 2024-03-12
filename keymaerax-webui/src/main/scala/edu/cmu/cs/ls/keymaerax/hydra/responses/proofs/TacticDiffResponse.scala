/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.proofs

import edu.cmu.cs.ls.keymaerax.bellerophon.TacticDiff
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BellePrettyPrinter
import edu.cmu.cs.ls.keymaerax.hydra.Response
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
