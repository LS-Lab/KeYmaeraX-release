/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.configuration

import edu.cmu.cs.ls.keymaerax.hydra.Response
import edu.cmu.cs.ls.keymaerax.tools.ToolPathFinder
import spray.json.{JsBoolean, JsObject, JsString, JsValue}

import java.io.File

class MathematicaConfigSuggestionResponse(
    os: String,
    suggestionFound: Boolean,
    suggestion: ToolPathFinder.MathematicaPaths,
) extends Response {

  private def convertSuggestion(info: ToolPathFinder.MathematicaPaths): JsValue = JsObject(
    "kernelPath" -> JsString(info.mathKernel.getParent.toString + File.separator),
    "kernelName" -> JsString(info.mathKernel.getFileName.toString),
    "jlinkPath" -> JsString(info.jlinkLib.getParent.toString + File.separator),
    "jlinkName" -> JsString(info.jlinkLib.getFileName.toString),
  )

  def getJson: JsValue = JsObject(
    "os" -> JsString(os),
    "suggestionFound" -> JsBoolean(suggestionFound),
    "suggestion" -> convertSuggestion(suggestion),
  )
}
