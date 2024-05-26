/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.configuration

import edu.cmu.cs.ls.keymaerax.hydra.Response
import edu.cmu.cs.ls.keymaerax.tools.install.ToolConfiguration
import spray.json.{JsArray, JsBoolean, JsObject, JsString, JsValue}

class MathematicaConfigSuggestionResponse(
    os: String,
    suggestionFound: Boolean,
    suggestion: ToolConfiguration.ConfigSuggestion,
    allSuggestions: List[ToolConfiguration.ConfigSuggestion],
) extends Response {

  private def convertSuggestion(info: ToolConfiguration.ConfigSuggestion): JsValue = JsObject(
    "version" -> JsString(info.version),
    "kernelPath" -> JsString(info.kernelPath),
    "kernelName" -> JsString(info.kernelName),
    "jlinkPath" -> JsString(info.jlinkPath),
    "jlinkName" -> JsString(info.jlinkName),
  )

  def getJson: JsValue = JsObject(
    "os" -> JsString(os),
    "jvmArchitecture" -> JsString("64"),
    "suggestionFound" -> JsBoolean(suggestionFound),
    "suggestion" -> convertSuggestion(suggestion),
    "allSuggestions" -> JsArray(allSuggestions.map(convertSuggestion): _*),
  )
}
