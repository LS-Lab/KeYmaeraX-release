/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.modelplex

import edu.cmu.cs.ls.keymaerax.core.{Expression, Formula}
import edu.cmu.cs.ls.keymaerax.hydra.{ModelPOJO, Response}
import edu.cmu.cs.ls.keymaerax.parser.{ArchiveParser, PrettierPrintFormatProvider}
import spray.json.{JsObject, JsString, JsValue}

abstract class ModelPlexResponse(model: ModelPOJO, code: String) extends Response {
  protected def prettierPrint(e: Expression): String = PrettierPrintFormatProvider(e, 80).print(e.prettyString)

  def getJson: JsValue = {
    JsObject(
      "modelid" -> JsString(model.modelId.toString),
      "modelname" -> JsString(model.name),
      "code" -> JsString(code),
      "source" -> JsString(prettierPrint(ArchiveParser(model.keyFile).head.expandedModel)),
    )
  }
}

class ModelPlexArtifactResponse(model: ModelPOJO, artifact: Expression)
    extends ModelPlexResponse(model, PrettierPrintFormatProvider(artifact, 80).print(artifact.prettyString)) {}

class ModelPlexMonitorResponse(model: ModelPOJO, artifact: Expression, proofArchive: String)
    extends ModelPlexArtifactResponse(model, artifact) {
  override def getJson: JsValue = {
    val artifact = super.getJson.asJsObject
    artifact.copy(artifact.fields + ("proof" -> JsString(proofArchive)))
  }
}

class ModelPlexSandboxResponse(model: ModelPOJO, conjecture: Formula, artifact: Expression)
    extends ModelPlexArtifactResponse(model, artifact) {
  override def getJson: JsValue = {
    val artifact = super.getJson.asJsObject
    artifact.copy(artifact.fields + ("conjecture" -> JsString(prettierPrint(conjecture))))
  }
}

class ModelPlexCCodeResponse(model: ModelPOJO, code: String) extends ModelPlexResponse(model, code) {}
