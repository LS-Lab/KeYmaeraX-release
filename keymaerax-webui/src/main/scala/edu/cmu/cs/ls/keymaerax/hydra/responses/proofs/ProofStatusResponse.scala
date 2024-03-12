/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.proofs

import edu.cmu.cs.ls.keymaerax.hydra.Response
import spray.json.{JsObject, JsString, JsValue}

class ProofStatusResponse(proofId: String, status: String, error: Option[String] = None) extends Response {
  override val schema: Option[String] = Some("proofstatus.js")
  def getJson: JsValue = JsObject(
    "proofId" -> JsString(proofId),
    "type" -> JsString("ProofLoadStatus"),
    "status" -> JsString(status),
    "textStatus" -> JsString(status + ": " + proofId),
    "errorThrown" -> JsString(error.getOrElse("")),
  )
}
class ProofIsLoadingResponse(proofId: String) extends ProofStatusResponse(proofId, "loading")
class ProofNotLoadedResponse(proofId: String) extends ProofStatusResponse(proofId, "notloaded")
class ProofIsLoadedResponse(proofId: String) extends ProofStatusResponse(proofId, "loaded")
// progress "open": open goals
// progress "closed": no open goals but not checked for isProved
class ProofProgressResponse(proofId: String, isClosed: Boolean)
    extends ProofStatusResponse(proofId, if (isClosed) "closed" else "open")
