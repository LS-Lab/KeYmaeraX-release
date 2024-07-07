/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.configuration

import org.keymaerax.hydra.{DBAbstraction, PlainResponse, ReadRequest, Response, UserRequest}
import spray.json._

class GetUserThemeRequest(db: DBAbstraction, userId: String) extends UserRequest(userId, _ => true) with ReadRequest {
  override def resultingResponse(): Response = {
    val config = db.getConfiguration(userId).config
    new PlainResponse(
      "themeCss" -> config.getOrElse("themeCss", "\"app\"").parseJson,
      "themeFontSize" -> config.getOrElse("themeFontSize", "14").parseJson,
      "renderMargins" -> config.getOrElse("renderMargins", "[40,80]").parseJson,
    )
  }
}
