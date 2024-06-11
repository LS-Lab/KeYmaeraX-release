/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.hydra.{
  ConfigurationPOJO,
  DBAbstraction,
  PlainResponse,
  ReadRequest,
  Response,
  UserRequest,
}
import spray.json._

/** Sets the UI theme. @note ReadRequest allows changing theme in guest mode for presentation purposes. */
class SetUserThemeRequest(
    db: DBAbstraction,
    userId: String,
    themeCss: String,
    themeFontSize: String,
    renderMargins: String,
) extends UserRequest(userId, _ => true) with ReadRequest {
  override def resultingResponse(): Response = {
    val config = db.getConfiguration(userId)
    db.updateConfiguration(new ConfigurationPOJO(
      userId,
      config
        .config
        .updated("themeCss", themeCss)
        .updated("themeFontSize", themeFontSize)
        .updated("renderMargins", renderMargins),
    ))
    new PlainResponse(
      "themeCss" -> themeCss.parseJson,
      "themeFontSize" -> themeFontSize.parseJson,
      "renderMargins" -> renderMargins.parseJson,
    )
  }
}
