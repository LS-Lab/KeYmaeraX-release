/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.configuration

import org.keymaerax.Configuration
import org.keymaerax.btactics.ToolProvider
import org.keymaerax.hydra.responses.configuration.{ToolConfigErrorResponse, ToolConfigStatusResponse}
import org.keymaerax.hydra.{DBAbstraction, ReadRequest, Request, Response}
import org.keymaerax.tools.ToolName

class WolframEngineConfigStatusRequest(db: DBAbstraction) extends Request with ReadRequest {
  override def resultingResponse(): Response = {
    ToolProvider.tool("wolframEngine") match {
      case Some(_) => new ToolConfigStatusResponse(
          ToolName.WolframEngine,
          Configuration.contains(Configuration.Keys.WOLFRAMENGINE_LINK_NAME) &&
            Configuration.contains(Configuration.Keys.WOLFRAMENGINE_JLINK_LIB_DIR) &&
            Configuration.contains(Configuration.Keys.WOLFRAMENGINE_TCPIP),
        )
      case None => new ToolConfigErrorResponse(
          ToolName.WolframEngine,
          "Wolfram Engine could not be started; please double-check the configured paths and make sure you are online for license checking. Temporarily using " +
            ToolProvider.tools().map(_.name).mkString(",") + " with potentially limited functionality.",
        )
    }
  }
}
