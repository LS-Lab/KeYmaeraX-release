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

class MathematicaConfigStatusRequest(db: DBAbstraction) extends Request with ReadRequest {
  override def resultingResponse(): Response = {
    ToolProvider.tool("mathematica") match {
      case Some(_) => new ToolConfigStatusResponse(
          ToolName.Mathematica,
          Configuration.contains(Configuration.Keys.MATHEMATICA_LINK_NAME) &&
            Configuration
              .contains(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR) && ToolProvider.tool("mathematica").isDefined,
        )
      case None => new ToolConfigErrorResponse(
          ToolName.Mathematica,
          "Mathematica could not be started; please double-check the configured paths and make sure you have a valid license (if you use a license server, make sure it is reachable). Temporarily using " +
            ToolProvider.tools().map(_.name).mkString(",") + " with potentially limited functionality.",
        )
    }
  }
}
