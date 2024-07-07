/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.tools

import org.keymaerax.btactics.ToolProvider
import org.keymaerax.hydra.responses.configuration.ToolConfigErrorResponse
import org.keymaerax.hydra.responses.tools.ToolStatusResponse
import org.keymaerax.hydra.{DBAbstraction, ReadRequest, Request, Response}
import org.keymaerax.tools.{ToolName, ToolOperationManagement}

class ToolStatusRequest(db: DBAbstraction, toolId: String) extends Request with ReadRequest {
  override def resultingResponse(): Response = {
    // @todo switchSolver tactic switches tool without telling UI
    ToolProvider.tool(toolId) match {
      case Some(t: ToolOperationManagement) => new ToolStatusResponse(toolId, t.getAvailableWorkers)
      case Some(_) => new ToolStatusResponse(toolId, -1)
      case None => new ToolConfigErrorResponse(
          ToolName.parse(toolId),
          "Tool could not be started; please check KeYmaera X -> Preferences. Temporarily using " +
            ToolProvider.tools().map(_.name).mkString(",") + " with potentially limited functionality.",
        )
    }
  }
}
