/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.tools

import edu.cmu.cs.ls.keymaerax.btactics.ToolProvider
import edu.cmu.cs.ls.keymaerax.hydra.responses.configuration.ToolConfigErrorResponse
import edu.cmu.cs.ls.keymaerax.hydra.responses.tools.ToolStatusResponse
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, ReadRequest, Request, Response}
import edu.cmu.cs.ls.keymaerax.tools.ToolOperationManagement

class ToolStatusRequest(db: DBAbstraction, toolId: String) extends Request with ReadRequest {
  override def resultingResponse(): Response = {
    // @todo switchSolver tactic switches tool without telling UI
    ToolProvider.tool(toolId) match {
      case Some(t: ToolOperationManagement) => new ToolStatusResponse(toolId, t.getAvailableWorkers)
      case Some(_) => new ToolStatusResponse(toolId, -1)
      case None => new ToolConfigErrorResponse(
          toolId,
          "Tool could not be started; please check KeYmaera X -> Preferences. Temporarily using " +
            ToolProvider.tools().map(_.name).mkString(",") + " with potentially limited functionality.",
        )
    }
  }
}
