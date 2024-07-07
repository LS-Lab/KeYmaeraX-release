/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.tools

import org.keymaerax.btactics.ToolProvider
import org.keymaerax.hydra.{DBAbstraction, ErrorResponse, GenericOKResponse, LocalhostOnlyRequest, Response}
import org.keymaerax.tools.Tool

import scala.collection.immutable.{List, Nil}

class RestartToolRequest(db: DBAbstraction, toolId: String) extends LocalhostOnlyRequest {
  override def resultingResponse(): Response = {
    ToolProvider.tool(toolId) match {
      case Some(t: Tool) =>
        t.restart()
        new GenericOKResponse
      case _ => new ErrorResponse(s"Restarting failed: unknown tool '$toolId'. Please check the tool configuration.")
    }
  }
}
