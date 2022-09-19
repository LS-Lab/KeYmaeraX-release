/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.tools

import edu.cmu.cs.ls.keymaerax.btactics.ToolProvider
import edu.cmu.cs.ls.keymaerax.core.{Formula, QETool}
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, ErrorResponse, GenericOKResponse, LocalhostOnlyRequest, Response}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter.StringToStringConverter
import edu.cmu.cs.ls.keymaerax.tools.Tool

import java.util.concurrent.{FutureTask, TimeUnit, TimeoutException}
import scala.collection.immutable.{List, Nil}

class TestToolConnectionRequest(db: DBAbstraction, toolId: String) extends LocalhostOnlyRequest {
  override def resultingResponses(): List[Response] = {
    ToolProvider.tool(toolId) match {
      case Some(t: QETool) =>
        val simpleQeTask = new FutureTask[Either[Formula, Throwable]](() =>
          try {
            Left(t.quantifierElimination("1+2=3".asFormula))
          } catch {
            case e: Throwable => Right(e)
          })
        new Thread(simpleQeTask).start()
        try {
          val result = simpleQeTask.get(1, TimeUnit.SECONDS)
          if (result.isLeft && result.left.get == "true".asFormula) new GenericOKResponse :: Nil
          else if (result.isLeft && result.left.get != "true".asFormula) new ErrorResponse("Testing connection failed: unexpected result " + result.left.get + " for test 2+3=5") :: Nil
          else /* result.isRight */ new ErrorResponse("Testing connection failed", result.right.get) :: Nil
        } catch {
          case _: TimeoutException =>
            new ErrorResponse("Testing connection failed: tool is not responding. Please restart KeYmaera X.") :: Nil
        }
      case Some(t: Tool) => new ErrorResponse(s"Testing connection failed: do not know how to test '${t.getClass}' tool") :: Nil
      case _ => new ErrorResponse(s"Testing connection failed: unknown tool '$toolId'. Please check the tool configuration.") :: Nil
    }

  }
}