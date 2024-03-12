/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.tools

import edu.cmu.cs.ls.keymaerax.btactics.ToolProvider
import edu.cmu.cs.ls.keymaerax.core.{Box, ODESystem}
import edu.cmu.cs.ls.keymaerax.hydra.responses.tools.ODEConditionsResponse
import edu.cmu.cs.ls.keymaerax.hydra._
import edu.cmu.cs.ls.keymaerax.tools.{MathematicaComputationAbortedException, MathematicaComputationTimedOutException}

import scala.collection.immutable.{List, Nil}

class ODEConditionsRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
    extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId) match {
      case None => new ErrorResponse("Unknown node " + nodeId) :: Nil
      case Some(node) =>
        try {
          node.goal match {
            case Some(sequent) => sequent
                .succ
                .find({
                  case Box(_: ODESystem, _) => true
                  case _ => false
                }) match {
                case Some(Box(ode: ODESystem, post)) => ToolProvider.invGenTool() match {
                    case Some(tool) =>
                      val (sufficient, necessary) = tool.genODECond(ode, sequent.ante, post)
                      new ODEConditionsResponse(sufficient, necessary) :: Nil
                    case None => new ODEConditionsResponse(Nil, Nil) :: Nil
                  }
                case None =>
                  new ErrorResponse(
                    "ODE system needed to search for ODE conditions, but succedent does not contain an ODE system or ODE system may not be at top level. Please perform additional proof steps until ODE system is at top level."
                  ) :: Nil
              }
            case None => new ErrorResponse("ODE system needed to search for ODE conditions, but goal is empty.") :: Nil
          }
        } catch {
          case _: MathematicaComputationAbortedException => new ErrorResponse("ODE conditions search timeout.") :: Nil
          case _: MathematicaComputationTimedOutException => new ErrorResponse("ODE conditions search timeout.") :: Nil
        }
    }
  }
}
