/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.tools

import org.keymaerax.btactics.ToolProvider
import org.keymaerax.core.{Box, ODESystem}
import org.keymaerax.hydra._
import org.keymaerax.hydra.responses.tools.PegasusCandidatesResponse
import org.keymaerax.infrastruct.Augmentors.FormulaAugmentor
import org.keymaerax.tools.{MathematicaComputationAbortedException, MathematicaComputationTimedOutException}

import scala.collection.immutable.Nil

class PegasusCandidatesRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
    extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponse(): Response = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId) match {
      case None => new ErrorResponse("Unknown node " + nodeId)
      case Some(node) =>
        try {
          node.goal match {
            case Some(sequent) => sequent
                .succ
                .find({
                  case Box(_: ODESystem, _) => true
                  case _ => false
                }) match {
                case Some(Box(ode: ODESystem, post)) if post.isFOL =>
                  ToolProvider.invGenTool() match {
                    case Some(tool) =>
                      val invs = tool.invgen(ode, sequent.ante, post)
                      new PegasusCandidatesResponse(invs)
                    case None => new PegasusCandidatesResponse(Nil)
                  }
                case Some(Box(_, post)) if !post.isFOL =>
                  new ErrorResponse(
                    "Post-condition in FOL is needed to search for invariants; please perform further proof steps until the post-condition of the ODE is a formula in first-order logic."
                  )
                case None => new ErrorResponse(
                    "ODE system needed to search for invariant candidates, but succedent does not contain an ODE system or ODE system may not be at top level. Please perform additional proof steps until ODE system is at top level."
                  )
              }
            case None => new ErrorResponse("ODE system needed to search for invariant candidates, but goal is empty.")
          }
        } catch {
          case _: MathematicaComputationAbortedException => new ErrorResponse("ODE invariant search timeout.")
          case _: MathematicaComputationTimedOutException => new ErrorResponse("ODE invariant search timeout.")
        }
    }
  }
}
