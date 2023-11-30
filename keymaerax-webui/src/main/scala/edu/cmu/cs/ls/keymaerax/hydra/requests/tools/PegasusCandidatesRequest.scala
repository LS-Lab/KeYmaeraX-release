/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.tools

import edu.cmu.cs.ls.keymaerax.btactics.ToolProvider
import edu.cmu.cs.ls.keymaerax.core.{Box, ODESystem}
import edu.cmu.cs.ls.keymaerax.hydra.responses.tools.PegasusCandidatesResponse
import edu.cmu.cs.ls.keymaerax.hydra._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.FormulaAugmentor
import edu.cmu.cs.ls.keymaerax.tools.{MathematicaComputationAbortedException, MathematicaComputationTimedOutException}

import scala.collection.immutable.{List, Nil}

class PegasusCandidatesRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId) match {
      case None => new ErrorResponse("Unknown node " + nodeId) :: Nil
      case Some(node) =>
        try {
          node.goal match {
            case Some(sequent) => sequent.succ.find({ case Box(_: ODESystem, _) => true case _ => false }) match {
              case Some(Box(ode: ODESystem, post)) if post.isFOL => ToolProvider.invGenTool() match {
                case Some(tool) =>
                  val invs = tool.invgen(ode, sequent.ante, post)
                  new PegasusCandidatesResponse(invs) :: Nil
                case None => new PegasusCandidatesResponse(Nil) :: Nil
              }
              case Some(Box(_, post)) if !post.isFOL => new ErrorResponse("Post-condition in FOL is needed to search for invariants; please perform further proof steps until the post-condition of the ODE is a formula in first-order logic.") :: Nil
              case None => new ErrorResponse("ODE system needed to search for invariant candidates, but succedent does not contain an ODE system or ODE system may not be at top level. Please perform additional proof steps until ODE system is at top level.") :: Nil
            }
            case None => new ErrorResponse("ODE system needed to search for invariant candidates, but goal is empty.") :: Nil
          }
        } catch {
          case _: MathematicaComputationAbortedException => new ErrorResponse("ODE invariant search timeout.") :: Nil
          case _: MathematicaComputationTimedOutException => new ErrorResponse("ODE invariant search timeout.") :: Nil
        }
    }
  }
}