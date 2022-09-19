/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleProvable, BelleSubProof, BelleThrowable}
import edu.cmu.cs.ls.keymaerax.hydra.responses.proofs.{TacticErrorResponse, TaskResultResponse}
import edu.cmu.cs.ls.keymaerax.hydra.{BellerophonTacticExecutor, DBAbstraction, DbProofTree, ErrorResponse, ProofSession, ProofTree, ProofTreeNode, ReadRequest, RequestHelper, Response, UserProofRequest}

import scala.collection.immutable.{::, List, Nil}
import spray.json._
import spray.json.DefaultJsonProtocol._

class TaskResultRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, taskId: String)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
  /* It's very important not to report a branch as closed when it isn't. Other wise the user will carry on in blissful
  * ignorance thinking the hardest part of their proof is over when it's not. This is actually a bit difficult to get
  * right, so check the actual provables to make sure we're closing a branch. */
  private def noBogusClosing(tree: ProofTree, pn: ProofTreeNode): Boolean =
    pn.children.size == pn.localProvable.subgoals.size &&
      pn.children.zip(pn.localProvable.subgoals).forall({case (c, sg) => c.localProvable.conclusion == sg})

  override protected def doResultingResponses(): List[Response] = {
    val executor = BellerophonTacticExecutor.defaultExecutor
    val marginLeft::marginRight::Nil = db.getConfiguration(userId).config.getOrElse("renderMargins", "[40,80]").parseJson.convertTo[Array[Int]].toList
    executor.synchronized {
      val response = executor.wait(taskId) match {
        case Some(Left(_: BelleProvable)) =>
          val tree = DbProofTree(db, proofId)
          tree.locate(nodeId) match {
            case None => new ErrorResponse("Unknown node " + nodeId)
            case Some(node) =>
              //@todo construct provable (expensive!)
              //assert(noBogusClosing(tree, node), "Server thinks a goal has been closed when it clearly has not")
              val proofSession = session(proofId).asInstanceOf[ProofSession]
              session(proofId) = RequestHelper.updateProofSessionDefinitions(proofSession, node)
              TaskResultResponse(proofId, node, marginLeft, marginRight, progress=true)
          }
        //          val positionLocator = if (parentNode.children.isEmpty) None else RequestHelper.stepPosition(db, parentNode.children.head)
        //          assert(noBogusClosing(finalTree, parentNode), "Server thinks a goal has been closed when it clearly has not")
        //          new TaskResultResponse(proofId, parentNode, positionLocator, progress = true)
        case Some(Left(BelleSubProof(subId))) =>
          //@todo untested with new tree data structure
          //@HACK for stepping into Let steps
          val tree = DbProofTree(db, subId.toString)
          val node = tree.root//findNode(nodeId).get
          //val positionLocator = if (parentNode.subgoals.isEmpty) None else RequestHelper.stepPosition(db, parentNode.children.head)
          assert(noBogusClosing(tree, node), "Server thinks a goal has been closed when it clearly has not")
          TaskResultResponse(subId.toString, node, marginLeft, marginRight, progress = true)
        case Some(Right(error: BelleThrowable)) => new TacticErrorResponse(error.getMessage, "", error)
        case None => new ErrorResponse("Tactic cancelled, proof state may not reflect result of full tactic")
      }
      //@note may have been cancelled in the meantime
      executor.tryRemove(taskId)
      response :: Nil
    }
  }
}