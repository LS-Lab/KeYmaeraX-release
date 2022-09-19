/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.bellerophon.IOListeners.CollectProgressListener
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, BelleThrowable, BelleValue, SpoonFeedingInterpreter}
import edu.cmu.cs.ls.keymaerax.hydra.responses.proofs.TaskStatusResponse
import edu.cmu.cs.ls.keymaerax.hydra.{BellerophonTacticExecutor, DBAbstraction, ReadRequest, Response, UserProofRequest}

import scala.collection.immutable.{List, Nil, Seq}

class TaskStatusRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, taskId: String)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val executor = BellerophonTacticExecutor.defaultExecutor
    type Progress = (Option[(BelleExpr, Long)], Seq[(BelleExpr, Either[BelleValue, BelleThrowable])])
    val (isDone, progress: Option[Progress]) = executor.synchronized {
      executor.getTask(taskId) match {
        case Some(task) =>
          val progressList = task.interpreter match {
            case SpoonFeedingInterpreter(_, _, _, _, _, interpreterFactory, _, _, _, _) =>
              //@note the inner interpreters have CollectProgressListeners attached
              interpreterFactory(Nil).listeners.flatMap({
                case l@CollectProgressListener(p) => Some(
                  l.getCurrentTactic.map(f => (f._1, System.currentTimeMillis() - f._2)),
                  scala.collection.immutable.Seq(p:_*))
                case _ => None
              }).headOption
            case _ => None
          }
          (executor.isDone(taskId), progressList)
        case _ => (!executor.contains(taskId) || executor.isDone(taskId), None)
      }
    }
    TaskStatusResponse(proofId, nodeId, taskId, if (isDone) "done" else "running", progress) :: Nil
  }
}