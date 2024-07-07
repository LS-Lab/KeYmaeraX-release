/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

import org.keymaerax.bellerophon.IOListeners.CollectProgressListener
import org.keymaerax.bellerophon.{BelleExpr, SpoonFeedingInterpreter}
import org.keymaerax.hydra.responses.proofs.TaskStatusResponse
import org.keymaerax.hydra.{
  BellerophonTacticExecutor,
  DBAbstraction,
  DbProofTree,
  ReadRequest,
  Response,
  UserProofRequest,
  VerboseTraceToTacticConverter,
}

class TaskStatusRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, taskId: String)
    extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponse(): Response = {
    val executor = BellerophonTacticExecutor.defaultExecutor
    val (isDone, currentStep: Option[(BelleExpr, Long)]) = executor.synchronized {
      executor.getTask(taskId) match {
        case Some(task) =>
          val progressList = task.interpreter match {
            case SpoonFeedingInterpreter(_, _, _, _, _, interpreterFactory, _, _, _, _) =>
              // @note the inner interpreters have CollectProgressListeners attached
              interpreterFactory(List.empty)
                .listeners
                .flatMap({
                  case l: CollectProgressListener =>
                    l.getCurrentTactic.map(f => (f._1, System.currentTimeMillis() - f._2))
                  case _ => None
                })
                .headOption
            case _ => None
          }
          (executor.isDone(taskId), progressList)
        case _ => (!executor.contains(taskId) || executor.isDone(taskId), None)
      }
    }
    val tree = DbProofTree(db, proofId)
    val (tacticProgress, _) = tree.tacticString(new VerboseTraceToTacticConverter(tree.info.defs(db)))
    TaskStatusResponse(
      proofId,
      nodeId,
      taskId,
      if (isDone) "done" else "running",
      currentStep,
      tree.nodes,
      tacticProgress,
    )
  }
}
