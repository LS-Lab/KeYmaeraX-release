/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

import org.keymaerax.Logging
import org.keymaerax.bellerophon.{BelleExpr, BelleInterpreter, BelleProvable}
import org.keymaerax.core.{Formula, Provable}
import org.keymaerax.hydra.DBAbstraction
import org.keymaerax.parser.Declaration
import org.keymaerax.pt.ElidingProvable

import scala.collection.mutable

/**
 * Global server state for proof validation requests. For now, scheduling immediately dispatches a new thread where the
 * validation occurs. In the future, we may want to rate-limit validation requests. The easiest way to do that is to
 * create a thread pool with a max size.
 */
object ProofValidationRunner extends Logging {
  private val results: mutable.Map[String, (Formula, BelleExpr, Option[Boolean])] = mutable.Map()

  case class ValidationRequestDNE(taskId: String) extends Exception(s"The requested taskId $taskId does not exist.")

  /** Returns Option[Proved] which is None iff the task is still running, and True if formula didn't prove. */
  def status(taskId: String): Option[Boolean] = results.get(taskId) match {
    case Some((_, _, proved)) => proved
    case None => throw ValidationRequestDNE(taskId)
  }

  /** Schedules a proof validation request and returns the UUID. */
  def scheduleValidationRequest(db: DBAbstraction, model: Formula, proof: BelleExpr, defs: Declaration): String = {
    val taskId = java.util.UUID.randomUUID().toString
    results update (taskId, (model, proof, None))

    new Thread(new Runnable() {
      override def run(): Unit = {
        logger.trace(s"Received request to validate $taskId. Running in separate thread.")
        val provable = ElidingProvable(Provable.startProof(model), defs)

        try {
          BelleInterpreter(proof, BelleProvable.plain(provable)) match {
            case BelleProvable(p, _) if p.isProved => results update (taskId, (model, proof, Some(true)))
            case _ => results update (taskId, (model, proof, Some(false)))
          }
        } catch {
          // Catch everything and indicate a failed proof attempt.
          case e: Throwable => results update (taskId, (model, proof, Some(false)))
        }

        logger.trace(s"Done executing validation check for $taskId")
      }
    }).start()

    taskId
  }
}
