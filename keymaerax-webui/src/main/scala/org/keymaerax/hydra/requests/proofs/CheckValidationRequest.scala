/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

import org.keymaerax.hydra.responses.proofs.ValidateProofResponse
import org.keymaerax.hydra.{DBAbstraction, ErrorResponse, ReadRequest, Request, Response}

/**
 * An idempotent request for the status of a validation request; i.e., validation requests aren't removed until the
 * server is resst.
 */
class CheckValidationRequest(db: DBAbstraction, taskId: String) extends Request with ReadRequest {
  override def resultingResponse(): Response =
    try { new ValidateProofResponse(taskId, ProofValidationRunner.status(taskId)) }
    catch { case e: ProofValidationRunner.ValidationRequestDNE => new ErrorResponse(e.getMessage, e) }
}
