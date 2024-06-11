/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.core.Formula
import edu.cmu.cs.ls.keymaerax.hydra.responses.proofs.ValidateProofResponse
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, ReadRequest, Request, Response}
import edu.cmu.cs.ls.keymaerax.parser.Declaration

/**
 * Returns a UUID whose status can be queried at a later time ({complete: true/false[, proves: true/false]}.
 *
 * @see
 *   CheckValidationRequest - calling this with the returned UUID should give the status of proof checking.
 */
class ValidateProofRequest(db: DBAbstraction, model: Formula, proof: BelleExpr, defs: Declaration)
    extends Request with ReadRequest {
  override def resultingResponse(): Response =
    // Spawn an async validation request and return the resulting UUID.
    new ValidateProofResponse(ProofValidationRunner.scheduleValidationRequest(db, model, proof, defs), None)
}
