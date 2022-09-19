/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.bellerophon.TacticDiff
import edu.cmu.cs.ls.keymaerax.hydra.responses.models.ParseErrorResponse
import edu.cmu.cs.ls.keymaerax.hydra.responses.proofs.TacticDiffResponse
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, ProofSession, ReadRequest, Request, Response}
import edu.cmu.cs.ls.keymaerax.parser.{ArchiveParser, ParseException}

import scala.collection.immutable.{List, Nil}

class TacticDiffRequest(db: DBAbstraction, proofId: String, oldTactic: String, newTactic: String) extends Request with ReadRequest {
  override def resultingResponses(): List[Response] = {
    val proofSession = session(proofId).asInstanceOf[ProofSession]
    val oldT = ArchiveParser.tacticParser(oldTactic, proofSession.defs)
    try {
      val newT = ArchiveParser.tacticParser(newTactic, proofSession.defs)
      val diff = TacticDiff.diff(oldT, newT)
      new TacticDiffResponse(diff) :: Nil
    } catch {
      case e: ParseException => ParseErrorResponse(e.msg, e.expect, e.found, e.getDetails, e.loc, e) :: Nil
    }
  }
}
