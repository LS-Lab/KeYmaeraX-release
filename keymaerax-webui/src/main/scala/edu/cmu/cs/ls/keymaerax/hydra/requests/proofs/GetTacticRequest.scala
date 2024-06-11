/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BellePrettyPrinter
import edu.cmu.cs.ls.keymaerax.btactics.Idioms
import edu.cmu.cs.ls.keymaerax.hydra.responses.proofs.GetTacticResponse
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, ReadRequest, Response, UserProofRequest}
import edu.cmu.cs.ls.keymaerax.parser.Location
import spray.json.JsonParser.ParsingException
import spray.json._

import scala.collection.immutable.Map

class GetTacticRequest(db: DBAbstraction, userId: String, proofIdStr: String)
    extends UserProofRequest(db, userId, proofIdStr) with ReadRequest {
  override def doResultingResponse(): Response = {
    val proofInfo = db.getProofInfo(proofIdStr)
    val (tactic: String, proofStateInfo: Map[Location, String]) = proofInfo.tactic match {
      case Some(t) =>
        import TacticInfoJsonProtocol._
        try {
          val ti = t.parseJson.convertTo[TacticInfo]
          (ti.tacticText, ti.nodesByLocation.map(i => (i.loc, i.node)).toMap.asInstanceOf[Map[Location, String]])
        } catch {
          case _: ParsingException => (t, Map.empty) // @note backwards compatibility with database tactics not in JSON
        }
      case None => (BellePrettyPrinter(Idioms.nil), Map.empty)
    }
    GetTacticResponse(tactic, proofStateInfo)
  }
}
