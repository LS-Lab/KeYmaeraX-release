/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.hydra.responses.proofs.ExpandTacticResponse
import edu.cmu.cs.ls.keymaerax.hydra.{
  AgendaItem,
  DBAbstraction,
  DbProofTree,
  ReadRequest,
  Response,
  UserProofRequest,
  VerboseTraceToTacticConverter,
}
import spray.json.DefaultJsonProtocol._
import spray.json._

import scala.collection.immutable.{::, List, Nil}

class StepwiseTraceRequest(db: DBAbstraction, userId: String, proofId: String)
    extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponse(): Response = {
    val tree = DbProofTree(db, proofId)
    tree.load()
    val innerSteps = tree.nodes
    val agendaItems: List[AgendaItem] = tree
      .openGoals
      .map(n => AgendaItem(n.id.toString, AgendaItem.nameOf(n), proofId))
    // @todo fill in parent step for empty ""
    val marginLeft :: marginRight :: Nil = db
      .getConfiguration(userId)
      .config
      .getOrElse("renderMargins", "[40,80]")
      .parseJson
      .convertTo[Array[Int]]
      .toList
    ExpandTacticResponse(
      proofId.toInt,
      Nil,
      Nil,
      "",
      tree.tacticString(new VerboseTraceToTacticConverter(tree.info.defs(db)))._1,
      innerSteps,
      agendaItems,
      marginLeft,
      marginRight,
    )
  }
}
