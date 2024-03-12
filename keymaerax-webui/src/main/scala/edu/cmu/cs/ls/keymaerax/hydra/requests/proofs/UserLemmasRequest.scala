/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.hydra.responses.proofs.UserLemmasResponse
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, ModelPOJO, ReadRequest, Response, UserRequest}
import edu.cmu.cs.ls.keymaerax.lemma.{Lemma, LemmaDBFactory}

import java.io.File
import scala.collection.immutable.{List, Nil}

class UserLemmasRequest(db: DBAbstraction, userId: String) extends UserRequest(userId, _ => true) with ReadRequest {
  def resultingResponses(): List[Response] = {
    def getLemma(model: Option[ModelPOJO]): Option[(String, Lemma)] = model
      .flatMap(m => LemmaDBFactory.lemmaDB.get("user" + File.separator + m.name).map(m.name -> _))
    val proofs = db
      .getProofsForUser(userId)
      .filterNot(_._1.temporary)
      .filter(_._1.closed)
      .groupBy(_._1.modelId)
      .map(_._2.head)
      .map(proof => (proof._1, getLemma(proof._1.modelId.map(db.getModel))))
      .toList
    new UserLemmasResponse(proofs) :: Nil
  }
}
