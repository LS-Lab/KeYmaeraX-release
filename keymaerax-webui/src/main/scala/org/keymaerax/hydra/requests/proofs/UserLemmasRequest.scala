/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

import org.keymaerax.hydra.responses.proofs.UserLemmasResponse
import org.keymaerax.hydra.{DBAbstraction, ModelPOJO, ReadRequest, Response, UserRequest}
import org.keymaerax.lemma.{Lemma, LemmaDBFactory}

import java.io.File

class UserLemmasRequest(db: DBAbstraction, userId: String) extends UserRequest(userId, _ => true) with ReadRequest {
  def resultingResponse(): Response = {
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
    new UserLemmasResponse(proofs)
  }
}
