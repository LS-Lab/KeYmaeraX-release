/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.proofs

import edu.cmu.cs.ls.keymaerax.hydra.{ProofPOJO, Response}
import edu.cmu.cs.ls.keymaerax.lemma.Lemma
import spray.json.{JsArray, JsNull, JsObject, JsString, JsValue}

class UserLemmasResponse(proofs: List[(ProofPOJO, Option[(String, Lemma)])]) extends Response {
  lazy val objects: List[JsObject] = proofs.map({ case (proof, lemma) =>
    JsObject(
      "id" -> JsString(proof.proofId.toString),
      "name" ->
        (lemma match {
          case Some((n, _)) => JsString(n)
          case None => JsNull
        }),
      "conclusion" ->
        (lemma match {
          case Some((_, l)) => JsString(l.fact.conclusion.prettyString)
          case None => JsNull
        }),
    )
  })

  override def getJson: JsValue = JsArray(objects: _*)
}
