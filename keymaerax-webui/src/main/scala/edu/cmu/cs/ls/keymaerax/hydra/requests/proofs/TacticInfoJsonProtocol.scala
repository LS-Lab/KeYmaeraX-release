/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.parser.Region
import spray.json.{DefaultJsonProtocol, RootJsonFormat}

object TacticInfoJsonProtocol extends DefaultJsonProtocol {
  implicit val regionFormat: RootJsonFormat[Region] = jsonFormat4(Region.apply)
  implicit val proofStateInfoFormat: RootJsonFormat[ProofStateInfo] = jsonFormat2(ProofStateInfo)
  implicit val tacticInfoFormat: RootJsonFormat[TacticInfo] = jsonFormat2(TacticInfo)
}
