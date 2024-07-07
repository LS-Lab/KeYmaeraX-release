/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

import org.keymaerax.parser.Region
import spray.json.{DefaultJsonProtocol, RootJsonFormat}

object TacticInfoJsonProtocol extends DefaultJsonProtocol {
  implicit val regionFormat: RootJsonFormat[Region] = jsonFormat4(Region.apply)
  implicit val proofStateInfoFormat: RootJsonFormat[ProofStateInfo] = jsonFormat2(ProofStateInfo)
  implicit val tacticInfoFormat: RootJsonFormat[TacticInfo] = jsonFormat2(TacticInfo)
}
