/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import scala.collection.immutable.List

case class TacticInfo(tacticText: String, nodesByLocation: List[ProofStateInfo])