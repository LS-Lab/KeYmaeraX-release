/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

case class TacticInfo(tacticText: String, nodesByLocation: List[ProofStateInfo])
