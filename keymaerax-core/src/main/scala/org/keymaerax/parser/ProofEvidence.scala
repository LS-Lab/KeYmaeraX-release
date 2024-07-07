/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.parser

import org.keymaerax.lemma.Evidence

case class ProofEvidence( /*proof : List[LoadedBranch]*/ ) extends Evidence {
  override def toString: String = "Proof. End."
}
