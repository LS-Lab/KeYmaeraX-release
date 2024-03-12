/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.lemma.Evidence

case class ProofEvidence( /*proof : List[LoadedBranch]*/ ) extends Evidence {
  override def toString: String = "Proof. End."
}
