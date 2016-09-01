package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.Evidence

case class ProofEvidence(/*proof : List[LoadedBranch]*/) extends Evidence {
  override def toString: String = "Proof. End."
}
