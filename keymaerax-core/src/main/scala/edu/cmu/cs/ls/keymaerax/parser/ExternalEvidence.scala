package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.Evidence

case class ExternalEvidence(/*file:File*/) extends Evidence {
  override def toString: String = "External. End."
}
