/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics.macros

/** Auto-exported DerivationInfo map. */
object DerivationInfo {
  // copy output of TODO here
  def ofCodeName(codeName:String): DerivationInfo = ???
}

/** Derivation info container. */
case class DerivationInfo(name: String, persistentInputs: List[ArgInfo], numPositionArgs: Int) {

}