/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * Check whether underlying strategy of Kaisar proof is a strategy for a given game
  * @author Brandon Bohrer
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.ProofCheckException
import edu.cmu.cs.ls.keymaerax.core._

object RefinementChecker {
  private def refines(s: Statement, game: Program): Boolean = {
    // @TODO
    false
  }

  // @TODO: Do nice exceptions for each possible case
  def apply(s: Statement, game: Program): Unit = {
    if (!refines(s, game)) {
      throw ProofCheckException(s"Proof did not refine game $game")
    }
  }
}
