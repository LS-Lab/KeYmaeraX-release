/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.infrastruct

import edu.cmu.cs.ls.keymaerax.core.{Provable, USubst}

import scala.annotation.tailrec

/** Non-critical infrastructure to transform and substitute provables. */
object ProvableHelper {

  /** Applies substitutions `s` to provable `p` exhaustively. */
  @tailrec
  def exhaustiveSubst(p: Provable, s: USubst): Provable = {
    val substituted = p(s)
    if (substituted != p) exhaustiveSubst(substituted, s)
    else substituted
  }

}
