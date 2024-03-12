/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.parser

object BuiltinSymbols {

  /** Builtin/shipped reserved and interpreted symbols. */
  lazy val all = InterpretedSymbols.preshipped ++ TacticReservedSymbols.asDecl
}
