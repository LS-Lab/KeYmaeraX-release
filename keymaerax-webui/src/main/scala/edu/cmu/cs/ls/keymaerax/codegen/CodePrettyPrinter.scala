/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.codegen

import edu.cmu.cs.ls.keymaerax.core.{NamedSymbol, Sort}

/** Pretty-prints expressions to code. Returns a tuple of (declarations used in code, code). */
trait CodePrettyPrinter extends (CExpression => (String, String)) {

  /** Prints a named symbol as an identifier. */
  def nameIdentifier(s: NamedSymbol): String

  /** Prints a sort. */
  def printSort(s: Sort): String
}
