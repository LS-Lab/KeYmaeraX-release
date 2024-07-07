/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.parser

import org.keymaerax.core.{Expression, SubstitutionPair}
import org.keymaerax.infrastruct.UnificationMatch

object UnificationSubstitutionParser {

  def parseSubstitutionPair(s: String): SubstitutionPair = {
    SubstitutionParser.parseSubstitutionPair(
      s,
      (what: Expression, repl: Expression) => UnificationMatch(what, repl).usubst.subsDefsInput.head,
    )
  }

  def parseSubstitutionPairs(s: String): List[SubstitutionPair] = SubstitutionParser.parseSubstitutionPairs(s)
}
