/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.{Expression, SubstitutionPair}
import edu.cmu.cs.ls.keymaerax.infrastruct.UnificationMatch

object UnificationSubstitutionParser {

  def parseSubstitutionPair(s: String): SubstitutionPair = {
    SubstitutionParser.parseSubstitutionPair(
      s,
      (what: Expression, repl: Expression) => UnificationMatch(what, repl).usubst.subsDefsInput.head,
    )
  }

  def parseSubstitutionPairs(s: String): List[SubstitutionPair] = SubstitutionParser.parseSubstitutionPairs(s)
}
