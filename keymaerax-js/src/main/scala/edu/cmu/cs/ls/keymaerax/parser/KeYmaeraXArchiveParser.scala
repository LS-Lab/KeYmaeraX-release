/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.parser.ParsedArchiveEntry
import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr

/** Empty placeholder, ignores tactics. */
object KeYmaeraXArchiveParser extends KeYmaeraXArchiveParserBase {

  override def parseFromFile(file: String): List[ParsedArchiveEntry] = Nil
  override protected def convert(t: Tactic, defs: Declaration): (String, String, BelleExpr) = ("", "", new BelleExpr())

}
