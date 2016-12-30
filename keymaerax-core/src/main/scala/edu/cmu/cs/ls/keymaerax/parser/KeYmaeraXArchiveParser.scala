/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.core.Expression

/**
  * Splits a KeYmaera X archive into its parts and forwards to respective problem/tactic parsers. An archive contains
  * at least one entry combining a model in the .kyx format and a (partial) proof tactic in .kyt format.
  *
  * Format example:
  * {{{
  *   ArchiveEntry "Entry 1".
  *     Functions. ... End.
  *     ProgramVariables. ... End.
  *     Problem. ... End.
  *     Tactic "Proof 1". ... End.
  *     Tactic "Proof 2". ... End.
  *   End.
  *   ArchiveEntry "Entry 2". ... End.
  * }}}
  *
  * Created by smitsch on 12/29/16.
  */
object KeYmaeraXArchiveParser {
  private val ARCHIVE_ENTRY_BEGIN: String = "ArchiveEntryBegin."
  private val ARCHIVE_ENTRY_END: String = "ArchiveEntryEnd."

  /** Two groups: entry name, model+optional tactic */
  private val NAME_REGEX = "^\"([^\"]*)\"\\.(?s)(.*)".r

  /** The entry name, kyx file content (model), parsed model, and parsed name+tactic. */
  type ArchiveEntry = (String, String, Expression, List[(String, BelleExpr)])

  /** Parses the archive content into archive entries  */
  def parse(archiveContent: String): List[ArchiveEntry] = {
    val entries = archiveContent.trim().split("ArchiveEntry").flatMap({s =>
      NAME_REGEX.findAllMatchIn(s.trim().stripSuffix("End.")).map(
        { m =>
          val modelName = m.group(1)
          val (model: String, tactics: List[(String, BelleExpr)]) = m.group(2).split("Tactic").toList match {
            case modelText :: ts => (modelText.trim(), ts.flatMap(tacticText => {
              NAME_REGEX.findAllMatchIn(tacticText.trim().stripSuffix("End.")).map({
                tm => (tm.group(1), BelleParser(tm.group(2)))
              })
            }))
          }
          (modelName, model, tactics)
        })
      })
    entries.map({case (name, modelText, tactic) =>
      (name, modelText, KeYmaeraXProblemParser(modelText), tactic)
    }).toList
  }
}
