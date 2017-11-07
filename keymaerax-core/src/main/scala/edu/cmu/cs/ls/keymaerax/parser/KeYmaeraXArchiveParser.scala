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
  private val ARCHIVE_ENTRY_BEGIN: String = "ArchiveEntry"
  private val LEMMA_BEGIN: String = "Lemma"
  private val THEOREM_BEGIN: String = "Theorem"
  private val TACTIC_BEGIN: String = "Tactic"
  private val EXERCISE_BEGIN: String = "Exercise"
  private val DEFINITIONS_BEGIN: String = "SharedDefinitions."
  private val END_BLOCK: String = "End."

  /** Two groups: entry name, model+optional tactic */
  private val NAME_REGEX = "^\"([^\"]*)\"\\.(?s)(.*)".r

  /** The entry name, kyx file content (model), parsed model, and parsed name+tactic. */
  case class ParsedArchiveEntry(name: String, kind: String, fileContent: String, model: Expression, tactics: List[(String, BelleExpr)])
  /** The entry name, kyx file content, entry kind (theorem, lemma, etc.), and list of name+tactic text. */
  type ArchiveEntry = (String, String, String, List[(String, String)])

  /** Reads all (file.kyx) or a specific archive entry (file.kyx#entry) from said `file`. */
  def apply(file: String): List[ParsedArchiveEntry] = {
    file.split('#').toList match {
      case fileName :: Nil =>
        val input = scala.io.Source.fromFile(fileName).mkString
        KeYmaeraXArchiveParser.parse(input)
      case fileName :: entryName :: Nil =>
        val input = scala.io.Source.fromFile(fileName).mkString
        KeYmaeraXArchiveParser.getEntry(entryName, input).
          getOrElse(throw new IllegalArgumentException("Unknown archive entry " + entryName)) :: Nil
    }
  }

  /** Parses the archive content into archive entries with parsed model and tactics. */
  def parse(archiveContentBOM: String): List[ParsedArchiveEntry] = {
    val archiveContents: List[ArchiveEntry] = read(archiveContentBOM)
    archiveContents.map(parseEntry)
  }

  /** Reads a specific entry from the archive. */
  def getEntry(entryName: String, archiveContentBOM: String): Option[ParsedArchiveEntry] = {
    val archiveContents: List[ArchiveEntry] = read(archiveContentBOM)
    archiveContents.find(_._1 == entryName).map(parseEntry)
  }

  /** Parses an entry (model and tactic). */
  private def parseEntry(entry: ArchiveEntry): ParsedArchiveEntry = {
    val (name, modelText, kind, tactics) = entry
    val (defs, formula) = KeYmaeraXProblemParser.parseProblem(modelText)
    val parsedTactics = tactics.map({
      case (tacticName, tacticText) => (tacticName, BelleParser.parseWithInvGen(tacticText, None, defs)) })
    ParsedArchiveEntry(name, kind, modelText, formula, parsedTactics)
  }

  /** Reads the archive content into string-only archive entries. */
  def read(archiveContentBOM: String): List[ArchiveEntry] = {
    val archiveContent: String = ParserHelper.removeBOM(archiveContentBOM)
    // match the word boundary before ArchiveEntry etc. followed by "Name".
    val regex = s"(?s)\\b(?=$DEFINITIONS_BEGIN)|\\b(?=($ARCHIVE_ENTRY_BEGIN|$LEMMA_BEGIN|$THEOREM_BEGIN|$EXERCISE_BEGIN)" +
      "(?=(\\W*)\"([^\"]*)\"\\.(.*)$))"

    var globalDefs: Option[String] = None

    archiveContent.trim().split(regex).filter(_.nonEmpty).flatMap({s =>
      val (entry, kind) =
        if (s.startsWith(DEFINITIONS_BEGIN)) (s.stripPrefix(DEFINITIONS_BEGIN), "definitions")
        else if (s.startsWith(ARCHIVE_ENTRY_BEGIN)) (s.stripPrefix(ARCHIVE_ENTRY_BEGIN), "theorem")
        else if (s.startsWith(THEOREM_BEGIN)) (s.stripPrefix(THEOREM_BEGIN), "theorem")
        else if (s.startsWith(LEMMA_BEGIN)) (s.stripPrefix(LEMMA_BEGIN), "lemma")
        else if (s.startsWith(EXERCISE_BEGIN)) (s.stripPrefix(EXERCISE_BEGIN), "exercise")
        else throw new IllegalArgumentException(s"Expected either $DEFINITIONS_BEGIN, $ARCHIVE_ENTRY_BEGIN, $LEMMA_BEGIN, $THEOREM_BEGIN, but got unknown entry kind $s")

        kind match {
          case "definitions" =>
            globalDefs = Some(entry.trim().stripSuffix(END_BLOCK).trim())
            Nil
          case _ =>
            NAME_REGEX.findAllMatchIn(entry.trim().stripSuffix(END_BLOCK)).map({ m =>
              val modelName = m.group(1)
              val (model: String, tactics: List[(String, String)]) = m.group(2).split(TACTIC_BEGIN).toList match {
                case modelText :: ts => (modelText.trim(), ts.flatMap(tacticText => {
                  NAME_REGEX.findAllMatchIn(tacticText.trim().stripSuffix(END_BLOCK)).map({
                    tm => (tm.group(1), tm.group(2))
                  })
                }))
              }
              //@note copies shared definitions into each Functions/Definitions block.
              val augmentedModel = globalDefs match {
                case Some(d) if model.contains("Functions.") || model.contains("Definitions.") =>
                  "(Functions\\.)|(Definitions\\.)".r.replaceFirstIn(model,
                    "Definitions.\n" + d.replaceAllLiterally("\\", "\\\\") + "\n")
                case Some(d) if !(model.contains("Functions.") || model.contains("Definitions.")) =>
                  "Definitions.\n" + d + "\nEnd.\n" + model
                case None => model
              }
              (modelName, augmentedModel, kind, tactics)
            })
        }
    }).toList
  }
}
