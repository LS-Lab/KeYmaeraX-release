/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BellePrettyPrinter
import edu.cmu.cs.ls.keymaerax.core._

/**
  * Prints a KeYmaera X archive.
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
  *   Lemma "Entry 2". ... End.
  * }}}
  *
  * Created by smitsch on 01/04/18.
  */
class KeYmaeraXArchivePrinter extends (KeYmaeraXArchiveParser.ParsedArchiveEntry => String) {
  private val ARCHIVE_ENTRY_BEGIN: String = "ArchiveEntry"
  private val LEMMA_BEGIN: String = "Lemma"
  private val THEOREM_BEGIN: String = "Theorem"
  private val TACTIC_BEGIN: String = "Tactic"
  private val EXERCISE_BEGIN: String = "Exercise"
  private val END_BLOCK: String = "End."

  /** Prints the `entry`. */
  def apply(entry: KeYmaeraXArchiveParser.ParsedArchiveEntry): String = {
    val head = entry.kind match {
      case "lemma" => LEMMA_BEGIN
      case "theorem" => THEOREM_BEGIN
      case "exercise" => EXERCISE_BEGIN
      case _ => ARCHIVE_ENTRY_BEGIN
    }

    def printName(name: String, idx: Option[Int]): String = name + (idx match {
      case Some(i) => "_" + i
      case None => ""
    })

    def printSort(domain: Sort): String = domain match {
      case Real => "R"
      case Bool => "B"
      case Unit => ""
      case Tuple(l, r) => printSort(l) + "," + printSort(r)
    }

    def printDef(codomain: Sort, interpretation: Option[Expression]): String = interpretation match {
      case Some(i) =>
        val op = codomain match {
          case Real => "="
          case Bool => "<->"
        }
        s"$op ( ${i.prettyString})"
      case None => ""
    }

    val symbols = StaticSemantics.symbols(entry.model)

    val printedDecls = symbols.map({
      case Function(name, idx, domain, sort, _) if !entry.defs.decls.contains((name, idx)) =>
        s"${printSort(sort)} ${printName(name, idx)}(${printSort(domain)})."
      case _ => "" // either printedDefs or printedVars
    }).filter(_.nonEmpty).mkString("\n")

    val printedDefs = entry.defs.decls.map({
      case((name, idx), (domain, codomain, interpretation, _)) =>
        s"$codomain ${printName(name, idx)}(${printSort(domain.getOrElse(Unit))}) ${printDef(codomain, interpretation)}."
      case _ => ""
    }).filter(_.nonEmpty).mkString("\n")

    val printedVars = symbols.map({
      case v: BaseVariable => printSort(v.sort) + " " + printName(v.name, v.index) + "."
      case _ => "" // see printDecls and printDefs above
    }).filter(_.nonEmpty).mkString("\n")

    val printedTactics = entry.tactics.map({
      case (tname, t) =>
        s"""$TACTIC_BEGIN "$tname".\n${BellePrettyPrinter(t)}\n$END_BLOCK"""
    }).mkString("\n\n")

    s"""$head "${entry.name}".
       |Definitions.
       |$printedDecls
       |$printedDefs
       |$END_BLOCK
       |
       |ProgramVariables.
       |$printedVars
       |$END_BLOCK
       |
       |Problem.
       |  ${entry.model.prettyString}
       |$END_BLOCK
       |
       |$printedTactics
       |$END_BLOCK""".stripMargin
  }


}
