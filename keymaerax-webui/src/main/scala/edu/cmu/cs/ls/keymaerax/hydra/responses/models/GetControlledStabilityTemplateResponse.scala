/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.models

import edu.cmu.cs.ls.keymaerax.btactics.SwitchedSystems
import edu.cmu.cs.ls.keymaerax.btactics.SwitchedSystems.SwitchedSystem
import edu.cmu.cs.ls.keymaerax.core.{BaseVariable, Program, StaticSemantics, Variable}
import edu.cmu.cs.ls.keymaerax.hydra.Response
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettierPrinter
import spray.json.{JsNull, JsObject, JsString, JsValue}

class GetControlledStabilityTemplateResponse(code: String, switched: SwitchedSystem, specKind: List[String])
    extends Response {
  private val prg = switched.asProgram
  private val printer = new KeYmaeraXPrettierPrinter(80)
  private val fmls = specKind.map({
    case s @ "stability" => s ->
        printer(SwitchedSystems.stabilitySpec(switched))
          .linesWithSeparators
          .zipWithIndex
          .map({ case (l, i) => if (i == 0) l else "  " + l })
          .mkString
    case s @ "attractivity" => s ->
        printer(SwitchedSystems.attractivitySpec(switched))
          .linesWithSeparators
          .zipWithIndex
          .map({ case (l, i) => if (i == 0) l else "  " + l })
          .mkString
    case s @ "custom" => s ->
        s"""true /* todo */ ->
           |  [ ${printer(prg)
            .linesWithSeparators
            .zipWithIndex
            .map({ case (l, i) => if (i == 0) l else "    " + l })
            .mkString}
           |  ]false /* todo */
           |""".stripMargin
  })
  private val entries = fmls
    .map({ case (s, fml) =>
      s"""ArchiveEntry "New Entry: $s"
         |/*
         | * Generated from hybrid automaton
         | * ${code.linesWithSeparators.zipWithIndex.map({ case (l, i) => if (i == 0) l else " * " + l }).mkString}
         | */
         |
         |Definitions
         |  ${definitionsContent(prg)}
         |End.
         |
         |ProgramVariables
         |  ${programVariablesContent(prg)}
         |End.
         |
         |Problem
         |  $fml
         |End.
         |
         |End.
         |""".stripMargin
    })
    .mkString("\n\n")

  def getJson: JsValue = JsObject(
    "title" -> JsString(""),
    "description" -> JsString(""),
    "text" -> JsString(entries),
    "selectRange" -> JsObject(),
    "imageUrl" -> JsNull, // @todo automaton SVG?
  )

  private def definitionsContent(prg: Program): String = {
    val consts = StaticSemantics.symbols(prg) -- StaticSemantics.boundVars(prg).toSet
    val (m, c) = consts.partition(s => switched.modeNames.contains(s.prettyString))
    m.toList
      .sortBy(_.prettyString)
      .zipWithIndex
      .map({ case (v, i) => v.sort.toString + " " + v.prettyString + " = " + i + ";" })
      .mkString("\n  ") + c.map(v => v.sort.toString + " " + v.prettyString + ";").mkString("\n  ")
  }

  private def programVariablesContent(prg: Program): String = {
    StaticSemantics
      .boundVars(prg)
      .toSet[Variable]
      .filter(_.isInstanceOf[BaseVariable])
      .map(v => v.sort.toString + " " + v.prettyString + ";")
      .mkString("\n  ")
  }
}
