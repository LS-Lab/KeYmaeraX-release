package edu.cmu.cs.ls.keymaerax.js

import edu.cmu.cs.ls.keymaerax.{Configuration, MapConfiguration}
import edu.cmu.cs.ls.keymaerax.core.PrettyPrinter
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXPrettyPrinter, ParseException, Parser}
import scala.scalajs.js.Dictionary

import scala.scalajs.js.annotation.JSExportTopLevel

object KeYmaeraX {
  @JSExportTopLevel("parsesAsExpression")
  def parsesAsExpression(answer: String, solution: String): Dictionary[Any] = {
    Configuration.setConfiguration(MapConfiguration)
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
    try {
      Parser(answer)
      Dictionary(
        "is_error" -> false,
        "is_correct" -> false,
        "ratio" -> 1.0,
        "feedback" -> "Parsed OK"
      )
    } catch {
      case ex: ParseException =>
        val answerLines = answer.linesWithSeparators.toList
        val info = answerLines.patch(ex.loc.line-1, answerLines(ex.loc.line-1).patch(ex.loc.column-1, " ⚠ ", 0), 1).mkString("")
        Dictionary(
          "is_error" -> false,
          "is_correct" -> false,
          "ratio" -> 0.0,
          "feedback" -> ("Parse error: " + info + " (" + ex.getMessage + ")")
        )
    }
  }
}
