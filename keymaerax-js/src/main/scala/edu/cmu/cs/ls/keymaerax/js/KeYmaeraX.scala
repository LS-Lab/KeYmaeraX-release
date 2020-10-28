package edu.cmu.cs.ls.keymaerax.js

import edu.cmu.cs.ls.keymaerax.{Configuration, MapConfiguration}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.FormulaTools
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXPrettyPrinter, ParseException, Parser}
import scala.scalajs.js.Dictionary

import scala.scalajs.js.annotation.JSExportTopLevel

object KeYmaeraX {
  @JSExportTopLevel("parsesAsExpression")
  def parsesAsExpression(answer: String, solution: String): Dictionary[Any] = {
    parseCheck(answer, Parser, (_: Expression) => "Parsed OK")
  }

  @JSExportTopLevel("parsesAsDGLExpression")
  def parsesAsDGLExpression(answer: String, solution: String): Dictionary[Any] = {
    parseCheck(answer, Parser, (_: Expression) => "Parsed OK")
  }

  @JSExportTopLevel("parsesAsTerm")
  def parsesAsTerm(answer: String, solution: String): Dictionary[Any] = {
    parseCheck(answer, Parser, (expr: Expression) => expr match {
      case _: Term => "Parsed OK"
      case _ => "Parsed OK, but not a term"
    })
  }

  @JSExportTopLevel("parsesAsFormula")
  def parsesAsFormula(answer: String, solution: String): Dictionary[Any] = {
    parseCheck(answer, Parser, (expr: Expression) => expr match {
      case _: Formula => "Parsed OK"
      case _ => "Parsed OK, but not a formula"
    })
  }

  @JSExportTopLevel("parsesAsHP")
  def parsesAsHP(answer: String, solution: String): Dictionary[Any] = {
    parseCheck(answer, Parser, (expr: Expression) => expr match {
      case hp: Program if FormulaTools.dualFree(hp) => "Parsed OK"
      case _ => "Parsed OK, but not a hybrid program"
    })
  }

  @JSExportTopLevel("parsesAsHG")
  def parsesAsHG(answer: String, solution: String): Dictionary[Any] = {
    parseCheck(answer, Parser, (expr: Expression) => expr match {
      case hp: Program => "Parsed OK"
      case _ => "Parsed OK, but not a hybrid game/program"
    })
  }

  private def parseCheck[T](answer: String, parser: String=>T, check: T=>String): Dictionary[Any] = {
    Configuration.setConfiguration(MapConfiguration)
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
    try {
      Dictionary(
        "is_error" -> false,
        "is_correct" -> false,
        "ratio" -> 1.0,
        "feedback" -> check(parser(answer))
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
      case ex: Throwable =>
        Dictionary(
          "is_error" -> false,
          "is_correct" -> false,
          "ratio" -> 0.0,
          "feedback" -> ("Parsing failed: " + ex.getMessage)
        )
    }
  }
}
