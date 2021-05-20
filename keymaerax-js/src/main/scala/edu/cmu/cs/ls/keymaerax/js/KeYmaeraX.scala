package edu.cmu.cs.ls.keymaerax.js

import edu.cmu.cs.ls.keymaerax.{Configuration, MapConfiguration}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.FormulaTools
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, PositionLocator}
import edu.cmu.cs.ls.keymaerax.parser.{ArchiveParser, Declaration, KeYmaeraXPrettyPrinter, ParseException, Parser, SubstitutionParser, KeYmaeraXArchiveParser}

import scala.util.Try
import scala.scalajs.js.{Array, Dictionary}
import scala.scalajs.js.JSConverters._
import scala.scalajs.js.annotation.JSExportTopLevel

object KeYmaeraX {
  Configuration.setConfiguration(MapConfiguration)
  PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
  ArchiveParser.setParser(KeYmaeraXArchiveParser)

  @JSExportTopLevel("parseArchive")
  def parseArchive(input: String): Array[Dictionary[Any]] = {
    try {
      ArchiveParser(input)
      List.empty.toJSArray
    } catch {
      case ex: ParseException => List(Dictionary(
        "line" -> ex.loc.begin.line,
        "column" -> ex.loc.begin.column,
        "endLine" -> ex.loc.end.line,
        "endColumn" -> ex.loc.end.column,
        "message" -> ex.msg,
        "found" -> ex.found,
        "expect" -> ex.expect,
        "hint" -> ex.hint
      )).toJSArray
    }
  }

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

  @JSExportTopLevel("parsesAsSubstitution")
  def parsesAsSubstitution(answer: String, solution: String): Dictionary[Any] = {
    Try(Parser(answer)).toOption match {
      case Some(Divide(BaseVariable(n, None, Real), BaseVariable(a, None, Real))) if a=="a" && n=="n" =>
        fillDictionary("Parsed OK", 1.0)
      case _ => parseCheck(answer, SubstitutionParser.parseSubstitutionPairs, (_: List[SubstitutionPair]) => "Parsed OK")
    }
  }

  private def parseCheck[T](answer: String, parser: String=>T, check: T=>String): Dictionary[Any] = {
    try {
      fillDictionary(check(parser(answer)), 1.0)
    } catch {
      case ex: ParseException =>
        val answerLines = answer.linesWithSeparators.toList
        val info = answerLines.patch(ex.loc.line-1, answerLines(ex.loc.line-1).patch(ex.loc.column-1, " ⚠ ", 0), 1).mkString("")
        fillDictionary("Parse error: " + info + "\n" + ex.getMessage, 0.0)
      case ex: Throwable => fillDictionary( "Parsing failed: " + ex.getMessage, 0.0)
    }
  }

  private def fillDictionary(feedback: String, ratio: Double): Dictionary[Any] = Dictionary(
    "is_error" -> false,
    "is_correct" -> false,
    "ratio" -> ratio,
    "feedback" -> feedback
  )
}
