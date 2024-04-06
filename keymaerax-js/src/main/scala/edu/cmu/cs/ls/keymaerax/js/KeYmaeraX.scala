package edu.cmu.cs.ls.keymaerax.js

import edu.cmu.cs.ls.keymaerax.{Configuration, JsMapConfiguration}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.FormulaTools
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, PositionLocator}
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.DLBelleParser
import edu.cmu.cs.ls.keymaerax.parser.{ArchiveParser, Declaration, KeYmaeraXPrettyPrinter, InterpretedSymbols,
  ParseException, Parser, SubstitutionParser, DLArchiveParser, MockBellePrettyPrinter, MockExpressionBuilder,
  SequentParser, ParsedArchiveEntry}

import scala.util.Try
import scala.scalajs.js.{Array, Dictionary}
import scala.scalajs.js.JSConverters._
import scala.scalajs.js.annotation.JSExportTopLevel

object KeYmaeraX {
  Configuration.setConfiguration(JsMapConfiguration)
  PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
  ArchiveParser.setParser(new DLArchiveParser(new DLBelleParser(MockBellePrettyPrinter, MockExpressionBuilder)))

  //region Parsing for ACE Editor

  /** Parses archives for the KeYmaera X web UI, return values compatible with ACE editor. */
  @JSExportTopLevel("parseArchive")
  def parseArchive(input: String): Array[Dictionary[Any]] = {
    try {
      val entries = ArchiveParser(input)
      // inspect archives and print warning if no program variables block/definitions but archive entry defs nonempty
      val noDefEntries = entries.filter(e => e.defs.decls.nonEmpty && !e.fileContent.contains("Definitions") && !e.fileContent.contains("ProgramVariables"))
      val noDefEntryWarnings = noDefEntries.map(e => {
        val fc = e.fileContent.linesIterator
        val eline = if (fc.hasNext) input.linesIterator.indexOf(fc.next) + 1 else 1
        Dictionary(
          "kind" -> "warning",
          "line" -> eline,
          "column" -> 1,
          "endLine" -> eline,
          "endColumn" -> 1,
          "message" -> "Entry does not specify functions and variables in Definitions/ProgramVariables blocks."
        )
      }).toJSArray

      noDefEntryWarnings
    } catch {
      case ex: ParseException =>
        // unknown locations have beginning/end=-1 (won't show), anchor them at the very top of the editor
        val line = Math.max(1, ex.loc.begin.line)
        val column = Math.max(1, ex.loc.begin.column)
        List(Dictionary(
          "kind" -> "error",
          "line" -> line,
          "column" -> column,
          "endLine" -> Math.max(line, ex.loc.end.line),
          "endColumn" -> Math.max(column, ex.loc.end.column),
          "message" -> ex.msg,
          "found" -> ex.found,
          "expect" -> ex.expect,
          "hint" -> ex.hint
        )).toJSArray
    }
  }

  @JSExportTopLevel("parseTactic")
  def parseTactic(input: String): Array[Dictionary[Any]] = {
    try {
      ArchiveParser.tacticParser(input)
      List.empty.toJSArray
    } catch {
      case ex: ParseException =>
        // unknown locations have beginning/end=-1 (won't show), anchor them at the very top of the editor
        val line = Math.max(1, ex.loc.begin.line)
        val column = Math.max(1, ex.loc.begin.column)
        List(Dictionary(
          "line" -> line,
          "column" -> column,
          "endLine" -> Math.max(line, ex.loc.end.line),
          "endColumn" -> Math.max(column, ex.loc.end.column),
          "message" -> ex.msg,
          "found" -> ex.found,
          "expect" -> ex.expect,
          "hint" -> ex.hint
        )).toJSArray
    }
  }

  //endregion

  //region Parsing for Diderot

  @JSExportTopLevel("parsesAsArchive")
  def parsesAsArchive(answer: String, solution: String): Dictionary[Any] =
    parseCheck(answer, ArchiveParser.parse(_, parseTactics=false), (_: List[ParsedArchiveEntry]) => "Parsed OK")

  @JSExportTopLevel("parsesAsExpression")
  def parsesAsExpression(answer: String, solution: String): Dictionary[Any] =
    parseCheck(answer, Parser, (_: Expression) => "Parsed OK")

  @JSExportTopLevel("parsesAsDLExpression")
  def parsesAsDLExpression(answer: String, solution: String): Dictionary[Any] =
    parseCheck(answer, Parser, (_: Expression) => "Parsed OK")

  @JSExportTopLevel("parsesAsDGLExpression")
  def parsesAsDGLExpression(answer: String, solution: String): Dictionary[Any] = parseCheck(answer, Parser, (_: Expression) match {
    case fml: Formula => if (FormulaTools.dualFree(fml)) "Parsed OK" else "Parsed OK, but not a DGL expression"
    case hp: Program => if (FormulaTools.dualFree(hp)) "Parsed OK" else "Parsed OK, but not a DGL expression"
    case _ => "Parsed OK"
  })

  @JSExportTopLevel("parsesAsTerm")
  def parsesAsTerm(answer: String, solution: String): Dictionary[Any] = parseCheck(answer, Parser, (_: Expression) match {
    case _: Term => "Parsed OK"
    case _ => "Parsed OK, but not a term"
  })

  @JSExportTopLevel("parsesAsFormula")
  def parsesAsFormula(answer: String, solution: String): Dictionary[Any] = parseCheck(answer, Parser, (_: Expression) match {
    case _: Formula => "Parsed OK"
    case _ => "Parsed OK, but not a formula"
  })

  @JSExportTopLevel("parsesAsDLFormula")
  def parsesAsDLFormula(answer: String, solution: String): Dictionary[Any] = parseCheck(answer, Parser, (_: Expression) match {
    case fml: Formula if FormulaTools.dualFree(fml) => "Parsed OK"
    case _ => "Parsed OK, but not a formula"
  })

  @JSExportTopLevel("parsesAsDGLFormula")
  def parsesAsDGLFormula(answer: String, solution: String): Dictionary[Any] = parsesAsFormula(answer, solution)

  @JSExportTopLevel("parsesAsFOLFormula")
  def parsesAsFOLFormula(answer: String, solution: String): Dictionary[Any] = parseCheck(answer, Parser, (_: Expression) match {
    case fml: Formula if fml.isFOL => "Parsed OK"
    case _ => "Parsed OK, but not a FOL formula"
  })

  @JSExportTopLevel("parsesAsQFFOLFormula")
  def parsesAsQFFOLFormula(answer: String, solution: String): Dictionary[Any] = parseCheck(answer, Parser, (_: Expression) match {
    case fml: Formula if fml.isFOL && StaticSemantics.boundVars(fml).isEmpty => "Parsed OK"
    case _ => "Parsed OK, but not a Quantifier-free FOL formula"
  })

  @JSExportTopLevel("parsesAsFormulaList")
  def parsesAsFormulaList(answer: String, solution: String): Dictionary[Any] =
    parseCheck(answer, SequentParser.parseFormulaList(_), (_: List[Formula]) => "Parsed OK")

  @JSExportTopLevel("parsesAsFOLFormulaList")
  def parsesAsFOLFormulaList(answer: String, solution: String): Dictionary[Any] =
    parseCheck(answer, SequentParser.parseFormulaList(_), (l: List[Formula]) =>
      if (l.forall(_.isFOL)) "Parsed OK"
      else "Parsed OK, but at least one formula is not FOL")

  @JSExportTopLevel("parsesAsHP")
  def parsesAsHP(answer: String, solution: String): Dictionary[Any] = parseCheck(answer, Parser, (_: Expression) match {
    case hp: Program if FormulaTools.literalDualFree(hp) => "Parsed OK"
    case _ => "Parsed OK, but not a hybrid program"
  })

  @JSExportTopLevel("parsesAsHG")
  def parsesAsHG(answer: String, solution: String): Dictionary[Any] = parseCheck(answer, Parser, (_: Expression) match {
    case _: Program => "Parsed OK"
    case _ => "Parsed OK, but not a hybrid game/program"
  })

  @JSExportTopLevel("parsesAsODE")
  def parsesAsODE(answer: String, solution: String): Dictionary[Any] =
    parseCheck(answer, (s: String) => Parser("{" + s + "}"), (_: Expression) match {
      case _: DifferentialProgram | _: ODESystem => "Parsed OK"
      case _ => "Parsed OK, but not an ODE"
    })

  @JSExportTopLevel("parsesAsSubstitution")
  def parsesAsSubstitution(answer: String, solution: String): Dictionary[Any] =
    parseCheck(answer, SubstitutionParser.parseSubstitutionPairs, (_: List[SubstitutionPair]) => "Parsed OK")

  @JSExportTopLevel("parsesAsSequent")
  def parsesAsSequent(answer: String, solution: String): Dictionary[Any] =
    parseCheck(answer, SequentParser.parseSequent, (_: Sequent) => "Parsed OK" )

  @JSExportTopLevel("parsesAsSequentList")
  def parsesAsSequentList(answer: String, solution: String): Dictionary[Any] =
    parseCheck(answer, _.split(";;").map(SequentParser.parseSequent(_)).toList, (_: List[Sequent]) => "Parsed OK")

  @JSExportTopLevel("parsesAsInteger")
  def parsesAsInteger(answer: String, solution: String): Dictionary[Any] =
    parseCheck(answer, _.toInt, (_: Int) => "Parsed OK")

  @JSExportTopLevel("parsesAsIntegerList")
  def parsesAsIntegerList(answer: String, solution: String): Dictionary[Any] =
    parseCheck(answer, _.split(",").map(_.toInt).toList, (_: List[Int]) => "Parsed OK")

  @JSExportTopLevel("parsesAsNumber")
  def parsesAsNumber(answer: String, solution: String): Dictionary[Any] = parseCheck(answer, Parser, (_: Expression) match {
    case _: Number => "Parsed OK"
    case _ => "Not a number"
  })

  private def parseCheck[T](answer: String, parser: String=>T, check: T=>String): Dictionary[Any] = {
    Try(Parser(answer)).toOption match {
      // allow n/a or na in any combination of lower/upper case
      case Some(BaseVariable(n, None, Real)) if n.equalsIgnoreCase("na") => fillDictionary("Parsed OK", 1.0)
      case Some(Divide(BaseVariable(n, None, Real), BaseVariable(a, None, Real))) if n.equalsIgnoreCase("n") && a.equalsIgnoreCase("a") =>
        fillDictionary("Parsed OK", 1.0)
      case _ => try {
        fillDictionary(check(parser(answer)), 1.0)
      } catch {
        case ex: ParseException => try {
          val answerLines = answer.linesWithSeparators.toList
          val info = answerLines.patch(ex.loc.line - 1, answerLines(ex.loc.line - 1).patch(ex.loc.column - 1, " ⚠ ", 0), 1).mkString("")
          fillDictionary("Parse error: " + info + "\n" + ex.getMessage, 0.0)
        } catch {
          case _: Throwable => fillDictionary("Parse error: " + ex.getMessage, 0.0)
        }
        case ex: Throwable => fillDictionary("Parsing failed: " + ex.getMessage, 0.0)
      }
    }
  }

  private def fillDictionary(feedback: String, ratio: Double): Dictionary[Any] = Dictionary(
    "is_error" -> false,
    "is_correct" -> false,
    "ratio" -> ratio,
    "feedback" -> feedback
  )

  //endregion
}
