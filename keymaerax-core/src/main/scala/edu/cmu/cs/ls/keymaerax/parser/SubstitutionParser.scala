/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.{
  CoreException,
  DotTerm,
  Expression,
  Formula,
  FormulaKind,
  Program,
  SubstitutionClashException,
  SubstitutionPair,
  Term,
  TermKind,
}
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaerax.infrastruct.{ExpressionTraversal, PosInExpr}

/** Parses substitutions. */
object SubstitutionParser {
  private lazy val EXPR_LIST_SPLITTER = """(?:\{[^{}]*})|(,)""".r

  /**
   * Converts a string `what ~> repl` or `(what ~> repl)` into a substitution pair. Provide a `matcher` to perform
   * post-processing, e.g., unification between `what` and `repl`.
   */
  def parseSubstitutionPair(
      s: String,
      matcher: (Expression, Expression) => SubstitutionPair = SubstitutionPair,
  ): SubstitutionPair = {
    val exprs =
      if (s.startsWith("(") && s.endsWith(")")) s.stripPrefix("(").stripSuffix(")").split("~>") else s.split("~>")
    assert(exprs.size == 2, "Expected substitution pair of shape what ~> repl, but got " + s)
    val repl =
      try { Parser(exprs(1)) }
      catch {
        case ex: ParseException =>
          val newLines = exprs(0).count(_ == '\n')
          val columns = exprs(0).length + "~>".length - (if (newLines > 0) exprs(0).lastIndexOf('\n') else 0)
          throw ex.copy(loc = Region(ex.loc.begin.line + newLines, ex.loc.begin.column + columns))
      }
    val what =
      try {
        if (repl.kind == FormulaKind) Parser.parser.formulaParser(exprs(0))
        else if (repl.kind == TermKind) Parser.parser.termParser(exprs(0))
        else Parser.parser.programParser(exprs(0))
      } catch {
        case ex: ParseException =>
          if (s.startsWith("(")) throw ex.copy(loc = Region(ex.loc.begin.line, ex.loc.begin.column + 1)) else throw ex
      }
    try { matcher(what, repl) }
    catch {
      case _: CoreException => throw ParseException(
          "Non-substitutable expression on left-hand side of ~>",
          Region(1, 1, 1, exprs(0).length),
          exprs(0),
          "substitutable expression (e.g., predicate, function, program constant)",
        )
    }
  }

  /**
   * Parses a list of substitution pairs `what~>repl, what2~>repl2, ..., whatn~>repln`, optionally enclosed in
   * parentheses.
   */
  def parseSubstitutionPairs(s: String): List[SubstitutionPair] = {
    val commaMatches = EXPR_LIST_SPLITTER.findAllMatchIn(s).filter(_.group(1) != null)
    val indices = (-1 +: commaMatches.map(_.start).toList :+ s.length).sliding(2).toList
    val exprStrings = indices.map({ case i :: j :: Nil => s.substring(i + 1, j) })
    val hasOuterParens = exprStrings.headOption.exists(_.trim.startsWith("(")) &&
      exprStrings.lastOption.exists(_.trim.endsWith(")"))
    val trimmed =
      if (hasOuterParens) {
        exprStrings
          .zipWithIndex
          .map({ case (s, i) =>
            if (i == 0) s.trim.stripPrefix("(")
            else if (i == exprStrings.length - 1) s.trim.stripSuffix(")")
            else s.trim
          })
      } else exprStrings.map(_.trim)
    trimmed
      .zipWithIndex
      .map({ case (s, i) =>
        try { parseSubstitutionPair(s) }
        catch {
          case ex: ParseException =>
            val trimmedLength = exprStrings(i).indexOf(s)
            throw ex.copy(loc = Region(ex.loc.begin.line, ex.loc.begin.column + indices(i).head + trimmedLength + 1))
        }
      })
  }
}
