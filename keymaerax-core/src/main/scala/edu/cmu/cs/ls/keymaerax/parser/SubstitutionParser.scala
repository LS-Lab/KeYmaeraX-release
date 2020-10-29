/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.{DotTerm, Expression, Formula, FormulaKind, Program, SubstitutionPair, Term, TermKind}
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaerax.infrastruct.{ExpressionTraversal, PosInExpr}

/** Parses substitutions. */
object SubstitutionParser {
  private lazy val EXPR_LIST_SPLITTER = """(?:\{[^{}]*})|(,)""".r

  /** Converts a string `what ~> repl` or `(what ~> repl)` into a substitution pair. Provide a `matcher` to perform
    * post-processing, e.g., unification between `what` and `repl`. */
  def parseSubstitutionPair(s: String, matcher: (Expression, Expression) => SubstitutionPair = SubstitutionPair): SubstitutionPair = {
    //@note workaround for unification messing up indices when 0-based
    def incrementer(increment: Int) = new ExpressionTraversalFunction() {
      override def preT(p: PosInExpr, e: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = e match {
        case DotTerm(s, Some(i)) => Right(DotTerm(s, Some(i+increment)))
        case _ => Left(None)
      }
    }
    def incrementDotIdxs(x: Expression, increment: Int): Expression = x match {
      case f: Formula => ExpressionTraversal.traverse(incrementer(increment), f).get
      case t: Term => ExpressionTraversal.traverse(incrementer(increment), t).get
      case p: Program => ExpressionTraversal.traverse(incrementer(increment), p).get
    }

    val exprs =
      if (s.startsWith("(") && s.endsWith(")")) s.stripPrefix("(").stripSuffix(")").split("~>")
      else s.split("~>")
    assert(exprs.size == 2, "Expected substitution pair of shape what ~> repl, but got " + s)
    val repl = Parser(exprs(1))
    val what =
      if (repl.kind == FormulaKind) Parser.parser.formulaParser(exprs(0))
      else if (repl.kind == TermKind) Parser.parser.termParser(exprs(0))
      else Parser.parser.programParser(exprs(0))
    val result = matcher(incrementDotIdxs(what, 1), incrementDotIdxs(repl, 1))
    result.copy(what = incrementDotIdxs(result.what, -1), repl = incrementDotIdxs(result.repl, -1))
  }

  /** Parses a list of substitution pairs `what~>repl, what2~>repl2, ..., whatn~>repln`, optionally enclosed in parentheses. */
  def parseSubstitutionPairs(s: String): List[SubstitutionPair] = {
    val commaMatches = EXPR_LIST_SPLITTER.findAllMatchIn(s).filter(_.group(1) != null)
    val indices = (-1 +: commaMatches.map(_.start).toList :+ s.length).sliding(2).toList
    val exprStrings = indices.map({ case i :: j :: Nil => s.substring(i+1,j) })
    val hasOuterParens = exprStrings.headOption.exists(_.trim.startsWith("(")) && exprStrings.lastOption.exists(_.trim.endsWith(")"))
    val trimmed =
      if (hasOuterParens) {
        exprStrings.zipWithIndex.map({ case (s, i) =>
          if (i == 0) s.trim.stripPrefix("(")
          else if (i == exprStrings.length - 1) s.trim.stripSuffix(")")
          else s.trim
        })
      } else exprStrings.map(_.trim)
    trimmed.map(parseSubstitutionPair(_))
  }
}
