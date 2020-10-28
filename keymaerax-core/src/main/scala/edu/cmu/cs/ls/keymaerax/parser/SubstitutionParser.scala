/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.{DotTerm, Expression, Formula, FormulaKind, Program, SubstitutionPair, Term, TermKind}
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaerax.infrastruct.{ExpressionTraversal, PosInExpr, UnificationMatch}

/** Parses substitutions. */
object SubstitutionParser {
  /** Converts a string `what ~> repl` or `(what ~> repl)` into a substitution pair. */
  def parseSubstitutionPair(s: String): SubstitutionPair = {
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
    val result = UnificationMatch(incrementDotIdxs(what, 1), incrementDotIdxs(repl, 1)).usubst.subsDefsInput.head
    result.copy(what = incrementDotIdxs(result.what, -1), repl = incrementDotIdxs(result.repl, -1))
  }
}
