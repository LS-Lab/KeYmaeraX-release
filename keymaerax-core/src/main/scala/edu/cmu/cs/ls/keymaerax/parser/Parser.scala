/**
 * Differential Dynamic Logic parser for concrete KeYmaera X notation.
 * @author aplatzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.{Expression, Term, Formula, Program}

/**
 * Parser interface for KeYmaera X.
 * @author aplatzer
 */
trait Parser extends (String => Expression) {

  def parseExpression(input: String) = apply(input)

  def parseTerm(input: String): Term = parseExpression(input) match {
    case t: Term => t
    case e@_ => throw new ParseException("Input does not parse as a term but as " + e.kind + "\nInput: " + input + "\nParsed: " + e)
  }

  def parseFormula(input: String): Formula = parseExpression(input) match {
    case f: Formula => f
    case e@_ => throw new ParseException("Input does not parse as a formula but as " + e.kind + "\nInput: " + input + "\nParsed: " + e)
  }

  def parseProgram(input: String): Program = parseExpression(input) match {
    case p: Program => p
    case e@_ => throw new ParseException("Input does not parse as a program but as " + e.kind + "\nInput: " + input + "\nParsed: " + e)
  }
}
