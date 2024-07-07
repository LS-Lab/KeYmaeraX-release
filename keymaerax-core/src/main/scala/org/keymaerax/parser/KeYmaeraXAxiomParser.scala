/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.parser

import org.keymaerax.Logging
import org.keymaerax.core.Formula
import org.keymaerax.parser.KeYmaeraXLexer.TokenStream

/**
 * Parse an axiom string to a list of named formulas that are to be used as axioms in a theory. Created by nfulton on
 * 6/11/15.
 * @author
 *   nfulton
 * @see
 *   [[DLAxiomParser]]
 */
object KeYmaeraXAxiomParser extends (String => List[(String, Formula)]) with Logging {

  /**
   * @todo
   *   sort checking.
   * @param input
   *   The contents of the axiom file.
   * @return
   *   A list of named axioms occurring in the file.
   */
  def apply(input: String): List[(String, Formula)] = {
    val tokens = KeYmaeraXLexer.inMode(input, AxiomFileMode)
    logger.debug("Tokens are: " + tokens)
    try { parseAxioms(tokens) }
    catch { case e: ParseException => throw e.inContext("<AxiomBase>" /*input*/ ) }
  }

  /**
   * Parse all axioms from input stream till EOF.
   * @param input
   *   Token string for the axiom file.
   * @return
   *   A list of axiom names and the associated formulas.
   */
  private def parseAxioms(input: TokenStream): List[(String, Formula)] = {
    require(input.last.tok == EOF, "token streams have to end in " + EOF)
    require(
      input.head.tok.equals(AXIOM_BEGIN),
      "expected axiom file contents to begin with Axiom block.\nFound: " + input.head,
    )
    val (nextAxiom, nextFormula, remainder) = parseNextAxiom(input)
    if (remainder.length == 1 && remainder.head.tok.equals(EOF)) List((nextAxiom, nextFormula))
    else (nextAxiom, nextFormula) +: parseAxioms(remainder)
  }

  /**
   * Parse one axiom till AXIOM_END from input stream
   * @param input
   * @return
   *   named axiom along with remaining token stream.
   */
  private def parseNextAxiom(input: TokenStream): (String, Formula, TokenStream) = {
    require(
      input.head.tok.equals(AXIOM_BEGIN),
      "expected axiom file contents to begin with Axiom block.\nFound: " + input.head,
    )
    require(
      input.tail.head.tok.isInstanceOf[DOUBLE_QUOTES_STRING],
      "expected axiom file content block to have a string as a name.\nFound: " + input.tail.head,
    )

    val name = input.tail.head match {
      case Token(DOUBLE_QUOTES_STRING(x), _) => x
      case _ => throw new AssertionError("Require should have failed.")
    }
    logger.debug("Axiom " + name)
    // Find the End. token and exclude it.
    val (axiomTokens, remainderTokens) =
      // 1st element is AXIOM_BEGIN, 2nd is AXIOM_NAME, 3rd is optional .
      input.tail.tail.span(_.tok != END_BLOCK) match {
        case (a, Token(END_BLOCK, _) :: Token(PERIOD, _) :: r) => (a, r)
        case e @ _ => throw ParseException("Lexicographically incomplete axiom: " + name, e._1.head.loc)
      }

    try {
      val axiom = KeYmaeraXParser.strictParser.formulaTokenParser(axiomTokens :+ Token(EOF, UnknownLocation))
      (name, axiom, remainderTokens)
    } catch {
      case e: ParseException =>
        throw e.inContext(input.toString, "Error occurred while parsing formula associated with axiom named " + name)
      case e: AssertionError => throw new AssertionError(
          e.getMessage + " Error occurred while parsing formula associated with axiom named " + name,
          e,
        )
    }
  }

}
