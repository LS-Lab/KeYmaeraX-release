/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core._

/**
 * Parser interface for KeYmaera X reading token streams instead of strings. Provides a parser to read token streams
 * with differential dynamic logic. A token parser is a function from token sequences to differential dynamic logic
 * [[edu.cmu.cs.ls.keymaerax.core.Expression expressions]].
 * {{{
 * TokenParser: TokenStream => Expression
 * }}}
 * @author
 *   Stefan Mitsch
 * @see
 *   [[Parser]]
 */
trait TokenParser {

  /** Lexer's token stream with first token at head. */
  type TokenStream = KeYmaeraXLexer.TokenStream

  /**
   * Parse the input tokens in the concrete syntax as a differential dynamic logic expression
   * @param input
   *   the token stream to parse as a dL formula, dL term, or dL program.
   * @throws ParseException
   *   if `input` is not a well-formed expression of differential dynamic logic or differential game logic.
   */
  def parse(input: TokenStream): Expression

  /** Parse the input tokens in the concrete syntax as a differential dynamic logic term */
  val termTokenParser: TokenStream => Term

  /** Parse the input tokens in the concrete syntax as a differential dynamic logic formula */
  val formulaTokenParser: TokenStream => Formula

  /** Parse the input tokens in the concrete syntax as a differential dynamic logic program */
  val programTokenParser: TokenStream => Program

  /** Parse the input tokens in the concrete syntax as a differential dynamic logic differential program */
  val differentialProgramTokenParser: TokenStream => DifferentialProgram
}
