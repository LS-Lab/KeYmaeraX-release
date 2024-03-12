/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.{Formula, Sequent}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXLexer.TokenStream

import scala.collection.immutable
import scala.collection.mutable.ListBuffer

/**
 * Parses provable strings in the format stored by [[edu.cmu.cs.ls.keymaerax.core.Provable.toStorageString()]].
 * @author
 *   Stefan Mitsch
 */
object KeYmaeraXStoredProvableParser extends (String => immutable.List[Sequent]) {

  /**
   * Returns the sequents parsed from `input`.
   * @param input
   *   The contents of the stored provable
   * @return
   *   A list of sequents.
   * @throws ParseException
   *   When input cannot be parsed.
   */
  def apply(input: String): immutable.List[Sequent] =
    try { parseProvable(KeYmaeraXLexer.inMode(input, StoredProvableMode)) }
    catch {
      case e: ParseException => throw e.inContext("input:  " + input)
      case e: MatchError => throw ParseException("Unexpected input sequence " + e.getMessage(), e).inInput(input)
      case e: IllegalArgumentException => throw ParseException("Illegal argument", e).inInput(input)
    }

  /**
   * Parses the token stream `input` into a list of sequents.
   * @param input
   *   Token stream.
   * @return
   *   A list of sequents.
   */
  private def parseProvable(input: TokenStream): immutable.List[Sequent] = {
    require(
      input.takeRight(2).map(_.tok) == QED :: EOF :: Nil,
      "Stored provable token streams have to end in " + QED + EOF,
    )
    require(input.count(_.tok == QED) == 1, "Expected a single \\qed token")
    split(input.dropRight(2), (t: Token) => t.tok != FROM).map(parseSequent)
  } ensures (r => r.size == 1 + input.count(_.tok == FROM))

  /** Parses a sequent. */
  private def parseSequent(input: TokenStream): Sequent = {
    val (anteTokens, Token(TURNSTILE, _) :: succTokens) = input.span(_.tok != TURNSTILE)
    Sequent(parseFormulas(anteTokens), parseFormulas(succTokens))
  } ensures
    (r => {
      val (anteTokens, Token(TURNSTILE, _) :: succTokens) = input.splitAt(input.indexWhere(_.tok == TURNSTILE))
      r.ante.size == (if (anteTokens.isEmpty) 0 else 1) + anteTokens.count(_.tok == FORMULA_SEPARATOR) &&
      r.succ.size == (if (succTokens.isEmpty) 0 else 1) + succTokens.count(_.tok == FORMULA_SEPARATOR)
    })

  /** Parses a list of formulas. */
  private def parseFormulas(input: TokenStream): immutable.IndexedSeq[Formula] = {
    val formulaTokens = split(input, (t: Token) => t.tok != FORMULA_SEPARATOR)
    formulaTokens.map(ts => KeYmaeraXParser.formulaTokenParser(ts :+ Token(EOF))).toIndexedSeq
  } ensures (r => r.size == (if (input.isEmpty) 0 else 1) + input.count(_.tok == FORMULA_SEPARATOR))

  /**
   * Splits `tokens` into sub-streams at boundaries satisfying `pred`. The boundary token is removed from the result.
   */
  private def split(tokens: TokenStream, pred: Token => Boolean): List[TokenStream] = {
    var rest = tokens
    val result: ListBuffer[TokenStream] = ListBuffer.empty
    while (rest.nonEmpty) {
      val (prefix, r) = rest.span(pred)
      result.append(prefix)
      rest = if (r.isEmpty) Nil else r.tail
    }
    result.toList
  } /* ensures (r => r.size == (if (elements.isEmpty) 0 else 1) + elements.count(pred)) */

}
