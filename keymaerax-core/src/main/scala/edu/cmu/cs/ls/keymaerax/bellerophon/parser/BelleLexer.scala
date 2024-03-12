/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import edu.cmu.cs.ls.keymaerax.Logging
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser.BelleToken
import edu.cmu.cs.ls.keymaerax.parser.{COLON => _, COMMA => _, EOF => _, IDENT => _, _}
import org.apache.commons.lang3.StringUtils

import scala.annotation.tailrec
import scala.collection.immutable.{List, StringOps}
import scala.collection.mutable.ListBuffer
import scala.util.matching.Regex

/**
 * A lexer for the Bellerophon tactics language.
 *
 * @author
 *   Nathan Fulton
 */
object BelleLexer extends (String => List[BelleToken]) with Logging {
  type TokenStream = List[BelleToken]

  private val whitespace = """^(\s+)""".r
  // @note Assuming all newlines are just \n is OK because we normalize newlines prior to lexing.
  private val newline = """(?s)(^\n)""".r
  private val comment = """(?s)(^/\*[\s\S]*?\*/)""".r

  def apply(s: String): List[BelleToken] = {
    // Avoids importing a thing with lots of potential name clashes.
    val correctedInput = edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXLexer.normalizeNewlines(s)
    // @todo not sure if this position is Ok. This is what's used in the KeYmaera X lexer.
    val startingLocation = SuffixRegion(1, 1)

    logger.debug("LEX: " + correctedInput)
    lex(s, startingLocation)
  }

  /**
   * @param input
   *   The input
   * @param inputLocation
   *   The location of this input. If this is a recursive call, then inputLocation might not be (0,0).
   */
  private def lex(input: String, inputLocation: Location): TokenStream = {
    var remaining = input
    var location = inputLocation
    val tokens = ListBuffer.empty[BelleToken]
    while (remaining.trim.nonEmpty) {
      findNextToken(remaining, location) match {
        case Some((nextInput, token, nextLoc)) =>
          tokens += token
          remaining = nextInput
          location = nextLoc
        case None =>
          // note: This case can happen if the input is e.g. only a comment or only whitespace.
          remaining = ""
      }
    }
    tokens += BelleToken(EOF, location)
    tokens.toList
  }

  /**
   * Helper method for findNextToken
   *
   * @param cols
   *   Number of columns to move cursor.
   * @param terminal
   *   terminal to generate a token for.
   * @return
   *   Return value of findNextToken
   */
  private def consumeColumns(s: String, cols: Int, terminal: BelleTerminal, loc: Location) = {
    assert(cols > 0, "Cannot move cursor less than 1 columns.")
    Some((s.substring(cols), BelleToken(terminal, spanningRegion(loc, cols - 1)), suffixOf(loc, cols)))
  }

  /** Helper method for findNextToken */
  private def consumeTerminalLength(s: String, terminal: BelleTerminal, location: Location) =
    consumeColumns(s, terminal.img.length, terminal, location)

  private val lexers
      : Seq[(Regex, (String, Location, String) => Either[(String, Location), Option[(String, BelleToken, Location)]])] =
    Seq(
      // comments, newlines, and white-space. These are all copied from the KeYmaera X lexer.
      // update location if we encounter whitespace/comments.
      comment ->
        ((s: String, loc: Location, theComment: String) => {
          val comment = s.substring(0, theComment.length)
          val lastLineCol = (comment: StringOps).linesIterator.toList.last.length // column of last line.
          val lineCount = (comment: StringOps).linesIterator.length
          Left((
            s.substring(theComment.length),
            loc match {
              case UnknownLocation => UnknownLocation
              case Region(sl, _, el, ec) => Region(sl + lineCount - 1, lastLineCol, el, ec)
              case SuffixRegion(sl, sc) => SuffixRegion(sl + lineCount - 1, sc + theComment.length)
            },
          ))
        }),
      newline ->
        ((s: String, loc: Location, _: String) =>
          Left(
            s.tail,
            loc match {
              case UnknownLocation => UnknownLocation
              case Region(sl, _, el, ec) => Region(sl + 1, 1, el, ec)
              case SuffixRegion(sl, _) => SuffixRegion(sl + 1, 1)
            },
          )
        ),
      whitespace ->
        ((s: String, loc: Location, spaces: String) =>
          Left(
            s.substring(spaces.length),
            loc match {
              case UnknownLocation => UnknownLocation
              case Region(sl, sc, el, ec) => Region(sl, sc + spaces.length, el, ec)
              case SuffixRegion(sl, sc) => SuffixRegion(sl, sc + spaces.length)
            },
          )
        ),
      // stuff that could be confused as an identifier.
      ON_ALL.startPattern -> ((s: String, loc: Location, _: String) => Right(consumeTerminalLength(s, ON_ALL, loc))),
      US_MATCH.startPattern ->
        ((s: String, loc: Location, _: String) => Right(consumeTerminalLength(s, US_MATCH, loc))),
      PARTIAL.startPattern -> ((s: String, loc: Location, _: String) => Right(consumeTerminalLength(s, PARTIAL, loc))),
      LET.startPattern -> ((s: String, loc: Location, _: String) => Right(consumeTerminalLength(s, LET, loc))),
      IN.startPattern -> ((s: String, loc: Location, _: String) => Right(consumeTerminalLength(s, IN, loc))),
      TACTIC.startPattern -> ((s: String, loc: Location, _: String) => Right(consumeTerminalLength(s, TACTIC, loc))),
      AS.startPattern -> ((s: String, loc: Location, _: String) => Right(consumeTerminalLength(s, AS, loc))),
      USING.startPattern -> ((s: String, loc: Location, _: String) => Right(consumeTerminalLength(s, USING, loc))),
      // built-in tactics.
      IDENT.startPattern ->
        ((s: String, loc: Location, name: String) => Right(consumeTerminalLength(s, IDENT(name), loc))),
      N_TIMES.startPattern ->
        ((s: String, loc: Location, n: String) =>
          Right(consumeTerminalLength(s, N_TIMES(Integer.parseInt(n.tail)), loc))
        ),
      // Combinators
      SEQ_COMBINATOR.startPattern ->
        ((s: String, loc: Location, _: String) => Right(consumeTerminalLength(s, SEQ_COMBINATOR, loc))),
      DEPRECATED_SEQ_COMBINATOR.startPattern ->
        ((s: String, loc: Location, _: String) => Right(consumeTerminalLength(s, DEPRECATED_SEQ_COMBINATOR, loc))),
      EITHER_COMBINATOR.startPattern ->
        ((s: String, loc: Location, _: String) => Right(consumeTerminalLength(s, EITHER_COMBINATOR, loc))),
      KLEENE_STAR.startPattern ->
        ((s: String, loc: Location, _: String) => Right(consumeTerminalLength(s, KLEENE_STAR, loc))),
      SATURATE.startPattern ->
        ((s: String, loc: Location, _: String) => Right(consumeTerminalLength(s, SATURATE, loc))),
      BRANCH_COMBINATOR.startPattern ->
        ((s: String, loc: Location, _: String) => Right(consumeTerminalLength(s, BRANCH_COMBINATOR, loc))),
      OPTIONAL.startPattern ->
        ((s: String, loc: Location, _: String) => Right(consumeTerminalLength(s, OPTIONAL, loc))),
      // positions
      ABSOLUTE_POSITION.startPattern ->
        ((s: String, loc: Location, pos: String) => Right(consumeTerminalLength(s, ABSOLUTE_POSITION(pos), loc))),
      LAST_SUCCEDENT.startPattern ->
        ((s: String, loc: Location, pos: String) => Right(consumeTerminalLength(s, LAST_SUCCEDENT(pos), loc))),
      LAST_ANTECEDENT.startPattern ->
        ((s: String, loc: Location, pos: String) => Right(consumeTerminalLength(s, LAST_ANTECEDENT(pos), loc))),
      SEARCH_SUCCEDENT.startPattern ->
        ((s: String, loc: Location, pos: String) => Right(consumeTerminalLength(s, SEARCH_SUCCEDENT(pos), loc))),
      SEARCH_ANTECEDENT.startPattern ->
        ((s: String, loc: Location, pos: String) => Right(consumeTerminalLength(s, SEARCH_ANTECEDENT(pos), loc))),
      SEARCH_EVERYWHERE.startPattern ->
        ((s: String, loc: Location, pos: String) => Right(consumeTerminalLength(s, SEARCH_EVERYWHERE(pos), loc))),
      EXACT_MATCH.startPattern ->
        ((s: String, loc: Location, _: String) => Right(consumeTerminalLength(s, EXACT_MATCH, loc))),
      UNIFIABLE_MATCH.startPattern ->
        ((s: String, loc: Location, _: String) => Right(consumeTerminalLength(s, UNIFIABLE_MATCH, loc))),
      // delimited expressions
      BELLE_EXPRESSION.startPattern ->
        ((s: String, loc: Location, expr: String) =>
          Right(try {
            // Constructing an EXPRESSION results in an attempt to parse expressionString, which might
            // result in a parse error that should be passed back to the user.
            if (expr.startsWith("{`")) {
              // deprecated syntax
              var opening = expr.sliding(2).count(_ == "{`")
              var closing = expr.sliding(2).count(_ == "`}")
              val expression: StringBuilder = new StringBuilder(expr)
              while (opening - closing > 0) {
                val remainder = s.substring(expression.length)
                val matchingClosingIdx = StringUtils.ordinalIndexOf(remainder, "`}", opening - closing)
                val suffix = remainder.substring(0, matchingClosingIdx + 2)
                opening += suffix.sliding(2).count(_ == "{`")
                closing += suffix.sliding(2).count(_ == "`}")
                expression.append(suffix)
              }
              consumeTerminalLength(s, BELLE_EXPRESSION(expression.toString, "{`" -> "`}"), loc)
            } else if (expr.startsWith("\"")) {
              // new syntax (does not support nesting since opening delimiter indistinguishable from closing delimiter)
              if (expr.endsWith("\\\"")) {
                var endQuoteIdx = s.indexOf("\"", expr.length)
                while (endQuoteIdx > 0 && s.charAt(endQuoteIdx - 1) == '\\') {
                  endQuoteIdx = s.indexOf("\"", endQuoteIdx + 1)
                }
                if (endQuoteIdx >= 0)
                  consumeTerminalLength(s, BELLE_EXPRESSION(s.substring(0, endQuoteIdx + 1), "\"" -> "\""), loc)
                else throw LexException("Missing end delimiter \" in expression " + expr, loc)
              } else consumeTerminalLength(s, BELLE_EXPRESSION(expr, "\"" -> "\""), loc)
            } else throw LexException(s"Unknown starting delimiter in expression $expr", loc)
          } catch { case _: Throwable => throw LexException(s"Could not parse expression: $expr", loc) })
        ),
      // misc.
      OPEN_PAREN.startPattern ->
        ((s: String, loc: Location, _: String) => Right(consumeTerminalLength(s, OPEN_PAREN, loc))),
      CLOSE_PAREN.startPattern ->
        ((s: String, loc: Location, _: String) => Right(consumeTerminalLength(s, CLOSE_PAREN, loc))),
      COMMA.startPattern -> ((s: String, loc: Location, _: String) => Right(consumeTerminalLength(s, COMMA, loc))),
      COLON.startPattern -> ((s: String, loc: Location, _: String) => Right(consumeTerminalLength(s, COLON, loc))),
      RIGHT_ARROW.startPattern ->
        ((s: String, loc: Location, _: String) => Right(consumeTerminalLength(s, RIGHT_ARROW, loc))),
    )

  @tailrec
  private def findNextToken(input: String, loc: Location): Option[(String, BelleToken, Location)] = {
    if (input.isEmpty) { None }
    else {
      val lexPrefix = lexers
        .view
        .map({ case (r, lexer) => r.findPrefixOf(input).map(lexer(input, loc, _)) })
        .find(_.isDefined)
        .flatten
      lexPrefix match {
        case Some(Left(lexed)) => findNextToken(lexed._1, lexed._2)
        case Some(Right(lexed)) => lexed
        case None => throw LexException(
            s"${loc.begin} Lexer does not recognize input at $loc in `\n$input\n` beginning with character `${input(0)}`=${input(0).getNumericValue}",
            loc,
          ).inInput(input)
      }
    }
  }

  /**
   * Returns the region containing everything between the starting position of the current location location and the
   * indicated offset of from the starting positiong of the current location, inclusive.
   *
   * @param location
   *   Current location
   * @param endColOffset
   *   Column offset of the region
   * @return
   *   The region spanning from the start of ``location" to the offset from the start of ``location".
   */
  private def spanningRegion(location: Location, endColOffset: Int) = location match {
    case UnknownLocation => UnknownLocation
    case Region(sl, sc, _, _) => Region(sl, sc, sl, sc + endColOffset)
    case SuffixRegion(sl, sc) => Region(sl, sc, sl, sc + endColOffset)
  }

  /**
   * @param location
   *   Current location
   * @param colOffset
   *   Number of columns to chop off from the starting position of location.
   * @return
   *   A region containing all of location except the indicated columns in the initial row. I.e., the colOffset-suffix
   *   of location.
   */
  private def suffixOf(location: Location, colOffset: Int): Location = location match {
    case UnknownLocation => UnknownLocation
    case Region(sl, sc, el, ec) => Region(sl, sc + colOffset, el, ec)
    case SuffixRegion(sl, sc) => SuffixRegion(sl, sc + colOffset)
  }
}
