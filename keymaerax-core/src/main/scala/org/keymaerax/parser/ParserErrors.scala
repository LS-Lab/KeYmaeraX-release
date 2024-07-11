/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.parser

import org.keymaerax.Configuration
import org.keymaerax.core.Expression
import org.keymaerax.core.ProverException
import org.keymaerax.parser.KeYmaeraXLexer.TokenStream
import org.keymaerax.parser.KeYmaeraXParser.ParseState

import scala.collection.immutable.StringOps

import scala.collection.immutable.StringOps

/**
 * Indicates a parse error at the given location, with the context information state.
 * @author
 *   Andre Platzer
 * @see
 *   [[ProverException.getContext]]
 */
case class ParseException(
    msg: String,
    loc: Location,
    found: String /*Token*/,
    expect: String /**/,
    after: String /*ParseState*/,
    state: String /*ParseState*/,
    cause: Throwable = null,
    hint: String = "",
) extends ProverException(
      s"${loc.begin} $msg\nFound:    $found at $loc\nExpected: $expect" + (if (hint == "") "" else "\nHint: " + hint),
      cause,
    ) {

  /**
   * Add the input context information to this exception, returning the resulting exception to be thrown.
   * @param input
   *   textual description of the input in which this prover exception occurred.
   * @param tokenStream
   *   optionally the tokenStream lexed from the input.
   * @see
   *   [[ProverException.getContext]]
   */
  def inInput(input: String, tokenStream: Option[TokenStream] = None): ParseException = {
    // @todo take loc into account to project input to loc
    val lineInfo =
      if (input == "") "<empty>"
      else loc match {
        case UnknownLocation => "<unknown>"
        case _ =>
          assert(loc.line > 0 && loc.column > 0, "positive location")
          val lines = (input: StringOps).linesIterator.toList
          if (loc.line > lines.size) "<past EOF> at line " + loc.line
          else {
            // assert(!lines.isEmpty, "nonempty number of lines:\n" + input)
            val rem = lines.drop(loc.line - 1)
            val count =
              if (loc.end != UnknownLocation && loc.line == loc.end.line) Math.max(1, loc.end.column - loc.column + 1)
              else 1
            // assert(!rem.isEmpty, "nonempty number of lines after drop:\n" + input)
            if (rem.nonEmpty) rem.head + "\n" + (" " * (loc.column - 1)) + ("^" * count) + "\n"
            else "<past EOF> unexpectedly at line " + loc.line
          }
      }
    inContext(
      s"$loc\n$lineInfo\ninput:  \n$input" +
        (if (Configuration(Configuration.Keys.DEBUG) == "true") "\ntokens: " + tokenStream.getOrElse("<unknown>")
         else "")
    ).asInstanceOf[ParseException]
  }

  /** Get more details on the error message in addition to [[getContext]]. */
  def getDetails: String = "After:   " + after + "\nin " + state

  override def toString: String = super.getMessage + getContext +
    (if (Configuration(Configuration.Keys.DEBUG) == "true") "\n" + getDetails else "")
}

object ParseException {
//  def apply(msg: String, loc: Location, found: Token, expect: String/**/, after: ParseState, state: ParseState,
//            cause: Throwable = null, hint: String = ""): ParseException =
//    new ParseException(msg, loc, found=found + "", expect=expect, after=after + "", state=state + "", cause, hint)

  def apply(msg: String, state: ParseState /*, cause: Throwable = null*/ ): ParseException =
    new ParseException(msg, state.location, state.la.description, "", state.topString, state.toString /*, cause*/ )

  def apply(msg: String, state: ParseState, expect: List[Expected] /*, cause: Throwable = null*/ ): ParseException =
    new ParseException(
      msg,
      state.location,
      state.la.description,
      expect.mkString("\n      or: "),
      state.topString,
      state.toString, /*, cause*/
    )

  def apply(msg: String, state: ParseState, found: Token, expect: String): ParseException = new ParseException(
    msg,
    found.loc,
    found = found.description,
    expect = expect,
    after = state.topString,
    state = state.toString,
  )

  def apply(msg: String, state: ParseState, found: String, expect: String): ParseException = new ParseException(
    msg,
    state.location,
    found = found,
    expect = expect,
    after = state.topString,
    state = state.toString,
  )

  def apply(msg: String, loc: Location, found: String, expect: String): ParseException =
    new ParseException(msg, loc, found = found, expect = expect, after = "<unknown>", state = "<unknown>")

  def apply(msg: String, loc: Location, found: String, expect: String, after: String): ParseException =
    new ParseException(msg, loc, found = found, expect = expect, after = after, state = "<unknown>")

  def apply(msg: String, loc: Location, found: String, expect: String, after: String, hint: String): ParseException =
    new ParseException(msg, loc, found = found, expect = expect, after = after, state = "<unknown>", hint = hint)

  def apply(msg: String, state: ParseState, expect: String): ParseException = new ParseException(
    msg,
    state.location,
    found = state.la.description,
    expect = expect,
    after = state.topString,
    state = state.toString,
  )

  def apply(msg: String, after: Expression): ParseException = new ParseException(
    msg,
    UnknownLocation,
    "<unknown>",
    "<unknown>",
    after = KeYmaeraXParser.printer.stringify(after),
    "",
  )

  /** Avoid throwing this unlocated errors */
  @deprecated("Avoid throwing ParseException without location information")
  def apply(msg: String): ParseException = new ParseException(msg, UnknownLocation, "<unknown>", "<unknown>", "", "")

  def apply(msg: String, loc: Location): ParseException = new ParseException(msg, loc, "<unknown>", "<unknown>", "", "")

  def apply(msg: String, loc: Location, cause: Throwable): ParseException =
    new ParseException(msg, loc, "<unknown>", "<unknown>", "", "", cause)

  def apply(msg: String, cause: Throwable): ParseException =
    new ParseException(msg, UnknownLocation, "<unknown>", "<unknown>", "", "", cause)

  /** Imbalanced parentheses parse errors */
  def imbalancedError(msg: String, unmatched: Token, state: ParseState): ParseException =
    imbalancedError(msg, unmatched, expect = "", state = state)

  /**
   * Imbalanced parentheses parse errors: opening `unmatched` expects closing `expect` at the latest at location of
   * current parse state (location is unmatched)
   */
  def imbalancedError(
      msg: String,
      unmatched: Token,
      expect: String,
      state: ParseState,
      hint: String = "",
  ): ParseException =
    if (state.la.tok == EOF) new ParseException(
      msg,
      unmatched.loc,
      found = unmatched.description,
      expect = expect,
      after = state.topString,
      state = state.toString,
      null,
      hint = hint,
    )
    else new ParseException(
      msg + "\nunmatched: " + unmatched + " at " + unmatched.loc + "--" + state.location,
      unmatched.loc -- state.location,
      found = state.la.toString,
      expect = expect,
      after = state.topString,
      state.toString,
      hint = hint, /*, cause*/
    )

  /**
   * Imbalanced parentheses parse errors needed here: opening `unmatched` expects closing `expect` exactly at the
   * location of current parse state (location is state.location)
   */
  def imbalancedErrorHere(
      msg: String,
      unmatched: Token,
      expect: String,
      state: ParseState,
      hint: String = "",
  ): ParseException = new ParseException(
    msg + "\nunmatched: " + unmatched.description + " at " + unmatched.loc + "--" + state.location,
    if (false) unmatched.loc -- state.location else state.location,
    found = state.la.toString,
    expect = expect,
    after = state.topString,
    state.toString,
    null,
    hint = hint,
  )

  /** Type parse errors */
  private def typeException(
      msg: String,
      loc: Location,
      found: String,
      expect: String,
      hint: String = "",
      cause: Throwable = null,
  ) = new ParseException("type analysis: " + msg, loc, found, expect, "", "", cause, hint = hint)

  /** Type parse error with mismatch in found type illtyped and expected type */
  def typeError(
      msg: String,
      illtyped: Expression,
      expectedType: String,
      loc: Location,
      hint: String = "",
  ): ParseException = typeException(
    msg,
    loc,
    s"$illtyped ${illtyped.getClass.getSimpleName} of sort ${illtyped.sort}",
    expectedType,
    hint = hint,
  )

  def typeDeclGuessError(
      msg: String,
      declaredType: String,
      expected: String,
      loc: Location,
      hint: String = "",
  ): ParseException = typeException(msg, loc, declaredType, expected, hint = hint)

  def typeDeclError(
      msg: String,
      declaredType: String,
      expectedType: String,
      loc: Location,
      hint: String = "",
  ): ParseException = typeException(msg, loc, declaredType, expectedType, hint = hint)

  def duplicateSymbolError(n: String, i: Option[Int], loc: Location, other: Location): ParseException = ParseException(
    "Duplicate symbol '" + (n + i.map("_" + _).getOrElse("")) + "': already defined at " + other,
    loc,
    n + i.map("_" + _).getOrElse(""),
    "<unique name>",
  )
}

object LexException {
  def apply(msg: String, loc: Location, found: String = "<unknown>"): ParseException =
    new ParseException("Lexer " + msg, loc, found, "<unknown>", "", "")
}

//@todo something like case class LexException(msg: String, loc: Location) extends ParseException
