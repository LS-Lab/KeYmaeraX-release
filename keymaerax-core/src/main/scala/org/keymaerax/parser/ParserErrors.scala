/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.parser

import org.keymaerax.Configuration
import org.keymaerax.core.{Expression, ProverException}
import org.keymaerax.parser.KeYmaeraXLexer.TokenStream

import scala.collection.immutable.StringOps
import scala.util.Try

/**
 * Indicates a parse error at the given location, with the context information state.
 * @author Andre Platzer
 * @see [[ProverException.getContext]]
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

  private lazy val debug = Try(Configuration(Configuration.Keys.DEBUG) == "true").getOrElse(false)

  /**
   * Add the input context information to this exception, returning the resulting exception to be thrown.
   * @param input textual description of the input in which this prover exception occurred.
   * @param tokenStream optionally the tokenStream lexed from the input.
   * @see [[ProverException.getContext]]
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
      s"$loc\n$lineInfo\ninput:  \n$input" + (if (debug) "\ntokens: " + tokenStream.getOrElse("<unknown>") else "")
    ).asInstanceOf[ParseException]
  }

  /** Get more details on the error message in addition to [[getContext]]. */
  def getDetails: String = "After:   " + after + "\nin " + state

  override def toString: String = super.getMessage + getContext + (if (debug) "\n" + getDetails else "")
}

object ParseException {
  def apply(msg: String, loc: Location, found: String, expect: String): ParseException =
    new ParseException(msg, loc, found = found, expect = expect, after = "<unknown>", state = "<unknown>")

  def apply(msg: String, loc: Location, found: String, expect: String, after: String): ParseException =
    new ParseException(msg, loc, found = found, expect = expect, after = after, state = "<unknown>")

  def apply(msg: String, loc: Location, found: String, expect: String, after: String, hint: String): ParseException =
    new ParseException(msg, loc, found = found, expect = expect, after = after, state = "<unknown>", hint = hint)

  def apply(msg: String, after: Expression): ParseException = new ParseException(
    msg,
    UnknownLocation,
    "<unknown>",
    "<unknown>",
    after = KeYmaeraXPrettyPrinter.stringify(after),
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
}

object LexException {
  def apply(msg: String, loc: Location, found: String = "<unknown>"): ParseException =
    new ParseException("Lexer " + msg, loc, found, "<unknown>", "", "")
}

//@todo something like case class LexException(msg: String, loc: Location) extends ParseException
