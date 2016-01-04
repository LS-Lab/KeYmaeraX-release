/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.Expression
import edu.cmu.cs.ls.keymaerax.core.ProverException
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser.{TokenStream, ParseState}

/**
 * Indicates a parse error at the given location,
 * with the context information state.
 * @author Andre Platzer
 */
case class ParseException(msg: String, loc: Location, found: String/*Token*/, expect: String/**/, after: String/*ParseState*/, state: String/*ParseState*/, cause: Throwable = null)
  extends ProverException(loc.begin + " " + msg + "\nat " + loc + "\nFound:    " + found + "\nExpected: " + expect + "\nAfter:   " + after + "\nin " + state, cause)

object ParseException {
  def apply(msg: String, state: ParseState/*, cause: Throwable = null*/): ParseException =
    new ParseException(msg, state.input.head.loc, state.input.head.toString, "", state.topString, state.toString/*, cause*/)
  def apply(msg: String, state: ParseState, expect: List[Expected]/*, cause: Throwable = null*/): ParseException =
    new ParseException(msg, state.input.head.loc, state.input.head.toString, expect.mkString("\n      or: "), state.topString, state.toString/*, cause*/)
  def apply(msg: String, state: ParseState, expect: String): ParseException =
    new ParseException(msg, state.input.head.loc, state.input.head.toString, expect, state.topString, state.toString)
  def apply(msg: String, after: Expression, input: TokenStream): ParseException =
    new ParseException(msg, UnknownLocation, "<unknown>", "<unknown>", KeYmaeraXParser.printer.stringify(after), "\nInput: " + input)
  def apply(msg: String, after: Expression, input: String): ParseException =
    new ParseException(msg, UnknownLocation, "<unknown>", "<unknown>", KeYmaeraXParser.printer.stringify(after), "\nInput: " + input)
  def apply(msg: String, after: String, input: TokenStream): ParseException =
    new ParseException(msg, UnknownLocation, "<unknown>", "<unknown>", after, "\nInput: " + input)
  def apply(msg: String, after: String, input: String): ParseException =
    new ParseException(msg, UnknownLocation, "<unknown>", "<unknown>", after, "\nInput: " + input)
  def apply(msg: String, loc: Location, after: String, input: String): ParseException =
    new ParseException(msg, loc, "<unknown>", "<unknown>", after, "\nInput: " + input)
}
//@todo something like case class LexException(msg: String, loc: Location) extends ParseException