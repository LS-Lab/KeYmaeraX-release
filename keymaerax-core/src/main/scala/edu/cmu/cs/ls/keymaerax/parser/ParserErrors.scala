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
  extends ProverException(loc.begin + " " + msg + "\nat " + loc + "\nFound:    " + found + "\nExpected: " + expect + "\nAfter:   " + after + "\nin " + state, cause) {

  /**
    * Add the input context information to this exception, returning the resulting exception to be thrown.
    * @param input textual description of the input in which this prover exception occurred.
    * @param tokenStream optionally the tokenStream lexed from the input.
    */
  def inInput(input: String, tokenStream: Option[TokenStream] = None): ParseException = {
    //@todo take loc into account to project input to loc
    val lineInfo = loc match {
      case UnknownLocation => "<unknown>"
      case _ => assert(loc.line>0 && loc.column>0);
        val lines = input.lines
        if (loc.line > lines.size) "<past EOF> at line " + loc.line
        else {
          val rem = lines.drop(loc.line-1)
          if (rem.hasNext) rem.next() else "past EOF> at line " + loc.line
        }
    }
    throw if (tokenStream.isDefined) inContext("     " + lineInfo + "\ninput:  " + input) else inContext("     " + lineInfo + "\ninput:  " + input + "\nas tokens: " + tokenStream.get)
  }
}

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