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
 * @see [[ProverException.getContext]]
 */
case class ParseException (msg: String, loc: Location, found: String/*Token*/, expect: String/**/, after: String/*ParseState*/, state: String/*ParseState*/, cause: Throwable = null)
  extends ProverException(loc.begin + " " + msg + "\nFound:    " + found + " at " + loc + "\nExpected: " + expect, cause) {
  /**
    * Add the input context information to this exception, returning the resulting exception to be thrown.
    * @param input textual description of the input in which this prover exception occurred.
    * @param tokenStream optionally the tokenStream lexed from the input.
    * @see [[ProverException.getContext]]
    */
  def inInput(input: String, tokenStream: Option[TokenStream] = None): ParseException = {
    //println("inInput\n" + input)
    //@todo take loc into account to project input to loc
    val lineInfo = if (input == "") "<empty>" else loc match {
      case UnknownLocation => "<unknown>"
      case _ => assert(loc.line>0 && loc.column>0, "positive location");
        val lines = input.lines.toList
        if (loc.line > lines.size) "<past EOF> at line " + loc.line
        else {
          //assert(!lines.isEmpty, "nonempty number of lines:\n" + input)
          val rem = lines.drop(loc.line-1)
          val count = if (loc.end!=UnknownLocation && loc.line==loc.end.line) Math.max(1,loc.end.column-loc.column+1) else 1
          //assert(!rem.isEmpty, "nonempty number of lines after drop:\n" + input)
          if (!rem.isEmpty) rem.head + "\n" + (" " * (loc.column-1)) + ("^"*count) + "\n" else "<past EOF> unexpectedly at line " + loc.line
        }
    }
    throw inContext(loc + "\n" + lineInfo + "\ninput:  \n" + input + (if (KeYmaeraXParser.DEBUG) "\ntokens: " + tokenStream.getOrElse("<unknown>") else ""))
  }

  /** Get more details on the error message in addition to [[getContext]]. */
  def getDetails: String = "After:   " + after + "\nin " + state

  override def toString: String = super.getMessage + getContext + (if (KeYmaeraXParser.DEBUG) "\n" + getDetails else "")
}

object ParseException {
  def apply(msg: String, state: ParseState /*, cause: Throwable = null*/): ParseException =
    new ParseException(msg, state.location, state.la.toString, "", state.topString, state.toString /*, cause*/)

  def apply(msg: String, state: edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser.ParserState/*, cause: Throwable = null*/): ParseException =
    new ParseException(msg, state.location, state.input.headOption.toString, "", state.topString, state.toString /*, cause*/)

  def apply(msg: String, state: ParseState, expect: List[Expected] /*, cause: Throwable = null*/): ParseException =
    new ParseException(msg, state.location, tokenDescription(state.la), expect.mkString("\n      or: "), state.topString, state.toString /*, cause*/)

  def apply(msg: String, state: ParseState, found: Token, expect: String): ParseException =
    new ParseException(msg, found.loc, tokenDescription(found), expect, state.topString, state.toString)

  def apply(msg: String, state: ParseState, expect: String): ParseException =
    new ParseException(msg, state.location, tokenDescription(state.la), expect, state.topString, state.toString)

  def apply(msg: String, after: Expression): ParseException =
    new ParseException(msg, UnknownLocation, "<unknown>", "<unknown>", KeYmaeraXParser.printer.stringify(after), "")

  def apply(msg: String, loc: Location): ParseException =
    new ParseException(msg, loc, "<unknown>", "<unknown>", "", "")

  def apply(msg: String, cause: Throwable): ParseException =
    new ParseException(msg, UnknownLocation, "<unknown>", "<unknown>", "", "", cause)

  def imbalancedError(msg: String, unmatched: Token, state: ParseState): ParseException = if (state.la.tok == EOF)
    new ParseException(msg, unmatched.loc, unmatched.toString, "", state.topString, state.toString /*, cause*/)
  else
    new ParseException(msg + "\nunmatched: :" + unmatched + " at " + unmatched.loc, state.location, state.la.toString, "", state.topString, state.toString /*, cause*/)

  private[parser] def tokenDescription(tok: Token): String = tokenDescription(tok.tok)
  private[parser] def tokenDescription(tok: Terminal): String = tok.img + " (" + tok + ")"
}

object LexException {
  def apply(msg: String, loc: Location): ParseException =
    new ParseException("Lexer " + msg, loc, "<unknown>", "<unknown>", "", "")
}

//@todo something like case class LexException(msg: String, loc: Location) extends ParseException