/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.core.Expression
import edu.cmu.cs.ls.keymaerax.core.ProverException

import scala.collection.immutable.StringOps

case class ParseException (msg: String, loc: Location, found: String, expect: String, after: String, state: String,
                           cause: Throwable = null, hint: String = "")
  extends ProverException(loc.begin + " " + msg + "\nFound:    " + found + " at " + loc + "\nExpected: " + expect + (if (hint=="") "" else "\nHint: " + hint), cause) {

  def inInput(input: String, tokenStream: Option[Any] = None): ParseException = {
    val lineInfo = if (input == "") "<empty>" else loc match {
      case UnknownLocation => "<unknown>"
      case _ => assert(loc.line>0 && loc.column>0, "positive location")
        val lines = (input: StringOps).lines.toList
        if (loc.line > lines.size) "<past EOF> at line " + loc.line
        else {
          //assert(!lines.isEmpty, "nonempty number of lines:\n" + input)
          val rem = lines.drop(loc.line-1)
          val count = if (loc.end!=UnknownLocation && loc.line==loc.end.line) Math.max(1,loc.end.column-loc.column+1) else 1
          //assert(!rem.isEmpty, "nonempty number of lines after drop:\n" + input)
          if (rem.nonEmpty) rem.head + "\n" + (" " * (loc.column-1)) + ("^"*count) + "\n" else "<past EOF> unexpectedly at line " + loc.line
        }
    }
    inContext(loc + "\n" + lineInfo + "\ninput:  \n" + input).asInstanceOf[ParseException]
  }

  /** Get more details on the error message in addition to [[getContext]]. */
  def getDetails: String = "After:   " + after + "\nin " + state

  override def toString: String = super.getMessage + getContext + (if (Configuration(Configuration.Keys.DEBUG) == "true") "\n" + getDetails else "")
}

object ParseException {
  def apply(msg: String, loc: Location, found: String, expect: String): ParseException =
    new ParseException(msg, loc, found = found, expect = expect, after = "<unknown>", state = "<unknown>")

  def apply(msg: String, loc: Location, found: String, expect: String, after: String): ParseException =
    new ParseException(msg, loc, found = found, expect = expect, after = after, state = "<unknown>")

  def apply(msg: String, loc: Location, found: String, expect: String, after: String, hint: String): ParseException =
    new ParseException(msg, loc, found = found, expect = expect, after = after, state = "<unknown>", hint = hint)

  def apply(msg: String, after: Expression): ParseException =
    new ParseException(msg, UnknownLocation, "<unknown>", "<unknown>", after = KeYmaeraXPrettyPrinter.stringify(after), "")

  /** Avoid throwing this unlocated errors */
  @deprecated("Avoid throwing ParseException without location information")
  def apply(msg: String): ParseException =
    new ParseException(msg, UnknownLocation, "<unknown>", "<unknown>", "", "")

  def apply(msg: String, loc: Location): ParseException =
    new ParseException(msg, loc, "<unknown>", "<unknown>", "", "")

  def apply(msg: String, loc: Location, cause: Throwable): ParseException =
    new ParseException(msg, loc, "<unknown>", "<unknown>", "", "", cause)

  def apply(msg: String, cause: Throwable): ParseException =
    new ParseException(msg, UnknownLocation, "<unknown>", "<unknown>", "", "", cause)

  /** Type parse errors */
  private def typeException(msg: String, loc: Location, found: String, expect: String, hint: String = "", cause: Throwable = null) =
    new ParseException("type analysis: " + msg, loc, found, expect, "", "", cause, hint=hint)

  /** Type parse error with mismatch in found type illtyped and expected type */
  def typeError(msg: String, illtyped: Expression, expectedType: String, loc: Location, hint: String = ""): ParseException =
    typeException(msg, loc, illtyped + " " + illtyped.getClass.getSimpleName + " of sort " + illtyped.sort, expectedType, hint=hint)

  def typeDeclGuessError(msg: String, declaredType: String, expected: Expression, loc: Location, hint: String = ""): ParseException =
    typeException(msg, loc, declaredType, expected.getClass.getSimpleName + " of sort " + expected.sort, hint=hint)

  def typeDeclError(msg: String, declaredType: String, expectedType: String, loc: Location, hint: String = ""): ParseException =
    typeException(msg, loc, declaredType, expectedType, hint=hint)

  def duplicateSymbolError(n: String, i: Option[Int], loc: Location, other: Location): ParseException =
    ParseException("Duplicate symbol '" + (n + i.map("_" + _).getOrElse("")) + "': already defined at " + other, loc, n + i.map("_" + _).getOrElse(""), "<unique name>")
}
