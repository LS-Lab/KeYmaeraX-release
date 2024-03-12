/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import edu.cmu.cs.ls.keymaerax.parser.{Location, Region, UnknownLocation}

/**
 * Prints the model with the problematic portion underlined and a message displayed.
 * @author
 *   Nathan Fulton
 */
//@todo : @deprecated("This should be replaced with a proper pretty-printer that takes a bellexpr instead of a string and handles all locations properly", "4.1b2")
private[keymaerax] object HackyInlineErrorMsgPrinter {
  def apply(input: String, location: Location, message: String): String = {
    "\n" +
      input
        .split("\n")
        .zipWithIndex
        .foldLeft("")((result, next) => {
          if (next._2 == location.begin.line - 1) { result + next._1 + "\n" + alignWith(location, message) + "\n" }
          else result + next._1 + "\n"
        })
  }

  private def alignWith(location: Location, message: String): String = location match {
    case Region(_, c, _, ec) =>
      val result = new StringBuffer()
      result.append(" " * (c - 1))
      result.append("^" * (ec - c))
      result.append(message)
      result.toString
    case UnknownLocation => "<unknown>"
    case _ => "<unknown>"
  }
}
