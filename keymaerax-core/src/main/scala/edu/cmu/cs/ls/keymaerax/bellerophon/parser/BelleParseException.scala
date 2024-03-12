/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import edu.cmu.cs.ls.keymaerax.parser.ParseException

object BelleParseException {
  def apply(
      msg: String,
      state: edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser.ParserState, /*, cause: Throwable = null*/
  ): ParseException = new ParseException(
    msg,
    state.location,
    state.input.headOption.toString,
    "",
    state.topString,
    state.toString, /*, cause*/
  )
}
