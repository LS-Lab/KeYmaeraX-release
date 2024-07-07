/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.bellerophon.parser

import org.keymaerax.parser.ParseException

object BelleParseException {
  def apply(
      msg: String,
      state: org.keymaerax.bellerophon.parser.BelleParser.ParserState, /*, cause: Throwable = null*/
  ): ParseException = new ParseException(
    msg,
    state.location,
    state.input.headOption.toString,
    "",
    state.topString,
    state.toString, /*, cause*/
  )
}
