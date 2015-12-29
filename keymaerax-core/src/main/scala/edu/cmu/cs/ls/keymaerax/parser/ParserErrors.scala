/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.ProverException

/**
 * Indicates a parse error at the given location,
 * with the context information state.
 * @author Andre Platzer
 */
case class ParseException(msg: String, loc: Location, state: String/*ParseState*/, cause: Throwable = null)
  extends ProverException(loc.begin + " " + msg + "\nat " + loc + "\nin " + state, cause)

//@todo something like case class LexException(msg: String, loc: Location) extends ParseException