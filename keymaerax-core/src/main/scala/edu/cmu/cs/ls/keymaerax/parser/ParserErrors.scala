/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.ProverException

/**
 * Indicates a parse error at the given location,
 * with the context information state.
 * @author Andre Platzer
 */
case class ParseException(msg: String, loc: Location, state: String/*ParseState*/) extends ProverException(loc.begin + " " + msg + "\nat " + loc + "\nin " + state)
