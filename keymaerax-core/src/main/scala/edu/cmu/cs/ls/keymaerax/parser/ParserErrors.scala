package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.ProverException

/**
 * Indicates a parse error at the given location,
 * with the context information state.
 * @author aplatzer
 */
case class ParseException(msg: String, loc: Location, state: String/*ParseState*/) extends ProverException(msg + "\nat " + loc + "\nin " + state)
