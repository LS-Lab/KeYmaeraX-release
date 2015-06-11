package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.ProverException

/**
 * Created by aplatzer on 6/7/15.
 * @author aplatzer
 */
class ParseException(msg: String, state: String) extends ProverException(msg + "\nin " + state)
