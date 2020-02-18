/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * @note Code Review: 2016-08-02 postponed since Polya output processing needs to be made more robust
  */
package edu.cmu.cs.ls.keymaerax.tools.qe

import java.io.{File, FileWriter}

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.lemma.Evidence
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXPrettyPrinter, ParseException}
import edu.cmu.cs.ls.keymaerax.tools._
import org.apache.logging.log4j.scala.Logging

import scala.collection.immutable
import scala.sys.process._

/**
  * Starts a Polya process with the binary at `polyaPath`, converting KeYmaera X datastructures to SMT-Lib format
  * with `converter`.
  * @param polyaPath The path to the Polya binary.
  * @param converter Converts from KeYmaera X datastructures to SMT-Lib format.
  * Created by ran on 4/24/15.
  * @author Ran Ji
 */
class PolyaSolver(val polyaPath: String, val converter: SMTConverter) extends Logging {

  /**
   * Get result from Polya output
   *
   * @param output Polya output of the form:
   *                  command
   *                  information
   *                  -----
   *                  input
   *                  -----
   *                  result
   *
   * @return result
    * @todo Code Review: this is not a trustworthy way of getting reliable decisions from Polya. Example broken output would be {{{
    *       I am about to multiply
    *       x*5+2*x*x*y+
    *       1
    *    }}}
    *    stop, which will be incorrectly interpreted as True
    * @todo Consider direct Java->Python link instead of misparsing
   */
  private def getTruncatedResult(output: String) : String = {
    var reversedOutput = output.reverse
    while(reversedOutput.startsWith("\n")) {
      reversedOutput = reversedOutput.stripPrefix("\n")
    }
    val reversedResult = reversedOutput.substring(0, reversedOutput.indexOf("\n"))
    reversedResult.reverse
  }

  /** Return Polya QE result and the proof evidence */
  def qe(f: Formula): (Formula, Evidence) = {
    val smtCode = converter(f)
    logger.debug("[Solving with Polya...] \n" + smtCode)
    val smtFile = File.createTempFile("polyaQe", ".smt2")
    val writer = new FileWriter(smtFile)
    writer.write(smtCode)
    writer.flush()
    writer.close()
    val cmd = polyaPath + " " + smtFile.getAbsolutePath
    /** Polya output as String, (check-sat) gives 1, -1 or 0 */
    val polyaOutput = cmd.!!
    logger.debug("[Polya result] \n" + polyaOutput)
    val polyaResult = getTruncatedResult(polyaOutput)
    /** Interpretation of Polya output as KeYmaera X formula
      * if Polya output is 1, then return True
      * if Polya output is -1 or 0, then throw exception
      * Polya does not have other possible result for (check-sat)
      */
    if (polyaResult == "-1") throw new SMTQeException("QE with Polya gives -1 (POSSIBLY SAT). Cannot reduce the following formula to True:\n" + KeYmaeraXPrettyPrinter(f) + "\n")
    else if (polyaResult == "1") (True, ToolEvidence(immutable.List("input" -> smtCode, "output" -> polyaOutput)))
    else if (polyaResult == "0") throw new SMTQeException("QE with Polya gives 0 (FAILED). Cannot reduce the following formula to True:\n" + KeYmaeraXPrettyPrinter(f) + "\n")
    else throw ConversionException("Conversion of Polya result \n" + polyaResult + "\n is not defined")
  }

  /**
   * Simplify a KeYmaera X term into a possibly simple term
   * @param t  KeYmaera X term to be simplified
   * @return   the simplified term, or the original term if the simplify result is not a parsable KeYmaera X term
   */
  def simplify(t: Term): Term = {
    val (varDec, smt) = DefaultSMTConverter.generateSMT(t)
    val smtCode = varDec + "(simplify " + smt + ")"
    logger.debug("[Simplifying with Polya ...] \n" + smtCode)
    val smtFile = File.createTempFile("polyaSimplify", ".smt2")
    val writer = new FileWriter(smtFile)
    writer.write(smtCode)
    writer.flush()
    writer.close()
    val cmd = polyaPath + " " + smtFile.getAbsolutePath
    val polyaOutput = cmd.!!
    logger.debug("[Polya simplify result] \n" + polyaOutput + "\n")
    val polyaResult = getTruncatedResult(polyaOutput)
    try {
      KeYmaeraXParser.termParser(polyaResult)
    } catch {
      case _: ParseException =>
        logger.debug("[Info] Cannot parse Polya simplified result: " + polyaResult)
        t
    }
  }
}

