/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tools

import java.io.{FileWriter, FileOutputStream, File, InputStream}
import java.nio.channels.Channels
import java.util.Locale

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXPrettyPrinter, ParseException, KeYmaeraXParser}
import scala.collection.immutable
import scala.sys.process._

/**
 * Created by ran on 4/24/15.
 * @author Ran Ji
 */
class PolyaSolver extends SMTSolver {

  /** Get the absolute path to Polya jar */
  private val pathToPolya : String = {
    val polyaTempDir = System.getProperty("user.home") + File.separator + ".keymaerax"
    if(!new File(polyaTempDir).exists) new File(polyaTempDir).mkdirs
    val osName = System.getProperty("os.name").toLowerCase(Locale.ENGLISH)

    // so far only for Mac Os and linux
    //@todo: support for other OS
    if(new File(polyaTempDir+"polya").exists()) {
      polyaTempDir+"polya"
    } else {
      val osArch = System.getProperty("os.arch")
      var resource : InputStream = null
      if(osName.contains("mac")) {
        if(osArch.contains("64")) {
          resource = this.getClass.getResourceAsStream("/polya/mac64/polya")
        }
      } else if(osName.contains("linux")) {
        if(osArch.contains("64")) {
          resource = this.getClass.getResourceAsStream("/polya/ubuntu64/polya")
        }
      } else {
        throw new Exception("Polya solver is currently not supported in your operating system.")
      }
      if(resource == null)
        throw new Exception("Could not find Polya in classpath: " + System.getProperty("user.dir"))

      val polyaSource = Channels.newChannel(resource)
      val polyaTemp = new File(polyaTempDir, "polya")
      // Get a stream to the script in the resources dir
      val polyaDest = new FileOutputStream(polyaTemp)
      // Copy file to temporary directory
      polyaDest.getChannel.transferFrom(polyaSource, 0, Long.MaxValue)
      val polyaAbsPath = polyaTemp.getAbsolutePath
      Runtime.getRuntime.exec("chmod u+x " + polyaAbsPath)
      polyaSource.close()
      polyaDest.close()
      assert(new File(polyaAbsPath).exists())
      polyaAbsPath
    }
  }

  /**
   * Check satisfiability with Polya
   * @param cmd the command for running Polya with a given SMT file
   * @return    Polya output as String and the interpretation of Polya output as KeYmaera X formula
   */
  def run(cmd: String) : (String, Formula)= {
    val polyaOutput = cmd.!!
    println("[Polya result] \n" + polyaOutput + "\n")
    val kResult = {
      if (polyaOutput.startsWith("-1")) False
      else if(polyaOutput.startsWith("1")) True
      else if(polyaOutput.startsWith("0")) False
      else throw new SMTConversionException("Conversion of Polya result \n" + polyaOutput + "\n is not defined")
    }
    (polyaOutput, kResult)
  }

  /** Return Polya QE result */
  def qe(f: Formula) : Formula = {
    qeEvidence(f)._1
  }

  /** Return Polya QE result and the proof evidence */
  def qeEvidence(f: Formula) : (Formula, Evidence) = {
    val smtCode = SMTConverter(f, "Polya") + "\n(check-sat)\n"
    println("[Solving with Polya...] \n" + smtCode)
    val smtFile = getUniqueSmt2File()
    val writer = new FileWriter(smtFile)
    writer.write(smtCode)
    writer.flush()
    writer.close()
    val cmd = pathToPolya + " " + smtFile.getAbsolutePath
    val (polyaOutput, kResult) = run(cmd)
    kResult match {
      case f: Formula => (f, new ToolEvidence(immutable.Map("input" -> smtCode, "output" -> polyaOutput)))
      case _ => throw new Exception("Expected a formula from QE call but got a non-formula expression.")
    }
  }

  /**
   * Simplify a KeYmaera X term into a possibly simple term
   * @param t  KeYmaera X term to be simplified
   * @return   the simplified term, or the original term if the simplify result is not a parsable KeYmaera X term
   */
  def simplify(t: Term) : Term = {
    val smtCode = SMTConverter.generateSimplify(t, "Z3")
    println("[Simplifying with Polya ...] \n" + smtCode)
    val smtFile = getUniqueSmt2File()
    val writer = new FileWriter(smtFile)
    writer.write(smtCode)
    writer.flush()
    writer.close()
    val cmd = pathToPolya + " " + smtFile.getAbsolutePath
    val polyaOutput = cmd.!!
    println("[Polya simplify result] \n" + polyaOutput + "\n")
    try {
      KeYmaeraXParser.termParser(polyaOutput)
    } catch {
      case e: ParseException => println("[Info] Cannot parse Z3 simplified result: " + polyaOutput); t
    }
  }
}

