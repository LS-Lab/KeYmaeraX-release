/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tools

import java.io.{FileWriter, FileOutputStream, File, InputStream}
import java.nio.channels.Channels
import java.util.Locale

import edu.cmu.cs.ls.keymaerax.core.{False, True, Term, Formula}
import edu.cmu.cs.ls.keymaerax.parser.{ParseException, KeYmaeraXParser}
import scala.sys.process._

/**
 * Created by ran on 4/24/15.
 * @author Ran Ji
 */
class PolyaSolver extends SMTSolver {

  val k2s = new KeYmaeraToSMT("Polya")
  def toSMT(expr : KExpr): SExpr = k2s.convertToSMT(expr)

  val pathToPolya : String = {
    val polyaTempDir = System.getProperty("user.home") + File.separator + ".keymaerax"
    if(!new File(polyaTempDir).exists) new File(polyaTempDir).mkdirs
    val osName = System.getProperty("os.name").toLowerCase(Locale.ENGLISH)

    // so far only for Mac Os and linux
    // TODO: support for other OS
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

  def run(cmd: String) = {
    val output : String = cmd.!!
    println("[Polya result] \n" + output + "\n")
    val result = {
      if (output.contains("-1")) False
      else if(output.contains("1")) True
      else if(output.contains("0")) False
      else throw new SMTConversionException("Conversion of Polya result \n" + output + "\n is not defined")
    }
    (output, result)
  }

  def qe(f : Formula) : Formula = {
    qeInOut(f)._1
  }

  def qeInOut(f : Formula) : (Formula, String, String) = {
    var smtCode = toSMT(f).getVariableList + "(assert (not " + toSMT(f).getFormula + "))"
    smtCode += "\n(check-sat)\n"
    println("[Solving with Polya...] \n" + smtCode)
    val smtTempDir = System.getProperty("user.home") + File.separator + ".keymaerax"
    val smtFile = new File(smtTempDir, "KeymaeraToPolya.smt2")
    val writer = new FileWriter(smtFile)
    writer.write(smtCode)
    writer.flush()
    writer.close()
    val cmd = pathToPolya + " " + smtFile.getAbsolutePath
    val (output, result) = run(cmd)
    smtFile.delete()
    result match {
      case f : Formula => (f, cmd, output)
      case _ => throw new Exception("Expected a formula from QE call but got a non-formula expression.")
    }
  }

  def simplify(t: Term) = {
    val smtCode = toSMT(t).getVariableList + "(simplify " + toSMT(t).getFormula + ")"
//    println("[Simplifying with Polya ...] \n" + smtCode)
    val smtTempDir = System.getProperty("user.home") + File.separator + ".keymaerax"
    val smtFile = new File(smtTempDir, "KeymaeraToPolyaSimplify.smt2")
    val writer = new FileWriter(smtFile)
    writer.write(smtCode)
    writer.flush()
    writer.close()
    val cmd = pathToPolya + " " + smtFile.getAbsolutePath
    val output: String = cmd.!!
//    println("[Polya simplify result] \n" + output + "\n")
    smtFile.delete()
    try {
      KeYmaeraXParser.termParser(output)
    } catch {
      case e: ParseException => t
    }
  }

}

