/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tools

import java.io.{InputStream, FileOutputStream, FileWriter, File}
import java.nio.channels.Channels
import java.util.Locale

import edu.cmu.cs.ls.keymaerax.core.{True, False, Term, Formula}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraParser
import scala.sys.process._

/**
 * Created by ran on 3/27/15.
 * @author Ran Ji
 */
class Z3Solver extends SMTSolver {

  val k2s = new KeYmaeraToSMT("Z3")
  def toSMT(expr : KExpr): SExpr = k2s.convertToSMT(expr)

  val pathToZ3 : String = {
    val z3TempDir = System.getProperty("user.home") + File.separator + ".keymaerax"
    if(!new File(z3TempDir).exists) new File(z3TempDir).mkdirs
    val osName = System.getProperty("os.name").toLowerCase(Locale.ENGLISH)
    if(osName.contains("windows") && new File(z3TempDir+"z3.exe").exists()) {
      z3TempDir+"z3.exe"
    } else if(new File(z3TempDir+"z3").exists()) {
      z3TempDir+"z3"
    } else {
      val osArch = System.getProperty("os.arch")
      var resource : InputStream = null
      if(osName.contains("mac")) {
        if(osArch.contains("64")) {
          resource = this.getClass.getResourceAsStream("/z3/mac64/z3")
        }
      } else if(osName.contains("windows")) {
        if(osArch.contains("64")) {
          resource = this.getClass.getResourceAsStream("/z3/windows64/z3.exe")
        } else {
          resource = this.getClass.getResourceAsStream("/z3/windows32/z3.exe")
        }
      } else if(osName.contains("linux")) {
        if(osArch.contains("64")) {
          resource = this.getClass.getResourceAsStream("/z3/ubuntu64/z3")
        } else {
          resource = this.getClass.getResourceAsStream("/z3/ubuntu32/z3")
        }
      } else if(osName.contains("freebsd")) {
        if(osArch.contains("64")) {
          resource = this.getClass.getResourceAsStream("/z3/freebsd64/z3")
        }
      } else {
        throw new Exception("Z3 solver is currently not supported in your operating system.")
      }
      if(resource == null)
        throw new Exception("Could not find Z3 in classpath: " + System.getProperty("user.dir"))
      val z3Source = Channels.newChannel(resource)
      val z3Temp = {
        if(osName.contains("windows")) {
          new File(z3TempDir, "z3.exe")
        } else {
          new File(z3TempDir, "z3")
        }
      }

      // Get a stream to the script in the resources dir
      val z3Dest = new FileOutputStream(z3Temp)
      // Copy file to temporary directory
      z3Dest.getChannel.transferFrom(z3Source, 0, Long.MaxValue)
      val z3AbsPath = z3Temp.getAbsolutePath
      Runtime.getRuntime.exec("chmod u+x " + z3AbsPath)
      z3Source.close()
      z3Dest.close()
      assert(new File(z3AbsPath).exists())
      z3AbsPath
    }
  }

  def run(cmd: String) = {
    val output : String = cmd.!!
    println("[Z3 result] \n" + output + "\n")
    // TODO So far does not handle get-model or unsat-core
    val result = {
      if (output.contains("unsat")) True
      else if(output.contains("sat")) False
      else if(output.contains("unknown")) False
      else throw new SMTConversionException("Conversion of Z3 result \n" + output + "\n is not defined")
    }
    (output, result)
  }

  def qe(f : Formula) : Formula = {
    qeInOut(f)._1
  }

  def qeInOut(f : Formula) : (Formula, String, String) = {
    var smtCode = toSMT(f).getVariableList + "(assert (not " + toSMT(f).getFormula + "))"
    smtCode += "\n(check-sat)\n"
    println("[Solving with Z3...] \n" + smtCode)
    val smtTempDir = System.getProperty("user.home") + File.separator + ".keymaerax"
    val smtFile = new File(smtTempDir, "KeymaeraToZ3.smt2")
    val writer = new FileWriter(smtFile)
    writer.write(smtCode)
    writer.flush()
    writer.close()
    val cmd = pathToZ3 + " " + smtFile.getAbsolutePath
    val (output, result) = run(cmd)
    smtFile.delete()
    result match {
      case f : Formula => (f, cmd, output)
      case _ => throw new Exception("Expected a formula from QE call but got a non-formula expression.")
    }
  }

  def simplify(t: Term) = {
    val smtCode = toSMT(t).getVariableList + "(simplify " + toSMT(t).getFormula + ")"
//    println("[Simplifying with Z3 ...] \n" + smtCode)
    val smtTempDir = System.getProperty("user.home") + File.separator + ".keymaerax"
    val smtFile = new File(smtTempDir, "KeymaeraToZ3Simplify.smt2")
    val writer = new FileWriter(smtFile)
    writer.write(smtCode)
    writer.flush()
    writer.close()
    val cmd = pathToZ3 + " " + smtFile.getAbsolutePath
    val output: String = cmd.!!
//    println("[Z3 simplify result] \n" + output + "\n")
    smtFile.delete()
    new KeYmaeraParser().parseBareTerm(output) match {
      case Some(output) => output
      case None => t
    }
  }

}
