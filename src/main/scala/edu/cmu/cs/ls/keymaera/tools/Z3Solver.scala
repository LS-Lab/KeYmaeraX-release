package edu.cmu.cs.ls.keymaera.tools

import java.io.{InputStream, FileOutputStream, FileWriter, File}
import java.nio.channels.Channels
import java.util.Locale

import edu.cmu.cs.ls.keymaera.core.{Term, Formula}
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraParser
import scala.sys.process._

/**
 * Created by ran on 3/27/15.
 */
class Z3Solver extends SMTSolver {

  val pathToZ3 : String = {
    val z3TempDir = System.getProperty("java.io.tmpdir")
    val osName = System.getProperty("os.name").toLowerCase(Locale.ENGLISH)
    if(osName.contains("windows") && new java.io.File(z3TempDir+"z3.exe").exists()) {
      z3TempDir+"z3.exe"
    } else if(new java.io.File(z3TempDir+"z3").exists()) {
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
      assert(new java.io.File(z3AbsPath).exists())
      z3AbsPath
    }
  }

  def run(cmd: String) = {
    val output : String = cmd.!!
    println("[Z3 result] \n" + output + "\n")
    // TODO So far does not handle get-model or unsat-core
    (output, toKeYmaera(output))
  }

  def qe(f : Formula) : Formula = {
    qeInOut(f)._1
  }

  def qeInOut(f : Formula) : (Formula, String, String) = {
    var inSMT = toSMT(f).getVariableList + "(assert (not " + toSMT(f).getFormula + "))"
    inSMT += "\n(check-sat)\n"
    println("[Solving with Z3...] \n" + inSMT)
    val inputFile = new File("KeymaeraToZ3.smt2")
    val writer = new FileWriter(inputFile)
    writer.write(inSMT)
    writer.flush()
    writer.close()
    val cmd = pathToZ3 + " " + inputFile.getAbsolutePath
    val (output, result) = run(cmd)
    inputFile.delete()
    result match {
      case f : Formula => (f, cmd, output)
      case _ => throw new Exception("Expected a formula from Reduce call but got a non-formula expression.")
    }
  }

  def simplify(t: Term) = {
    val simp = toSMT(t).getVariableList + "(simplify " + toSMT(t).getFormula + ")"
//    println("[Simplifying with Z3 ...] \n" + simp)
    val inputFileSimp = new File("KeymaeraToZ3Simplify.smt2")
    val writer = new FileWriter(inputFileSimp)
    writer.write(simp)
    writer.flush()
    writer.close()
    val cmd = pathToZ3 + " " + inputFileSimp.getAbsolutePath
    val output: String = cmd.!!
    inputFileSimp.delete()
    new KeYmaeraParser().parseBareTerm(output) match {
      case Some(output) => output
      case None => t
    }
  }

}
