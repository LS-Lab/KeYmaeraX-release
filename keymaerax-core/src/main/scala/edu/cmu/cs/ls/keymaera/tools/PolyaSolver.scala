package edu.cmu.cs.ls.keymaera.tools

import java.io.{FileWriter, FileOutputStream, File, InputStream}
import java.nio.channels.Channels
import java.util.Locale

import edu.cmu.cs.ls.keymaera.core.{False, True, Term, Formula}
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraParser
import scala.sys.process._

/**
 * Created by ran on 4/24/15.
 */
class PolyaSolver extends SMTSolver {

  val PolyaPath = "/Users/ran/software/polya/polya"
  val exportPolya = "export PYTHONPATH=PYTHONPATH:" + PolyaPath
  val runPolya = "python /Users/ran/software/polya/smtlib2polya/batch_translate.py"
  val smtDir = "/Users/ran/software/polya/keymaera-smt2"

  def run(cmd: String) = {
    val output : String = cmd.!!
    println("[Ploya result] \n" + output + "\n")
    // TODO So far does not handle get-model or unsat-core
    val result = {
      if (output.contains("1 successes")) True
      else if(output.contains("1 failures")) False
      else if(output.contains("1 errors")) False
      else throw new SMTConversionException("Conversion of SMT result " + output + " is not defined")
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
    val smtFile = new File(smtDir, "KeymaeraToPolya.smt2")
    val writer = new FileWriter(smtFile)
    writer.write(smtCode)
    writer.flush()
    writer.close()
//    val cmd = exportPolya + " & " + runPolya
    val cmd = runPolya
    val (output, result) = run(cmd)
    smtFile.delete()
    result match {
      case f : Formula => (f, cmd, output)
      case _ => throw new Exception("Expected a formula from Reduce call but got a non-formula expression.")
    }
  }


}

