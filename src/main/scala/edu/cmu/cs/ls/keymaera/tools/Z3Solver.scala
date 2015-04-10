package edu.cmu.cs.ls.keymaera.tools

import java.io.{FileWriter, File}

import edu.cmu.cs.ls.keymaera.core.{Term, Formula}
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraParser
import scala.sys.process._

/**
 * Created by ran on 3/27/15.
 */
class Z3Solver extends SMTSolver {

  //TODO change to set path option
  val pathToZ3 = "/usr/z3/build/z3"

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
    val inputFile = new File("KeymaeraToZ3Simplify.smt2")
    val writer = new FileWriter(inputFile)
    writer.write(simp)
    writer.flush()
    writer.close()
    val cmd = pathToZ3 + " " + inputFile.getAbsolutePath
    val output: String = cmd.!!
    inputFile.delete()
    new KeYmaeraParser().parseBareTerm(output) match {
      case Some(output) => output
      case None => t
    }
  }

}
