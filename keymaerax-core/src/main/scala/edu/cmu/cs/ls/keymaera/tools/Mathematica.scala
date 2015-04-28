package edu.cmu.cs.ls.keymaera.tools

import edu.cmu.cs.ls.keymaera.core._

import scala.collection.immutable.Map

/**
 * Mathematica tool for quantifier elimination and solving differential equations.
 *
 * Created by smitsch on 4/27/15.
 * @author Stefan Mitsch
 */
class Mathematica extends ToolBase("Mathematica") with QETool with DiffSolutionTool {
  private val jlink = new JLinkMathematicaLink

  // TODO replace with constructor and dependency injection
  override def init(config: Map[String,String]) = {
    val linkName = config.get("linkName") match {
      case Some(l) => l
      case None => throw new IllegalArgumentException("Missing configuration parameter 'linkName'")
    }
    val libDir = config.get("libDir") // doesn't need to be defined
    jlink.init(linkName, libDir)
    initialized = libDir.isDefined
  }

  override def shutdown() = jlink.shutdown()

  override def qe(formula: Formula): Formula = jlink.qe(formula)
  override def qeInOut(formula: Formula): (Formula, String, String) = jlink.qeInOut(formula)
  override def diffSol(diffSys: DifferentialProgram, diffArg: Variable,
                       iv: Predef.Map[Variable, Function]): Option[Formula] = jlink.diffSol(diffSys, diffArg, iv)
}
