package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tools.MathematicaConversion.KExpr
import org.apache.logging.log4j.scala.Logging

/**
 * A continuous invariant implementation using Mathematica over the JLink interface.
 * @author Andrew Sogokon, based on QETool by Nathan Fulton and Stefan Mitsch
 */
class MathematicaInvGenTool(override val link: MathematicaLink)
  extends BaseKeYmaeraMathematicaBridge[KExpr](link, KeYmaeraToMathematica, MathematicaToKeYmaera)
    with InvGenTool with Logging {

  def invgen(problem: String): Formula = {
    try {
      val (output, result) = runUnchecked(problem)
      logger.debug("\nGenerated invariant: "+ result.prettyString + "\n" + "from raw output " + output + "\n")
      result match {
        case continuousInvariant: Formula => continuousInvariant
        case _ => throw ToolException("Expected a formula from Pegasus call but got a non-formula expression: " +
          result.prettyString)
      }
    } //finally { input.dispose() }
  }

}
