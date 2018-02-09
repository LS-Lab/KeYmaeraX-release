package edu.cmu.cs.ls.keymaerax.tools

import com.wolfram.jlink.Expr
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, StringConverter}
import edu.cmu.cs.ls.keymaerax.tools.MathematicaConversion.{KExpr, MExpr}

import scala.collection.immutable

/**
 * A continuous invariant implementation using Mathematica over the JLink interface.
 * @author Andrew Sogokon, based on QETool by Nathan Fulton and Stefan Mitsch
 */
class MathematicaInvGenTool(override val link: MathematicaLink)
  extends BaseKeYmaeraMathematicaBridge[KExpr](link, KeYmaeraToMathematica, MathematicaToKeYmaera) with InvGenTool {

  def invgen(problem:String): Formula = {

    try {
      val (output, result) = runUnchecked(problem)
      print ("\nGenerated invariant: "+ result.toString + "\n")
      //new StringConverter(output.toString).asFormula
      result match {
        case continuousInvariant: Formula =>
          if (DEBUG) {
            println(s"Invariant: " + continuousInvariant.prettyString)
          }
          continuousInvariant
        case _ => throw ToolException("Expected a formula from Pegasus call but got a non-formula expression."+ "as")
      }
    } //finally { input.dispose() }
  }

}
