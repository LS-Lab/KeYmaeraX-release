/**
 * This file contains MathematicaLink, as well as associated classes for
 * converting expressions to and from Mathematica.
 */
package edu.cmu.cs.ls.keymaera.tools

import com.wolfram.jlink._
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraPrettyPrinter
import scala.math.BigDecimal

/**
 * Creating a MathematicaLink object insantiates a new connection to a
 * Mathematica Kernel.
 * 
 * @author Nathan Fulton
 */
class MathematicaLink extends Tool {
  /** @TODO-nrf replace this with a function that works on something other
   * than unix.
   */
  val ml : KernelLink = {
    MathLinkFactory.createKernelLink(Array[String](
      "-linkmode", "create",
      "-linkname", "math -mathlink"))
  }
  ml.discardAnswer()

  /**
   * Runs the command and then halts program execption until answer is returned.
   */
  def run(cmd : String) = {
    dispatch(cmd);
    getAnswer()
  }
  
  def run(cmd:com.wolfram.jlink.Expr) = {
    ml.evaluate(cmd);
    getAnswer()
  }

  def dispatch(cmd : String) : Unit = {
    ml.evaluate(cmd)
  }

  /**
   * blocks and returns the answer.
   */
  def getAnswer() = {
    ml.waitForAnswer()
    MathematicaToKeYmaera.fromMathematica(ml.getExpr())
  }
    
}

