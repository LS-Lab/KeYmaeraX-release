package edu.cmu.cs.ls.keymaera.tools

import com.wolfram.jlink._
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraPrettyPrinter
import scala.math.BigDecimal

/**
 * An abstract interface to Mathematica link implementations.
 * The link may be used syncrhonously or asychronously.
 * Multiple MathematicaLinks may be created by instantiating multiple copies
 * of implementing classes.
 * 
 * @author Nathan Fulton
 */
trait MathematicaLink extends Tool with QETool {
  def run(cmd : String) : edu.cmu.cs.ls.keymaera.core.Expr
  def run(cmd : com.wolfram.jlink.Expr) : edu.cmu.cs.ls.keymaera.core.Expr
  
  def dispatch(cmd : String) : Unit
  def dispatch(cmd : com.wolfram.jlink.Expr) : Unit

  /**
   * @returns true if the job is finished, false if it is still running.
   */
  def ready : Boolean

  /**
   * @returns The result of a dispatched job. This method blocks on
   * Mathematica.
   */
  def getAnswer : edu.cmu.cs.ls.keymaera.core.Expr

  /** Cancels the current request.
   * @returns True if job is successfully cancelled, or False if the new
   * status is unknown.
   */
  def cancel : Boolean

  def toMathematica(expr : edu.cmu.cs.ls.keymaera.core.Expr) =
    KeYmaeraToMathematica.fromKeYmaera(expr)

  def toKeYmaera(expr : com.wolfram.jlink.Expr) =
    MathematicaToKeYmaera.fromMathematica(expr)
}

/**
 * Creating a MathematicaLink object insantiates a new connection to a
 * Mathematica Kernel.
 * 
 * @author Nathan Fulton
 */
class JLinkMathematicaLink extends  MathematicaLink {
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

  def dispatch(cmd : com.wolfram.jlink.Expr) = {
    ml.evaluate(cmd)
  }

  /**
   * blocks and returns the answer.
   */
  def getAnswer() = {
    ml.waitForAnswer()
    MathematicaToKeYmaera.fromMathematica(ml.getExpr())
  }

  def ready = ???

  def cancel = ???


  def qe(f : Formula) : edu.cmu.cs.ls.keymaera.core.Expr = run("Resolve[" + toMathematica(f) + "]")
}

