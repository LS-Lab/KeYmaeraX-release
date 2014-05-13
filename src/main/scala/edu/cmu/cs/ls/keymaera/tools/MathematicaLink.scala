package edu.cmu.cs.ls.keymaera.tools

import com.wolfram.jlink._
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraPrettyPrinter
import scala.math.BigDecimal

/**
 * An abstract interface to Mathematica link implementations.
 * The link may be used syncrhonously or asychronously.
 * Each MathematicaLink 
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
   * @return true if the job is finished, false if it is still running.
   */
  def ready : Boolean

  /**
   * @return The result of a dispatched job. This method blocks on
   * Mathematica.
   */
  def getAnswer : edu.cmu.cs.ls.keymaera.core.Expr

  /** Cancels the current request.
   * @return True if job is successfully cancelled, or False if the new
   * status is unknown.
   */
  def cancel : Boolean

  def toMathematica(expr : edu.cmu.cs.ls.keymaera.core.Expr) =
    KeYmaeraToMathematica.fromKeYmaera(expr)

  def toKeYmaera(expr : com.wolfram.jlink.Expr) =
    MathematicaToKeYmaera.fromMathematica(expr)
}

/**
 * Creating a MathematicaLink object instantiates a new connection to a
 * Mathematica Kernel.
 * 
 * @author Nathan Fulton
 */
class JLinkMathematicaLink extends  MathematicaLink {
  val ml : KernelLink = {
    MathLinkFactory.createKernelLink(Array[String](
      "-linkmode", "launch",
      "-linkname", "MathKernel -mathlink"))
  }
  ml.discardAnswer()

  /**
   * Runs the command and then halts program exception until answer is returned.
   */
  def run(cmd : String) = {
    dispatch(cmd);
    getAnswer()
  }
  
  def run(cmd:com.wolfram.jlink.Expr) = {
    dispatch(cmd);
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


  def qe(f : Formula) : Formula = {
    val result = run("Reduce[" + toMathematica(f) + "]")
    if(result.isInstanceOf[Formula]) {
      result.asInstanceOf[Formula]
    }
    else {
      throw new Exception("Expected a formula from Reduce call but got a non-formula expression.")
    }
  }
}

