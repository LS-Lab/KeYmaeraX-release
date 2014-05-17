package edu.cmu.cs.ls.keymaera.tools

import com.wolfram.jlink._
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraPrettyPrinter
import scala.math.BigDecimal
import java.io.FileReader

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
  def run(cmd : String) : (String, edu.cmu.cs.ls.keymaera.core.Expr)
  def run(cmd : com.wolfram.jlink.Expr) : (String, edu.cmu.cs.ls.keymaera.core.Expr)
  
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
  def getAnswer : (String, edu.cmu.cs.ls.keymaera.core.Expr)

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
    val call: String = try {
      import java.io.File
      val prop = new java.util.Properties()
      val f = new File(System.getProperties.get("user.home") + File.separator + ".keymaera" + File.separator + "proof-settings.props")
      prop.load(new FileReader(f))
      prop.get("[MathematicaOptions]mathKernel").asInstanceOf[String]
    } catch {
      case x: java.io.IOException => "MathKernel"
    }
    MathLinkFactory.createKernelLink(Array[String](
      "-linkmode", "launch",
      "-linkname", call + " -mathlink"))
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
    val res = ml.getExpr
    (res.toString, MathematicaToKeYmaera.fromMathematica(res))
  }

  def ready = ???

  def cancel = ???

  def qe(f : Formula) : Formula = {
    qeInOut(f)._1
  }

  def qeInOut(f : Formula) : (Formula, String, String) = {
    val input = "Reduce[" + toMathematica(f) + ",{}, Reals" + "]"
    val (output, result) = run(input)
    if(result.isInstanceOf[Formula]) {
      (result.asInstanceOf[Formula], input, output)
    }
    else {
      throw new Exception("Expected a formula from Reduce call but got a non-formula expression.")
    }
  }
}

