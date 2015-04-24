/**
 * Infrastructure for external tools
 *
 * - part of core because some rules invoke external tools to do
 *   their computation
 * - invoking an external tool blocks; the rule invoking tactics
 *   should therefore be dispatched to a corresponding thread for
 *   this tool's scheduler.
 */

package edu.cmu.cs.ls.keymaera.core

// require favoring immutable Seqs for soundness

import scala.collection.immutable.Seq
import scala.collection.immutable.IndexedSeq

import scala.collection.immutable.List
import scala.collection.immutable.Map
import scala.collection.immutable.SortedSet
import scala.collection.immutable.Set

import edu.cmu.cs.ls.keymaera.tools._

/**
 * Defines the lifecycle for external tools. A tool is available once init is called.
 * It cannot be used after shutdown. For intermediate restarting, use check_and_recover.
 */
trait Tool {
  // TODO replace with constructor in tool base and dependency injection
  /**
   * Initializes the tool.
   * @param config The tool configuration.
   */
  def init(config : Map[String,String])

  def isInitialized: Boolean

  /**
   * Check whether the managed tool is still alive and recover it if not.
   * Yes, this is the mathematica kernel dies on interrupt fix-up!
   */
  def check_and_recover()

  /**
   * Shutdown the tool
   */
  def shutdown()

  /**
   * The name of the tool.
   * @return The tool name.
   */
  def name: String
}

/**
 * Base class for tool instances (e.g., a specific mathematica kernel)
 */
abstract class ToolBase(val name: String) extends Tool {

  protected var initialized = false

  def init(config : Map[String,String]) { initialized = true }

  def isInitialized: Boolean = initialized

  /**
   * Check whether the managed tool is still alive and recover it if not.
   * Yes, this is the mathematica kernel dies on interrupt fix-up!
   */
  def check_and_recover() {}

  /**
   * Shutdown the tool
   */
  def shutdown() {}

}

object KeYmaera extends ToolBase("KeYmaera") {}

class Mathematica extends ToolBase("Mathematica") {
  //@TODO illegal access to out of core. Fix!
  private val jlink = new JLinkMathematicaLink
  //@TODO illegal access to out of core. Fix!
  private[core] val cricitalQE: QETool = jlink
  val diffSolver: DiffSolutionTool = jlink

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
}

class Z3 extends ToolBase("Z3") {
  private val z3 = new Z3Solver
  private[core] val cricitalQE: QETool = z3
}

class Polya extends ToolBase("Polya") {
  private val polya = new PolyaSolver
  private[core] val cricitalQE: QETool = polya
}
