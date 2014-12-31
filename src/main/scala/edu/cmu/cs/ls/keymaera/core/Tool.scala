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

import edu.cmu.cs.ls.keymaera.tools.{JLinkMathematicaLink, QETool}

/**
 * Tool instance (e.g., a specific mathematica kernel)
 */
abstract class Tool(val name: String) {

  // TODO replace with constructor and dependency injection
  def init(config : Map[String,String]) {}

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

object KeYmaera extends Tool("KeYmaera") {}

class Mathematica extends Tool("Mathematica") {
  private[core] val cricitalQE: QETool = new JLinkMathematicaLink

  // TODO replace with constructor and dependency injection
  override def init(config: Map[String,String]) = {
    val linkName = config.get("linkName") match {
      case Some(l) => l
      case None => throw new IllegalArgumentException("Missing configuration parameter 'linkName'")
    }
    cricitalQE match {
      case t: JLinkMathematicaLink => t.init(linkName)
      case _ => throw new IllegalStateException("Unknown tool")
    }
  }

  override def shutdown = {
    cricitalQE match {
      case t: JLinkMathematicaLink => t.shutdown()
      case _ => throw new IllegalStateException("Unknown tool")
    }
  }
}
