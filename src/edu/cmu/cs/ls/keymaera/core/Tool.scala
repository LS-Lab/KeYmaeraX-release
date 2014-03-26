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

/**
 * Tool instance (e.g., mathematica kernel)
 */

abstract class Tool {

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

object KeYmaera extends Tool {
}
