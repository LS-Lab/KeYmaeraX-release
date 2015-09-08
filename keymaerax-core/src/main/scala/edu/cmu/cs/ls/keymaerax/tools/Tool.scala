/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tools

import scala.collection.immutable.Map

/**
 * Defines the lifecycle for external tools. A tool is available once init is called.
 * It cannot be used after shutdown. For intermediate restarting, use check_and_recover.
 */
trait Tool {
  // TODO replace with constructor in tool base and dependency injection
  /**
   * Initializes the tool with tool-specific configuration parameters.
   */
  def init(config : Map[String,String])

  def isInitialized: Boolean

  /**
   * Check whether the managed tool is still alive and restart it if need be.
   */
  def restart()

  /**
   * Shutdown the tool
   */
  def shutdown()

  /**
   * Returns the name of the tool.
   */
  def name: String
}
