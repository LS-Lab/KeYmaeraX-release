/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * @note Code Review 2016-08-02
  */
package edu.cmu.cs.ls.keymaerax.tools

import scala.collection.immutable.Map

/**
 * Defines the lifecycle for external tools. A tool is available once init is called.
 * It cannot be used after shutdown. For intermediate restarting, use check_and_recover.
 */
trait Tool {
  /**
    * Returns the name of the tool.
    */
  val name: String

  /**
   * Initializes the tool with tool-specific configuration parameters.
   * @ensures isInitialized
   */
  def init(config : Map[String,String])

  /** Checks whether this tool has been initialized already. */
  def isInitialized: Boolean

  /**
   * Check whether the managed tool is still alive and restart it if need be.
   * @requires isInitialized
   * @ensures isInitialized
   */
  def restart()

  /**
   * Shutdown the tool
   * @ensures !isInitialized
   */
  def shutdown()

}
