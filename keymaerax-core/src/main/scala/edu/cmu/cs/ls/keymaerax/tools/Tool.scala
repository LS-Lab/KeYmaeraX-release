package edu.cmu.cs.ls.keymaerax.tools

import scala.collection.immutable.Map

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
