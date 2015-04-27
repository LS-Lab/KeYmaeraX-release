package edu.cmu.cs.ls.keymaera.tools

import scala.collection.immutable.Map

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
