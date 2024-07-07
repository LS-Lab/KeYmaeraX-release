/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/** @note Code Review 2016-08-02 */
package org.keymaerax.tools

/**
 * Defines the lifecycle for external tools. A tool is available once init is called. It cannot be used after shutdown.
 * For intermediate restarting, use check_and_recover.
 */
trait Tool {

  /** Returns the name of the tool. */
  val name: String

  /** Checks whether this tool has been initialized already. */
  def isInitialized: Boolean

  /**
   * Check whether the managed tool is still alive and restart it if need be.
   * @requires
   *   isInitialized
   * @ensures
   *   isInitialized
   */
  def restart(): Unit

  /**
   * Shutdown the tool
   * @ensures
   *   !isInitialized
   */
  def shutdown(): Unit

  /** Cancels the current tool operation and returns true on success, false otherwise. */
  def cancel(): Boolean
}
