/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.tools

/** Base trait tagging interfaces to tools. */
trait ToolInterface

/** Manages how a tool's operations work (e.g., timeouts). */
trait ToolOperationManagement extends ToolInterface {

  /** Sets a maximum duration of this tool's operations (e.g., QE). */
  def setOperationTimeout(timeout: Int): Unit

  /** Returns the timeout duration. */
  def getOperationTimeout: Int

  def getAvailableWorkers: Int
}

/** Base class for tool operation management */
abstract class ToolOperationManagementBase extends ToolOperationManagement {
  private var timeout = -1

  /** Sets a maximum duration of this tool's operations (e.g., QE). */
  override def setOperationTimeout(timeout: Int): Unit = this.timeout = timeout

  /** Returns the timeout duration. */
  override def getOperationTimeout: Int = timeout
}
