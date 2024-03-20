/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.bellerophon

/**
 * Provides the interpreter for running tactics.
 * @author
 *   Stefan Mitsch
 */
object BelleInterpreter extends Interpreter {
  private[this] var theInterpreter: Interpreter = _

  /** Unsets the interpreter, killing it in the process. */
  def unsetInterpreter(): Unit = {
    if (theInterpreter != null) kill()
    theInterpreter = null
  }

  /** Sets a new interpreter (kills the old one). */
  def setInterpreter(i: Interpreter): Unit = {
    unsetInterpreter()
    theInterpreter = i
    start()
  }

  /** Returns the interpreter. */
  def interpreter: Interpreter = theInterpreter

  /** Starts the interpreter. */
  override def start(): Unit = interpreter.start()

  /** Returns the result of applying tactic `expr` to the proof value `v` (usually a provable). */
  override def apply(expr: BelleExpr, v: BelleValue): BelleValue = interpreter(expr, v)

  /** Stops the interpreter and kills all its tactic executions. */
  override def kill(): Unit = interpreter.kill()

  /** Indicates whether the interpreter is still operational. A killed interpreter refuses to run tactics. */
  override def isDead: Boolean = interpreter.isDead

  /** Registered listeners. */
  override def listeners: scala.collection.immutable.Seq[IOListener] = interpreter.listeners
}
