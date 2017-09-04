/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.bellerophon

/**
  * Provides the interpreter for running tactics.
  * @author Stefan Mitsch
  */
object BelleInterpreter extends Interpreter {
  private[this] var theInterpreter: Interpreter = _

  /** Sets a new interpreter (kills the old one). */
  def setInterpreter(i: Interpreter): Unit = {
    if (interpreter != null) kill()
    theInterpreter = i
  }

  /** Returns the interpreter. */
  def interpreter: Interpreter = theInterpreter

  /** Returns the result of applying tactic `expr` to the proof value `v` (usually a provable). */
  override def apply(expr: BelleExpr, v: BelleValue): BelleValue = interpreter(expr, v)

  /** Stops the interpreter and kills all its tactic executions. */
  override def kill(): Unit = interpreter.kill()
}
