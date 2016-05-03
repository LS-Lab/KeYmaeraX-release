package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core.Provable

/**
  * Interpreter for Bellerophon tactic expressions that transforms [[BelleValue Bellerophon values]] using
  * [[BelleExpr Bellerophon tactic language expressions]] to ultimately produce [[Provable]].
  * {{{
  *   Interpreter : BelleExpr * BelleValue => BelleValue
  * }}}
  * @author Nathan Fulton
  * @see [[SequentialInterpreter]]
  */
trait Interpreter {
  def apply(expr: BelleExpr, v : BelleValue) : BelleValue
}

/**
  * Listeners for input/output results during the [[Interpreter interpretation]] of Bellerophon tactic expressions.
  */
trait IOListener {
  def begin(input: BelleValue, expr: BelleExpr): Unit
  def end(input: BelleValue, expr: BelleExpr, output: Either[BelleValue,BelleError]): Unit
  def kill(): Unit
}