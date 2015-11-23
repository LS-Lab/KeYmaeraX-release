package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core.Provable
import edu.cmu.cs.ls.keymaerax.pt.ProofTerm

/**
 * @author Nathan Fulton
 */
trait Interpreter {
  def apply(expr: BelleExpr, v : BelleValue) : BelleValue
}

trait IOListener {
  private[bellerophon] def begin(input: BelleValue, expr: BelleExpr): Unit
  private[bellerophon] def end(input: BelleValue, expr: BelleExpr, output: BelleValue): Unit
  private[bellerophon] def kill(): Unit
}