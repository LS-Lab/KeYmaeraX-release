package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core.Provable
import edu.cmu.cs.ls.keymaerax.pt.ProofTerm

/**
 * @author Nathan Fulton
 */
trait Interpreter {
  def apply(expr: BelleExpr, v : BelleValue) : BelleValue
}