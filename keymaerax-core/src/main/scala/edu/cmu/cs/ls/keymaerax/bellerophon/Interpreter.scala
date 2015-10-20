package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core.Provable
import edu.cmu.cs.ls.keymaerax.pt.ProofTerm

/**
 * Created by nfulton on 10/20/15.
 */
trait Interpreter {
  def apply(expr: BelleExpr, values: Seq[BelleValue]) : Seq[BelleValue]
}