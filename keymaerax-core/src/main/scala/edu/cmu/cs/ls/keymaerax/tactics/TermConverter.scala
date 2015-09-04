/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction, TraverseToPosition}
import edu.cmu.cs.ls.keymaerax.core._

/**
 * Additional implicit functions defined for sequents when imported.
 * @author Andre Platzer
 */
@deprecated("Use TermAugmentor instead")
object TermConverter {
  import scala.language.implicitConversions
  implicit def TermToTermConverter(t: Term): TermConverter = new TermConverter(t)
}
@deprecated("Use TermAugmentor instead")
class TermConverter(val trm: Term) {
  //@todo this is a hack implementation
  def apply(pos: PosInExpr): Term = new FormulaConverter(Equal(trm,Number(99))).apply(PosInExpr(0::Nil).append(pos)).asInstanceOf[Term]
}
