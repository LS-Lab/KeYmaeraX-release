/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, SaturateTactic}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.Variable
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
 * Tactics for real arithmetic.
 *
 * @author
 *   Stefan Mitsch
 */
object ArithmeticLibrary {

  // Atomic QE splitters

  /** Maximum splitting */
  lazy val exhaustivePropositional: BelleExpr = SaturateTactic(onAll(alphaRule | betaRule))

  /** Maximum splitting of top-level branching operators */
  lazy val exhaustiveBeta: BelleExpr = SaturateTactic(onAll(betaRule))

  /** Splits on the left-hand side if it results in lower number of variables */
  lazy val varEliminationLeft: BelleExpr = SaturateTactic(alphaRule) & SaturateTactic(onAll(
    orL(Symbol("Llike"), "x=f_(|x|) | x=g_(|x|)".asFormula) | // top-level case distinction
      orL(Symbol("Llike"), "p_()&x=f_(|x|) | q_()&x=g_(|x|)".asFormula) // case for min/max/abs expansion
  ))

  /** Splits on the left-hand side to eliminate a specific variable */
  def varEliminationLeft(x: Variable): BelleExpr = SaturateTactic(alphaRule) &
    orL(Symbol("Llike"), s"$x=f_(|$x|) | $x=g_(|$x|)".asFormula) // top-level case distinction

}
