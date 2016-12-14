package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.Variable
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/** Tactics for real arithmetic.
  *
  * @author Stefan Mitsch
  */
object ArithmeticLibrary {

  // Atomic QE splitters

  /** Maximum splitting */
  lazy val exhaustivePropositional: BelleExpr = onAll(alphaRule | betaRule)*
  /** Maximum splitting of top-level branching operators */
  lazy val exhaustiveBeta: BelleExpr = onAll(betaRule)*
  /** Splits on the left-hand side if it results in lower number of variables */
  lazy val varEliminationLeft: BelleExpr = (alphaRule*) & (onAll(
    orL('Llike, "x=f_(|x|) | x=g_(|x|)".asFormula) |         // top-level case distinction
    orL('Llike, "p_()&x=f_(|x|) | q_()&x=g_(|x|)".asFormula) // case for min/max/abs expansion
  )*)
  /** Splits on the left-hand side to eliminate a specific variable */
  def varEliminationLeft(x: Variable): BelleExpr = (alphaRule*) &
    orL('Llike, s"$x=f_(|$x|) | $x=g_(|$x|)".asFormula)         // top-level case distinction

}
