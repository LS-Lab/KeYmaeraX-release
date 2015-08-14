/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.core.StaticSemantics.signature

/**
 * Convenience wrapper around contexts such as f(.) or p(.) or C{_} etc
 * Created by smitsch on 3/29/15.
 * @author Stefan Mitsch
 */
sealed case class Context[+T <: Expression](ctx: T) {
  // either a term or a formula context, not both
  assert(!(signature(ctx).contains(DotFormula) && signature(ctx).contains(DotTerm)))

  /** Return the result of filling the dot placeholder of this context with expression e */
  def apply(e: Expression) = e match {
    case f: Formula => instantiate(f)
    case t: Term => instantiate(t)
  }

  def isFormulaContext = signature(ctx).contains(DotFormula)
  def isTermContext = signature(ctx).contains(DotTerm)

  /**
   * Instantiates the context fml with the formula withF
   * @param withF The formula to instantiate context fml with.
   * @return The instantiated context.
   */
  def instantiate(withF: Formula): Formula = {
    val context = Function("dottingC_", None, Bool, Bool)//@TODO eisegesis  should be Function("dottingC_", None, Real->Bool, Bool) //@TODO introduce function types or the Predicational datatype
    USubst(SubstitutionPair(PredicationalOf(context, DotFormula), ctx) :: Nil)(PredicationalOf(context, withF))
  }

  /**
   * Instantiates the context fml with the term withT
   * @param withT The term to instantiate context fml with.
   * @return The instantiated context.
   */
  def instantiate(withT: Term): Formula = {
    val context = Function("dottingC_", None, Real, Bool)
    USubst(SubstitutionPair(PredOf(context, DotTerm), ctx) :: Nil)(PredOf(context, withT))
  }
}
