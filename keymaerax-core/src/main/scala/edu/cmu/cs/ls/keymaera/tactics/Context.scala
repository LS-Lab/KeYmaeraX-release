package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.core.StaticSemantics.signature

/**
 * Created by smitsch on 3/29/15.
 * @author Stefan Mitsch
 */
sealed case class Context(ctx: Formula) {
  // either a term or a formula context, not both
  assert(!(signature(ctx).contains(CDotFormula) && signature(ctx).contains(CDot)))

  def apply(e: Expr) = e match {
    case f: Formula => instantiate(f)
    case t: Term => instantiate(t)
  }

  def isFormulaContext = signature(ctx).contains(CDotFormula)
  def isTermContext = signature(ctx).contains(CDot)

  /**
   * Instantiates the context fml with the formula withF
   * @param withF The formula to instantiate context fml with.
   * @return The instantiated context.
   */
  def instantiate(withF: Formula): Formula = {
    val context = Function("dottingC__", None, Bool, Bool)//@TODO eisegesis  should be Function("dottingC__", None, Real->Bool, Bool) //@TODO introduce function types or the Predicational datatype
    USubst(SubstitutionPair(ApplyPredicational(context, CDotFormula), ctx) :: Nil)(ApplyPredicational(context, withF))
  }

  /**
   * Instantiates the context fml with the term withT
   * @param withT The term to instantiate context fml with.
   * @return The instantiated context.
   */
  def instantiate(withT: Term): Formula = {
    val context = Function("dottingC__", None, Real, Bool)
    USubst(SubstitutionPair(ApplyPredicate(context, CDot), ctx) :: Nil)(ApplyPredicate(context, withT))
  }
}
