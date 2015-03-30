package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core._

/**
 * Created by smitsch on 3/29/15.
 * @author Stefan Mitsch
 */
sealed case class Context(ctx: Formula) {
  def apply(f: Formula) = instantiate(f)

  /**
   * Instantiates the context fml with the formula withF
   * @param withF The formula to instantiate context fml with.
   * @return The instantiated context.
   */
  def instantiate(withF: Formula): Formula = {
    val context = Function("dottingC__", None, Bool, Bool)//@TODO eisegesis  should be Function("dottingC__", None, Real->Bool, Bool) //@TODO introduce function types or the Predicational datatype
    USubst(SubstitutionPair(ApplyPredicational(context, CDotFormula), ctx) :: Nil)(ApplyPredicational(context, withF))
  }
}
