package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core.{Provable, Formula}
import edu.cmu.cs.ls.keymaerax.pt.ProofTerm

/**
 * Algebraic Data Type whose elements are well-formed Bellephoron expressions.
 * See Table 1 of "Bellerophon: A Typed Language for Automated Deduction in a Uniform Substitution Calculus"
 * @author Nathan Fulton
 */
abstract class BelleExpr
abstract case class BuiltInTactic() extends BelleExpr {
  def apply(provable : Provable) : Seq[Provable]

  /**
   * Constructs a proof term for the provable.
   * @param provable The provable at which this tactic should be applied
   * @return A list of resulting subgoals and a function that maps a list of proof terms for these to a proof for the input provable.
   */
  def pt(provable: Provable) : (Seq[Provable], Seq[ProofTerm] => ProofTerm)
}
case class SeqTactic(left: BelleExpr, right: BelleExpr) extends BelleExpr
case class EitherTactic(left: BelleExpr, right: BelleExpr) extends BelleExpr
case class ParallelTactic(left: BelleExpr, right: BelleExpr) extends BelleExpr
case class ExactIterTactic(child: BelleExpr, count: Int) extends BelleExpr
case class SaturateTactic(child: BelleExpr, annotation: BelleType) extends BelleExpr
case class BranchTactic(children: Seq[BelleExpr]) extends BelleExpr
case class OptionalTactic(child: BelleExpr) extends BelleExpr
case class USubstPatternTactic(options: Seq[(BelleType, BelleExpr)]) extends BelleExpr
case class ParametricTactic(t: BelleTypeVariable, child: BelleExpr) extends BelleExpr
case class ParaAppTactic(fn : ParametricTactic, arg: BelleType) extends BelleExpr
case class ProductProjection(left: BelleExpr, right: BelleExpr) extends BelleExpr

abstract trait BelleValue
case class BelleProvable(p : Provable) extends BelleExpr with BelleValue
case class LeftResult(vs: Seq[BelleValue]) extends BelleExpr with BelleValue
case class RightResult(vs: Seq[BelleValue]) extends BelleExpr  with BelleValue


/**
 * @todo incomplete.
 */
abstract class BelleType
case class BelleTypeVariable(name: String) extends BelleType


case class BelleError(message: String)
  extends Exception(s"[Bellerophon Runtime] $message")

class CompoundException(left: BelleError, right: BelleError)
  extends BelleError(s"Left Message: ${left.getMessage}\nRight Message: ${right.getMessage})")