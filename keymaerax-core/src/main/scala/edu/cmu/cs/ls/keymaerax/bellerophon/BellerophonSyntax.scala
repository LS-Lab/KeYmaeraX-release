package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.Position

/**
 * Algebraic Data Type whose elements are well-formed Bellephoron expressions.
 * See Table 1 of "Bellerophon: A Typed Language for Automated Deduction in a Uniform Substitution Calculus"
 * @author Nathan Fulton
 */
abstract class BelleExpr {
  // Syntactic sugar for combinators.
  //@todo copy documentation
  def &(other: BelleExpr)             = SeqTactic(this, other)
  def |(other: BelleExpr)             = EitherTactic(this, other)
  def *@(annotation: BelleType)       = SaturateTactic(this, annotation)
  def *(times: Int/*, annotation: BelleType*/) = RepeatTactic(this, times, null)
  def <(children: BelleExpr*)         = SeqTactic(this, BranchTactic(children))
  def U(p: (SequentType, BelleExpr)*) = SeqTactic(this, USubstPatternTactic(p))
  def partial                         = PartialTactic(this)
}

abstract case class BuiltInTactic(name: String) extends BelleExpr {
  def result(provable : Provable) : Provable
}
abstract case class BuiltInPositionTactic(name: String) extends BelleExpr {
  def applyAt(provable: Provable, pos: Position) : Provable

  def apply(pos: Position) = new BuiltInTactic(s"$name@$pos") {
    override def result(provable: Provable) = applyAt(provable, pos)
  }
}
abstract case class BuiltInLeftTactic(name: String) extends BelleExpr {
  def applyAt(provable: Provable, pos: AntePos) : Provable

  def apply(pos: AntePos) = new BuiltInTactic(s"$name@$pos") {
    override def result(provable: Provable) = applyAt(provable, pos)
  }
}
abstract case class BuiltInRightTactic(name: String) extends BelleExpr {
  def applyAt(provable: Provable, pos: SuccPos) : Provable

  def apply(pos: SuccPos) = new BuiltInTactic(s"$name@$pos") {
    override def result(provable: Provable) = applyAt(provable, pos)
  }
}
abstract case class BuiltInTwoPositionTactic(name: String) extends BelleExpr {
  def applyAt(provable : Provable, posOne: Position, posTwo: Position) : Provable
}
/**
 * Dependent tactics compute a tactic to apply based on their input.
 * These tactics are probably not necessary very often, but are useful for idiomatic shortcuts.
 * See e.g., AtSubgoal.
 * @note similar to the ConstructionTactics in the old framework, except they should not be necessary
 *       nearly as often because BuiltIns have direct access to a Provable.
 * @param name The name of the tactic.
 */
abstract case class DependentTactic(name: String) extends BelleExpr {
  def computeExpr(v : BelleValue): BelleExpr
}
abstract case class InputTactic[T](input: T) extends BelleExpr {
  def computeExpr(): BelleExpr
}

case class PartialTactic(child: BelleExpr) extends BelleExpr

case class SeqTactic(left: BelleExpr, right: BelleExpr) extends BelleExpr
case class EitherTactic(left: BelleExpr, right: BelleExpr) extends BelleExpr
//case class ExactIterTactic(child: BelleExpr, count: Int) extends BelleExpr
case class SaturateTactic(child: BelleExpr, annotation: BelleType) extends BelleExpr
case class RepeatTactic(child: BelleExpr, times: Int, annotation: BelleType) extends BelleExpr
case class BranchTactic(children: Seq[BelleExpr]) extends BelleExpr
//case class OptionalTactic(child: BelleExpr) extends BelleExpr
case class USubstPatternTactic(options: Seq[(BelleType, BelleExpr)]) extends BelleExpr

/** @todo eisegesis
  * DoAll(e)(BelleProvable(p)) == < (e, ..., e) where e occurs p.subgoals.length times.
  */
case class DoAll(e: BelleExpr) extends BelleExpr

/**
 * Bellerophon expressions that are values.
 */
abstract trait BelleValue
case class BelleProvable(p : Provable) extends BelleExpr with BelleValue

////////////////////////////////////////////////////////////////////////////////////////////////////
// Bellerophon Types
////////////////////////////////////////////////////////////////////////////////////////////////////

/** @todo eisegesis -- simple types */
abstract trait BelleType
case class TheType() extends BelleType
/** @todo Added because SequentTypes are needed for unification tactics. */
case class SequentType(s : Sequent) extends BelleType

////////////////////////////////////////////////////////////////////////////////////////////////////
// Errors
////////////////////////////////////////////////////////////////////////////////////////////////////

//@todo extend some ProverException and use the inherited inContext functionality throughout the interpreter.
case class BelleError(message: String)
  extends Exception(s"[Bellerophon Runtime] $message")

case class BelleUserGeneratedError(message: String)
  extends Exception(s"[Bellerophon User-Generated Message] $message")

class CompoundException(left: BelleError, right: BelleError)
  extends BelleError(s"Left Message: ${left.getMessage}\nRight Message: ${right.getMessage})")
