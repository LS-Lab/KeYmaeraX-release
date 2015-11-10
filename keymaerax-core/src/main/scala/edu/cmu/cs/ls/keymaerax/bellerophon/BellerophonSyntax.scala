package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.btactics.RenUSubst
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.{AntePosition, SuccPosition, Position}

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
  def U(p: (SequentType, RenUSubst => BelleExpr)*) = SeqTactic(this, USubstPatternTactic(p))
  def partial                         = PartialTactic(this)
}

abstract case class BuiltInTactic(name: String) extends BelleExpr {
  private[bellerophon] def result(provable : Provable) : Provable
  override def toString = name
}

/** ⎵: Placeholder for tactics. Reserved tactic expression */
object BelleDot extends BelleExpr { override def toString = ">>_<<" }

////////////////////////////////////////////////////////////////////////////////////////////////////
// Positional tactics
////////////////////////////////////////////////////////////////////////////////////////////////////

/** Generalizes the built in position tactics (normal, left, right) */
trait PositionalTactic extends BelleExpr {
  /** @note this should be called from within interpreters, but not by end-users */
  def computeResult(provable: Provable, position: Position) : Provable

  /**
    * Applies a positional tactic to a position.
    * @param position The position at which this tactic should be executed.
    * @return An [[AppliedPositionTactic]] that records the tactic and where it was applied --
    *         enough information to reconstruct the effect of the tactic using computeResult,
    *         but also an internal representation of the application.
    */
  def apply(position: Position) = AppliedPositionTactic(this, position)
}

abstract case class BuiltInPositionTactic(name: String) extends PositionalTactic

abstract case class BuiltInLeftTactic(name: String) extends BelleExpr with PositionalTactic {
  override def computeResult(provable: Provable, position:Position) =
    if(position.isInstanceOf[AntePosition]) computeAnteResult(provable, position.asInstanceOf[AntePosition])
    else throw BelleError("LeftTactics can only be applied at a AntePos")

  def computeAnteResult(provable: Provable, pos: AntePosition): Provable
}

abstract case class BuiltInRightTactic(name: String) extends PositionalTactic {
  override def computeResult(provable: Provable, position:Position) =
    if(position.isInstanceOf[SuccPosition]) computeSuccResult(provable, position.asInstanceOf[SuccPosition])
    else throw BelleError("RightTactics can only be applied at a SuccPos")

  def computeSuccResult(provable: Provable, pos: SuccPosition) : Provable
}

/**
  * Stores the position tactics and position at which the tactic was applied.
  * Useful for storing execution traces.
  */
case class AppliedPositionTactic(positionTactic: BelleExpr with PositionalTactic, pos: Position) extends BelleExpr {
  def computeResult(provable: Provable) : Provable = positionTactic.computeResult(provable, pos)
}

abstract case class BuiltInTwoPositionTactic(name: String) extends BelleExpr {
  /** @note this should be called from within interpreters, but not by end users. */
  def computeResult(provable : Provable, posOne: Position, posTwo: Position) : Provable

  /** Returns an explicit representation of the application of this tactic to the provided positions. */
  def apply(posOne: Position, posTwo: Position) = AppliedTwoPositionTactic(this, posOne, posTwo)
}

/** Motivation is similar to [[AppliedPositionTactic]], but for [[BuiltInTwoPositionTactic]] */
case class AppliedTwoPositionTactic(positionTactic: BuiltInTwoPositionTactic, posOne: Position, posTwo: Position) extends BelleExpr {
  def computeResult(provable: Provable) : Provable = positionTactic.computeResult(provable, posOne, posTwo)
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
abstract case class DependentPositionTactic(name: String) extends BelleExpr {
  def apply(pos: Position) : DependentTactic
}
abstract case class InputTactic[T](input: T) extends BelleExpr {
  def computeExpr(): BelleExpr
}

/** A partial tactic is allowed to leave its subgoals around as unproved */
case class PartialTactic(child: BelleExpr) extends BelleExpr { override def toString = "partial(" + child + ")" }

case class SeqTactic(left: BelleExpr, right: BelleExpr) extends BelleExpr { override def toString = "(" + left + "&" + right + ")" }
case class EitherTactic(left: BelleExpr, right: BelleExpr) extends BelleExpr { override def toString = "(" + left + "|" + right + ")" }
//case class ExactIterTactic(child: BelleExpr, count: Int) extends BelleExpr
case class SaturateTactic(child: BelleExpr, annotation: BelleType) extends BelleExpr { override def toString = "(" + child + ")*" }
case class RepeatTactic(child: BelleExpr, times: Int, annotation: BelleType) extends BelleExpr { override def toString = "(" + child + ")*" + times }
case class BranchTactic(children: Seq[BelleExpr]) extends BelleExpr { override def toString = "<(" + children.mkString(",") + ")" }
//case class OptionalTactic(child: BelleExpr) extends BelleExpr
case class USubstPatternTactic(options: Seq[(BelleType, RenUSubst => BelleExpr)]) extends BelleExpr

/** @todo eisegesis
  * DoAll(e)(BelleProvable(p)) == < (e, ..., e) where e occurs p.subgoals.length times.
  */
case class DoAll(e: BelleExpr) extends BelleExpr




/**
 * Bellerophon expressions that are values.
 */
abstract trait BelleValue {
  def prettyString: String = toString
}
case class BelleProvable(p : Provable) extends BelleExpr with BelleValue {
  override def toString: String = p.prettyString
}

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
class BelleError(message: String)
  extends ProverException(s"[Bellerophon Runtime] $message") {
  /* @note mutable state for gathering the logical context that led to this exception */
  private var tacticContext: BelleExpr = BelleDot  //@todo BelleUnknown?
  def context: BelleExpr = tacticContext
  def inContext(context: BelleExpr): BelleError = {
    this.tacticContext = context
    this
  }
  override def toString: String = super.toString + "\nin " + tacticContext
}
object BelleError {
  def apply(message: String) = new BelleError(message)
}

case class BelleUserGeneratedError(message: String)
  extends Exception(s"[Bellerophon User-Generated Message] $message")

class CompoundException(left: BelleError, right: BelleError)
  extends BelleError(s"Left Message: ${left.getMessage}\nRight Message: ${right.getMessage})")

////////////////////////////////////////////////////////////////////////////////////////////////////
// Errors
////////////////////////////////////////////////////////////////////////////////////////////////////


///**
//  * Abstract positions are either actual positions, or else indicate that the tactic should point back to a position
//  * that was generated by a previous tactic.
//  *
//  * Example:
//  * {{{
//  *   AndR(SuccPos(2)) <(
//  *     ImplyR(GeneratedPosition()) & TrivialCloser,
//  *     ImplyR(GeneratedPosition()) & TrivialCloser
//  *   )
//  * }}}
//  *
//  * is equivalent to:
//  *
//  * {{{
//  *   AndR(SuccPos(2)) <(
//  *     ImplyR(SuccPos(2)) & ...,
//  *     ImplyR(SuccPos(2)) & ...
//  *   )
//  * }}}
//  *
//  * @todo Not currently using these; one thing at at a time.
//  */
//sealed trait AbstractPosition
//case class AbsolutePosition(p : Position) extends AbstractPosition
//case class GeneratedPosition()              extends AbstractPosition