package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.pt.ProofTerm
import edu.cmu.cs.ls.keymaerax.tactics.SuccPosition

/**
 * Algebraic Data Type whose elements are well-formed Bellephoron expressions.
 * See Table 1 of "Bellerophon: A Typed Language for Automated Deduction in a Uniform Substitution Calculus"
 * @author Nathan Fulton
 */
abstract class BelleExpr {
  // Syntactic sugar for combinators.
  def &(other: BelleExpr)      = SeqTactic(this, other)
  def |(other: BelleExpr)      = EitherTactic(this, other)
  def *(annotation: BelleType) = SaturateTactic(this, annotation)
}

abstract case class BuiltInTactic(name: String) extends BelleExpr {
  def apply(provable : Provable) : Provable
}
abstract case class BuiltInPositionTactic(name: String) extends BelleExpr {
  def applyAt(provable: Provable, pos: SeqPos) : Provable

  def apply(pos: SeqPos) = new BuiltInTactic(s"$name@$pos") {
    override def apply(provable: Provable) = applyAt(provable, pos)
  }
}
abstract case class BuiltInLeftTactic(name: String) extends BelleExpr {
  def applyAt(provable: Provable, pos: AntePos) : Provable

  def apply(pos: AntePos) = new BuiltInTactic(s"$name@$pos") {
    override def apply(provable: Provable) = applyAt(provable, pos)
  }
}
abstract case class BuiltInRightTactic(name: String) extends BelleExpr {
  def applyAt(provable: Provable, pos: SuccPos) : Provable

  def apply(pos: SuccPos) = new BuiltInTactic(s"$name@$pos") {
    override def apply(provable: Provable) = applyAt(provable, pos)
  }
}
abstract case class BuiltInTwoPositionTactic(name: String) extends BelleExpr {
  def applyAt(provable : Provable, posOne: SeqPos, posTwo: SeqPos) : Provable
}

case class SeqTactic(left: BelleExpr, right: BelleExpr) extends BelleExpr
case class EitherTactic(left: BelleExpr, right: BelleExpr) extends BelleExpr
case class ExactIterTactic(child: BelleExpr, count: Int) extends BelleExpr
case class SaturateTactic(child: BelleExpr, annotation: BelleType) extends BelleExpr
case class BranchTactic(children: Seq[BelleExpr]) extends BelleExpr
//case class OptionalTactic(child: BelleExpr) extends BelleExpr
case class USubstPatternTactic(options: Seq[(BelleType, BelleExpr)]) extends BelleExpr

/** @todo eisegesis */
case class Map(e: BelleExpr) extends BelleExpr

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

////////////////////////////////////////////////////////////////////////////////////////////////////
// Errors
////////////////////////////////////////////////////////////////////////////////////////////////////

case class BelleError(message: String)
  extends Exception(s"[Bellerophon Runtime] $message")

class CompoundException(left: BelleError, right: BelleError)
  extends BelleError(s"Left Message: ${left.getMessage}\nRight Message: ${right.getMessage})")