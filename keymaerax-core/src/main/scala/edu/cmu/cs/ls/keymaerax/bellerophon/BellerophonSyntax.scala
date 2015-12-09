package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.{AntePosition, SuccPosition, Position, PosInExpr}

import scala.collection.immutable

/**
 * Algebraic Data Type whose elements are well-formed Bellephoron expressions.
 * See Table 1 of "Bellerophon: A Typed Language for Automated Deduction in a Uniform Substitution Calculus"
 * @author Nathan Fulton
 */
abstract class BelleExpr(val location: Array[StackTraceElement] = Thread.currentThread().getStackTrace) {
  // Syntactic sugar for combinators.
  //@todo copy documentation
  def &(other: BelleExpr)             = SeqTactic(this, other)
  def |(other: BelleExpr)             = EitherTactic(this, other)
  def *@(annotation: BelleType)       = SaturateTactic(this, annotation)
  def *(times: Int/*, annotation: BelleType*/) = RepeatTactic(this, times, null)
  def <(children: BelleExpr*)         = SeqTactic(this, BranchTactic(children))
  def U(p: (SequentType, RenUSubst => BelleExpr)*) = SeqTactic(this, USubstPatternTactic(p))
  def partial                         = PartialTactic(this)

  override def toString: String = prettyString
  /** pretty-printed form of this Bellerophon expression */
  def prettyString: String
}

abstract case class BuiltInTactic(name: String) extends BelleExpr {
  private[bellerophon] final def execute(provable: Provable): Provable = try {
    result(provable)
  } catch {
    case be: BelleError => throw be
    case t: Throwable => throw new BelleError(t.getMessage, t)
  }
  private[bellerophon] def result(provable : Provable): Provable
  override def prettyString = name
}

/** ⎵: Placeholder for tactics. Reserved tactic expression */
object BelleDot extends BelleExpr { override def prettyString = ">>_<<" }

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
  def apply(position: Position): AppliedPositionTactic = apply(Fixed(position))
  def apply(seqIdx: Int, inExpr: List[Int] = Nil): AppliedPositionTactic = apply(PositionConverter.convertPos(seqIdx, inExpr))
  def apply(locator: Symbol): AppliedPositionTactic = locator match {
    case 'la => apply(FindAnte())
    case 'ls => apply(FindSucc())
  }
  def apply(locator: PositionLocator): AppliedPositionTactic = AppliedPositionTactic(this, locator)
}

abstract case class BuiltInPositionTactic(name: String) extends PositionalTactic {override def prettyString = name}

abstract case class BuiltInLeftTactic(name: String) extends BelleExpr with PositionalTactic {
  override def computeResult(provable: Provable, position:Position) = position match {
    case p: AntePosition => computeAnteResult(provable, p)
    case _ => throw new BelleError("LeftTactics can only be applied at a AntePos")
  }

  def computeAnteResult(provable: Provable, pos: AntePosition): Provable

  override def prettyString = name

}

abstract case class BuiltInRightTactic(name: String) extends PositionalTactic {
  override def computeResult(provable: Provable, position:Position) = position match {
    case p: SuccPosition => computeSuccResult(provable, p)
    case _ => throw new BelleError("RightTactics can only be applied at a SuccPos")
  }

  def computeSuccResult(provable: Provable, pos: SuccPosition) : Provable

  override def prettyString = name
}

/**
  * Stores the position tactic and position at which the tactic was applied.
  * Useful for storing execution traces.
  */
case class AppliedPositionTactic(positionTactic: BelleExpr with PositionalTactic, locator: PositionLocator) extends BelleExpr {
  def computeResult(provable: Provable) : Provable = locator match {
    case Fixed(pos) => positionTactic.computeResult(provable, pos)
    case FindAnte(goal, start) =>
      require(provable.subgoals(goal).ante.nonEmpty, "Antecedent must be non-empty")
      tryAllAfter(provable, goal, start, null)
    case FindSucc(goal, start) =>
      require(provable.subgoals(goal).succ.nonEmpty, "Succedent must be non-empty")
      tryAllAfter(provable, goal, start, null)
  }

  /** Recursively tries the position tactic at positions at or after pos in the specified provable. */
  private def tryAllAfter(provable: Provable, goal: Int, pos: Position, cause: BelleError): Provable =
    if (pos.isIndexDefined(provable.subgoals(goal))) {
      try {
        positionTactic.computeResult(provable, pos)
      } catch {
        case e: Throwable =>
          val newCause = if (cause == null) new BelleError(s"Position tactic ${positionTactic.prettyString} is not " +
            s"applicable at ${pos.prettyString}", e)
          else new CompoundException(
            new BelleError(s"Position tactic ${positionTactic.prettyString} is not applicable at ${pos.prettyString}", e),
            cause)
          tryAllAfter(provable, goal, pos+1, newCause)
      }
    } else throw cause

  override def prettyString = positionTactic.prettyString + "(" + locator.prettyString + ")"
}

abstract case class BuiltInTwoPositionTactic(name: String) extends BelleExpr {
  /** @note this should be called from within interpreters, but not by end users. */
  def computeResult(provable : Provable, posOne: Position, posTwo: Position) : Provable

  /** Returns an explicit representation of the application of this tactic to the provided positions. */
  def apply(posOne: Position, posTwo: Position) = AppliedTwoPositionTactic(this, posOne, posTwo)

  override def prettyString = name
}

/** Motivation is similar to [[AppliedPositionTactic]], but for [[BuiltInTwoPositionTactic]] */
case class AppliedTwoPositionTactic(positionTactic: BuiltInTwoPositionTactic, posOne: Position, posTwo: Position) extends BelleExpr {
  def computeResult(provable: Provable) : Provable = positionTactic.computeResult(provable, posOne, posTwo)

  override def prettyString = positionTactic.prettyString + "(" + posOne.prettyString + "," + posTwo.prettyString + ")"
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
  override def prettyString: String = "DependentTactic(" + name + ")"
}
abstract case class DependentPositionTactic(name: String) extends BelleExpr {
  def apply(pos: Position) : DependentTactic
  def apply(seqIdx: Int, inExpr: List[Int] = Nil): DependentTactic = apply(PositionConverter.convertPos(seqIdx, inExpr))
  override def prettyString: String = "DependentPositionTactic(" + name + ")"
}
abstract case class InputTactic[T](input: T) extends BelleExpr {
  def computeExpr(): BelleExpr
  override def prettyString: String = "input(" + input + ")"
}

/** A partial tactic is allowed to leave its subgoals around as unproved */
case class PartialTactic(child: BelleExpr) extends BelleExpr { override def prettyString = "partial(" + child.prettyString + ")" }

case class SeqTactic(left: BelleExpr, right: BelleExpr, override val location: Array[StackTraceElement] = Thread.currentThread().getStackTrace) extends BelleExpr { override def prettyString = "(" + left.prettyString + "&" + right.prettyString + ")" }
case class EitherTactic(left: BelleExpr, right: BelleExpr, override val location: Array[StackTraceElement] = Thread.currentThread().getStackTrace) extends BelleExpr { override def prettyString = "(" + left.prettyString + "|" + right.prettyString + ")" }
//case class ExactIterTactic(child: BelleExpr, count: Int) extends BelleExpr
case class SaturateTactic(child: BelleExpr, annotation: BelleType, override val location: Array[StackTraceElement] = Thread.currentThread().getStackTrace) extends BelleExpr { override def prettyString = "(" + child.prettyString + ")*" }
case class RepeatTactic(child: BelleExpr, times: Int, annotation: BelleType, override val location: Array[StackTraceElement] = Thread.currentThread().getStackTrace) extends BelleExpr { override def prettyString = "(" + child.prettyString + ")*" + times }
case class BranchTactic(children: Seq[BelleExpr], override val location: Array[StackTraceElement] = Thread.currentThread().getStackTrace) extends BelleExpr { override def prettyString = "<( " + children.map(_.prettyString).mkString(", ") + " )" }
//case class OptionalTactic(child: BelleExpr) extends BelleExpr
case class USubstPatternTactic(options: Seq[(BelleType, RenUSubst => BelleExpr)], override val location: Array[StackTraceElement] = Thread.currentThread().getStackTrace) extends BelleExpr { override def prettyString = "case { " + options.mkString(", ") + " }"}

/** @todo eisegesis
  * DoAll(e)(BelleProvable(p)) == < (e, ..., e) where e occurs p.subgoals.length times.
  */
case class DoAll(e: BelleExpr, override val location: Array[StackTraceElement] = Thread.currentThread().getStackTrace) extends BelleExpr { override def prettyString = "doall(" + e.prettyString + ")" }




/**
 * Bellerophon expressions that are values.
 */
trait BelleValue {
  def prettyString: String = toString
}
case class BelleProvable(p : Provable) extends BelleExpr with BelleValue {
  override def toString: String = p.prettyString
  override def prettyString: String = p.prettyString
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Bellerophon Types
////////////////////////////////////////////////////////////////////////////////////////////////////

/** @todo eisegesis -- simple types */
trait BelleType
case class TheType() extends BelleType
/** @todo Added because SequentTypes are needed for unification tactics. */
case class SequentType(s : Sequent) extends BelleType

////////////////////////////////////////////////////////////////////////////////////////////////////
// Errors
////////////////////////////////////////////////////////////////////////////////////////////////////

//@todo extend some ProverException and use the inherited inContext functionality throughout the interpreter.
class BelleError(message: String, cause: Throwable = null)
    extends ProverException(s"[Bellerophon Runtime] $message", if (cause != null) cause else new Throwable(message)) {
  /* @note mutable state for gathering the logical context that led to this exception */
  private var tacticContext: BelleExpr = BelleDot  //@todo BelleUnknown?
  def context: BelleExpr = tacticContext
  def inContext(context: BelleExpr, additionalMessage: String): BelleError = {
    this.tacticContext = context
    context.location.find(e => !("Thread.java"::"BellerophonSyntax.scala"::"SequentialInterpreter.scala"::Nil).contains(e.getFileName)) match {
      case Some(location) => getCause.setStackTrace(location +: getCause.getStackTrace)
      case None => // no specific stack trace element outside the tactic framework found -> nothing to do
    }
    super.inContext(context.prettyString, additionalMessage)
    this
  }
  override def toString: String = super.toString + "\nin " + tacticContext
}

case class BelleUserGeneratedError(message: String)
  extends Exception(s"[Bellerophon User-Generated Message] $message")

class CompoundException(left: BelleError, right: BelleError)
  extends BelleError(s"Left Message: ${left.getMessage}\nRight Message: ${right.getMessage})")

object PositionConverter {
  def convertPos(seqIdx: Int, inExpr: List[Int] = Nil): Position = {
    require(seqIdx != 0, "Sequent index must be strictly negative (antecedent) or strictly positive (succedent)")
    if (seqIdx < 0) new AntePosition(-seqIdx - 1, PosInExpr(inExpr))
    else new SuccPosition(seqIdx - 1, PosInExpr(inExpr))
  }
}

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