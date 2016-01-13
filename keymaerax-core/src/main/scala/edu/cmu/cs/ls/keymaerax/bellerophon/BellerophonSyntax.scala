/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.btactics.Augmentors
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.SerializationNames.SerializationName

object BelleExpr {
  private[keymaerax] val DEBUG = System.getProperty("DEBUG", "false")=="true"
}

/**
 * Algebraic Data Type whose elements are well-formed Bellephoron tactic expressions.
 * See Table 1 of "Bellerophon: A Typed Language for Automated Deduction in a Uniform Substitution Calculus"
 * @author Nathan Fulton
 * @see [[edu.cmu.cs.ls.keymaerax.bellerophon.SequentialInterpreter]]
 * @see [[edu.cmu.cs.ls.keymaerax.bellerophon]]
 */
abstract class BelleExpr(val location: Array[StackTraceElement] = Thread.currentThread().getStackTrace) {
  private[keymaerax] val DEBUG = BelleExpr.DEBUG
  // tactic combinators

  /** this & other: sequential composition executes other on the output of this, failing if either fail. */
  def &(other: BelleExpr)             = SeqTactic(this, other)
  /** this | other: alternative composition executes other if applying this fails, failing if both fail. */
  def |(other: BelleExpr)             = EitherTactic(this, other)
  /** this*: saturating repetition executes this tactic to a fixpoint, casting result to type annotation, diverging if no fixpoint. */
  def *@(annotation: BelleType)       = SaturateTactic(this, annotation)
  /** this+: saturating repetition executes this tactic to a fixpoint, requires at least one successful application */
  def +@(annotation: BelleType) = this & (this*@annotation)
  /** this*: bounded repetition executes this tactic to `times` number of times, failing if any of those repetitions fail. */
  def *(times: Int/*, annotation: BelleType*/) = RepeatTactic(this, times, null)
  /** <(e1,...,en): branching to run tactic `ei` on branch `i`, failing if any of them fail or if there are not exactly `n` branches. */
  def <(children: BelleExpr*)         = SeqTactic(this, BranchTactic(children))
  /** case _ of {fi => ei} uniform substitution case pattern applies the first ei such that fi uniformly substitutes to current provable for which ei does not fail, fails if the ei of all matching fi fail. */
  def U(p: (SequentType, RenUSubst => BelleExpr)*) = SeqTactic(this, USubstPatternTactic(p))
  /** partial: marks a tactic that is allowed to not close all its goals. */
  def partial                         = PartialTactic(this)
  //@todo Maybe support ?(e) or try(e) or optional(e) defined as this|skip

  override def toString: String = prettyString
  /** pretty-printed form of this Bellerophon tactic expression */
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
case class NamedTactic(name: String, tactic: BelleExpr) extends BelleExpr { override def prettyString = name }

/** ⎵: Placeholder for tactics. Reserved tactic expression */
object BelleDot extends BelleExpr { override def prettyString = ">>_<<" }

////////////////////////////////////////////////////////////////////////////////////////////////////
// Positional tactics
////////////////////////////////////////////////////////////////////////////////////////////////////

/** Applied at a position, AtPosition turns into a tactic of type T. Turns a position or position locator into a tactic.
  * That is, an AtPosition[T] tactic is essentially a function of type
  * {{{
  *   Position => T
  * }}}
  * but one that also supports indirect positioning via position locators that merely identify positions
  * {{{
  *   PositionLocator => T
  * }}}
  *
  * An AtPosition tactic `t` supports [[Position direct positions]] and indirect [[PositionLocator position locators]].
  *
  *   - `t(1)` applied at the first [[edu.cmu.cs.ls.keymaerax.core.Sequent.succ succedent]] formula.
  *   - `t(-1)` applied at the first [[edu.cmu.cs.ls.keymaerax.core.Sequent.ante antecedent]] formula.
  *   - `t(-4, 0::1::1::Nil)` applied at [[PosInExpr subexpression positioned at]] `.0.1.1` of the fourth antecedent formula,
  *     that is at the second child of the second child of the first child of the fourth antecedent formula in the sequent.
  *   - `t('L)` applied at the first applicable position in the [[edu.cmu.cs.ls.keymaerax.core.Sequent.ante antecedent]] (left side of the sequent).
  *   - `t('R)` applied at the first applicable position in the [[edu.cmu.cs.ls.keymaerax.core.Sequent.succ succedent]] (right side of the sequent).
  *   - `t('_)` applied at the first applicable position in the side of the sequent to which tactic `t` applies.
  *     The side of the sequent is uniquely determined by type of tactic.
  *   - `t('Last)` applied at the last antecedent position (left side of the sequent).
  *   - `t('Rast)` applied at the last succedent position (right side of the sequent).
  *
  * In addition, the formulas expected or sought for at the respective positions identified by the locators can be provided,
  * which is useful for tactic contract and tactic documentation purposes.
  * It is also useful for finding a corresponding formula by pattern matching.
  *
  *   - `t(2, fml)` applied at the second [[edu.cmu.cs.ls.keymaerax.core.Sequent.succ succedent]] formula,
  *     ensuring that the formula `fml` is at that position.
  *   - `t(-2, fml)` applied at the second [[edu.cmu.cs.ls.keymaerax.core.Sequent.ante antecedent]] formula,
  *     ensuring that the formula `fml` is at that position.
  *   - `t(5, 0::1::1::Nil, ex)` applied at [[PosInExpr subexpression positioned at]] `.0.1.1` of the fifth succedent formula,
  *     that is at the second child of the second child of the first child of the fifth succcedent formula in the sequent,
  *     ensuring that the expression `ex` is at that position.
  *   - `t('L, fml)` applied at the antecedent position (left side of the sequent)
  *     where the expected formula `fml` can be found (on the top level).
  *   - `t('R, fml)` applied at the succedent position (right side of the sequent)
  *     where the expected formula `fml` can be found (on the top level).
  *   - `t('_, fml)` applied at the suitable position (uniquely determined by type of tactic)
  *     where the expected formula `fml` can be found (on the top level).
  *
  * @author Stefan Mitsch
  * @author Andre Platzer
  */
trait AtPosition[T <: BelleExpr] extends BelleExpr with (PositionLocator => T) {
  import Find._

  /**
    * Returns the tactic that can be applied at the position identified by `locator`.
    * @param locator The locator: Fixed, Find, LastAnte, or LastSucc
    * @return The tactic of type `T` that can be readily applied at the position identified by `locator` to any given BelleExpr.
    * @see [[PositionLocator]]
    */
  def apply(locator: PositionLocator): T

  /**
   * Applied at a fixed position.
   * @param position The position where this tactic will be applied at.
   * @return The tactic of type `T` that can be readily applied at the specified position to any given BelleExpr.
   * @note Convenience wrapper
   * @see [[apply(locator: PositionLocator)]]
   * @see [[Fixed]]
   */
  /*private[keymaerax]*/ final def apply(position: Position): T = apply(Fixed(position))
  /**
    * Applied at a fixed position, ensuring that the formula `expected` will be found at that position, verbatim.
    * @param position The position where this tactic will be applied at.
    * @param expected the formula expected at `position`. Contract fails if that expectation is not met.
    * @return The tactic of type `T` that can be readily applied at the specified position to any given BelleExpr.
    * @note Convenience wrapper
    * @see [[apply(locator: PositionLocator)]]
    * @see [[Fixed]]
    */
  /*private[keymaerax]*/ final def apply(position: Position, expected: Formula): T = apply(Fixed(position, Some(expected)))
  /**
    * Applied at a fixed position, ensuring that the formula `expected` will be found at that position, verbatim.
    * @param position The position where this tactic will be applied at.
    * @param expected the formula expected at `position`. Contract fails if that expectation is not met.
    * @return The tactic of type `T` that can be readily applied at the specified position to any given BelleExpr.
    * @note Convenience wrapper
    * @see [[apply(locator: PositionLocator)]]
    * @see [[Fixed]]
    */
  final def apply(seqIdx: Int, expected: Formula): T = apply(Fixed(Position(seqIdx), Some(expected)))
  /**
    * Applied at a fixed position, ensuring that the formula `expected` will be found at that position, verbatim.
    * @param position The position where this tactic will be applied at.
    * @param expected the formula expected at `position`. Contract fails if that expectation is not met.
    * @return The tactic of type `T` that can be readily applied at the specified position to any given BelleExpr.
    * @note Convenience wrapper
    * @see [[apply(locator: PositionLocator)]]
    * @see [[Fixed]]
    */
  final def apply(seqIdx: Int, inExpr: List[Int], expected: Formula): T = apply(Fixed(Position(seqIdx, inExpr), Some(expected)))
  private[ls] final def apply(position: SeqPos): T = apply(Fixed(Position(position)))

  /**
   * Applied at a fixed position in (signed) sequent position `seqIdx` at subexpression `inExpr`.
   * @param seqIdx The signed index in the sequent (strictly negative index for antecedent, strictly positive for succedent).
   * @param inExpr Where to apply inside the formula at index seqIdx interpreted as a [[PosInExpr]].
   * @return The tactic of type `T` that can be readily applied at the specified position to any given BelleExpr.
   * @note Convenience wrapper
   * @see [[PosInExpr]]
   * @see [[apply(position: Position)]]
   * @see [[Fixed]]
   */
  final def apply(seqIdx: Int, inExpr: List[Int] = Nil): T = apply(Fixed(Position(seqIdx, inExpr)))
  /**
    * Returns the tactic at the position identified by `locator`.
    * @param locator The locator symbol at which to apply this AtPosition:
    *                'L (find left),
    *                'R (find right),
    *                '_ (find left/right appropriately for tactic),
    *                'Llast (at last position in antecedent), or
    *                'Rlast (at last position in succedent).
    * @note Convenience wrapper
    * @see [[edu.cmu.cs.ls.keymaerax.bellerophon.AtPosition]]
    * @see [[apply(locator: PositionLocator)]]
    */
  final def apply(locator: Symbol): T = locator match {
    case 'L => apply(FindL(0, None))
    case 'R => apply(FindR(0, None))
    case '_ => this match {
      case _: BuiltInLeftTactic => apply(FindL(0, None))
      case _: BuiltInRightTactic => apply(FindR(0, None))
      case _ => throw new BelleError(s"Cannot determine whether this tactic is left/right. Please use 'L or 'R as appropriate.")
    }
    case 'Llast => apply(LastAnte(0))
    case 'Rlast => apply(LastSucc(0))
  }
  /**
    * Returns the tactic at the position identified by `locator`, ensuring that `locator` will yield the formula `expected` verbatim.
    * @param locator The locator symbol at which to apply this AtPosition:
    *                'L (find left),
    *                'R (find right),
    *                '_ (find left/right appropriately for tactic),
    *                'Llast (at last position in antecedent), or
    *                'Rlast (at last position in succedent).
    * @param expected the formula expected at the position that `locator` identifies. Contract fails if that expectation is not met.
    * @note Convenience wrapper
    * @see [[edu.cmu.cs.ls.keymaerax.bellerophon.AtPosition]]
    * @see [[apply()]]
    */
  final def apply(locator: Symbol, expected: Formula): T = locator match {
    case 'L => apply(FindL(0, Some(expected)))
    case 'R => apply(FindR(0, Some(expected)))
    case '_ => this match {
      case _: BuiltInLeftTactic => apply(FindL(0, Some(expected)))
      case _: BuiltInRightTactic => apply(FindR(0, Some(expected)))
      case _ => throw new BelleError(s"Cannot determine whether this tactic is left/right. Please use 'L or 'R as appropriate.")
    }
    //@todo how to check expected formula?
    case 'Llast => println("INFO: will not check expected for 'Llast yet"); apply(LastAnte(0))
    case 'Rlast => println("INFO: will not check expected for 'Rlast yet"); apply(LastSucc(0))
  }

}

/** PositionTactics are tactics that can be [[AtPosition applied at positions]] giving ordinary tactics.
  * @see [[AtPosition]] */
trait PositionalTactic extends BelleExpr with AtPosition[AppliedPositionTactic] {
  /** @note this should be called from within interpreters, but not by end-users */
  def computeResult(provable: Provable, position: Position): Provable
  final override def apply(locator: PositionLocator): AppliedPositionTactic = AppliedPositionTactic(this, locator)
}

abstract case class BuiltInPositionTactic(name: String) extends PositionalTactic {override def prettyString = name}

abstract case class BuiltInLeftTactic(name: String) extends BelleExpr with PositionalTactic {
  final override def computeResult(provable: Provable, position:Position) = position match {
    case p: AntePosition => computeAnteResult(provable, p)
    case _ => throw new BelleError("LeftTactics can only be applied at a AntePos")
  }

  def computeAnteResult(provable: Provable, pos: AntePosition): Provable

  override def prettyString = name

}

abstract case class BuiltInRightTactic(name: String) extends PositionalTactic {
  final override def computeResult(provable: Provable, position:Position) = position match {
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
  import Augmentors._
  final def computeResult(provable: Provable) : Provable = try { locator match {
      //@note interprets PositionLocator
      case Fixed(pos, shape, exact) => shape match {
        case Some(f:Formula) =>
          require(provable.subgoals.size == 1, "Locator 'fixed with shape' applies only to provables with exactly 1 subgoal since otherwise ill-defined")
          //@note (implicit .apply needed to ensure subposition to pos.inExpr
          if (( exact && provable.subgoals.head.sub(pos).contains(f)) ||
              (!exact && UnificationMatch.unifiable(f, provable.subgoals.head.sub(pos).get).isDefined)) {
            positionTactic.computeResult(provable, pos)
          } else {
            throw new BelleError("Formula " + provable.subgoals.head.sub(pos) + " at position " + pos +
              " is not of expected shape " + f)
          }
        case None => positionTactic.computeResult(provable, pos)
      }
      case Find(goal, shape, start, exact) =>
        require(start.isTopLevel, "Start position must be top-level in sequent")
        require(start.isIndexDefined(provable.subgoals(goal)), "Start position must be valid in sequent")
        tryAllAfter(provable, goal, shape, start, exact, null)
      case LastAnte(goal) => positionTactic.computeResult(provable, AntePosition.base0(provable.subgoals(goal).ante.size-1))
      case LastSucc(goal) => positionTactic.computeResult(provable, SuccPosition.base0(provable.subgoals(goal).succ.size-1))
    }
  } catch {
    case be: BelleError => throw be
    case t: Throwable => throw new BelleError(t.getMessage, t)
  }

  /** Recursively tries the position tactic at positions at or after pos in the specified provable. */
  private def tryAllAfter(provable: Provable, goal: Int, shape: Option[Formula], pos: Position, exact: Boolean,
                          cause: BelleError): Provable =
    if (pos.isIndexDefined(provable.subgoals(goal))) {
      try {
        shape match {
          case Some(f) if !exact && UnificationMatch.unifiable(f, provable.subgoals(goal)(pos.top)).isDefined =>
            positionTactic.computeResult(provable, pos)
          case Some(f) if !exact && UnificationMatch.unifiable(f, provable.subgoals(goal)(pos.top)).isEmpty =>
            tryAllAfter(provable, goal, shape, pos.advanceIndex(1), exact, new BelleError(s"Formula is not of expected shape", cause))
          case Some(f) if exact && provable.subgoals(goal)(pos.top) == f => positionTactic.computeResult(provable, pos)
          case Some(f) if exact && provable.subgoals(goal)(pos.top) != f =>
            tryAllAfter(provable, goal, shape, pos.advanceIndex(1), exact, new BelleError(s"Formula is not of expected shape", cause))
          case None => positionTactic.computeResult(provable, pos)
        }
      } catch {
        case e: Throwable =>
          val newCause = if (cause == null) new BelleError(s"Position tactic ${positionTactic.prettyString} is not " +
            s"applicable at ${pos.prettyString}", e)
          else new CompoundException(
            new BelleError(s"Position tactic ${positionTactic.prettyString} is not applicable at ${pos.prettyString}", e),
            cause)
          tryAllAfter(provable, goal, shape, pos.advanceIndex(1), exact, newCause)
      }
    } else throw cause

  override def prettyString = positionTactic.prettyString + "(" + locator.prettyString + ")"
}

abstract case class BuiltInTwoPositionTactic(name: String) extends BelleExpr {
  /** @note this should be called from within interpreters, but not by end users. */
  def computeResult(provable : Provable, posOne: Position, posTwo: Position) : Provable

  /** Returns an explicit representation of the application of this tactic to the provided positions. */
  final def apply(posOne: Position, posTwo: Position): AppliedTwoPositionTactic = AppliedTwoPositionTactic(this, posOne, posTwo)
  /** Returns an explicit representation of the application of this tactic to the provided positions.
    * @note Convenience wrapper
    */
  final def apply(posOne: Int, posTwo: Int): AppliedTwoPositionTactic = apply(Position(posOne), Position(posTwo))

  override def prettyString = name
}

/** Motivation is similar to [[AppliedPositionTactic]], but for [[BuiltInTwoPositionTactic]] */
case class AppliedTwoPositionTactic(positionTactic: BuiltInTwoPositionTactic, posOne: Position, posTwo: Position) extends BelleExpr {
  final def computeResult(provable: Provable) : Provable = try {
    positionTactic.computeResult(provable, posOne, posTwo)
  } catch {
    case be: BelleError => throw be
    case t: Throwable => throw new BelleError(t.getMessage, t)
  }

  override def prettyString = positionTactic.prettyString + "(" + posOne.prettyString + "," + posTwo.prettyString + ")"
}

/**
 * Dependent tactics compute a tactic to apply based on their input.
 * These tactics are probably not necessary very often, but are useful for idiomatic shortcuts.
 * See e.g., AtSubgoal.
 * @note similar to the ConstructionTactics in the old framework, except they should not be necessary
 *       nearly as often because BuiltIns have direct access to a Provable.
 * @param name The name of the tactic.
 * @todo is there a short lambda abstraction notation as syntactic sugar?
 */
abstract case class DependentTactic(name: String) extends BelleExpr {
  def computeExpr(provable: Provable): BelleExpr = throw new BelleError("Not implemented")
  def computeExpr(e: BelleValue with BelleError): BelleExpr = throw e
  /** Generic computeExpr; prefer overriding computeExpr(Provable) and computeExpr(BelleError) */
  def computeExpr(v : BelleValue): BelleExpr = try { v match {
      case BelleProvable(provable, _) => computeExpr(provable)
      case e: BelleError => computeExpr(e)
    }
  } catch {
    case be: BelleError => throw be
    case t: Throwable => if (DEBUG) t.printStackTrace(); throw new BelleError(t.getMessage, t)
  }
  override def prettyString: String = "DependentTactic(" + name + ")"
}
abstract class SingleGoalDependentTactic(override val name: String) extends DependentTactic(name) {
  def computeExpr(sequent: Sequent): BelleExpr
  final override def computeExpr(provable: Provable): BelleExpr = {
    require(provable.subgoals.size == 1, "Exactly 1 subgoal expected, but got " + provable.subgoals.size)
    computeExpr(provable.subgoals.head)
  }
}
/** DependentPositionTactics are tactics that can be [[AtPosition applied at positions]] giving dependent tactics.
  * @see [[AtPosition]] */
abstract case class DependentPositionTactic(name: String) extends BelleExpr with AtPosition[DependentTactic] {
  final override def apply(locator: PositionLocator): AppliedDependentPositionTactic = new AppliedDependentPositionTactic(this, locator)
  override def prettyString: String = "DependentPositionTactic(" + name + ")"
  /** Create the actual tactic to be applied at position pos */
  def factory(pos: Position): DependentTactic
}
abstract case class InputTactic[T](name: SerializationName, input: T) extends BelleExpr {
  def computeExpr(): BelleExpr
  override def prettyString: String = "input(" + input + ")"
}
abstract case class InputPositionTactic[T](input: T, pos: Position) extends BelleExpr {
  def computeExpr(): BelleExpr
}

class AppliedDependentPositionTactic(val pt: DependentPositionTactic, locator: PositionLocator) extends DependentTactic(pt.name) {
  import Augmentors._
  override def prettyString: String = "AppliedDependentPositionTactic(" + pt.name + ")(" + locator.prettyString + ")"
  final override def computeExpr(v: BelleValue): BelleExpr = locator match {
    //@note interprets PositionLocator
    case Fixed(pos, shape, exact) => shape match {
      case Some(f) => v match {
        case BelleProvable(provable, _) =>
          require(provable.subgoals.size == 1, "Locator 'fixed with shape' applies only to provables with exactly 1 subgoal")
          //@note (implicit .apply needed to ensure subposition to pos.inExpr
          if ((exact && provable.subgoals.head.sub(pos).contains(f)) ||
            (!exact && UnificationMatch.unifiable(f, provable.subgoals.head.sub(pos).get).isDefined)) {
            pt.factory(pos).computeExpr(v)
          } else {
            throw new BelleError("Formula " + provable.subgoals.head.sub(pos) + " at position " + pos +
              " is not of expected shape " + f)
          }
      }
      case None => pt.factory(pos).computeExpr(v)
    }
    case Find(goal, shape, start, exact) =>
      require(start.isTopLevel, "Start position must be top-level in sequent")
      tryAllAfter(goal, shape, start, exact, null)
    case LastAnte(goal) => pt.factory(v match { case BelleProvable(provable, _) => AntePosition.base0(provable.subgoals(goal).ante.size-1) })
    case LastSucc(goal) => pt.factory(v match { case BelleProvable(provable, _) => SuccPosition.base0(provable.subgoals(goal).succ.size-1) })
  }

  /** Recursively tries the position tactic at positions at or after pos in the specified provable. */
  private def tryAllAfter(goal: Int, shape: Option[Formula], pos: Position, exact: Boolean,
                          cause: BelleError): DependentTactic = new DependentTactic(name) {
    override def computeExpr(v: BelleValue): BelleExpr = v match {
      case BelleProvable(provable, _) =>
        if (pos.isIndexDefined(provable.subgoals(goal))) {
          try {
            shape match {
              case Some(f) if !exact && UnificationMatch.unifiable(f, provable.subgoals(goal)(pos.top)).isDefined =>
                pt.factory(pos).computeExpr(v)
              case Some(f) if !exact && UnificationMatch.unifiable(f, provable.subgoals(goal)(pos.top)).isEmpty =>
                tryAllAfter(goal, shape, pos.advanceIndex(1), exact, new BelleError(s"Formula is not of expected shape", cause))
              case Some(f) if exact && f == provable.subgoals(goal)(pos.top) => pt.factory(pos).computeExpr(v)
              case Some(f) if exact && f != provable.subgoals(goal)(pos.top) =>
                tryAllAfter(goal, shape, pos.advanceIndex(1), exact, new BelleError(s"Formula is not of expected shape", cause))
              case None => pt.factory(pos).computeExpr(v)
            }
          } catch {
            case e: Throwable =>
              val newCause = if (cause == null) new BelleError(s"Dependent position tactic ${pt.prettyString} is not " +
                s"applicable at ${pos.prettyString}", e)
              else new CompoundException(
                new BelleError(s"Dependent position tactic ${pt.prettyString} is not applicable at ${pos.prettyString}", e),
                cause)
              tryAllAfter(goal, shape, pos.advanceIndex(1), exact, newCause)
          }
        } else throw cause
      case _ => pt.factory(pos).computeExpr(v) // cannot search recursively, because don't know when to abort
    }
  }
}

/** A partial tactic is allowed to leave its subgoals around as unproved */
case class PartialTactic(child: BelleExpr, label: Option[BelleLabel] = None) extends BelleExpr {
  override def prettyString = label match {
    case Some(theLabel) => s"partial(${child.prettyString})@(${theLabel.prettyString})"
    case None => s"partial(${child.prettyString})"
  }
}

case class SeqTactic(left: BelleExpr, right: BelleExpr, override val location: Array[StackTraceElement] = Thread.currentThread().getStackTrace) extends BelleExpr { override def prettyString = "(" + left.prettyString + "&" + right.prettyString + ")" }
case class EitherTactic(left: BelleExpr, right: BelleExpr, override val location: Array[StackTraceElement] = Thread.currentThread().getStackTrace) extends BelleExpr { override def prettyString = "(" + left.prettyString + "|" + right.prettyString + ")" }
case class SaturateTactic(child: BelleExpr, annotation: BelleType, override val location: Array[StackTraceElement] = Thread.currentThread().getStackTrace) extends BelleExpr { override def prettyString = "(" + child.prettyString + ")*" }
case class RepeatTactic(child: BelleExpr, times: Int, annotation: BelleType, override val location: Array[StackTraceElement] = Thread.currentThread().getStackTrace) extends BelleExpr { override def prettyString = "(" + child.prettyString + ")*" + times }
case class BranchTactic(children: Seq[BelleExpr], override val location: Array[StackTraceElement] = Thread.currentThread().getStackTrace) extends BelleExpr { override def prettyString = "<( " + children.map(_.prettyString).mkString(", ") + " )" }
case class USubstPatternTactic(options: Seq[(BelleType, RenUSubst => BelleExpr)], override val location: Array[StackTraceElement] = Thread.currentThread().getStackTrace) extends BelleExpr { override def prettyString = "case { " + options.mkString(", ") + " }"}

/**
  * DoAll(e)(BelleProvable(p)) == <(e, ..., e) where e occurs the appropriate number of times, which is `p.subgoals.length` times.
  * @todo eisegesis
  */
case class DoAll(e: BelleExpr, override val location: Array[StackTraceElement] = Thread.currentThread().getStackTrace) extends BelleExpr { override def prettyString = "doall(" + e.prettyString + ")" }

//@todo case class DoSome[A](options: Iterator[A], e: A => BelleExpr) extends BelleExpr, which runs some (usually first) generator output whose proof succeeds.

/**
 * Bellerophon expressions that are values.
 */
trait BelleValue {
  def prettyString: String = toString
}
case class BelleProvable(p : Provable, label: Option[BelleLabel] = None) extends BelleExpr with BelleValue {
  override def toString: String = p.prettyString
  override def prettyString: String = p.prettyString
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Bellerophon Labels
////////////////////////////////////////////////////////////////////////////////////////////////////
trait BelleLabel {
  protected val LABEL_DELIMITER: String = ":"

  def prettyString : String = this match {
    case topLevel: BelleTopLevelLabel    => topLevel.label
    case BelleSubLabel(parent, theLabel) => parent.prettyString + LABEL_DELIMITER + theLabel
  }
  }
case class BelleTopLevelLabel(label: String) extends BelleLabel {require(!label.contains(LABEL_DELIMITER), s"Label should not contain the sublabel delimiter $LABEL_DELIMITER")}
case class BelleSubLabel(parent: BelleLabel, label: String)  extends BelleLabel {require(!label.contains(LABEL_DELIMITER), s"Label should not contain the sublabel delimiter $LABEL_DELIMITER")}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Bellerophon Types
////////////////////////////////////////////////////////////////////////////////////////////////////

/** @todo eisegesis -- simple types */
trait BelleType
case class TheType() extends BelleType
/** @todo Added because SequentTypes are needed for unification tactics. */
case class SequentType(s : Sequent) extends BelleType

