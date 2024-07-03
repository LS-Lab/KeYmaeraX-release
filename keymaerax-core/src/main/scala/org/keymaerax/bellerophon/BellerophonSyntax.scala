/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.bellerophon

import org.keymaerax.btactics._
import org.keymaerax.btactics.macros.DerivationInfo
import org.keymaerax.core._
import org.keymaerax.infrastruct.ExpressionTraversal.ExpressionTraversalFunction
import org.keymaerax.infrastruct.PosInExpr.HereP
import org.keymaerax.infrastruct._
import org.keymaerax.parser.{BuiltinSymbols, Declaration}
import org.keymaerax.pt.ProvableSig
import org.keymaerax.{Configuration, Logging}

import scala.annotation.tailrec

object BelleExpr {
  val INTERNAL_NAME_PREFIX: String = "_"

  private[keymaerax] val RECHECK = Configuration(Configuration.Keys.DEBUG) == "true"

  /** Indicates whether name `n` is an internal name. */
  def isInternal(n: String): Boolean = n.startsWith(INTERNAL_NAME_PREFIX)

  // Don't persist generator arguments
  private[bellerophon] def persistable[T](args: Seq[T]): Seq[T] = {
    args.filter {
      case _: Generator[_] => false
      case _ => true
    }
  }

  private[bellerophon] def prettyArgs(inputs: Seq[Any]): String = {
    persistable(inputs).flatMap(printOne(_, inputs.size <= 1)) match {
      case Nil => ""
      case args => "(" + args.mkString(",") + ")"
    }
  }

  private[bellerophon] def printOne(x: Any, listAsVarArgs: Boolean): Option[String] = {
    x match {
      case None => None
      case Some(y) => printOne(y, listAsVarArgs)
      case input: Expression => Some("\"" + input.prettyString + "\"")
      case input: USubst =>
        Some(input.subsDefsInput.map(p => "\"" + p.what.prettyString + "~>" + p.repl.prettyString + "\"").mkString(","))
      case input: SubstitutionPair => Some("\"" + input.what.prettyString + "~>" + input.repl.prettyString + "\"")
      case input: String => Some("\"" + input + "\"")
      case (head: Expression) :: Nil => Some("\"" + head.prettyString + "\"")
      case (head: Expression) :: tail =>
        if (listAsVarArgs) Some((head :: tail).map(printOne(_, listAsVarArgs)).mkString(","))
        else Some("\"" + (head :: tail).map(_.asInstanceOf[Expression].prettyString).mkString("::") + "::nil\"")
      case Nil => Some("\"nil\"")
      case input => Some("\"" + input.toString + "\"")
    }
  }
}

/**
 * Algebraic Data Type whose elements are well-formed Bellerophon tactic expressions. All Bellerophon tactic expressions
 * are of type [[org.keymaerax.bellerophon.BelleExpr]], which provides the following tactic combinators
 *
 *   - `s ; t` alias `s & t` [[org.keymaerax.bellerophon.SeqTactic sequential composition]] executes t` on the output of
 *     `s`, failing if either fail.
 *   - `s | t` [[org.keymaerax.bellerophon.EitherTactic alternative composition]] executes `t` if applying `s` fails,
 *     failing if both fail.
 *   - `t*` [[org.keymaerax.bellerophon.SaturateTactic saturating repetition]] executes tactic `t` repeatedly to a
 *     fixpoint, casting result to type annotation, diverging if no fixpoint.
 *   - `t*n` [[org.keymaerax.bellerophon.RepeatTactic bounded repetition]] executes `t` tactic `n` number of times,
 *     failing if any of those repetitions fail.
 *   - `t+` saturating repetition executes tactic `t` to a fixpoint, requires at least one successful application.
 *   - `<(e1,...,en)` [[org.keymaerax.bellerophon.BranchTactic branching]] to run tactic `ei` on branch `i`, failing if
 *     any of them fail or if there are not exactly `n` branches.
 *
 * @todo
 *   Consolidate the members of BelleExpr and finalize an abstract syntax.
 * @see
 *   Table 1 of
 *   [[https://doi.org/10.1007/978-3-319-66107-0_14 Bellerophon: A Typed Language for Automated Deduction in a Uniform Substitution Calculus]].
 *   In Mauricio Ayala-Rincón and César A. Muñoz, editors, Interactive Theorem Proving, International Conference, ITP
 *   2017, volume 10499 of LNCS, pp. 207-224. Springer, 2017.
 * @author
 *   Nathan Fulton
 * @author
 *   Stefan Mitsch
 * @author
 *   Andre Platzer
 * @see
 *   [[org.keymaerax.bellerophon.Interpreter]]
 * @see
 *   [[org.keymaerax.bellerophon.SequentialInterpreter]]
 */
sealed abstract class BelleExpr {
  // tactic combinators

  /**
   * `this & other`: sequential composition this ; other executes other on the output of this, failing if either fail.
   */
  def &(other: BelleExpr): BelleExpr = SeqTactic(this, other)

  /** `this | other`: alternative composition executes other if applying this fails, failing if both fail. */
  def |(other: BelleExpr): BelleExpr = EitherTactic(this, other)

  /**
   * `this |! other`: alternative composition executes other if applying this fails (even critically), failing if both
   * fail.
   */
  def |!(other: BelleExpr): BelleExpr = EitherTactic(
    TryCatch(
      this,
      classOf[Throwable],
      (ex: Throwable) => throw new TacticInapplicableFailure("Inapplicable due to critical exception", ex),
    ),
    other,
  )
  def ||(other: BelleExpr): BelleExpr = ParallelTactic(List(this, other))

  /**
   * `this*n`: bounded repetition executes this tactic to `times` number of times, failing if any of those repetitions
   * fail.
   */
  def *(n: Int): BelleExpr = RepeatTactic(this, n)

  /**
   * `<(e1,...,en)`: branching to run tactic `ei` on branch `i`, failing if any of them fail or if there are not exactly
   * `n` branches.
   * @note
   *   Equivalent to `a & Idioms.<(b,c)`
   */
  // @deprecated("Use & with explicit Idioms.< instead; import Idioms.<, so a & <(b,c)", since="4.2")
  def <(children: BelleExpr*): BelleExpr = SeqTactic(Seq(this, BranchTactic(children)))
  def switch(children: (BelleLabel, BelleExpr)*): BelleExpr = SeqTactic(Seq(this, CaseTactic(children)))

  /**
   * case _ of {fi => ei} uniform substitution case pattern applies the first ei such that fi uniformly substitutes to
   * current provable for which ei does not fail, fails if the ei of all matching fi fail.
   */
  def U(p: (SequentType, RenUSubst => BelleExpr)*): BelleExpr = SeqTactic(Seq(this, USubstPatternTactic(p)))
  // @todo Maybe support ?(e) or try(e) or optional(e) defined as this|skip

  override def toString: String = prettyString

  /** pretty-printed form of this Bellerophon tactic expression */
  def prettyString: String
}

/** A BelleExpr that has a proper code name, so is not just used internally during application. */
sealed trait NamedBelleExpr extends BelleExpr {

  /** The code name of this Belle Expression */
  val name: String

  override def prettyString: String = name

  /** Indicates whether this is an internal named tactic. */
  def isInternal: Boolean = BelleExpr.isInternal(name)

  // @note register the name with the DerivationInfo once the tactic is instantiated
  if (!isInternal) DerivationInfo.seeName(name)
}

// basic tactic combinators

/** `left ; right` sequential composition executes `right` on the output of `left`, failing if either fail. */
object SeqTactic {
  def apply(t1: BelleExpr, t2: BelleExpr): BelleExpr = (t1, t2) match {
    case (SeqTactic(s1), SeqTactic(s2)) => SeqTactic(s1 ++ s2)
    case (SeqTactic(s1), _) => SeqTactic(s1 :+ t2)
    case (_, SeqTactic(s2)) => SeqTactic(t1 +: s2)
    case _ => SeqTactic(Seq(t1, t2))
  }
  def apply(seq: Seq[BelleExpr]): BelleExpr = {
    if (seq.size > 1) new SeqTactic(seq) else seq.headOption.getOrElse(TactixLibrary.nil)
  }
}
case class SeqTactic(seq: Seq[BelleExpr]) extends BelleExpr {
  assert(seq.size > 1, "Sequential composition needs at least 2 elements")
  override def prettyString: String = "(" + seq.map(_.prettyString).mkString(";") + ")"
}

/** `left | right` alternative composition executes `right` if applying `left` fails, failing if both fail. */
object EitherTactic {
  def apply(t1: BelleExpr, t2: BelleExpr): BelleExpr = (t1, t2) match {
    case (EitherTactic(s1), EitherTactic(s2)) => EitherTactic(s1 ++ s2)
    case (EitherTactic(s1), _) => EitherTactic(s1 :+ t2)
    case (_, EitherTactic(s2)) => EitherTactic(t1 +: s2)
    case _ => EitherTactic(Seq(t1, t2))
  }
  def apply(alts: Seq[BelleExpr]): BelleExpr = {
    if (alts.size > 1) new EitherTactic(alts) else alts.headOption.getOrElse(TactixLibrary.nil)
  }
}
case class EitherTactic(alts: Seq[BelleExpr]) extends BelleExpr {
  assert(alts.size > 1, "Alternative composition needs at least 2 elements")
  override def prettyString: String = "(" + alts.map(_.prettyString).mkString("|") + ")"
}

/**
 * `left || right` alternative composition executes both `left` and `right` simultaneously and succeeds with the first
 * success, failing if both fail.
 */
case class ParallelTactic(expr: List[BelleExpr]) extends BelleExpr {
  override def prettyString: String = "(" + expr.map(_.prettyString).mkString("||") + ")"
}
//@note saturate and repeat tactic fully parenthesize for parser
/**
 * `child*` saturating repetition executes tactic `child` repeatedly to a fixpoint, casting result to type annotation,
 * diverging if no fixpoint.
 */
case class SaturateTactic(child: BelleExpr) extends BelleExpr {
  override def prettyString: String = "((" + child.prettyString + ")*)"
}

/**
 * `child*times` bounded repetition executes `child` tactic `times` number of times, failing if any of those repetitions
 * fail.
 */
case class RepeatTactic(child: BelleExpr, times: Int) extends BelleExpr {
  override def prettyString: String = "((" + child.prettyString + ")*" + times + ")"
}

/**
 * `<(e1,...,en)` branching to run tactic `ei` on branch `i`, failing if any of them fail or if there are not exactly
 * `n` branches.
 */
case class BranchTactic(children: Seq[BelleExpr]) extends BelleExpr {
  override def prettyString: String = "<( " + children.map(_.prettyString).mkString(", ") + " )"
}

/**
 * `<("l1":e1,...,"ln":en)` branching to run tactic `ei` on label `li`, failing if any of them fail, if there are not
 * exactly `n` branches, or if any of the labels does not exist.
 */
case class CaseTactic(children: Seq[(BelleLabel, BelleExpr)]) extends BelleExpr {
  override def prettyString: String = "<( " +
    children.map({ case (l, c) => "\"" + l.prettyString + "\": " + c.prettyString }).mkString(", ") + " )"
}

/**
 * `USubstPatternTactic((form1, us=>t1) :: ... (form2, us=>t2) :: Nil)` runs the first tactic `ti` for the unification
 * `us` with the first pattern `formi` that matches the current goal.
 *
 * In other words: `case _ of {fi => ei}` uniform substitution case pattern applies the first `ei` such that `fi`
 * uniformly substitutes to current provable for which `ei` does not fail, fails if the `ei` of all matching `fi` fail.
 */
case class USubstPatternTactic(options: Seq[(BelleType, RenUSubst => BelleExpr)]) extends BelleExpr {
  override def prettyString: String = "case { " + options.mkString(", ") + " }"
}

/**
 * Tries tactic `t` and executes
 *   - `c` (catch) on exceptions of type `T` that occur when executing `t`
 *   - `f` (finally) on the result of `t` (if `t` is successful), on the result of `c` (if `c` is successful), or on the
 *     initial problem if neither `t` nor `c` are successful (throwing the exceptions of `t` or `c` even if `f` is
 *     successful). Pattern: `TryCatch` should usually be used together with `|`. In that case, `c` should throw a proof
 *     search control exception instead of supplying a tactic, since it is usually intended to also execute the
 *     alternative tactic on success of `t` or if `t` throws other unrelated proof search control exceptions.
 *     {{{
 *       TryCatch(useAt("[:=] assign")(1), classOf[SubstitutionClashException],
 *         (ex: SubstitutionClashException) => throw new TacticInapplicableFailure("Inapplicable", ex)) | alternativeTactic
 *     }}}
 *     If indeed an alternative tactic should only be executed on exception, use
 *     {{{
 *       TryCatch(useAt("[:=] assign")(1), classOf[SubstitutionClashException],
 *         (ex: SubstitutionClashException) => alternativeTactic)
 *     }}}
 */
case class TryCatch[T <: Throwable](t: BelleExpr, cCatch: Class[T], c: T => BelleExpr, f: Option[BelleExpr] = None)
    extends BelleExpr {
  override def prettyString: String = "TryCatch"
}

/** Positive mention of expressions `es` to use when executing tactic `t`. */
case class Using(es: List[Expression], t: BelleExpr) extends BelleExpr {
  override def prettyString: String =
    if (es.nonEmpty) "(" + t.prettyString + ") using \"" + es.map(_.prettyString).mkString("::") + "::nil\""
    else t.prettyString
}

/** Marker for no-op tactics. */
trait NoOpTactic {}

/**
 * Mixing in NoOpTactic with existing tactic instances (e.g., obtained through TacticFactory methods)
 * @see
 *   https://stackoverflow.com/a/3896244
 */
object NoOpTactic {
  import scala.language.implicitConversions
  implicit def innerObj[T](o: MixNoOp[T]): T = o.obj

  def ::[T](o: T) = new MixNoOp(o)
  final class MixNoOp[T] private[NoOpTactic] (val obj: T) extends NoOpTactic
}

/** Give a code name to the given tactic `tactic` for serialization purposes. */
case class NamedTactic(name: String, tactic: BelleExpr) extends NamedBelleExpr

/** `⎵`: Placeholder for tactics in tactic contexts. Reserved tactic expression that cannot be executed. */
class BelleDot() extends BelleExpr {
  override def prettyString = ">>_<<"
}
object BelleDot extends BelleDot()

////////////////////////////////////////////////////////////////////////////////////////////////////
// Positional tactics
////////////////////////////////////////////////////////////////////////////////////////////////////

/**
 * Applied at a position, AtPosition turns into a tactic of type T. Turns a position or position locator into a tactic.
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
 *   - `t(1)` applied at the first [[org.keymaerax.core.Sequent.succ succedent]] formula.
 *   - `t(-1)` applied at the first [[org.keymaerax.core.Sequent.ante antecedent]] formula.
 *   - `t(-4, 0::1::1::Nil)` applied at [[PosInExpr subexpression positioned at]] `.0.1.1` of the fourth antecedent
 *     formula, that is at the second child of the second child of the first child of the fourth antecedent formula in
 *     the sequent.
 *   - `t('L)` applied at the first applicable position in the [[org.keymaerax.core.Sequent.ante antecedent]] (left side
 *     of the sequent).
 *   - `t('R)` applied at the first applicable position in the [[org.keymaerax.core.Sequent.succ succedent]] (right side
 *     of the sequent).
 *   - `t('_)` applied at the first applicable position in the side of the sequent to which tactic `t` applies. The side
 *     of the sequent is uniquely determined by type of tactic.
 *   - `t('Llast)` applied at the last antecedent position (left side of the sequent).
 *   - `t('Rlast)` applied at the last succedent position (right side of the sequent).
 *
 * In addition, the formulas expected or sought for at the respective positions identified by the locators can be
 * provided, which is useful for tactic contract and tactic documentation purposes. It is also useful for finding a
 * corresponding formula by pattern matching.
 *
 *   - `t(2, fml)` applied at the second [[org.keymaerax.core.Sequent.succ succedent]] formula, ensuring that the
 *     formula `fml` is at that position.
 *   - `t(-2, fml)` applied at the second [[org.keymaerax.core.Sequent.ante antecedent]] formula, ensuring that the
 *     formula `fml` is at that position.
 *   - `t(5, 0::1::1::Nil, ex)` applied at [[PosInExpr subexpression positioned at]] `.0.1.1` of the fifth succedent
 *     formula, that is at the second child of the second child of the first child of the fifth succcedent formula in
 *     the sequent, ensuring that the expression `ex` is at that position.
 *   - `t('L, fml)` applied at the antecedent position (left side of the sequent) where the expected formula `fml` can
 *     be found (on the top level).
 *   - `t('R, fml)` applied at the succedent position (right side of the sequent) where the expected formula `fml` can
 *     be found (on the top level).
 *   - `t('_, fml)` applied at the suitable position (uniquely determined by type of tactic) where the expected formula
 *     `fml` can be found (on the top level).
 *
 * @author
 *   Stefan Mitsch
 * @author
 *   Andre Platzer
 */
trait AtPosition[T <: BelleExpr] extends BelleExpr with (PositionLocator => T) with Logging {
  import Find._

  /**
   * Returns the tactic that can be applied at the position identified by `locator`.
   *
   * @param locator
   *   The locator: Fixed, Find, LastAnte, or LastSucc
   * @return
   *   The tactic of type `T` that can be readily applied at the position identified by `locator` to any given
   *   BelleExpr.
   * @see
   *   [[PositionLocator]]
   */
  def apply(locator: PositionLocator): T

  /**
   * Applied at a fixed position.
   *
   * @param position
   *   The position where this tactic will be applied at.
   * @return
   *   The tactic of type `T` that can be readily applied at the specified position to any given BelleExpr.
   * @note
   *   Convenience wrapper
   * @see
   *   [[apply(locator: PositionLocator)]]
   * @see
   *   [[Fixed]]
   */
  /*private[keymaerax]*/
  final def apply(position: Position): T = apply(Fixed(position))

  /**
   * Applied at a fixed position, ensuring that the formula `expected` will be found at that position, verbatim.
   *
   * @param position
   *   The position where this tactic will be applied at.
   * @param expected
   *   the formula expected at `position`. Contract fails if that expectation is not met.
   * @return
   *   The tactic of type `T` that can be readily applied at the specified position to any given BelleExpr.
   * @note
   *   Convenience wrapper
   * @see
   *   [[apply(locator: PositionLocator)]]
   * @see
   *   [[Fixed]]
   */
  /*private[keymaerax]*/
  final def apply(position: Position, expected: Formula): T = apply(Fixed(position, Some(expected)))

  /**
   * Applied at a fixed position, ensuring that the formula `expected` will be found at that position, verbatim.
   *
   * @param seqIdx
   *   The position where this tactic will be applied at (-1 based for antecedent, 1 based for succedent).
   * @param expected
   *   the formula expected at `position`. Contract fails if that expectation is not met.
   * @return
   *   The tactic of type `T` that can be readily applied at the specified position to any given BelleExpr.
   * @note
   *   Convenience wrapper
   * @see
   *   [[apply(locator: PositionLocator)]]
   * @see
   *   [[Fixed]]
   */
  final def apply(seqIdx: Int, expected: Formula): T = apply(Fixed(Position(seqIdx), Some(expected)))

  /**
   * Applied at a fixed position, ensuring that the formula `expected` will be found at that position, verbatim.
   *
   * @param seqIdx
   *   The position where this tactic will be applied at (-1 based for antecedent, 1 based for succedent).
   * @param expected
   *   the formula expected at `position`. Contract fails if that expectation is not met.
   * @return
   *   The tactic of type `T` that can be readily applied at the specified position to any given BelleExpr.
   * @note
   *   Convenience wrapper
   * @see
   *   [[apply(locator: PositionLocator)]]
   * @see
   *   [[Fixed]]
   */
  final def apply(seqIdx: Int, inExpr: List[Int], expected: Formula): T =
    apply(Fixed(Position(seqIdx, inExpr), Some(expected)))
  final def apply(seqIdx: Int, inExpr: PosInExpr, expected: Formula): T = apply(seqIdx, inExpr.pos, expected)
  private[keymaerax] final def apply(position: SeqPos): T = apply(Fixed(Position(position)))

  /**
   * Applied at a fixed position in (signed) sequent position `seqIdx` at subexpression `inExpr`.
   *
   * @param seqIdx
   *   The signed index in the sequent (strictly negative index for antecedent, strictly positive for succedent).
   * @param inExpr
   *   Where to apply inside the formula at index seqIdx interpreted as a [[PosInExpr]].
   * @return
   *   The tactic of type `T` that can be readily applied at the specified position to any given BelleExpr.
   * @note
   *   Convenience wrapper
   * @see
   *   [[PosInExpr]]
   * @see
   *   [[apply(position: Position)]]
   * @see
   *   [[Fixed]]
   */
  final def apply(seqIdx: Int, inExpr: List[Int] = Nil): T = apply(Fixed(Position(seqIdx, inExpr)))
  final def apply(seqIdx: Int, inExpr: PosInExpr): T = apply(Fixed(Position(seqIdx, inExpr.pos)))

  /**
   * Returns the tactic at the position identified by `locator`.
   *
   * @param locator
   *   The locator symbol at which to apply this AtPosition: 'L (find left), 'R (find right), '_ (find left/right
   *   appropriately for tactic), 'Llast (at last position in antecedent), or 'Rlast (at last position in succedent).
   * @note
   *   Convenience wrapper
   * @see
   *   [[org.keymaerax.bellerophon.AtPosition]]
   * @see
   *   [[apply(locator: PositionLocator)]]
   */
  // @todo turn into properly type-checkable locator arguments without going crazy long.
  final def apply(locator: Symbol, inExpr: PosInExpr): T = locator match {
    case Symbol("L") => apply(FindL(0, None, HereP, exact = true, BuiltinSymbols.all))
    case Symbol("R") => apply(FindR(0, None, HereP, exact = true, BuiltinSymbols.all))
    case Symbol("_") => this match {
        case _: LeftTactic => apply(FindL(0, None, HereP, exact = true, BuiltinSymbols.all))
        case _: RightTactic => apply(FindR(0, None, HereP, exact = true, BuiltinSymbols.all))
        case _ => throw new IllFormedTacticApplicationException(
            "Cannot determine whether this tactic is left/right. Please use 'L or 'R as appropriate."
          )
      }
    case Symbol("Llast") => apply(LastAnte(0, inExpr))
    case Symbol("Rlast") => apply(LastSucc(0, inExpr))
  }
  final def apply(locator: Symbol): T = apply(locator, HereP)

  /**
   * Returns the tactic at the position identified by `locator`, ensuring that `locator` will yield the formula
   * `expected` verbatim.
   *
   * @param locator
   *   The locator symbol at which to apply this AtPosition: 'L (find left), 'R (find right), '_ (find left/right
   *   appropriately for tactic), 'Llast (at last position in antecedent), or 'Rlast (at last position in succedent).
   * @param expected
   *   the formula expected at the position that `locator` identifies. Contract fails if that expectation is not met.
   * @note
   *   Convenience wrapper
   * @see
   *   [[org.keymaerax.bellerophon.AtPosition]]
   * @see
   *   [[apply()]]
   */
  final def apply(locator: Symbol, expected: Expression, defs: Declaration): T = locator match {
    case Symbol("L") => apply(FindL(0, Some(expected), HereP, exact = true, defs))
    case Symbol("Llike") => apply(FindL(0, Some(expected), HereP, exact = false, defs))
    case Symbol("R") => apply(FindR(0, Some(expected), HereP, exact = true, defs))
    case Symbol("Rlike") => apply(FindR(0, Some(expected), HereP, exact = false, defs))
    case Symbol("_") => this match {
        case _: LeftTactic => apply(FindL(0, Some(expected), HereP, exact = true, defs))
        case _: RightTactic => apply(FindR(0, Some(expected), HereP, exact = true, defs))
        case _ => throw new IllFormedTacticApplicationException(
            "Cannot determine whether this tactic is left/right. Please use 'L or 'R as appropriate."
          )
      }
    // @todo how to check expected formula?
    case Symbol("Llast") => logger.info("INFO: will not check expected for 'Llast yet"); apply(LastAnte(0))
    case Symbol("Rlast") => logger.info("INFO: will not check expected for 'Rlast yet"); apply(LastSucc(0))
  }
  final def apply(locator: Symbol, expected: Expression): T = apply(locator, expected, BuiltinSymbols.all)

}

/**
 * PositionTactics are tactics that can be [[AtPosition applied at positions]] giving ordinary tactics.
 *
 * @see
 *   [[AtPosition]]
 */
trait PositionalTactic extends BelleExpr with AtPosition[AppliedPositionTactic] {

  /** @note this should be called from within interpreters, but not by end-users */
  def computeResult(provable: ProvableSig, position: Position): ProvableSig
  final override def apply(locator: PositionLocator): AppliedPositionTactic = AppliedPositionTactic(this, locator)
}

/**
 * Tactics that can only be applied in the antecedent on the left.
 *
 * @see
 *   [[LeftRule]]
 */
trait LeftTactic extends PositionalTactic {

  /** @note this should be called from within interpreters, but not by end-users */
  def computeResult(provable: ProvableSig, position: AntePosition): ProvableSig

  @throws[IllFormedTacticApplicationException]("if rule applied on the (incorrect) right side")
  final override def computeResult(provable: ProvableSig, position: Position): ProvableSig = position match {
    case p: AntePosition => computeResult(provable, p)
    case _ => throw new IllFormedTacticApplicationException(
        "LeftTactics can only be applied at a left position not at " + position
      )
  }
}

/**
 * Tactics that can only be applied in the succedent on the right.
 *
 * @see
 *   [[RightRule]]
 */
trait RightTactic extends PositionalTactic {

  /** @note this should be called from within interpreters, but not by end-users */
  def computeResult(provable: ProvableSig, position: SuccPosition): ProvableSig

  @throws[IllFormedTacticApplicationException]("if rule applied on the (incorrect) left side")
  final override def computeResult(provable: ProvableSig, position: Position): ProvableSig = position match {
    case p: SuccPosition => computeResult(provable, p)
    case _ => throw new IllFormedTacticApplicationException(
        "RightTactics can only be applied at a right position not at " + position
      )
  }
}

/* Common base class for built-in tactics coming from the base layer of the tactic library directly manipulate core Provables. */
abstract case class BuiltInTactic(name: String) extends NamedBelleExpr with (ProvableSig => ProvableSig) {
  private[bellerophon] final def execute(provable: ProvableSig): ProvableSig = result(provable)
  private[keymaerax] def result(provable: ProvableSig): ProvableSig
  def apply(provable: ProvableSig): ProvableSig = result(provable)
}

/** Built-in position tactics such as assertAt */
abstract case class BuiltInPositionTactic(name: String) extends PositionalTactic with NamedBelleExpr

/**
 * Built-in position tactics coming from the core that are to be applied on the left. Unlike [[BuiltInLeftTactic]],
 * wraps [[MatchError]] from the core in readable errors.
 *
 * @see
 *   [[TacticInapplicableFailure]]
 */
abstract case class CoreLeftTactic(name: String) extends LeftTactic with NamedBelleExpr {
  @throws[TacticInapplicableFailure]("if formula has the wrong shape for this rule")
  final override def computeResult(provable: ProvableSig, position: AntePosition): ProvableSig =
    try { computeCoreResult(provable, position) }
    catch {
      case ex: MatchError => throw new TacticInapplicableFailure(
          "Tactic " + name + " applied at " + position + " on a non-matching expression in " + provable.prettyString,
          ex,
        )
    }

  def computeCoreResult(provable: ProvableSig, pos: AntePosition): ProvableSig
}

/**
 * Built-in position tactics coming from the core that are to be applied on the right Unlike [[BuiltInRightTactic]],
 * wraps [[MatchError]] from the core in readable errors.
 *
 * @see
 *   [[TacticInapplicableFailure]]
 */
abstract case class CoreRightTactic(name: String) extends RightTactic with NamedBelleExpr {
  @throws[TacticInapplicableFailure]("if formula has the wrong shape for this rule")
  final override def computeResult(provable: ProvableSig, position: SuccPosition): ProvableSig =
    try { computeCoreResult(provable, position) }
    catch {
      case ex: MatchError => throw new TacticInapplicableFailure(
          "Tactic " + name + " applied at " + position + " on a non-matching expression in " + provable.prettyString,
          ex,
        )
    }

  def computeCoreResult(provable: ProvableSig, pos: SuccPosition): ProvableSig
}

/** Built-in position tactics that are to be applied on the left */
abstract case class BuiltInLeftTactic(name: String) extends LeftTactic with NamedBelleExpr

/** Built-in position tactics that are to be applied on the right */
abstract case class BuiltInRightTactic(name: String) extends RightTactic with NamedBelleExpr

@deprecated
abstract case class DependentTwoPositionTactic(name: String) extends NamedBelleExpr {
  override def prettyString: String = s"UnappliedTwoPositionTactic of name $name" // @todo

  def computeExpr(p1: Position, p2: Position): DependentTactic

  def apply(p1: Position, p2: Position) = AppliedDependentTwoPositionTactic(this, p1, p2)
}
@deprecated
case class AppliedDependentTwoPositionTactic(t: DependentTwoPositionTactic, p1: Position, p2: Position)
    extends BelleExpr {

  /** Pretty-printed form of this Bellerophon tactic expression. */
  override def prettyString: String = t.prettyString + "(" + p1 + "," + p2 + ")"
}

/** Stores the position tactic and position at which the tactic was applied. Useful for storing execution traces. */
case class AppliedPositionTactic(positionTactic: PositionalTactic, locator: PositionLocator)
    extends BelleExpr with (ProvableSig => ProvableSig) {
  import org.keymaerax.infrastruct.Augmentors._

  /** True if the `fml` matches the `shape`, false otherwise. */
  private def matches(fml: Option[Expression], shape: Expression): Boolean = {
    // @note shape in tactics is always abbreviated (without interpretation), formula is either expanded fn<<...>>(x) or abbreviated fn(x)
    val traverse = new ExpressionTraversalFunction() {
      override def postT(p: PosInExpr, e: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = e match {
        case FuncOf(fn, args) => Right(FuncOf(fn.copy(interp = None), args))
        case _ => Left(None)
      }
    }
    ExpressionTraversal.traverse(traverse, shape) match {
      case Some(shapeAbbrev) => fml.flatMap(ExpressionTraversal.traverse(traverse, _)).contains(shapeAbbrev)
      case None => false
    }
  }

  final def computeResult(provable: ProvableSig): ProvableSig =
    try {
      locator match {
        // @note interprets PositionLocator
        case Fixed(pos, shape, exact) => shape match {
            case Some(f: Formula) =>
              require(
                provable.subgoals.size == 1,
                "Locator 'fixed with shape' applies only to provables with exactly 1 subgoal since otherwise ill-defined",
              )
              // @note (implicit .apply needed to ensure subposition to pos.inExpr
              if (
                (exact && matches(provable.subgoals.head.sub(pos), f)) ||
                (!exact && provable.subgoals.head.sub(pos).flatMap(UnificationMatch.unifiable(f, _)).isDefined)
              ) { positionTactic.computeResult(provable, pos) }
              else {
                throw new IllFormedTacticApplicationException(
                  "Formula " + provable.subgoals.head.sub(pos).getOrElse("") + " at position " + pos +
                    " is not of expected shape " + f + " in sequent \n" + provable.subgoals.head.prettyString
                )
              }
            case None => positionTactic.computeResult(provable, pos)
          }
        case l @ Find(_, _, start, _, _) => tryAllAfter(
            provable,
            l,
            new TacticInapplicableFailure(
              "Not found: locator " + locator.prettyString + "\nof position tactic " + prettyString +
                "\ndoes not match anywhere in " + (if (start.isAnte) "antecedent" else "succedent") + " of\n" +
                provable.prettyString
            ),
          )
        case LastAnte(goal, sub) => positionTactic
            .computeResult(provable, AntePosition.base0(provable.subgoals(goal).ante.size - 1, sub))
        case LastSucc(goal, sub) => positionTactic
            .computeResult(provable, SuccPosition.base0(provable.subgoals(goal).succ.size - 1, sub))
      }
    } catch {
      case be: BelleThrowable => throw be
      case ex: IndexOutOfBoundsException => throw new IllFormedTacticApplicationException(
          prettyString + ": applied at position " + locator.prettyString +
            " may point outside the positions of the goal " + provable.underlyingProvable.prettyString,
          ex,
        )
    }

  /** @inheritdoc */
  override def apply(provable: ProvableSig): ProvableSig = computeResult(provable)

  /** Recursively tries the position tactic at positions at or after the locator's start in the specified provable. */
  @tailrec
  private def tryAllAfter(provable: ProvableSig, locator: Find, cause: => BelleThrowable): ProvableSig = {
    if (provable.subgoals.isEmpty) throw new TacticInapplicableFailure(
      s"Dependent position tactic $prettyString is not applicable at ${locator.start.prettyString} since provable has no subgoals"
    )
    if (locator.start.isIndexDefined(provable.subgoals(locator.goal))) {

      /**
       * Left: definitely known to be applicable, Right: unknown to be applicable but worth a try; None: inapplicable.
       */
      @tailrec
      def toPos(locator: Find): Option[Either[Position, Position]] = {
        if (locator.start.isIndexDefined(provable.subgoals(locator.goal))) {
          locator.toPosition(provable) match {
            case Some(pos) => provable.subgoals(locator.goal).sub(pos) match {
                case Some(expr) => TacticIndex.default.isApplicable(expr, this) match {
                    case Some(true) => Some(Left(pos))
                    case Some(false) => toPos(
                        Find(locator.goal, locator.shape, pos.topLevel.advanceIndex(1), locator.exact, locator.defs)
                      )
                    case None => Some(Right(pos))
                  }
                case None =>
                  toPos(Find(locator.goal, locator.shape, pos.topLevel.advanceIndex(1), locator.exact, locator.defs))
              }
            case None => None
          }
        } else { None }
      }
      toPos(locator) match {
        case Some(Left(pos)) => positionTactic.computeResult(provable, pos)
        case Some(Right(pos)) =>
          try { positionTactic.computeResult(provable, pos) }
          catch {
            case _: BelleProofSearchControl =>
              // trial-and-error fallback for default case in TacticIndex.isApplicable
              tryAllAfter(provable, locator.copy(start = locator.start.advanceIndex(1)), cause)
          }
        case _ => throw cause
      }
    } else throw cause
  }

  override def prettyString: String = positionTactic.prettyString + "(" + locator.prettyString + ")"

  override def toString: String = prettyString + "\n with locator " + locator.toString + ")"
}

abstract case class BuiltInTwoPositionTactic(name: String) extends NamedBelleExpr {

  /** @note this should be called from within interpreters, but not by end users. */
  def computeResult(provable: ProvableSig, posOne: Position, posTwo: Position): ProvableSig

  /** Returns an explicit representation of the application of this tactic to the provided positions. */
  final def apply(posOne: Position, posTwo: Position): AppliedBuiltinTwoPositionTactic =
    AppliedBuiltinTwoPositionTactic(this, posOne, posTwo)

  /**
   * Returns an explicit representation of the application of this tactic to the provided positions.
   *
   * @note
   *   Convenience wrapper
   */
  final def apply(posOne: Int, posTwo: Int): AppliedBuiltinTwoPositionTactic = apply(Position(posOne), Position(posTwo))
}

/** Motivation is similar to [[AppliedPositionTactic]], but for [[BuiltInTwoPositionTactic]] */
case class AppliedBuiltinTwoPositionTactic(positionTactic: BuiltInTwoPositionTactic, posOne: Position, posTwo: Position)
    extends BelleExpr with (ProvableSig => ProvableSig) {
  final def computeResult(provable: ProvableSig): ProvableSig = positionTactic.computeResult(provable, posOne, posTwo)
  override def apply(provable: ProvableSig): ProvableSig = computeResult(provable)

  override def prettyString: String = positionTactic.prettyString + "(" + posOne.prettyString + "," +
    posTwo.prettyString + ")"
}

/**
 * Dependent tactics compute a tactic to apply based on their input. These tactics are probably not necessary very
 * often, but are useful for idiomatic shortcuts. See e.g., AtSubgoal.
 *
 * @note
 *   similar to the ConstructionTactics in the old framework, except they should not be necessary nearly as often
 *   because BuiltIns have direct access to a Provable.
 * @param name
 *   The name of the tactic.
 * @todo
 *   is there a short lambda abstraction notation as syntactic sugar?
 */
abstract case class DependentTactic(name: String) extends NamedBelleExpr {

  /** Creates a tactic by inspecting the `provable`. */
  def computeExpr(provable: ProvableSig): BelleExpr = throw new NotImplementedError

  /** Creates a tactic by inspecting the `provable`. Default: forwards to [[computeExpr]](ProvableSig). */
  def computeExpr(provable: ProvableSig, labels: Option[List[BelleLabel]]): BelleExpr = computeExpr(provable)
  def computeExpr(e: BelleValue with BelleThrowable): BelleExpr = throw e

  /** Generic computeExpr, forwards to [[computeExpr]](Provable) and [[computeExpr]](BelleThrowable). */
  final def computeExpr(v: BelleValue): BelleExpr = v match {
    case BelleProvable(provable, labels) => computeExpr(provable, labels)
    case e: BelleThrowable => computeExpr(e)
  }
}
abstract class SingleGoalDependentTactic(override val name: String) extends DependentTactic(name) {
  def computeExpr(sequent: Sequent): BelleExpr = throw new NotImplementedError
  def computeExpr(sequent: Sequent, defs: Declaration): BelleExpr = computeExpr(sequent)

  /** @inheritdoc */
  final override def computeExpr(provable: ProvableSig): BelleExpr = computeExpr(provable, None)

  /** @inheritdoc */
  final override def computeExpr(provable: ProvableSig, labels: Option[List[BelleLabel]]): BelleExpr = {
    require(
      provable.subgoals.size <= 1,
      "1 subgoal expected, but got " + provable.subgoals.size + "\n" + provable.prettyString,
    )
    if (provable.subgoals.size == 1) computeExpr(provable.subgoals.head, provable.defs)
    else DebuggingTactics.done("Goal is proved, skipped tactic " + name)
  }
}

/**
 * DependentPositionTactics are tactics that can be [[AtPosition applied at positions]] giving dependent tactics.
 *
 * @see
 *   [[AtPosition]]
 */
abstract case class DependentPositionTactic(name: String) extends NamedBelleExpr with AtPosition[DependentTactic] {
  override def apply(locator: PositionLocator): AppliedDependentPositionTactic =
    new AppliedDependentPositionTactic(this, locator)
  override def prettyString: String = name

  /** Create the actual tactic to be applied at position pos */
  def factory(pos: Position): DependentTactic
}
abstract case class InputTactic(name: String, inputs: Seq[Any]) extends BelleExpr with NamedBelleExpr {
  def computeExpr(): BelleExpr

  override def prettyString: String = s"$name${BelleExpr.prettyArgs(inputs)}"

  override def equals(other: Any): Boolean = other match {
    case o: InputTactic => name == o.name && inputs == o.inputs
    case _ => false
  }
}
abstract class StringInputTactic(override val name: String, val inputs: Seq[String]) extends BuiltInTactic(name) {
  override def prettyString: String = s"$name(${inputs
      .map(input =>
        "\"" + input.flatMap({
          case '"' => "\""
          case c => c.toString
        }) + "\""
      )
      .mkString(",")})"

  override def equals(other: Any): Boolean = other match {
    case o: StringInputTactic => name == o.name && inputs == o.inputs
    case _ => false
  }
}

abstract class DependentPositionWithAppliedInputTactic(private val n: String, val inputs: Seq[Any])
    extends DependentPositionTactic(n) {
  override def apply(locator: PositionLocator): AppliedDependentPositionTacticWithAppliedInput =
    new AppliedDependentPositionTacticWithAppliedInput(this, locator)
  // @note non-serializable pretty-string, only applied tactic is serializable. @see AppliedDependendPositionTacticWithAppliedInput
  override def prettyString: String = super.prettyString + BelleExpr.prettyArgs(inputs)

  override def equals(other: Any): Boolean = other match {
    case o: DependentPositionWithAppliedInputTactic => o.n == n && o.inputs == inputs
    case o: DependentPositionTactic => inputs.isEmpty && o.name == n
    case _ => false
  }
}
class AppliedDependentPositionTacticWithAppliedInput(
    override val pt: DependentPositionWithAppliedInputTactic,
    locator: PositionLocator,
) extends AppliedDependentPositionTactic(pt, locator) {
  override def prettyString: String =
    if (pt.inputs.nonEmpty) {
      val each = BelleExpr.persistable(pt.inputs).flatMap(BelleExpr.printOne(_, pt.inputs.size <= 1))
      s"${pt.name}(${each.mkString(", ")}, ${locator.prettyString})"
    } else pt.name + "(" + locator.prettyString + ")"

  override def equals(other: Any): Boolean = other match {
    case o: AppliedDependentPositionTactic => o.pt == pt && o.locator == locator
    case _ => false
  }
}
class AppliedDependentPositionTactic(val pt: DependentPositionTactic, val locator: PositionLocator)
    extends DependentTactic(pt.name) {
  import org.keymaerax.infrastruct.Augmentors._
  override def prettyString: String = pt.name + "(" + locator.prettyString + ")"

  /** True if the `fml` matches the `shape`, false otherwise. */
  private def matches(fml: Option[Expression], shape: Expression): Boolean = {
    // @note shape in tactics may or may not be with interpretation, formula is either expanded fn<<...>>(x) or abbreviated fn(x)
    val uninterp = ExpressionTraversal
      .traverse(
        new ExpressionTraversalFunction() {
          override def preT(p: PosInExpr, e: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = e match {
            case FuncOf(fn, args) => Right(FuncOf(fn.copy(interp = None), args))
            case _ => Left(None)
          }
        },
        _: Expression,
      )
      .get
    fml.map(uninterp).contains(uninterp(shape))
  }

  final override def computeExpr(provable: ProvableSig, labels: Option[List[BelleLabel]]): BelleExpr =
    /*final override def computeExpr(v: BelleValue): BelleExpr =*/ try {
      locator match {
        // @note interprets PositionLocator
        case Fixed(pos, shape, exact) => shape match {
            case Some(f) =>
              require(
                provable.subgoals.size == 1,
                "Locator 'fixed with shape' applies only to provables with exactly 1 subgoal",
              )
              // @note (implicit .apply needed to ensure subposition to pos.inExpr
              if (
                (exact && matches(provable.subgoals.head.sub(pos), f)) ||
                (!exact && UnificationMatch.unifiable(f, provable.subgoals.head.sub(pos).get).isDefined)
              ) { pt.factory(pos).computeExpr(BelleProvable(provable, labels)) }
              else {
                throw new TacticInapplicableFailure(
                  "Formula " + provable.subgoals.head.sub(pos) + " at position " + pos + " is not of expected shape " +
                    f + " in sequent \n" + provable.subgoals.head.prettyString
                )
              }
            case None => pt.factory(pos).computeExpr(BelleProvable(provable, labels))
          }
        case l @ Find(_, _, start, _, _) => tryAllAfter(
            l,
            new TacticInapplicableFailure(
              "Not found: locator " + locator.prettyString + "\nof position tactic " + prettyString +
                "\ndoes not match anywhere in " + (if (start.isAnte) "antecedent" else "succedent") + " of\n" +
                provable.prettyString
            ),
          )
        case LastAnte(goal, sub) => pt.factory(AntePosition.base0(provable.subgoals(goal).ante.size - 1, sub))
        case LastSucc(goal, sub) => pt.factory(SuccPosition.base0(provable.subgoals(goal).succ.size - 1, sub))
      }
    } catch {
      // note the following exceptions are likely caused by wrong positioning
      case be: BelleCriticalException => locator match {
          case _: Find => throw be
          case Fixed(pos, _, _) =>
            if (provable.subgoals.size == 1) {
              def printParents(p: Position): String =
                if (p.isTopLevel) { provable.subgoals.head(p.top).prettyString + " at " + p.prettyString }
                else {
                  (provable.subgoals.head.sub(p) match {
                    case Some(e) => e.prettyString + " at " + p.prettyString
                    case _ => "(nothing) at " + p.prettyString
                  }) + "\n" + printParents(p.topLevel ++ PosInExpr(p.inExpr.pos.dropRight(1)))
                }
              def printWithParents(p: Position): String =
                if (pos.isIndexDefined(provable.subgoals.head)) {
                  provable.subgoals.head.sub(p) match {
                    case Some(e) => e.prettyString
                    case _ => printParents(p)
                  }
                } else {
                  "position " + p.prettyString + " outside sequent: expected -1...-" +
                    provable.subgoals.head.ante.size + " or 1..." + provable.subgoals.head.succ.size
                }
              throw be.inContext(
                this,
                s"""Tactic $prettyString is not applicable for
                   |    ${printWithParents(pos)}
                   |at position ${locator.prettyString}
                   |because ${be.getMessage}""".stripMargin,
              )
            } else throw be
        }
      case ex: IndexOutOfBoundsException => throw new IllFormedTacticApplicationException(
          prettyString + ": applied at position " + locator.prettyString +
            " may point outside the positions of the goal " + provable.prettyString,
          ex,
        )
    }

  /** Recursively tries the position tactic at positions at or after pos in the specified provable. */
  private def tryAllAfter(locator: Find, cause: => BelleThrowable): DependentTactic = new DependentTactic(name) {

    /** @inheritdoc */
    final override def computeExpr(provable: ProvableSig, labels: Option[List[BelleLabel]]): BelleExpr = {
      if (provable.subgoals.isEmpty) throw new TacticInapplicableFailure(
        s"Dependent position tactic ${this.prettyString} is not applicable at ${locator.start.prettyString} since provable has no subgoals"
      )
      if (locator.start.isIndexDefined(provable.subgoals(locator.goal))) {
        @tailrec
        def toPos(locator: Find): Option[Either[Position, Position]] = {
          if (locator.start.isIndexDefined(provable.subgoals(locator.goal))) {
            locator.toPosition(provable) match {
              case Some(pos) => provable.subgoals(locator.goal).sub(pos) match {
                  case Some(expr) => TacticIndex.default.isApplicable(expr, this) match {
                      case Some(true) => Some(Left(pos))
                      case Some(false) => toPos(locator.copy(start = pos.topLevel.advanceIndex(1)))
                      case None => Some(Right(pos))
                    }
                  case _ => toPos(locator.copy(start = pos.topLevel.advanceIndex(1)))
                }
              case None => None
            }
          } else { None }
        }
        toPos(locator) match {
          case Some(Left(pos)) => pt.factory(pos)
          case Some(Right(pos)) => pt.factory(pos) |
              tryAllAfter(locator.copy(start = pos.topLevel.advanceIndex(1)), cause)
          case _ => throw cause
        }
      } else if (cause == null) {
        throw new TacticInapplicableFailure(
          s"Dependent position tactic ${this
              .prettyString} is not applicable at ${locator.start.prettyString} in ${provable.subgoals(locator.goal).prettyString}"
        )
      } else throw cause
    }

    /** @inheritdoc */
    final override def computeExpr(e: BelleValue with BelleThrowable): BelleExpr = pt
      .factory(locator.start)
      .computeExpr(e) | tryAllAfter(locator.copy(start = locator.start.advanceIndex(1)), cause)
  }

  override def equals(other: Any): Boolean = other match {
    case o: AppliedDependentPositionTactic => o.pt == pt && o.locator == locator
    case _ => false
  }
}

/**
 * A partial tactic marks an unclosed proof (mainly for testing purposes to not insist on a closed proof). To check for
 * closed subgoals, use [[TactixLibrary.done]].
 */
case class PartialTactic(child: BelleExpr, label: Option[BelleLabel] = None) extends BelleExpr {
  override def prettyString: String = label match {
    case Some(theLabel) => s"partial(${child.prettyString})@(${theLabel.prettyString})"
    case None => s"partial(${child.prettyString})"
  }
}

// advanced combinators

/**
 * `OnAll(e)(BelleProvable(p)) == <(e, ..., e)` does the same tactic on all branches where e occurs the appropriate
 * number of times, which is `p.subgoals.length` times.
 *
 * @todo
 *   eisegesis
 */
case class OnAll(e: BelleExpr) extends BelleExpr {
  override def prettyString: String = "doall(" + e.prettyString + ")"
}

/**
 * `ChooseSome(options, e)(pr)` proves `e(o)(pr)` after choosing some option `o` from `options` whose proof with tactic
 * `e` succeeds after supplying argument `o` to `e`. It's usually one of the first options `o` for which `e(o)(pr)` does
 * not fail. Fails if no choice from `options` made `e(o)(pr)` succeed.
 *
 * @param options
 *   The (lazy) iterator or stream from which subsequent options `o` will be tried.
 * @param e
 *   The tactic generator `e` that will be tried with input `o` on the Provable subsequently for each of the options `o`
 *   in `options` until one is found for which `e(o)` does not fail.
 * @author
 *   Andre Platzer
 * @see
 *   [[EitherTactic]]
 */
case class ChooseSome[A](options: () => Iterator[A], e: A => BelleExpr) extends BelleExpr {
  override def prettyString: String = "dosome(" + e + ")"
}

/**
 * `Let(abbr, value, inner)` alias `let abbr=value in inner` abbreviates `value` by `abbr` in the provable and proceeds
 * with an internal proof by tactic `inner`, resuming to the outer proof by a uniform substitution of `value` for `abbr`
 * of the resulting provable.
 *
 * @see
 *   [[ProvableSig.apply(USubst)]]
 * @todo
 *   generalize inner to also AtPosition[E]
 */
case class Let(abbr: Expression, value: Expression, inner: BelleExpr) extends BelleExpr {
  require(
    abbr.kind == value.kind,
    "Abbreviation and value must be of same kind, but got abbr.kind=" + abbr.kind + " and value.kind=" + value.kind,
  )
  override def prettyString: String = "let(" + abbr + "=" + value + " in " + inner + ")"
}

/**
 * `LetInspect(abbr, instantiator, inner)` alias `let abbr := inspect instantiator in inner` postpones the choice for
 * the definition of `abbr` until tactic `inner` finished on the Provable, and asks `instantiator` to choose a value for
 * `abbr` based on that Provable at the end of `inner`. Resumes to the outer proof by a uniform substitution of
 * `instantiator(result)` for `abbr` of the resulting provable.
 *
 * @see
 *   [[ProvableSig.apply(USubst)]]
 * @todo
 *   generalize inner to also AtPosition[E]
 * @note
 *   abbr should be fresh in the Provable
 */
case class LetInspect(abbr: Expression, instantiator: ProvableSig => Expression, inner: BelleExpr) extends BelleExpr {
  override def prettyString: String = "let(" + abbr + ":= inspect " + instantiator + " in " + inner + ")"
}

/**
 * `SearchAndRescue(abbr, common, instantiator, continuation)` alias `search abbr := after common among instantiator in
 * continuation` postpones the choice for the definition of `abbr` until tactic `common` finished on the Provable, but
 * then searches for the definition of `abbr` by trying to run `continuation` from the outcome of `common` until
 * `continuation` is successful. Each time it asks `instantiator` to choose a value for `abbr` based on the same
 * Provable at the end of `common` in addition to the present ProverException obtained after the current attempt of
 * running `continuation` with the last choice for `abbr`. Resumes to the outer proof by a uniform substitution of
 * instantiator(result)` for `abbr` of the resulting provable which corresponds to having run `USubst(abbr,inst){ common
 * } ; continuation`. Thus, the logical effect is identical to directly running `USubst(abbr,inst){ common } ;
 * continuation` but the operational effect differs by the above search to find the instantiation `inst` in the first
 * place.
 *
 * @see
 *   [[ProvableSig.apply(USubst)]]
 * @param abbr
 *   the abbreviation to instantie, which should be fresh in the Provable
 * @see
 *   Andre Platzer.
 *   [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]].
 *   Journal of Automated Reasoning, 59(2), pp. 219-266, 2017. Example 32.
 * @see
 *   [[NoProverException]]
 */
case class SearchAndRescueAgain(
    abbr: scala.collection.immutable.Seq[Expression],
    common: BelleExpr,
    instantiator: (ProvableSig, ProverException) => scala.collection.immutable.Seq[Expression],
    continuation: BelleExpr,
) extends BelleExpr {
  override def prettyString: String = "searchAndRescueAgain(" + abbr + ":= after " + common + " among " + instantiator +
    " in " + continuation + ")"
}

/** Defines a tactic for later execution. */
case class DefTactic(name: String, t: BelleExpr) extends BelleExpr {
  override def prettyString: String = s"tactic $name as (${t.prettyString})"
}

/** Applies the tactic definition `t`. */
case class ApplyDefTactic(t: DefTactic) extends BelleExpr {
  override def prettyString: String = t.name
}

/** Bellerophon expressions that are values, so should not be evaluated any further since irreducible. */
trait BelleValue {
  def prettyString: String = toString
}

object BelleProvable {
  def plain(p: ProvableSig): BelleProvable = BelleProvable(p, None)
  def labeled(p: ProvableSig, label: Option[List[BelleLabel]]): BelleProvable = BelleProvable(p, label)
}

/** A Provable during a Bellerophon interpreter run, readily paired with an optional list of BelleLabels */
case class BelleProvable(p: ProvableSig, label: Option[List[BelleLabel]]) extends BelleExpr with BelleValue {
  if (label.nonEmpty) insist(
    label.get.length == p.subgoals.length,
    s"Length of label set (${label.get.length}) should equal number of remaining subgoals (${p.subgoals.length})",
  )
  override def toString: String = p.prettyString
  override def prettyString: String = p.prettyString
}

/** A Provable that was produced with a delayed substitution `subst`. */
class BelleDelayedSubstProvable(
    override val p: ProvableSig,
    override val label: Option[List[BelleLabel]],
    val subst: USubst,
    // @todo parent needs to be a list of provables and substs to support nested constifications etc., or complete data structure refactoring to emulate goals that close later with subproofs
    val parent: Option[(ProvableSig, Int)],
) extends BelleProvable(p, label) {
  assert(
    parent.isEmpty || parent.get._2 < parent.get._1.subgoals.size,
    "Subgoal index points outside provable: " + parent.get._1.subgoals,
  )
  override def toString: String = "Delayed substitution\n" + p.prettyString + "\nby\n" + subst.toString
  override def prettyString: String = "Delayed substitution\n" + p.prettyString + "\nby\n" + subst.toString
}

/**
 * Internal: To communicate proof IDs of subproofs opened in the spoon-feeding interpreter in Let between requests. NOT
 * TO BE USED FOR ANYTHING ELSE
 */
case class BelleSubProof(id: Int) extends BelleValue

////////////////////////////////////////////////////////////////////////////////////////////////////
// Bellerophon Labeling
////////////////////////////////////////////////////////////////////////////////////////////////////

/** Assign the given label `label` to the present BelleProvable. */
case class LabelBranch(label: BelleLabel) extends BelleExpr with NoOpTactic {
  override def prettyString: String = "label(\"" + label.prettyString + "\")"
}

//abstract class LabelledGoalsDependentTactic(override val name: String) extends DependentTactic(name) with Logging {
//  def computeExpr(provable: ProvableSig, labels: List[BelleLabel]): BelleExpr = throw new NotImplementedError
//  /** Generic computeExpr; prefer overriding computeExpr(Provable) and computeExpr(BelleThrowable) */
//  override def computeExpr(v : BelleValue): BelleExpr = v match {
//    case BelleProvable(provable, Some(labels), _) => computeExpr(provable, labels)
//    case BelleProvable(provable, None, _) => computeExpr(provable)
//    case e: BelleThrowable => super.computeExpr(e)
//  }
//}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Bellerophon Types
////////////////////////////////////////////////////////////////////////////////////////////////////

/** @todo eisegesis -- simple types */
@deprecated("remove")
trait BelleType
@deprecated("remove")
case class TheType() extends BelleType

/** @todo Added because SequentTypes are needed for unification tactics. */
@deprecated("remove")
case class SequentType(s: Sequent) extends BelleType
