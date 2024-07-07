/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.bellerophon

import org.keymaerax.core.{Expression, False, NamedSymbol, Provable, ProverException, Sequent}
import org.keymaerax.infrastruct.LinearMatcher.Subst
import org.apache.commons.lang3.StringUtils

/** KeYmaera X Tactic Exceptions. */
//@todo class TacticException(msg:String) extends ProverException(msg)

/**
 * Common exception type for all Bellerophon tactic problems and exceptions. Tactic exceptions come on three different
 * kinds:
 *   1. [[BelleCriticalException]] indicates an internal bug in a tactic implementation, such as applying left rules on
 *      the right. They will be reported but need a KeYmaera X implementation change to fix. 2.
 *      [[BelleUserCorrectableException]] indicates that the user has provided an unsuitable input problem or made a
 *      correctable error in a proof step. They will be reported back to the user along with a legible message
 *      describing what needs to be changed in the problem or proof. 3. [[BelleProofSearchControl]] indicates that one
 *      proof attempt did not succeed so other proof options should be tried. They will be swallowed by any outer proof
 *      search tactics that will try something else instead.
 * Some advanced proof search tactics may "convert" between these exception types or swallow more of them when they
 * deliberately try steps they know may fail spectacularly but have a backup plan.
 */
abstract class BelleThrowable(message: => String, cause: Throwable = null) extends ProverException("", cause) {
  /* @note message not passed to super (constructing Bellerophon messages tends to be expensive, so construct on demand only) */

  /* @note mutable state for gathering the logical context that led to this exception */
  private var tacticContext: BelleExpr = BelleDot // @todo BelleUnknown?
  def context: BelleExpr = tacticContext
  // @todo optimizable lazy String for speed?
  def inContext(context: BelleExpr, additionalMessage: String): BelleThrowable = {
    this.tacticContext = context
    super.inContext(context.prettyString, additionalMessage)
    this
  }

  /** Read the message describing what went wrong. */
  override def getMessage: String = message

  override def toString: String = getMessage() + "\n" + super.toString + "\nin " +
    StringUtils.abbreviate(tacticContext.toString, 1000)
}

//<editor-fold desc="Exception groups">

/**
 * Reported bug: Major syntactic and semantic errors in bellerophon tactics that indicate a tactic is broken. For
 * example, forgetting to provide an expected position or applying a left tactic on the right. BelleInterpreter will
 * raise the error to the user's attention but it needs an internal fix to KeYmaera X.
 */
abstract class BelleCriticalException(message: => String, cause: Throwable = null)
    extends BelleThrowable(message, cause)

/**
 * User feedback: Indicates that the user has provided an unsuitable input problem or made a correctable error in a
 * proof step. They will be reported back to the user along with a legible message describing what needs to be changed
 * in the problem or proof.
 */
abstract class BelleUserCorrectableException(message: => String, cause: Throwable = null)
    extends BelleThrowable(message, cause)

/**
 * Search control: Silently raises issues to control proof search, indicating that one proof attempt did not succeed so
 * other proof options should be tried. They will be swallowed by any outer proof search tactics that will try something
 * else instead. For example, trying to apply an implyR tactic at a succedent position that contains an Or will be
 * inapplicable but does not indicate a bug in the tactic, merely that a different branch needs to be taken in proof
 * search.
 * @see
 *   [[BelleTacticFailure]]
 * @see
 *   [[TacticInapplicableFailure]]
 */
abstract class BelleProofSearchControl(message: => String, cause: Throwable = null)
    extends BelleThrowable(message, cause)

//</editor-fold>

//<editor-fold desc="Critical exceptions">

/**
 * Ill-formed ways of applying tactics, such as missing position for a position tactic or supplying a term when a
 * formula was expected. Or applying a tactic at -1 that can only applied in the succedent or vice versa. This indicates
 * a catastrophic logical error in the whole tactic implementation.
 */
class IllFormedTacticApplicationException(message: => String, cause: Throwable = null)
    extends BelleCriticalException(message, cause)

/** Incorrect prover setup, such as insufficient stack size or missing tools. */
class ProverSetupException(message: => String, cause: Throwable = null) extends BelleCriticalException(message, cause)

/** Signals an unexpected proof state (e.g., an open goal that should have been closed). */
class BelleUnexpectedProofStateError(message: => String, val proofState: Provable, cause: Throwable = null)
    extends BelleCriticalException(message, cause) {
  override def toString: String = message + "\n" + proofState.prettyString
}

/**
 * Raised to indicate that two expressions are not unifiable in the single-sided matching sense.
 * @param shape
 *   The shape against which to match.
 * @param input
 *   The expression that we were trying to match against the given shape.
 * @param info
 *   Additional information
 */
class UnificationException(val shape: Expression, val input: Expression, info: String = "", cause: Throwable = null)
    extends BelleCriticalException(
      "Un-Unifiable: " + shape.prettyString + "\nfor:          " + input.prettyString + "\n" + info,
      cause,
    ) {}

class SeqUnificationException(val shape: Sequent, val input: Sequent, info: String = "", cause: Throwable = null)
    extends BelleCriticalException(
      "Un-Unifiable: " + shape.prettyString + "\nfor:          " + input.prettyString + "\n" + info,
      cause,
    ) {}

class SubstUnificationException(val shape: Subst, val input: Subst, info: String = "", cause: Throwable = null)
    extends BelleCriticalException(
      "Un-Unifiable: <unifier> " + shape.toString + "\nfor:          <unifier> " + input + "\n" + info,
      cause,
    ) {}

/** Tactic requirements that failed and indicate a critical logical error in using it. */
class TacticRequirementError(message: => String) extends BelleCriticalException(message)

/** Tactic assertions. */
class TacticAssertionError(message: => String) extends BelleCriticalException(message)

/** Error indicates that a (critical) infinite tactic loop is detected indicating an implementation error. */
class InfiniteTacticLoopError(message: => String) extends BelleCriticalException(message)

/**
 * A Bellerophon critical exception that consists of two reasons why it is being raised, for example, if two things went
 * wrong out of which it would have sufficed if only one succeeds.
 * @param left
 *   Primary reason.
 * @param right
 *   Alternate reason.
 */
class CompoundCriticalException(val left: BelleThrowable, val right: BelleThrowable)
//@note critical for now since raised only in interpreter
    extends BelleCriticalException("Left: " + left.getMessage + "\nRight: " + right.getMessage + ")", left)

//</editor-fold>

//<editor-fold desc="User-correctable exceptions">

/** Signals that an annotated invariant is not provable and needs fixing. */
class UnprovableAnnotatedInvariant(message: => String, cause: Throwable = null)
    extends BelleUserCorrectableException(message, cause)

class UnexpandedDefinitionsFailure(message: => String, cause: Throwable = null)
    extends BelleUserCorrectableException(message, cause)

class MissingLyapunovFunction(message: => String, cause: Throwable = null)
    extends BelleUserCorrectableException(message, cause)

/**
 * Signaling that a tactic was not applicable or did not work at the current goal. BelleTacticFailures will be consumed
 * by the BelleInterpreter which will try something else instead.
 */
abstract class BelleTacticFailure(message: => String, cause: Throwable = null)
    extends BelleProofSearchControl(message, cause)

/**
 * Tactic happens to not be applicable as indicated in the present sequent. For example, InapplicableTactic can be
 * raised when trying to apply [[org.keymaerax.btactics.SequentCalculus.andR]] at the correct position 2 in bounds on
 * the right-hand side where it turns out there is an Or formula not an And formula. This does not indicate a
 * catastrophic failure in the tactic implementation, merely a promising but unsuccessful attempt of applying a tactic.
 */
class TacticInapplicableFailure(message: => String, cause: Throwable = null) extends BelleTacticFailure(message, cause)

/**
 * Tactic was unable to unify with the given key and is, thus, inapplicable as indicated in the present sequent. Besides
 * indicating genuine unifiable situations, this may indicate that the wrong key was chosen for the (derived) axiom in
 * its [[org.keymaerax.btactics.macros.AxiomInfo]].
 */
class InapplicableUnificationKeyFailure(message: => String, cause: Throwable = null)
    extends BelleTacticFailure(message, cause)

/**
 * Signaling that a tactic's implementation was incomplete and did not work out as planned, so tactic execution might
 * continue, but it is indicating a potential problem in the tactic's implementation.
 */
class UnsupportedTacticFeature(message: => String, cause: Throwable = null) extends BelleTacticFailure(message, cause)

/** Signaling that a tactic input was not as expected. */
class InputFormatFailure(message: => String, cause: Throwable = null) extends BelleTacticFailure(message, cause)

/**
 * Signals a proof search failure. Also thrown by calls that are not "tactics" per se but might, e.g., be called
 * internally by a tactic May be caught internally by tactics to direct searches.
 */
class ProofSearchFailure(message: => String, cause: Throwable = null) extends BelleTacticFailure(message, cause)

//</editor-fold>

//<editor-fold desc="Proof search control">

/**
 * Raised when a tactic decides that all further tactical work on a goal is useless and bellerophon should immediately
 * stop
 * @param status
 *   signaling the status of the goal such as Counterexample, Valid
 * @param message
 *   readable description of the issue
 */
class BelleAbort(status: => String, message: => String, cause: Throwable = null)
    extends BelleProofSearchControl(message, cause)

/** Raised when a tactic wants to indicate that it is/was not able to make progress on the goal. */
class BelleNoProgress(message: => String, cause: Throwable = null) extends BelleProofSearchControl(message, cause)

/** Raised when provable `p` is not yet proved. */
case class BelleUnfinished(message: String, p: Provable)
    extends BelleProofSearchControl(
      if (p.subgoals.size == 1 && p.subgoals.head.ante.isEmpty && p.subgoals.head.succ == False :: Nil)
        message + { if (message.nonEmpty) ": " else "" } + "expected to have proved, but got false"
      else message + { if (message.nonEmpty) ": " else "" } + "expected to have proved, but got open goals"
    )

/** Raised when counterexamples are found in sequent `s`; `cex` contains counterexample values per named symbol. */
case class BelleCEX(message: String, cex: Map[NamedSymbol, Expression], s: Sequent)
    extends BelleProofSearchControl(message)

/**
 * A Bellerophon proof search exception that consists of two reasons why it is being raised, for example, if two things
 * went wrong out of which it would have sufficed if only one succeeds.
 * @param left
 *   Primary reason.
 * @param right
 *   Alternate reason.
 */
class CompoundProofSearchException(val left: BelleThrowable, val right: BelleThrowable)
    extends BelleProofSearchControl("Left: " + left.getMessage + "\nRight: " + right.getMessage + ")", left)

//</editor-fold>
