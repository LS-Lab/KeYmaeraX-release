/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core.{Provable, ProverException}

/**
 * KeYmaera X Tactic Exceptions.
 */
//@todo class TacticException(msg:String) extends ProverException(msg)

/** Common exception type for all Bellerophon tactic problems and exceptions.
  * Tactic exceptions come on three different kinds:
  *   1. [[BelleReportedError]] indicates an internal bug in a tactic implementation, such as applying left rules on the right.
  *      They will be reported but need a KeYmaera X implementation change to fix.
  *   2. [[BelleUserProblemInput]] indicates that the user has provided an unsuitable input problem or made a correctable error in a proof step.
  *      They will be reported back to the user along with a legible message describing what needs to be changed in the problem or proof.
  *   3. [[BelleProofSearchControl]] indicates that one proof attempt did not succeed so other proof options should be tried.
  *      They will be swallowed by any outer proof search tactics that will try something else instead.
  * Some advanced proof search tactics may ``convert'' between these exception types or swallow more of them
  * when they deliberately try steps they know may fail spectacularly but have a backup plan.
  */
class BelleThrowable(message: => String, cause: Throwable = null) extends ProverException("", cause) {
  /* @note message not passed to super (constructing Bellerophon messages tends to be expensive, so construct on demand only) */

  /* @note mutable state for gathering the logical context that led to this exception */
  private var tacticContext: BelleExpr = BelleDot  //@todo BelleUnknown?
  def context: BelleExpr = tacticContext
  def inContext(context: BelleExpr, additionalMessage: String): BelleThrowable = {
    this.tacticContext = context
    super.inContext(context.prettyString, additionalMessage)
    this
  }

  /** Read the message describing what went wrong. */
  override def getMessage: String = s"[Bellerophon Runtime] ${message.stripPrefix("[Bellerophon Runtime] ")}"

  override def toString: String = getMessage() + "\n" + super.toString + "\nin " + tacticContext
}


// Main tactical exception categories

/** Reported bug: Major syntactic and semantic errors in bellerophon tactics that indicate a tactic is broken.
  * For example, forgetting to provide an expected position or applying a left tactic on the right.
  * BelleInterpreter will raise the error to the user's attention but it needs an internal fix to KeYmaera X.
  */
class BelleReportedError     (message: => String, cause: Throwable = null) extends BelleThrowable(message, cause)

/** User feedback: Indicates that the user has provided an unsuitable input problem or made a correctable error in a proof step.
  * They will be reported back to the user along with a legible message describing what needs to be changed in the problem or proof.
  */
class BelleUserProblemInput  (message: => String, cause: Throwable = null) extends BelleThrowable(message, cause)

/** Search control: Silently raises issues to control proof search, indicating that one proof attempt did not succeed
  * so other proof options should be tried.
  * They will be swallowed by any outer proof search tactics that will try something else instead.
  * For example, trying to apply an implyR tactic at a succedent position that contains an Or will be inapplicable but
  * does not indicate a bug in the tactic, merely that a different branch needs to be taken in proof search.
  * @see [[InapplicableTactic]]
  */
class BelleProofSearchControl(message: => String, cause: Throwable = null) extends BelleThrowable(message, cause)


// Subtypes

//@todo rename to BelleIllFormedTacticError for clarity?
class BelleIllFormedError(message: => String, cause: Throwable = null)     extends BelleReportedError(message, cause)

/** Tactic is not applicable as indicated.
  * For example, InapplicableTactic can be raised when trying to apply [[edu.cmu.cs.ls.keymaerax.btactics.SequentCalculus.andR]]
  * at the correct position 2 in bounds on the right-hand side where it turns out there is an Or formula not an And formula.
  * This does not indicate a catastrophic failure in the tactic implementation, merely a promising but unsuccessful attempt of applying a tactic.
  */
class InapplicableTactic(message: => String, cause: Throwable = null) extends BelleProofSearchControl(message, cause)


/** Signaling that a tactic was not applicable or did not work at the current goal.
  * BelleTacticFailures will be consumed by the BelleInterpreter which will try something else instead. */
class BelleTacticFailure(message: => String, cause: Throwable = null) extends BelleProofSearchControl(message, cause)



/** Signals an unexpected proof state (e.g., an open goal that should have been closed). */
class BelleUnexpectedProofStateError(message: => String, val proofState: Provable, cause: Throwable = null)
  extends BelleIllFormedError(message, cause) {
  override def toString: String = message + "\n" + proofState.prettyString
}


/** Signaling that a tactic's implementation was incomplete and did not work out as planned, so tactic execution might continue,
  * but it is indicating a potential problem in the tactic's implementation. */
//@todo should extend BelleTacticFailure
class BelleUnsupportedFailure(message: => String, cause: Throwable = null) extends BelleIllFormedError(message, cause)

/** Raised when a tactic decides that all further tactical work on a goal is useless and bellerophon should immediately stop
  * @param status signaling the status of the goal such as Counterexample, Valid
  * @param message readable description of the issue */
class BelleAbort(status: => String, message: => String, cause: Throwable = null) extends BelleProofSearchControl(message, cause)

/**
  * Raised to indicate that two expressions are not unifiable in the single-sided matching sense.
  * @param shape The shape against which to match.
  * @param input The expression that we were trying to match against the given shape.
  * @param info Additional information
  */
class UnificationException(val shape: String, val input: String, info: String = "")
  extends BelleThrowable("Un-Unifiable: " + shape + "\nfor:          " + input + "\n" + info) {}


case class BelleUserGeneratedError(msg: String) extends BelleThrowable(s"[Bellerophon User-Generated Message] $msg")

/**
  * A Bellerophon exception that consists of two reasons why it is being raised, for example,
  * if two things went wrong out of which it would have sufficed if only one succeeds.
  * @param left
  * @param right
  */
class CompoundException(val left: BelleThrowable, val right: BelleThrowable)
  extends BelleThrowable(s"Left Message: ${left.getMessage}\nRight Message: ${right.getMessage})")

/** These exceptions have well-understood causes and the given explanation should be propagated all the way to the user.
  * @todo give proper formatting and inContext and such.
  * @todo use BelleUserProblemInput instead? */
class BelleFriendlyUserMessage(message: => String) extends Exception(message)


