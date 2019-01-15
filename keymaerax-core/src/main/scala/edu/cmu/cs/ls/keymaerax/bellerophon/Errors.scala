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

/** These exceptions have well-understood causes and the given explanation should be propagated all the way to the user.
  * @todo give proper formatting and inContext and such. */
class BelleFriendlyUserMessage(message: String) extends Exception

/** Common exception type for all Bellerophon tactic exceptions. */
class BelleThrowable(message: => String, cause: Throwable = null) extends ProverException("", cause) {
  /* @note do not pass on message (constructing Bellerophon messages tends to be expensive, so construct on demand only) */

  /* @note mutable state for gathering the logical context that led to this exception */
  private var tacticContext: BelleExpr = BelleDot  //@todo BelleUnknown?
  def context: BelleExpr = tacticContext
  def inContext(context: BelleExpr, additionalMessage: String): BelleThrowable = {
    this.tacticContext = context
    super.inContext(context.prettyString, additionalMessage)
    this
  }

  override def getMessage: String = s"[Bellerophon Runtime] ${message.stripPrefix("[Bellerophon Runtime] ")}"

  override def toString: String = getMessage() + "\n" + super.toString + "\nin " + tacticContext
}

/** Signals an unexpected proof state (e.g., an open goal that should have been closed). */
class BelleUnexpectedProofStateError(message: => String, val proofState: Provable, cause: Throwable = null)
  extends BelleThrowable(message, cause)

/** Syntactic and semantic errors in bellerophon tactics, such as forgetting to provide an expected position.
  * BelleInterpreter will raise the error to the user's attention. */
case class BelleIllFormedError(message: String, cause: Throwable = null) extends BelleThrowable(message, cause)

/** Signaling that a tactic was not applicable or did not work at the current goal.
  * BelleTacticFailures will be consumed by the BelleInterpreter which will try something else instead. */
case class BelleTacticFailure(message: String, cause: Throwable = null) extends BelleThrowable(message, cause)

/** Signaling that a tactic's implementation was incomplete and did not work out as planned, so tactic execution might continue,
  * but it is indicating a potential problem in the tactic's implementation. */
//@todo should extend BelleTacticFailure
case class BelleUnsupportedFailure(message: String, cause: Throwable = null) extends BelleThrowable(message, cause)

/** Raised when a tactic decides that all further tactical work on a goal is useless and bellerophon should immediately stop
  * @param status signaling the status of the goal such as Counterexample, Valid
  * @param message readable description of the issue */
class BelleAbort(status: => String, message: => String, cause: Throwable = null) extends BelleThrowable(message, cause)

case class UnificationException(e1: String, e2: String, info: String = "")
  extends BelleThrowable("Un-Unifiable: " + e1 + "\nfor:          " + e2 + "\n" + info) {}

case class BelleUserGeneratedError(msg: String) extends BelleThrowable(s"[Bellerophon User-Generated Message] $msg")

class CompoundException(val left: BelleThrowable, val right: BelleThrowable)
  extends BelleThrowable(s"Left Message: ${left.getMessage}\nRight Message: ${right.getMessage})")

