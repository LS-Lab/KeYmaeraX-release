/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core.ProverException

/**
 * KeYmaera X Tactic Exceptions.
 */
//@todo class TacticException(msg:String) extends ProverException(msg)

/** Common exception type for all Bellerophon tactic exceptions. */
class BelleThrowable(message: String, cause: Throwable = null)
  extends ProverException(s"[Bellerophon Runtime] $message", if (cause != null) cause else new Throwable(message)) {
  /* @note mutable state for gathering the logical context that led to this exception */
  private var tacticContext: BelleExpr = BelleDot  //@todo BelleUnknown?
  def context: BelleExpr = tacticContext
  def inContext(context: BelleExpr, additionalMessage: String): BelleThrowable = {
    this.tacticContext = context
    super.inContext(context.prettyString, additionalMessage)
    this
  }
  override def toString: String = super.toString + "\nin " + tacticContext
}

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
class BelleAbort(status: String, message: String, cause: Throwable = null) extends BelleThrowable(message, cause)

case class UnificationException(e1: String, e2: String, info: String = "")
  extends BelleThrowable("Un-Unifiable: " + e1 + "\nfor:          " + e2 + "\n" + info) {}

case class BelleUserGeneratedError(msg: String) extends BelleThrowable(s"[Bellerophon User-Generated Message] $msg")

class CompoundException(left: BelleThrowable, right: BelleThrowable)
  extends BelleThrowable(s"Left Message: ${left.getMessage}\nRight Message: ${right.getMessage})")

