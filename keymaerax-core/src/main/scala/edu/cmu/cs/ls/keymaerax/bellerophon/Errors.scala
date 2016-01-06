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

case class UnificationException(e1: String, e2: String, info: String = "")
  extends BelleError("Un-Unifiable: " + e1 + "\nfor:          " + e2 + "\n" + info) {}

case class BelleUserGeneratedError(message: String) extends BelleError(s"[Bellerophon User-Generated Message] $message")

class CompoundException(left: BelleError, right: BelleError)
  extends BelleError(s"Left Message: ${left.getMessage}\nRight Message: ${right.getMessage})")

