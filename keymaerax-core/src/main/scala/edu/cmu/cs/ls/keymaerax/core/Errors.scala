/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * KeYmaera X Exception and Error Hierarchy.
  * @author Andre Platzer
  * @note Code Review: 2016-08-17
  */
package edu.cmu.cs.ls.keymaerax.core

/**
  * KeYmaera X Prover Exceptions.
  */
class ProverException(msg: String, cause: Throwable = null) extends RuntimeException(msg, cause) {

  /* @note mutable state for gathering the logical context that led to this exception */
  private var logicalContext: String = ""

  /**
    * Returns the logical context, i.e. stack of proof rules or nested logical context information
    * describing in which context this exception occurred.
    */
  def getContext = logicalContext

  /**
    * Add the context information to this exception, returning the resulting exception to be thrown.
    * @param context textual description of the context within which this prover exception occurred.
    * @param additionalMessage optional additional information about the situation in which this prover exception occurred, e.g., the state of affairs.
    */
  def inContext(context: String, additionalMessage : String = ""): ProverException = {
    this.logicalContext  = this.logicalContext + "\nin " + context
    if(!additionalMessage.equals("")) this.logicalContext = this.logicalContext + "\n\t(" + additionalMessage + ")"
    this
  }

  override def toString: String = super.getMessage + getContext

}


/** Reasoning exceptions directly from the KeYmaera X Prover Kernel.
  * The most important distinction of prover kernel exceptions are
  * [[CriticalCoreException]] for unsound logical mistakes versus
  * [[NoncriticalCoreException]] for plausible but inappropriate reasoning attempts. */
class CoreException(msg: String) extends ProverException(msg)

// critical prover kernel exceptions

/** Critical reasoning exceptions directly from the KeYmaera X Prover Core that indicate a proof step was
  * attempted that would be unsound, and was consequently denied. */
class CriticalCoreException(msg: String) extends CoreException(msg)

/** Substitution clashes are raised for unsound substitution reasoning attempts. */
case class SubstitutionClashException(subst: String/*USubst*/, U: String/*SetLattice[NamedSymbol]*/, e: String/*Expression*/, context: String/*Expression*/, clashes: String/*SetLattice[NamedSymbol]*/, info: String = "")
  extends CriticalCoreException("Substitution clash:\n" + subst + "\nis not (" + U + ")-admissible\nfor " + e + "\nwhen substituting in " + context + "\n" + info)

/** Uniform or bound renaming clashes are unsound renaming reasoning attempts. */
case class RenamingClashException(msg: String, ren: String/*URename*/, e: String/*Expression*/, info: String = "")
  extends CriticalCoreException(msg + "\nRenaming " + e + " via " + ren + "\nin " + info)

/** Skolem symbol clashes are unsound Skolemization reasoning attempts. */
case class SkolemClashException(msg: String, clashedNames:SetLattice[Variable], vars:String/*Seq[Variable]*/, s:String/*Sequent*/)
  extends CriticalCoreException(msg + " " + clashedNames + "\nwhen skolemizing variables " + vars + "\nin " + s)


// noncritical prover kernel exceptions

/** Noncritical reasoning exceptions directly from the KeYmaera X Prover Core that indicate a proof step was
  * perfectly plausible to try, just did not fit the expected pattern, and consequently turned out impossible. */
class NoncriticalCoreException(msg: String) extends CoreException(msg)

/** Rule is not applicable as indicated.
  * For example, InapplicableRuleException can be raised when trying to apply [[AndRight]]
  * at the correct position 2 in bounds on the right-hand side where it turns out there is an Or formula not an And formula.
  * For readability and code performance reasons, the prover kernel may also raise [[scala.MatchError]]
  * if the shape of a formula is not as expected.
  */
case class InapplicableRuleException(msg: String, r:Rule, s:Sequent = null)
  extends NoncriticalCoreException(msg + "\n" +
  "Rule " + r + (if (r.isInstanceOf[PositionRule]) s(r.asInstanceOf[PositionRule].pos) else "") +
  (if (s != null) " applied to " + s else "")) {
}


// internal prover kernel exceptions

/** Internal core assertions that fail in the prover */
case class ProverAssertionError(msg: String) extends ProverException("Assertion failed " + msg)

/** Thrown to indicate when an unknown operator occurs */
case class UnknownOperatorException(msg: String, e:Expression) extends ProverException(msg + ": " + e.prettyString + " of " + e.getClass + " " + e) {}

/** Nil case for exceptions, which is almost useless except when an exception type is needed to indicate that there really was none. */
object NoProverException extends ProverException("No prover exception has occurred")
