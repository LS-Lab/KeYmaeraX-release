/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * KeYmaera X Exception and Error Hierarchy.
  * @author Andre Platzer
  * @note Code Review: 2016-08-16
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
/** Critical exceptions from the KeYmaera X Prover Core. */
class CoreException(msg: String) extends ProverException(msg)

/** Substitution clash */
case class SubstitutionClashException(subst: String/*USubst*/, U: String/*SetLattice[NamedSymbol]*/, e: String/*Expression*/, context: String/*Expression*/, clashes: String/*SetLattice[NamedSymbol]*/, info: String = "")
  extends CoreException("Substitution clash:\n" + subst + "\nis not (" + U + ")-admissible\nfor " + e + "\nwhen substituting in " + context + "\n" + info)

/** Uniform or bound renaming clash exception */
case class RenamingClashException(msg: String, ren: String/*URename*/, e: String/*Expression*/, info: String = "") extends CoreException(msg + "\nRenaming " + e + " via " + ren + "\nin " + info)

/** Skolem symbol clash */
case class SkolemClashException(msg: String, clashedNames:SetLattice[Variable], vars:String/*Seq[Variable]*/, s:String/*Sequent*/)
  extends CoreException(msg + " " + clashedNames + "\nwhen skolemizing variables " + vars + "\nin " + s)

/** Rule is not applicable as indicated */
case class InapplicableRuleException(msg: String, r:Rule, s:Sequent = null) extends CoreException(msg + "\n" +
  "Rule " + r + (if (r.isInstanceOf[PositionRule]) s(r.asInstanceOf[PositionRule].pos) else "") +
  (if (s != null) " applied to " + s else "")) {
}

/** Assertions that fail in the prover */
case class ProverAssertionError(msg: String) extends ProverException("Assertion failed " + msg)

/** Thrown to indicate when an unknown operator occurs */
case class UnknownOperatorException(msg: String, e:Expression) extends ProverException(msg + ": " + e.prettyString + " of " + e.getClass + " " + e) {}
