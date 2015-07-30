/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
/**
 * KeYmaera Exception and Error Hierarchy
 * @author aplatzer
 * @note Code Review: 2015-05-01
 */
package edu.cmu.cs.ls.keymaerax.core

/**
 * KeYmaera Prover Exceptions.
 */
class ProverException(msg: String) extends RuntimeException(msg) {

  /* @note mutable state for gathering the logical context that led to this exception */
  private var logicalContext: String = ""

  /**
   * The logical context, i.e. stack of proof rules or nested logical context information
   * describing in which context this exception occurred.
   */
  def getContext = logicalContext

  /**
   * Add the context information to this exception, returning the resulting exception to be thrown.
   */
  def inContext(context: String, additionalMessage : String = ""): ProverException = {
    this.logicalContext  = this.logicalContext + "\nin " + context
    if(!additionalMessage.equals("")) this.logicalContext = this.logicalContext + "\n(" + additionalMessage + ")"
    this
  }

  override def toString: String = super.getMessage + getContext

  //@TODO Add functionality to prettyPrint all expressions passed in on demand.
}
// class ProverException private(ex: RuntimeException) extends RuntimeException(ex) {
//   def this(message:String) = this(new RuntimeException(message))
//   def this(message:String, throwable: Throwable) = this(new RuntimeException(message, throwable))
// }

/**
 * Critical exceptions from KeYmaera's Prover Core.
 */
class CoreException(msg: String) extends ProverException(msg)

case class SubstitutionClashException(subst: String/*Substitution*/, U: String/*SetLattice[NamedSymbol]*/, e: String/*Expression*/, context: String/*Expression*/, clashes: String/*SetLattice[NamedSymbol]*/, info: String = "")
  extends CoreException("Substitution clash:\n" + subst + "\nis not (" + U + ")-admissible\nfor " + e + "\nwhen substituting in " + context + "\n" + info) {
  //  def inContext(context: String): SubstitutionClashException =
    //new SubstitutionClashException(subst, U, e, this.context, clashes, info + "\nin " + context).initCause(this).asInstanceOf[SubstitutionClashException]
}

case class BoundRenamingClashException(msg: String, ren: String/*BoundRenaming*/, info: String = "") extends CoreException(msg + "\nBoundRenaming " + ren + " because\n" + info) {
  /**
   * Add the context information to this exception, returning the resulting exception to be thrown.
   */
//  def inContext(context: String): BoundRenamingClashException =
//    new BoundRenamingClashException(msg, ren, info + "\nin " + context).initCause(this).asInstanceOf[BoundRenamingClashException]
}

case class SkolemClashException(msg: String, clashedNames:Set[_ >: NamedSymbol], vars:String/*Seq[Variable]*/, s:String/*Sequent*/)
  extends CoreException(msg + " " + clashedNames + "\nwhen skolemizing variables " + vars + "\nin " + s)

case class InapplicableRuleException(msg: String, r:Rule, s:Sequent = null) extends CoreException(msg + "\nRule " + r + (if (s != null) " applied to " + s else "")) {
  //@TODO if (r instanceof PositionRule) msg + "\n" + s(r.pos) + "\nRule " + r + " applied to " + s
}

case class ProverAssertionError(msg: String) extends ProverException("Assertion failed " + msg)

case class UnknownOperatorException(msg: String, e:Expression) extends ProverException(msg + ": " + e.prettyString + " of " + e.getClass + " " + e) {}
