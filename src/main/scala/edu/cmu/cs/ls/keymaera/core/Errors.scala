/**
 * KeYmaera Exception and Error Hierarchy
 * @author aplatzer
 */
package edu.cmu.cs.ls.keymaera.core

/**
 * KeYmaera Prover Exceptions.
 */
class ProverException(msg: String) extends RuntimeException(msg) {
  //@TODO Add inContext():Throwable function that gives wraps the exception within some extra information that explains the context formula in which a problem occurred. So not just the local subformula but the whole context. Useful for try catch e => throw e.inContext("Context information")
  
  //@TODO Add functionality to prettyPrint all expressions passed in on demand.
}
// class ProverException private(ex: RuntimeException) extends RuntimeException(ex) {
//   def this(message:String) = this(new RuntimeException(message))
//   def this(message:String, throwable: Throwable) = this(new RuntimeException(message, throwable))
//   
//   //@TODO Add inContext():Throwable function that gives wraps the exception within some extra information that explains the context formula in which a problem occurred. So not just the local subformula but the whole context. Useful for try catch e => throw e.inContext("Context information")
//   
//   //@TODO Add functionality to prettyPrint all expressions passed in on demand.
// }

/**
 * Critical exceptions from KeYmaera's Prover Core.
 */
class CoreException(msg:String) extends ProverException(msg) {}

class SubstitutionClashException(msg:String, s:Any/*Substitution*/, e:Expr) extends CoreException(msg + "\nSubstitution " + s + " applied to " + e.prettyString) {}

class SkolemClashException(msg:String, clashedNames:Set[NamedSymbol]) extends CoreException(msg + " " + clashedNames) {}

class InapplicableRuleException(msg:String, r:Rule, s:Sequent) extends CoreException(msg + "\nRule " + r + " applied to " + s) {
  //@TODO if (r instanceof PositionRule) msg + "\n" + s(r.pos) + "\nRule " + r + " applied to " + s
}

class UnknownOperatorException(msg:String, e:Expr) extends ProverException(msg + ": " + e.prettyString) {}