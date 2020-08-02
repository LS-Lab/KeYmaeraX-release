/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * Syntactically compute variable sets for static semantics of Kaisar proofs
  * @author Brandon Bohrer
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof._
import edu.cmu.cs.ls.keymaerax.core._

/** Stores results of variable set computations for Kaisar proofs
  *
  * @param boundVars All program variables which are bound at some point in the proof
  * @param tabooVars All program variables which are taboo (not allowed to be referenced), usually because they are ghosts
  * @param tabooFunctions All function symbols which are taboo to reference, usually because they are inverse ghosts
  * @param tabooFacts All fact variables which are taboo to reference, usually because they are inverse ghosts
  */
case class VariableSets (boundVars: Set[Variable], tabooVars: Set[Variable], tabooFunctions: Set[Ident], tabooFacts: Set[Ident]) {
  def addTabooVars(v: Set[Variable]): VariableSets = VariableSets(boundVars, tabooVars.++(v), tabooFunctions, tabooFacts)
  def addTabooFuncs(f: Set[Ident]): VariableSets = VariableSets(boundVars, tabooVars, tabooFunctions.++(f), tabooFacts)
  def addTabooFacts(p: Set[Ident]): VariableSets = VariableSets(boundVars, tabooVars, tabooFunctions, tabooFacts.++(p))
  /** Set union  */
  def ++(other: VariableSets): VariableSets =
    VariableSets(boundVars.++(other.boundVars), tabooVars.++(other.tabooVars), tabooFunctions.++(other.tabooFunctions), tabooFacts.++(other.tabooFacts))
}

object VariableSets {
  val empty: VariableSets = VariableSets(Set(), Set(), Set(), Set())

  /** Set of taboo fact variables
    * @param isInverseGhost Was the context where the facts were defined enclosed by an inverse-ghost?
    * */
  private def ofFacts(vars: Set[Variable], isInverseGhost: Boolean) =
    VariableSets(boundVars = Set(), tabooVars = Set(), tabooFunctions = Set(), tabooFacts = if (isInverseGhost) vars else Set())

  /** Set of bound program variables
    * @param isGhost Was the context where the program variables were defined enclosed by a ghost?
    * */
  private def ofBound(vars: Set[Variable], isGhost: Boolean) =
    VariableSets(boundVars = vars, tabooVars = if(isGhost) vars else Set(), Set(), Set())

  /** Set of taboo function symbols
    * @param isInverseGhost Was the context where the functions were defined enclosed by an inverse-ghost?
    * */
  private def ofFunc(vars: Set[Variable], isInverseGhost: Boolean) =
    VariableSets(boundVars = Set(), tabooVars = Set(), tabooFunctions = if (isInverseGhost) vars else Set(), tabooFacts = Set())

  /** Compute static semantic variables sets for a given Kaisar [[statement]], depending on the context in which
    * [[statement]] appears
    *
    * @param statement The Kaisar statement whose variable sets should be computed
    * @param isGhost Does [[statement]] appear under the [[Ghost]] constructor?
    * @param isInverseGhost Does [[statement]] appear under the [[InverseGhost]] constructor
    * @return All bound and taboo variables of [[statement]]
    */
  def apply(statement: Statement, isGhost: Boolean = false, isInverseGhost: Boolean = false): VariableSets = statement match {
    case Triv() | Label(_, _) => VariableSets.empty
    case Ghost(s) => apply(s, isGhost = true, isInverseGhost = false)
    case InverseGhost(s) => apply(s, isGhost = false, isInverseGhost = true)
    case Assume(pat: Term, f) => ofFacts(StaticSemantics(pat).toSet, isInverseGhost)
    case Assert(pat: Term, f, m) => ofFacts(StaticSemantics(pat).toSet, isInverseGhost)
    case Modify(pat: AsgnPat, _) => ofBound(pat.boundVars, isGhost).++(ofFacts(pat.boundFacts, isInverseGhost))
    case Note(x, proof, ann) => ofFacts(Set(x), isInverseGhost)
    case LetFun(f, args, e) => ofFunc(Set(f), isInverseGhost)
    case Match(pat: Term, e) => ofBound(StaticSemantics(pat).toSet, isGhost)
    case Block(ss) => ss.map(apply(_, isGhost, isInverseGhost)).foldLeft(VariableSets.empty)((l, r) => l.++(r))
    case Switch(scrutinee, pats) =>
      pats.map({ case (x: Term, fml, s) => {
        val t = apply(s, isGhost, isInverseGhost)
        if (isInverseGhost) t.addTabooFacts(StaticSemantics(x).toSet) else t
      }
      }).reduce((l, r) => l.++(r))
    case BoxChoice(left, right) => apply(left, isGhost, isInverseGhost).++(apply(right, isGhost, isInverseGhost))
    case While(x: Term, j, s) => apply(s, isGhost, isInverseGhost).addTabooFacts(StaticSemantics(x).toSet)
    case BoxLoop(s) => apply(s, isGhost, isInverseGhost)
    case ProveODE(ds, dc) => apply(ds, isGhost, isInverseGhost).++(apply(dc, isGhost, isInverseGhost))
    case m: MetaNode => m.children.map(apply(_, isGhost, isInverseGhost)).foldLeft(VariableSets.empty)(_.++(_))
  }

  /** Compute static semantic variables sets for a given Kaisar differential statement, depending on the context in
    * which it appears
    *
    * @param diffStatement The differential Kaisar statement whose variable sets should be computed
    * @param isGhost Does statement appear under the [[Ghost]] constructor?
    * @param isInverseGhost Does statement appear under the [[InverseGhost]] constructor
    * @return All bound and taboo variables of statement
    */
  def apply(diffStatement: DiffStatement, isGhost: Boolean, isInverseGhost: Boolean): VariableSets = diffStatement match {
    case AtomicODEStatement(dp) => ofBound(Set(dp.xp.x), isGhost)
    case DiffProductStatement(l, r) => apply(l, isGhost, isInverseGhost).++(apply(r, isGhost, isInverseGhost))
    case DiffGhostStatement(ds) => apply(ds, isGhost = true, isInverseGhost = false)
    case InverseDiffGhostStatement(ds) => apply(ds, isGhost = false, isInverseGhost = true)
  }

  /** Compute static semantic variables sets for a given Kaisar domain statement, depending on the context in
    * which it appears
    *
    * @param domainStatement The Kaisar domain statement whose variable sets should be computed
    * @param isGhost Does statement appear under the [[Ghost]] constructor?
    * @param isInverseGhost Does statement appear under the [[InverseGhost]] constructor
    * @return All bound and taboo variables of statement
    */
  def apply(domainStatement: DomainStatement, isGhost: Boolean, isInverseGhost: Boolean): VariableSets = domainStatement match {
    case DomAssume(x: Term, f) => ofFacts(StaticSemantics(x).toSet, isInverseGhost)
    case DomAssert(x: Term, f, child) => ofFacts(StaticSemantics(x).toSet, isInverseGhost)
    case DomWeak(dc: DomainStatement) => apply(dc, isGhost = false, isInverseGhost = true)
    case DomModify(x: AsgnPat, f: Term) => ofBound(x.boundVars, isGhost).++(ofFacts(x.boundFacts, isInverseGhost))
    case DomAnd(l, r) => apply(l, isGhost, isInverseGhost).++(apply(r, isGhost, isInverseGhost))
  }

}
