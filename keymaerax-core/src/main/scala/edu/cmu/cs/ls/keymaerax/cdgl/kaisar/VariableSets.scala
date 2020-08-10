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
  * @param boundVars All program variables which are bound at some point in the proof, except Phi assignments
  * @param freeVars All program variables which are bound at some point in the proof
  * @param tabooVars All program variables which are taboo (not allowed to be referenced), usually because they are ghosts
  * @param tabooFunctions All function symbols which are taboo to reference, usually because they are inverse ghosts
  * @param tabooFacts All fact variables which are taboo to reference, usually because they are inverse ghosts
  */
case class VariableSets (boundVars: Set[Variable], freeVars: Set[Variable], tabooVars: Set[Variable], tabooFunctions: Set[Ident], tabooFacts: Set[Ident]) {
  def addFreeVars(v: Set[Variable]): VariableSets = VariableSets(boundVars, freeVars.++(v), tabooVars, tabooFunctions, tabooFacts)
  def addTabooVars(v: Set[Variable]): VariableSets = VariableSets(boundVars, freeVars, tabooVars.++(v), tabooFunctions, tabooFacts)
  def addTabooFuncs(f: Set[Ident]): VariableSets = VariableSets(boundVars, freeVars, tabooVars, tabooFunctions.++(f), tabooFacts)
  def addTabooFacts(p: Set[Ident]): VariableSets = VariableSets(boundVars, freeVars, tabooVars, tabooFunctions, tabooFacts.++(p))
  def forgetBound: VariableSets = VariableSets(Set(), freeVars, tabooVars, tabooFunctions, tabooFacts)
  /** Set union  */
  def ++(other: VariableSets): VariableSets =
    VariableSets(boundVars.++(other.boundVars), freeVars.++(other.freeVars), tabooVars.++(other.tabooVars), tabooFunctions.++(other.tabooFunctions), tabooFacts.++(other.tabooFacts))
}

object VariableSets {
  val empty: VariableSets = VariableSets(Set(), Set(), Set(), Set(), Set())

  /** Set of taboo fact variables
    * @param isInverseGhost Was the context where the facts were defined enclosed by an inverse-ghost?
    * */
  private def ofFacts(vars: Set[Variable], fml: Formula, isInverseGhost: Boolean) = {
    val fv = StaticSemantics(fml).fv.toSet
    VariableSets(boundVars = Set(), fv, tabooVars = Set(), tabooFunctions = Set(), tabooFacts = if (isInverseGhost) vars else Set())
  }

  /** Set of bound program variables
    * @param isGhost Was the context where the program variables were defined enclosed by a ghost?
    * */
  private def ofBound(vars: Set[Variable], isGhost: Boolean) =
    VariableSets(boundVars = vars, freeVars = Set(), tabooVars = if(isGhost) vars else Set(), Set(), Set())

  /** Set of taboo function symbols
    * @param isInverseGhost Was the context where the functions were defined enclosed by an inverse-ghost?
    * */
  private def ofFunc(vars: Set[Variable], args: List[Ident], e: Expression,  isInverseGhost: Boolean): VariableSets = {
    val bodyFree = e match {
      case f: Term => StaticSemantics(f).toSet
    }
    val free = bodyFree.--(args.toSet)
    VariableSets(boundVars = Set(), freeVars = free, tabooVars = Set(), tabooFunctions = if (isInverseGhost) vars else Set(), tabooFacts = Set())
  }

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
    case Assume(pat: Term, f) => ofFacts(StaticSemantics(pat).toSet, f, isInverseGhost)
    case Assert(pat: Term, f, m) => ofFacts(StaticSemantics(pat).toSet, f, isInverseGhost)
    case Modify(pat: AsgnPat, Left(f)) => ofBound(pat.boundVars, isGhost).++(ofFacts(pat.boundFacts, True, isInverseGhost)).addFreeVars(StaticSemantics(f).toSet)
    case Modify(pat: AsgnPat, _) => ofBound(pat.boundVars, isGhost).++(ofFacts(pat.boundFacts, True, isInverseGhost))
    case Note(x, proof, ann) => ofFacts(Set(x), ann.getOrElse(True), isInverseGhost)
    case LetFun(f, args, e) => ofFunc(Set(f), args, e, isInverseGhost)
    case Match(pat: Term, e) => ofBound(StaticSemantics(pat).toSet, isGhost)
    case Block(ss) => ss.map(apply(_, isGhost, isInverseGhost)).foldLeft(VariableSets.empty)((l, r) => l.++(r))
    case Switch(scrutinee, pats) =>
      pats.map({ case (x: Term, fml: Formula, s) => {
        val t = apply(s, isGhost, isInverseGhost)
        val tt = t.++(ofFacts(Set(), fml, isInverseGhost))
        if (isInverseGhost) tt.addTabooFacts(StaticSemantics(x).toSet) else tt
      }
      }).reduce((l, r) => l.++(r))
    case BoxChoice(left, right) => apply(left, isGhost, isInverseGhost).++(apply(right, isGhost, isInverseGhost))
    case While(x: Term, j, s) => apply(s, isGhost, isInverseGhost).addTabooFacts(StaticSemantics(x).toSet)
    case BoxLoop(s, _) => apply(s, isGhost, isInverseGhost)
    case ProveODE(ds, dc) => apply(ds, isGhost, isInverseGhost).++(apply(dc, isGhost, isInverseGhost))
    case m: Phi => apply(m.asgns, isGhost, isInverseGhost).forgetBound
    // @TODO: Are there ever cases where we want to check _bl instead?
    case BoxLoopProgress(_bl, progress) => apply(progress, isGhost, isInverseGhost)
    case m: MetaNode => m.children.map(apply(_, isGhost, isInverseGhost)).foldLeft(VariableSets.empty)(_.++(_))
  }
  def apply(kc: Context): VariableSets = apply(kc.s)

  /** Compute static semantic variables sets for a given Kaisar differential statement, depending on the context in
    * which it appears
    *
    * @param diffStatement The differential Kaisar statement whose variable sets should be computed
    * @param isGhost Does statement appear under the [[Ghost]] constructor?
    * @param isInverseGhost Does statement appear under the [[InverseGhost]] constructor
    * @return All bound and taboo variables of statement
    */
  def apply(diffStatement: DiffStatement, isGhost: Boolean, isInverseGhost: Boolean): VariableSets = diffStatement match {
    case AtomicODEStatement(dp) => ofBound(Set(dp.xp.x), isGhost).addFreeVars(StaticSemantics(dp.e).toSet)
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
    case DomAssume(x: Term, f) => ofFacts(StaticSemantics(x).toSet, f, isInverseGhost)
    case DomAssert(x: Term, f, child) => ofFacts(StaticSemantics(x).toSet, f, isInverseGhost)
    case DomWeak(dc: DomainStatement) => apply(dc, isGhost = false, isInverseGhost = true)
    case DomModify(x: AsgnPat, f: Term) => ofBound(x.boundVars, isGhost).++(ofFacts(x.boundFacts, True, isInverseGhost)).addFreeVars(StaticSemantics(f).toSet)
    case DomAnd(l, r) => apply(l, isGhost, isInverseGhost).++(apply(r, isGhost, isInverseGhost))
  }
}
