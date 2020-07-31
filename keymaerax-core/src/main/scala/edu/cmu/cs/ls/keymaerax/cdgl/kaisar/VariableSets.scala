package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.Context
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.Context.Context
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof._
import edu.cmu.cs.ls.keymaerax.core._

case class VariableSets (boundVars: Set[Variable], tabooVars: Set[Variable], functions: Set[Ident], facts: Set[Ident]) {
  def addTabooVars(v: Set[Variable]): VariableSets = VariableSets(boundVars, tabooVars.++(v), functions, facts)
  def addTabooFuncs(f: Set[Ident]): VariableSets = VariableSets(boundVars, tabooVars, functions.++(f), facts)
  def addTabooFacts(p: Set[Ident]): VariableSets = VariableSets(boundVars, tabooVars, functions, facts.++(p))
  def ++(other: VariableSets): VariableSets = VariableSets(boundVars.++(other.boundVars), tabooVars.++(other.tabooVars), functions.++(other.functions), facts.++(other.facts))
}

object VariableSets {
  val empty: VariableSets = VariableSets(Set(), Set(), Set(), Set())
  def apply(con: Context, isGhost: Boolean = false, isInverseGhost: Boolean = false): VariableSets = con match {
    case Triv() | Label(_, _) => VariableSets.empty
    case Ghost(s) => apply(s, isGhost = true, isInverseGhost = false)
    case InverseGhost(s) => apply(s, isGhost = false, isInverseGhost = true)
    case Assume(pat: Term, f) => VariableSets(boundVars = Set(), tabooVars = Set(), functions = Set(), facts = if (isInverseGhost) StaticSemantics(pat).toSet else Set())
    case Assert(pat: Term, f, m) => VariableSets(boundVars = Set(), tabooVars = Set(), functions = Set(), facts = if (isInverseGhost) StaticSemantics(pat).toSet else Set())
    case Modify(pat: AsgnPat, _) => VariableSets(boundVars = pat.boundVars, tabooVars = if (isGhost) pat.boundVars else Set(), functions = Set(), facts = if (isInverseGhost) pat.boundFacts else Set())
    case Note(x, proof, ann) => VariableSets(boundVars = Set(), tabooVars = Set(), functions = Set(), facts = if (isInverseGhost) Set(x) else Set())
    case LetFun(f, args, e) => VariableSets(boundVars = Set(), tabooVars = Set(), functions = if (isInverseGhost) Set(f) else Set(), facts = Set())
    case Match(pat: Term, e) => VariableSets(boundVars = StaticSemantics(pat).toSet, tabooVars = if (isGhost) StaticSemantics(pat).toSet else Set(), functions = Set(), facts = Set())
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

  def apply(con: DiffStatement, isGhost: Boolean, isInverseGhost: Boolean): VariableSets = con match {
    case AtomicODEStatement(dp) => VariableSets(boundVars = Set(dp.xp.x), tabooVars = if(isGhost) Set(dp.xp.x) else Set(), Set(), Set())
    case DiffProductStatement(l, r) => apply(l, isGhost, isInverseGhost).++(apply(r, isGhost, isInverseGhost))
    case DiffGhostStatement(ds) => apply(ds, isGhost = true, isInverseGhost = false)
    case InverseDiffGhostStatement(ds) => apply(ds, isGhost = false, isInverseGhost = true)
  }

  def apply(con: DomainStatement, isGhost: Boolean, isInverseGhost: Boolean): VariableSets = con match {
    case DomAssume(x: Term, f) => VariableSets(Set(), Set(), Set(), if(isInverseGhost) StaticSemantics(x).toSet else Set())
    case DomAssert(x: Term, f, child) => VariableSets(Set(), if(isGhost) StaticSemantics(x).toSet else Set(), Set(), Set())
    case DomWeak(dc: DomainStatement) => apply(dc, isGhost = false, isInverseGhost = true)
    case DomModify(x: AsgnPat, f: Term) => VariableSets(x.boundVars, if(isGhost) x.boundVars else Set(), Set(), if(isInverseGhost) x.boundFacts else Set())
    case DomAnd(l, r) => apply(l, isGhost, isInverseGhost).++(apply(r, isGhost, isInverseGhost))
  }

}
