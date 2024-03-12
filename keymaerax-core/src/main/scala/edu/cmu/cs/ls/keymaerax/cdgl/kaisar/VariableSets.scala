/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Syntactically compute variable sets for static semantics of Kaisar proofs
 * @author
 *   Brandon Bohrer
 */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof._
import edu.cmu.cs.ls.keymaerax.core._

/**
 * Stores results of variable set computations for Kaisar proofs
 *
 * @param boundVars
 *   All program variables which are bound at some point in the proof, except Phi assignments
 * @param mustBoundVars
 *   All program variables which are bound on every path in proof.
 * @param freeVars
 *   All program variables which appear free in proof without surrounding must-binder
 * @param tabooVars
 *   All program variables which are taboo (not allowed to be referenced), usually because they are ghosts
 * @param tabooFunctions
 *   All function symbols which are taboo to reference, usually because they are inverse ghosts
 * @param tabooFacts
 *   All fact variables which are taboo to reference, usually because they are inverse ghosts
 */
case class VariableSets(
    boundVars: Set[Variable],
    mustBoundVars: Set[Variable],
    freeVars: Set[Variable],
    tabooVars: Set[Variable],
    tabooFunctions: Set[Ident],
    tabooFacts: Set[Ident],
) {
  def addBoundVars(v: Set[Variable]): VariableSets =
    VariableSets(boundVars.++(v), mustBoundVars, freeVars, tabooVars, tabooFunctions, tabooFacts)
  def addFreeVars(v: Set[Variable]): VariableSets =
    VariableSets(boundVars, mustBoundVars, freeVars.++(v), tabooVars, tabooFunctions, tabooFacts)
  def addTabooVars(v: Set[Variable]): VariableSets =
    VariableSets(boundVars, mustBoundVars, freeVars, tabooVars.++(v), tabooFunctions, tabooFacts)
  def addTabooFuncs(f: Set[Ident]): VariableSets =
    VariableSets(boundVars, mustBoundVars, freeVars, tabooVars, tabooFunctions.++(f), tabooFacts)
  def addTabooFacts(p: Set[Ident]): VariableSets =
    VariableSets(boundVars, mustBoundVars, freeVars, tabooVars, tabooFunctions, tabooFacts.++(p))
  def forgetBound: VariableSets = VariableSets(Set(), mustBoundVars, freeVars, tabooVars, tabooFunctions, tabooFacts)
  def allVars: Set[Variable] = freeVars ++ boundVars

  /** Set union */
  def ++(other: VariableSets): VariableSets = VariableSets(
    boundVars.++(other.boundVars),
    mustBoundVars.++(other.mustBoundVars),
    freeVars.++(other.freeVars),
    tabooVars.++(other.tabooVars),
    tabooFunctions.++(other.tabooFunctions),
    tabooFacts.++(other.tabooFacts),
  )

  /** Combine alternative branches. Like ++ but must-bound is intersected */
  def choice(other: VariableSets): VariableSets = VariableSets(
    boundVars.++(other.boundVars),
    mustBoundVars.intersect(other.mustBoundVars),
    freeVars.++(other.freeVars),
    tabooVars.++(other.tabooVars),
    tabooFunctions.++(other.tabooFunctions),
    tabooFacts.++(other.tabooFacts),
  )

  /** Combine sequential steps. Allows tighter free-variables computation */
  def andThen(other: VariableSets): VariableSets = {
    val otherFree = other.freeVars -- mustBoundVars
    VariableSets(
      boundVars.++(other.boundVars),
      mustBoundVars.++(other.mustBoundVars),
      freeVars.++(otherFree),
      tabooVars.++(other.tabooVars),
      tabooFunctions.++(other.tabooFunctions),
      tabooFacts.++(other.tabooFacts),
    )
  }

  /** Clear must-bound variables for optional statements */
  def option: VariableSets = choice(VariableSets.empty)
}

object VariableSets {
  val empty: VariableSets = VariableSets(Set(), Set(), Set(), Set(), Set(), Set())

  /**
   * Set of taboo fact variables
   * @param isInverseGhost
   *   Was the context where the facts were defined enclosed by an inverse-ghost?
   */
  private def ofFacts(vars: Set[Variable], fml: Formula, isInverseGhost: Boolean) = {
    val plainFml = KaisarProof.forgetAt(fml)
    val setlattice = StaticSemantics(plainFml).fv
    val fv = StaticSemantics(plainFml).fv.toSet
    VariableSets(
      boundVars = Set(),
      mustBoundVars = Set(),
      fv,
      tabooVars = Set(),
      tabooFunctions = Set(),
      tabooFacts = if (isInverseGhost) vars else Set(),
    )
  }

  /**
   * Set of bound program variables
   * @param isGhost
   *   Was the context where the program variables were defined enclosed by a ghost?
   */
  private def ofMustBound(vars: Set[Variable], isGhost: Boolean) = VariableSets(
    boundVars = vars,
    mustBoundVars = vars,
    freeVars = Set(),
    tabooVars = if (isGhost) vars else Set(),
    Set(),
    Set(),
  )

  /**
   * Set of taboo function symbols
   * @param isInverseGhost
   *   Was the context where the functions were defined enclosed by an inverse-ghost?
   */
  private def ofFunc(vars: Set[Variable], args: List[Ident], e: Expression, isInverseGhost: Boolean): VariableSets = {
    val bodyFree = StaticSemantics(KaisarProof.forgetAt(e.asInstanceOf[Term]))
    val free = bodyFree.toSet -- (args.toSet)
    VariableSets(
      boundVars = Set(),
      mustBoundVars = Set(),
      freeVars = free,
      tabooVars = Set(),
      tabooFunctions = if (isInverseGhost) vars else Set(),
      tabooFacts = Set(),
    )
  }

  private def ofPred(vars: Set[Variable], args: List[Ident], e: Expression, isInverseGhost: Boolean): VariableSets = {
    val elabBody = KaisarProof.forgetAt(e.asInstanceOf[Formula])
    val bodyFree = StaticSemantics(elabBody).fv
    val free = bodyFree.toSet -- (args.toSet)
    VariableSets(
      boundVars = Set(),
      mustBoundVars = Set(),
      freeVars = free,
      tabooVars = Set(),
      tabooFunctions = if (isInverseGhost) vars else Set(),
      tabooFacts = Set(),
    )
  }

  /**
   * Compute static semantic variables sets for a given Kaisar [[statement]], depending on the context in which
   * [[statement]] appears
   *
   * @param statement
   *   The Kaisar statement whose variable sets should be computed
   * @return
   *   All bound and taboo variables of [[statement]]
   */
  def apply(statement: Statement): VariableSets = apply(Context(statement).withOuter)
  def apply(kc: Context): VariableSets = kc.s match {
    case Triv() | Label(_, _) => VariableSets.empty
    case Ghost(s) => apply(kc.reapply(s).withGhost)
    case InverseGhost(s) => apply(kc.reapply(s).withInverseGhost)
    case Assume(pat: Term, f) => ofFacts(StaticSemantics(pat).toSet, f, kc.isInverseGhost)
    case Assert(pat: Term, f, m) => ofFacts(StaticSemantics(pat).toSet, f, kc.isInverseGhost)
    case mod: Modify => mod
        .asgns
        .foldLeft[VariableSets](VariableSets.empty) {
          case (acc, (p, x, Some(f))) => acc.andThen(
              ofMustBound(Set(x), kc.isGhost)
                .++(ofFacts(p.toSet, True, kc.isInverseGhost))
                .addFreeVars(StaticSemantics(f).toSet)
            )
          case (acc, (p, x, None)) =>
            acc.andThen(ofMustBound(Set(x), kc.isGhost).++(ofFacts(p.toSet, True, kc.isInverseGhost)))
        }
    case Note(x, proof, ann) => ofFacts(Set(x), ann.getOrElse(True), kc.isInverseGhost)
    case LetSym(f, args, e: Term) => ofFunc(Set(f), args, e, kc.isInverseGhost)
    case LetSym(f, args, e: Formula) => ofPred(Set(f), args, e, kc.isInverseGhost)
    case Match(pat: Term, e) => ofMustBound(StaticSemantics(pat).toSet, kc.isGhost)
    case Block(ss) => ss.map(s => apply(kc.reapply(s))).foldLeft(VariableSets.empty)((l, r) => l.andThen(r))
    case Switch(scrutinee, pats) => pats
        .map({
          case (x: Term, fml: Formula, s) => {
            val t = apply(kc.reapply(s))
            val tt = t.++(ofFacts(Set(), fml, kc.isInverseGhost))
            if (kc.isInverseGhost) tt.addTabooFacts(StaticSemantics(x).toSet) else tt
          }
        })
        .reduce((l, r) => l.choice(r))
    case BoxChoice(left, right) => apply(kc.reapply(left)).choice(apply(kc.reapply(right)))
    case While(x: Term, j, s) => apply(kc.reapply(s)).addTabooFacts(StaticSemantics(x).toSet).option
    case For(metX, metF, metIncr, conv, guard, body, guardEpsilon) =>
      val mx = ofMustBound(Set(metX), kc.isGhost)
      val mf = mx.addFreeVars(StaticSemantics(metF).toSet)
      val mi = mf.addFreeVars(StaticSemantics(metIncr).toSet)
      val mg = mi ++ ofFacts(StaticSemantics(guard.pat).toSet, guard.f, kc.isInverseGhost)
      val mc = mg ++
        (conv
          .map(cnv => ofFacts(StaticSemantics(cnv.pat).toSet, cnv.f, kc.isInverseGhost))
          .getOrElse(VariableSets.empty))
      val mge = guardEpsilon.map(f => mc.addFreeVars(StaticSemantics(f).toSet)).getOrElse(mc)
      mge ++ apply(kc.reapply(body))
    case ForProgress(fr, prog) => apply(kc.reapply(fr)).addBoundVars(Set(fr.metX))
    case BoxLoop(s, _) => apply(kc.reapply(s)).option
    case BoxLoopProgress(bl, progress) => apply(kc.reapply(bl))
    case ProveODE(ds, dc) => apply(kc, ds).++(apply(kc, dc))
    case m: Phi => apply(m.asgns) /*.forgetBound*/
    // @TODO: Are there ever cases where we want to check _bl instead?
    case WhileProgress(wh, prog) => apply(kc.reapply(prog))
    case SwitchProgress(switch, onBranch, progress) =>
      val thisBranch =
        ofFacts(StaticSemantics(switch.pats(onBranch)._1).toSet, switch.pats(onBranch)._2, isInverseGhost = false)
      val body = apply(kc.reapply(progress))
      thisBranch ++ body
    case BoxChoiceProgress(bc, onBranch, progress) => apply(kc.reapply(progress))
    case m: MetaNode => m.children.map(s => apply(kc.reapply(s))).foldLeft(VariableSets.empty)(_.++(_))
  }

  /**
   * Compute static semantic variables sets for a given Kaisar differential statement, depending on the context in which
   * it appears
   *
   * @param kc
   *   Kaisar context surrounding statement
   * @param diffStatement
   *   The differential Kaisar statement whose variable sets should be computed
   * @return
   *   All bound and taboo variables of statement
   */
  def apply(kc: Context, diffStatement: DiffStatement): VariableSets = diffStatement match {
    case AtomicODEStatement(dp, _) =>
      ofMustBound(Set(dp.xp.x), kc.isGhost).addFreeVars(StaticSemantics(dp.e).toSet.+(dp.xp.x))
    case DiffProductStatement(l, r) => apply(kc, l).++(apply(kc, r))
    case DiffGhostStatement(ds) => apply(kc.withGhost, ds)
    case InverseDiffGhostStatement(ds) => apply(kc.withInverseGhost, ds)
  }

  /**
   * Compute static semantic variables sets for a given Kaisar domain statement, depending on the context in which it
   * appears
   *
   * @param kc
   *   Kaisar context surrounding statement
   * @param domainStatement
   *   The Kaisar domain statement whose variable sets should be computed
   * @return
   *   All bound and taboo variables of statement
   */
  def apply(kc: Context, domainStatement: DomainStatement): VariableSets = domainStatement match {
    case DomAssume(x: Term, f) => ofFacts(StaticSemantics(x).toSet, f, kc.isInverseGhost)
    case DomAssert(x: Term, f, child) => ofFacts(StaticSemantics(x).toSet, f, kc.isInverseGhost)
    case DomWeak(dc: DomainStatement) => apply(kc.withInverseGhost, dc)
    case DomModify(id, x, f) =>
      ofMustBound(Set(x), kc.isGhost).++(ofFacts(Set(x), True, kc.isInverseGhost)).addFreeVars(StaticSemantics(f).toSet)
    case DomAnd(l, r) => apply(kc, l).++(apply(kc, r))
  }
}
