/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * Lightweight static single assignment (SSA) transformation for Kaisar proofs.
  * SSA for proofs has several subtleties for Kaisar proofs compared to the usual SSA transformations in compilers.
  * A clear difference is that when we transform the variables of a verified program, we must be careful to update all
  * proof steps so that they prove the new program.
  *
  * Because we want a clear interpretation of proofs and also because we do not use a control flow graph (CFG)
  * representation, we do *not* use the standard notion of Phi nodes, which nondeterministically merge the versions
  * of a variable. We simulate phi nodes using assignments, and our [[Phi]] constructor is simply labels those
  * assignments used for this purpose.
  *
  * Whereas SSA is often used elsewhere to aid optimizers, we use it in Kaisar to support the implementation of
  * named/labeled states and other features which require a persistent proof context. While SSA leads to significantly
  * larger contexts, it gives a clear way to translate facts and contexts which may refer to different states or locations
  * in a proof/program
  * @author Brandon Bohrer
  * @see [[edu.cmu.cs.ls.keymaerax.cdgl.kaisar.Snapshot]]
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.ProofTraversal.TraversalFunction
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.Context._
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.{LabelDef, LabelRef}
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.Snapshot._
import edu.cmu.cs.ls.keymaerax.core.{Variable, _}
import edu.cmu.cs.ls.keymaerax.infrastruct.SubstitutionHelper

object SSAPass {
  // Substitution helper function which re-indexes SSA variables according to a snapshot
  private def renameUsingSnapshot(snapshot: Snapshot): (Term => Option[Term]) = ((f: Term) => {
    // f@x(args) is not eliminated during SSA (it has a separate pass), but the arguments are evaluated at the current
    // location, so they are SSA'd here
    (KaisarProof.getAt(f), f) match {
      case (Some((trm, LabelRef(name, args))), _) =>
        Some(KaisarProof.makeAt(trm, LabelRef(name, args.map(ssa(_, snapshot)))))
      case (None, bv: BaseVariable) => Some(BaseVariable(bv.name, opt(snapshot.getOpt(bv.name)), bv.sort))
      case (None, dv: DifferentialSymbol) => Some(DifferentialSymbol(BaseVariable(dv.x.name, opt(snapshot.getOpt(dv.x.name)), dv.sort)))
      case _ => None
    }
  })

  /**  SSA translation of a term */
  def ssa(f: Term, snapshot: Snapshot): Term = {
    SubstitutionHelper.replacesFree(f)(renameUsingSnapshot(snapshot))
  }

  /**  SSA translation of a hybrid program/game.
    *  We assume for simplicity that the hybrid program does not bind any of the variables subject to SSA, meaning
    *  we simply re-index free variable occurrences in [[hp]] */
  def ssa(hp: Program, snapshot: Snapshot): Program = {
    SubstitutionHelper.replacesFree(hp)(renameUsingSnapshot(snapshot))
  }

  /**  SSA translation of a differential program
    *  We assume for simplicity that the program does not bind any of the variables subject to SSA, meaning
    *  we simply re-index free variable occurrences */
  def ssa(dp: DifferentialProgram, snapshot: Snapshot): DifferentialProgram = {
    SubstitutionHelper.replacesFree(dp)(renameUsingSnapshot(snapshot)).asInstanceOf[DifferentialProgram]
  }

  /**  SSA translation of a formula
    *  We assume for simplicity that the formula does not bind any of the variables subject to SSA, meaning
    *  we simply re-index free variable occurrences */
  def ssa(fml: Formula, snapshot: Snapshot): Formula = {
    SubstitutionHelper.replacesFree(fml)(renameUsingSnapshot(snapshot))
  }

  /**  SSA translation of a hybrid program/game */
  def ssa(exp: Expression, snapshot: Snapshot): Expression = {
    SubstitutionHelper.replacesFree(exp)(renameUsingSnapshot(snapshot))
  }

  /**  SSA translation of a proof method */
  def ssa(m: Method, snapshot: Snapshot): Method = {
    m match {
      case _: RCF | _: Auto | _: Prop | _: Solution | _: DiffInduction | _: Exhaustive => m
      case Using(sels, m) =>
        Using(sels.map(ssa(_, snapshot)), ssa(m, snapshot))
      // @TODO: This means variable indices which are used in ss can be reused elsewhere. Is this what we want?
      case ByProof(ss) => ByProof(ssa(Block(ss), snapshot)._1.asInstanceOf[Block].ss)
    }
  }

  /** SSA translation of a fact selector */
  def ssa(sel: Selector, snapshot: Snapshot): Selector = {
    sel match {
      case DefaultSelector => sel
      /* @TODO: Revisit this once pattern selectors have really been used. It's arguably better for a pattern to select
       * facts regardless of which variable version/index is used. In that case, SSA renaming would be irrelevant here*/
      case PatternSelector(e) => PatternSelector(ssa(e, snapshot))
      case ForwardSelector(pt) => ForwardSelector(ssa(pt, snapshot))
    }
  }

  /** SSA transformation of a forward proof term */
  def ssa(pt: ProofTerm, snapshot: Snapshot): ProofTerm = {
    pt match {
      /* SSA doesn't re-index fact variable names, just program variables */
      case ProofVar(x) => ProofVar(x)
      /* ProgramVar(x) is used to search assignments of *all* versions of x, no re-index needed. */
      case ProgramVar(x) => ProgramVar(x)
      case ProofInstance(e) => ProofInstance(ssa(e, snapshot))
      case ProofApp(m, n) => ProofApp(ssa(m, snapshot), ssa(n, snapshot))
    }
  }

  /** Apply SSA to left disjunct */
  private def either(x: Either[Term, Unit], snapshot: Snapshot): Either[Term, Unit] = {
    x match {
      case Left(f) => Left(ssa(f, snapshot))
      case Right(()) => Right(())
    }
  }

  /** SSA translation of a [[Modify]] proof statement
    * @return Translated statement and snapshot of final state */
  def ssa(mod: Modify, snapshot: Snapshot): (Modify, Snapshot) = {
      mod match {
      case Modify(VarPat(x, p), rhs) =>
        val (xx, snap) = snapshot.increment(x)
        (Modify(VarPat(xx, p), either(rhs, snapshot)), snap)
      case Modify(TuplePat(pat :: Nil), rhs) => ssa(Modify(pat, rhs), snapshot)
      case Modify(TuplePat(pat :: pats), Left(Pair(l, r))) =>
        val (Modify(pat1, Left(l1)), snap1) = ssa(Modify(pat, Left(l)), snapshot)
        val (Modify(TuplePat(pats1), Left(r1)), snap2) = ssa(Modify(TuplePat(pats), Left(r)), snap1)
        (Modify(TuplePat(pat1 :: pats1), Left(Pair(l1, r1))), snap2)
      case Modify(TuplePat(pat :: pats), Right(_)) =>
        val (Modify(pat1, Right(_)), snap1) = ssa(Modify(pat, Right(())), snapshot)
        val (Modify(TuplePat(pats1), Right(_)), snap2) = ssa(Modify(TuplePat(pats), Right(())), snap1)
        (Modify(TuplePat(pat1 :: pats1), Right(())), snap2)
    }
  }

  /** Collapse double option. */
  private def opt[T](x: Option[Option[T]]): Option[T] = x match {case None => None case Some(None) => None case Some(Some(x)) => Some(x)}

  /** @return Stuttering assignments which cause other state snapshot to match ours. */
  private def stutters(ours: Snapshot, other: Snapshot): Statement = {
    val allKeys = other.keySet.++(ours.keySet)
    val varDiff = allKeys.filter(k => ours.getOpt(k) != other.getOpt(k))
    val asgns = varDiff.toList.map(x => Modify(VarPat(Variable(x, opt(other.getOpt(x))), None), Left(Variable(x, opt(ours.getOpt(x))))))
    if (asgns.isEmpty) Triv()
    else Phi(KaisarProof.block(asgns))
  }

  /** Translate indices of label arguments */
  def ssa(ld: LabelDef, snapshot: Snapshot): LabelDef = {
    LabelDef(ld.label, ld.args.map(ssa(_, snapshot).asInstanceOf[Variable]))
  }

  /** @returns Translated statement and snapshot of final state */
  def ssa(s: Statement, snapshot: Snapshot): (Statement, Snapshot) = {
    s match {
      case mod: Modify => ssa(mod, snapshot)
      case Label(ld, _) => (Label(ssa(ld, snapshot), Some(snapshot)), snapshot)
      case Block(ss) =>
        val (ssRev, finalSnap) =
          ss.foldLeft[(List[Statement], Snapshot)]((Nil, snapshot))({case ((acc, snapshot), s1) =>
            val (s2, snap) = ssa(s1, snapshot)
            (s2 :: acc, snap)
          })
        (KaisarProof.block(ssRev.reverse), finalSnap)
      case BoxChoice(left, right) =>
        val (leftS, leftSnap) = ssa(left, snapshot)
        val (rightS, rightSnap) = ssa(right, snapshot)
        val snap = leftSnap ++ rightSnap
        val leftStutters = stutters(leftSnap, snap)
        val rightStutters = stutters(rightSnap, snap)
        (BoxChoice(KaisarProof.block(leftS :: leftStutters :: Nil), KaisarProof.block(rightS :: rightStutters :: Nil)), snap)
      case BoxLoop(s, ih) =>
        val boundVars = VariableSets(s).boundVars
        val preSnap = snapshot.addSet(boundVars)
        val (body, postSnap) = ssa(s, preSnap)
        val baseStutters = stutters(snapshot, preSnap)
        val indStutters = stutters(postSnap, preSnap)
        val res = KaisarProof.block(baseStutters :: BoxLoop(KaisarProof.block(body :: indStutters :: Nil), ih) :: Nil)
        (res, preSnap)
      case While(x: Expression, j: Formula, s: Statement) =>
        val (body, bodySnap) = ssa(s, snapshot)
        val baseStutters = stutters(snapshot, bodySnap)
        val indStutters = stutters(bodySnap, snapshot)
        val (xx, jj) = (ssa(x, bodySnap), ssa(j, bodySnap))
        (KaisarProof.block(baseStutters :: While(xx, jj, KaisarProof.block(indStutters :: body :: Nil)) :: Nil), bodySnap)
      case Switch(scrutinee: Option[Selector], pats: List[(Expression, Expression, Statement)]) =>
        val scrut = scrutinee.map(ssa(_, snapshot))
        val clauses = pats.map ({case (x,f,s) => {
          val ff = ssa(f, snapshot)
          val (ss, snap2) = ssa(s, snapshot)
          ((x, ff, ss), snap2)
        }})
        val maxSnap = clauses.map(_._2).reduce(_ ++ _)
        val stutterClauses = clauses.map({case ((x, f, s), clauseSnap) =>
          val asgns = stutters(clauseSnap, maxSnap)
          (x, f, KaisarProof.block(asgns :: s :: Nil))
        }).reverse
        (Switch(scrut, stutterClauses), maxSnap)
      case Assume(pat, f) => (Assume(pat/*ssa(pat, snapshot)*/, ssa(f, snapshot)), snapshot)
      case Assert(pat, f, m) =>
        val ff = ssa(f, snapshot)
        val mm = ssa(m, snapshot)
        (Assert(pat, ff, mm), snapshot)
      case Note(x, proof, annotation) => (Note(x, ssa(proof, snapshot), annotation.map(ssa(_, snapshot))), snapshot)
      case LetFun(f, args, e) => {
        // Don't SSA parameters, only state variables
        val bound = args.toSet
        val local = snapshot.filter({case (k, v) => !bound.contains(Variable(k))})
        (LetFun(f, args, ssa(e, local)), snapshot)
      }
      case Ghost(s) =>
        val (ss, snap) = ssa(s, snapshot)
        (Ghost(ss), snap)
      case InverseGhost(s) =>
        val (ss, snap) = ssa(s, snapshot)
        (InverseGhost(ss), snap)
      case PrintGoal(msg) => (PrintGoal(msg), snapshot)
      case ProveODE(ds, dc) =>
        val bound = VariableSets(ProveODE(ds, dc)).boundVars
        val snap = snapshot.addSet(bound)
        val ds1 = ssa(ds, snap)
        val dc1 = ssa(dc, snap)
        val inStutter = stutters(snapshot, snap)
        (KaisarProof.block(inStutter:: ProveODE(ds1, dc1) :: Nil), snap)
      case Was(now: Statement, was: Statement) =>
        val (now1, snap) = ssa(now, snapshot)
        (Was(now1, was), snap)
      /* @TODO: Decide intended semantics of Match patterns. Here I assume that bound variables are not shadowed in a pattern-match,
       * but that free variables may be introduced */
      case Match(pat: Expression, e: Expression) =>
        val snap = snapshot.addPattern(pat)
        (Match(ssa(pat, snap), ssa(e, snapshot)), snap)
      case Triv() => (Triv(), snapshot)
    }
  }

  /** In contrast to other ssa functions, differential equations do not update the snapshot as we go.
    * instead, [[snapshot]] should be the snapshot at the *end* of the ODE, which must be precomputed.
    * this difference is due to product ODEs having to assign variables in parallel */
  def ssa(ds: DiffStatement, snapshot: Snapshot): DiffStatement = {
    ds match {
      case AtomicODEStatement(dp: AtomicODE, ident) =>
        val x = Variable(dp.xp.name, opt(snapshot.getOpt(dp.xp.name)), dp.xp.sort)
        val dx = DifferentialSymbol(x)
        AtomicODEStatement(AtomicODE(dx, ssa(dp.e, snapshot)), ident)
      case DiffProductStatement(l, r) => DiffProductStatement(ssa(l, snapshot), ssa(r, snapshot))
      case DiffGhostStatement(ds) => DiffGhostStatement(ssa(ds, snapshot))
      case InverseDiffGhostStatement(ds) => InverseDiffGhostStatement(ssa(ds, snapshot))
    }
  }

  /**  SSA translation of domain statement. [[DomModify]] might bind a duration variable, in which case [[snapshot]]
    * refers to the *final* state of the ODE. */
  def ssa(ds: DomainStatement, snapshot: Snapshot): DomainStatement = {
    ds match {
      case DomAssume(x, f) => (DomAssume(ssa(x, snapshot), ssa(f, snapshot)))
      case DomAssert(x, f, child) => (DomAssert(ssa(x, snapshot), ssa(f, snapshot), ssa(child, snapshot)))
      case DomWeak(dc) =>
        val dc1 = ssa(dc, snapshot)
        DomWeak(dc1)
      // note: final subscript of time variable t was already precomputed in snapshot. Don't use ssa(mod: Modify)
      // since it would doubly increment the subscript
      case DomModify(VarPat(x, p), f) =>
        val xt = ssa(x, snapshot).asInstanceOf[Variable]
        DomModify(VarPat(xt, p), ssa(f, snapshot))
      case DomAnd(l, r) =>
        val l1 = ssa(l, snapshot)
        val r1 = ssa(r, snapshot)
        DomAnd(l1, r1)
    }
  }

  /** Apply SSA translation pass to Kaisar statement */
  def apply(s: Statement): Statement = {
    ssa(s, Snapshot.empty)._1
  }
}
