package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.ProofTraversal.TraversalFunction
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.Context._
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.Snapshot
import edu.cmu.cs.ls.keymaerax.core.{Variable, _}
import edu.cmu.cs.ls.keymaerax.infrastruct.SubstitutionHelper

object SSAPass {

  def next(x: Variable, snapshot: Snapshot): (Variable, Snapshot) = {
    x match {
      case BaseVariable(name, Some(_), sort) => throw new Exception("SSA pass expected no subscripted variables in input")
      case BaseVariable(name, None, sort) =>
        val index: Option[Int] = snapshot.get(name) match {
          case None => Some(0)
          case Some(None) => Some(0)
          case Some(Some(i)) => Some(i+1)
        }
        val snap = snapshot.+(name -> index)
        (BaseVariable(name, index, sort), snap)
      case DifferentialSymbol(bv) =>
        val (v, snap) = next(x, snapshot)
        (DifferentialSymbol(v), snap)
    }
  }

  def nexts(xs: Set[Variable], snapshot: Snapshot): (Set[Variable], Snapshot) = {
    val acc: Set[Variable] = Set()
    xs.foldLeft((acc, snapshot))({ case ((acc, snap), v) =>
      val (x, snap1) = next(v, snap)
      (acc.+(x), snap1)
    })
  }

  private def replaceSnap(snapshot: Snapshot): (Term => Option[Term]) = ((f: Term) => {
    f match {
      case bv: BaseVariable => Some(BaseVariable(bv.name, opt(snapshot.get(bv.name)), bv.sort))
      case dv: DifferentialSymbol => Some(DifferentialSymbol(BaseVariable(dv.x.name, opt(snapshot.get(dv.x.name)), dv.sort)))
      case _ => None
    }
  })

  def ssa(f: Term, snapshot: Snapshot): Term = {
    SubstitutionHelper.replacesFree(f)(replaceSnap(snapshot))
  }

  def ssa(hp: Program, snapshot: Snapshot): Program = {
    SubstitutionHelper.replacesFree(hp)(replaceSnap(snapshot))
  }

  def ssa(dp: DifferentialProgram, snapshot: Snapshot): DifferentialProgram = {
    SubstitutionHelper.replacesFree(dp)(replaceSnap(snapshot)).asInstanceOf[DifferentialProgram]
  }

  def ssa(fml: Formula, snapshot: Snapshot): Formula = {
    SubstitutionHelper.replacesFree(fml)(replaceSnap(snapshot))
  }

  def ssa(exp: Expression, snapshot: Snapshot): Expression = {
    SubstitutionHelper.replacesFree(exp)(replaceSnap(snapshot))
  }

  def ssa(m: Method, snapshot: Snapshot): Method = {
    m match {
      case _: RCF | _: Auto | _: Prop => m
      case Using(sels, m) =>
        Using(sels.map(ssa(_, snapshot)), ssa(m, snapshot))
      // @TODO: Should this forget local proof variable numbering?
      case ByProof(pf) => ByProof(Proof(ssa(Block(pf.ss), snapshot)._1.asInstanceOf[Block].ss))
    }
  }
  def ssa(sel: Selector, snapshot: Snapshot): Selector = {
    sel match {
      case DefaultSelector => sel
      // @TODO: unsure / test
      case PatternSelector(e) => PatternSelector(ssa(e, snapshot))
      case ForwardSelector(pt) => ForwardSelector(ssa(pt, snapshot))
    }
  }

  def ssa(pt: ProofTerm, snapshot: Snapshot): ProofTerm = {
    pt match {
      // Don't rename facts, just program variables
      case ProofVar(x) => ProofVar(x)
      // Context lookup should treat programvar as referring to alll versions of x
      case ProgramVar(x) => ProgramVar(x)
      case ProofInstance(e) => ProofInstance(ssa(e, snapshot))
      case ProofApp(m, n) => ProofApp(ssa(m, snapshot), ssa(n, snapshot))
    }
  }

  private def either(x: Either[Term, Unit], snapshot: Snapshot): Either[Term, Unit] = {
    x match {
      case Left(f) => Left(ssa(f, snapshot))
      case Right(()) => Right(())
    }
  }
  def ssa(mod: Modify, snapshot: Snapshot): (Modify, Snapshot) = {
      mod match {
      case Modify(VarPat(x, p), rhs) =>
        val (xx, snap) = next(x, snapshot)
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

  private def snapshotUnion(l: Snapshot, r: Snapshot): Snapshot = {
    val keys: Set[String] = l.keySet.++(r.keySet)
    keys.foldLeft[Map[String, Option[Int]]](Map())((map, k) =>
      (opt(l.get(k)), opt(r.get(k))) match {
        case (Some(x: Int),Some(y: Int)) => map.+(k -> Some(x.max(y)))
        case (x: Some[Int], _) => map.+(k -> x)
        case (_, y: Some[Int]) => map.+(k -> y)
        case _ => map
      }
    )
  }

  private def patSnap(pat: Expression, snapshot: Snapshot): Snapshot = {
    val bv = snapshot.keySet.map(Variable(_))
    val fv = pat match {
      case f: Term => StaticSemantics(f)
      case fml: Formula => StaticSemantics(fml).fv
      case hp: Program => StaticSemantics(hp).fv
    }
    val fresh: Set[Variable] = fv.toSet.--(bv)
    val freshSet = fresh.foldLeft[Set[(String, Option[Int])]](Set())((acc, x) => acc.+((x.name, Some(0))))
    freshSet.toMap
  }

  def opt[T](x: Option[Option[T]]): Option[T] = x match {case None => None case Some(None) => None case Some(Some(x)) => Some(x)}
  def stutters(ours: Snapshot, other: Snapshot): Statement = {
    val allKeys = other.keySet.++(ours.keySet)
    val varDiff = allKeys.filter(k => ours.get(k) != other.get(k))
    KaisarProof.block(varDiff.toList.map(x =>
      Modify(VarPat(Variable(x, opt(other.get(x))), None), Left(Variable(x, opt(ours.get(x)))))))
  }

  def ssa(s: Statement, snapshot: Snapshot): (Statement, Snapshot) = {
    s match {
      case mod: Modify => ssa(mod, snapshot)
      case Label(st , _) => (Label(st, Some(snapshot)), snapshot)
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
        val leftStutters = stutters(leftSnap, rightSnap)
        val rightStutters = stutters(rightSnap, leftSnap)
        val snap = snapshotUnion(leftSnap, rightSnap)
        (BoxChoice(KaisarProof.block(leftS :: leftStutters :: Nil), KaisarProof.block(rightS :: rightStutters :: Nil)), snap)
      case BoxLoop(s) =>
        val (body, bodySnap) = ssa(s, snapshot)
        val baseStutters = stutters(snapshot, bodySnap)
        val indStutters = stutters(bodySnap, snapshot)
        (KaisarProof.block(baseStutters :: BoxLoop(KaisarProof.block(indStutters :: body :: Nil)) :: Nil), bodySnap)
      case While(x: Expression, j: Formula, s: Statement) =>
        val (body, bodySnap) = ssa(s, snapshot)
        val baseStutters = stutters(snapshot, bodySnap)
        val indStutters = stutters(bodySnap, snapshot)
        val (xx, jj) = (ssa(x, bodySnap), ssa(j, bodySnap))
        (KaisarProof.block(baseStutters :: While(xx, jj, KaisarProof.block(indStutters :: body :: Nil)) :: Nil), bodySnap)
      case Switch(scrutinee: Option[Selector], pats: List[(Expression, Expression, Statement)]) =>
        val scrut = scrutinee.map(ssa(_, snapshot))
        val clauses = pats.map ({case (x,f,s) => {
          val ps = patSnap(x, snapshot)
          val xx = ssa(x, ps)
          val ff = ssa(f, ps)
          val (ss, snap2) = ssa(s, ps)
          ((xx, ff, ss), snap2)
        }})
        val maxSnap = clauses.map(_._2).reduce(snapshotUnion)
        val stutterClauses = clauses.map({case ((x, f, s), clauseSnap) =>
          val asgns = stutters(clauseSnap, maxSnap)
          (x, f, KaisarProof.block(asgns :: s :: Nil))
        }).reverse
        (Switch(scrut, stutterClauses), maxSnap)
      case Assume(pat, f) => (Assume(ssa(pat, snapshot), ssa(f, snapshot)), snapshot)
      case Assert(pat, f, m) => (Assert(ssa(pat, snapshot), ssa(f, snapshot), ssa(m, snapshot)), snapshot)
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
        // @TODO: Test time variable handling
        val (_bv, snap) = nexts(odeVars(ProveODE(ds, dc)), snapshot)
        val ds1 = ssa(ds, snap)
        val dc1 = ssa(dc, snap)
        val inStutter = stutters(snapshot, snap)
        (KaisarProof.block(inStutter:: ProveODE(ds1, dc1) :: Nil), snap)
      case Was(now: Statement, was: Statement) =>
        val (now1, snap) = ssa(now, snapshot)
        (Was(now1, was), snap)
      // @TODO: Resolve semantics of Match patterns. Here I assume that bound variables are not shadowed in a pattern-match,
      // but that free variables may be introduced
      case Match(pat: Expression, e: Expression) =>
        // @TODO: snapshot needs to account for all variables seen in context as well.
        val snap = patSnap(pat, snapshot)
        (Match(ssa(pat, snap), ssa(e, snapshot)), snap)
      case Triv() => (Triv(), snapshot)
    }
  }


  // In contrast to other ssa functions, differential equations do not update the snapshot here.
  // instead, [[snapshot]] should be the snapshot at the *end* of the ODE, which must be precomputed.
  // this difference is due to product ODEs having to assign variables in parallel
  def ssa(ds: DomainStatement, snapshot: Snapshot): (DomainStatement) = {
    ds match {
      case DomAssume(x, f) => (DomAssume(ssa(x, snapshot), ssa(f, snapshot)))
      case DomAssert(x, f, child) => (DomAssert(ssa(x, snapshot), ssa(f, snapshot), ssa(child, snapshot)))
      case DomWeak(dc) =>
        val dc1 = ssa(dc, snapshot)
        DomWeak(dc1)
      case DomModify(x, f) =>
        val (Modify(ap, _), _) = ssa(Modify(x, Right(())), snapshot)
        DomModify(ap, ssa(f, snapshot))
      case DomAnd(l, r) =>
        val l1 = ssa(l, snapshot)
        val r1 = ssa(r, snapshot)
        DomAnd(l1, r1)
    }
  }

  def odeVars(ds: ProveODE): Set[Variable] = odeVars(ds.dc).++(odeVars(ds.ds))

  def odeVars(ds: DomainStatement): Set[Variable] = {
    ds match {
      case _: DomAssume | _: DomAssert => Set()
      case DomWeak(dc) => odeVars(dc)
      case DomModify(x, f) => x.boundVars
      case DomAnd(l, r) => odeVars(l).++(odeVars(r))
    }
  }

  def odeVars(ds: DiffStatement): Set[Variable] = {
    ds match {
      case AtomicODEStatement(dp) => Set(dp.xp.x)
      case DiffProductStatement(l, r) => odeVars(l).++(odeVars(r))
      case DiffGhostStatement(ds) => odeVars(ds)
      case InverseDiffGhostStatement(ds) => odeVars(ds)
    }
  }

  def ssa(ds: DiffStatement, snapshot: Snapshot): (DiffStatement) = {
    ds match {
      case AtomicODEStatement(dp: AtomicODE) =>
        val x = Variable(dp.xp.name, opt(snapshot.get(dp.xp.name)), dp.xp.sort)
        val dx = DifferentialSymbol(x)
        AtomicODEStatement(AtomicODE(dx, ssa(dp.e, snapshot)))
      case DiffProductStatement(l, r) => DiffProductStatement(ssa(l, snapshot), ssa(r, snapshot))
      case DiffGhostStatement(ds) => DiffGhostStatement(ssa(ds, snapshot))
      case InverseDiffGhostStatement(ds) => InverseDiffGhostStatement(ssa(ds, snapshot))
    }
  }
  def apply(s: Statement): Statement = {
    val snap: Snapshot = Map()
    ssa(s, snap)._1
  }
}
