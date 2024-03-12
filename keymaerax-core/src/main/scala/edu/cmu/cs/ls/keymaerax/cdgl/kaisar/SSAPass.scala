/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Lightweight static single assignment (SSA) transformation for Kaisar proofs. SSA for proofs has several subtleties
 * for Kaisar proofs compared to the usual SSA transformations in compilers. A clear difference is that when we
 * transform the variables of a verified program, we must be careful to update all proof steps so that they prove the
 * new program.
 *
 * Because we want a clear interpretation of proofs and also because we do not use a control flow graph (CFG)
 * representation, we do *not* use the standard notion of Phi nodes, which nondeterministically merge the versions of a
 * variable. We simulate phi nodes using assignments, and our [[Phi]] constructor is simply labels those assignments
 * used for this purpose.
 *
 * Whereas SSA is often used elsewhere to aid optimizers, we use it in Kaisar to support the implementation of
 * named/labeled states and other features which require a persistent proof context. While SSA leads to significantly
 * larger contexts, it gives a clear way to translate facts and contexts which may refer to different states or
 * locations in a proof/program
 * @author
 *   Brandon Bohrer
 * @see
 *   [[edu.cmu.cs.ls.keymaerax.cdgl.kaisar.Snapshot]]
 */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.ProofTraversal.TraversalFunction
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.Context._
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.{Ident, LabelDef, LabelRef, TransformationException}
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.Snapshot._
import edu.cmu.cs.ls.keymaerax.core.{Variable, _}
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.ASTNode._
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaerax.infrastruct.{ExpressionTraversal, PosInExpr, SubstitutionHelper}

object SSAPass {

  /** Collapse double option. */
  private def opt[T](x: Option[Option[T]]): Option[T] = x match {
    case None => None
    case Some(None) => None
    case Some(Some(x)) => Some(x)
  }

  /** @return Stuttering assignment proofs which cause other state snapshot to match ours. */
  private def stutters(ours: Snapshot, other: Snapshot, locator: ASTNode = Triv()): Statement = {
    val allKeys = other.keySet.++(ours.keySet)
    val varDiff = allKeys.filter(k => ours.getOpt(k) != other.getOpt(k))
    val asgns = varDiff
      .toList
      .map(x =>
        locate(Modify(Nil, List((Variable(x, opt(other.getOpt(x))), Some(Variable(x, opt(ours.getOpt(x))))))), locator)
      )
    if (asgns.isEmpty) Triv() else locate(Phi(locate(KaisarProof.block(asgns), locator)), locator)
  }

  private def flatten(hp: Program): List[Program] = {
    hp match {
      case Compose(l, r) => flatten(l) ++ flatten(r)
      case _ => List(hp)
    }
  }

  private def compose(asgns: List[Program]): Program = {
    val atoms = asgns.flatMap(flatten)
    atoms match {
      case Nil => Test(True)
      case asgn :: Nil => asgn
      case hps =>
        val red = hps.reduceRight(Compose)
        red
    }
  }

  /** @return stuttering assignment programs which cause other state snapshot to match ours */
  private def pstutters(ours: Snapshot, other: Snapshot): Program = {
    val allKeys = other.keySet.++(ours.keySet)
    val varDiff = allKeys.filter(k => ours.getOpt(k) != other.getOpt(k))
    val asgns = varDiff.toList.map(x => Assign(Variable(x, opt(other.getOpt(x))), Variable(x, opt(ours.getOpt(x)))))
    compose(asgns)
  }

  private def snapRenameETF(snapshot: Snapshot): ExpressionTraversalFunction = new ExpressionTraversalFunction {
    override def preF(p: PosInExpr, fml: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] =
      (KaisarProof.getAt(fml, node = Triv()), fml) match {
        case (Some((trm, LabelRef(name, args))), _) =>
          Right(KaisarProof.makeAt(trm, LabelRef(name, args.map(ssa(_, snapshot)))))
        case _ => Left(None)
      }

    override def preT(p: PosInExpr, f: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] =
      (KaisarProof.getAt(f), f) match {
        case (Some((trm, LabelRef(name, args))), _) =>
          Right(KaisarProof.makeAt(trm, LabelRef(name, args.map(ssa(_, snapshot)))))
        case (None, bv: BaseVariable) => Right(BaseVariable(bv.name, opt(snapshot.getOpt(bv.name)), bv.sort))
        case (None, dv: DifferentialSymbol) =>
          Right(DifferentialSymbol(BaseVariable(dv.x.name, opt(snapshot.getOpt(dv.x.name)), dv.sort)))
        case _ => Left(None)
      }
  }
  // Substitution helper function which re-indexes SSA variables according to a snapshot
  private def renameUsingSnapshot(snapshot: Snapshot): (Term => Option[Term]) = (
      (f: Term) => {
        // f@x(args) is not eliminated during SSA (it has a separate pass), but the arguments are evaluated at the current
        // location, so they are SSA'd here
        (KaisarProof.getAt(f), f) match {
          case (Some((trm, LabelRef(name, args))), _) =>
            Some(KaisarProof.makeAt(trm, LabelRef(name, args.map(ssa(_, snapshot)))))
          case (None, bv: BaseVariable) => Some(BaseVariable(bv.name, opt(snapshot.getOpt(bv.name)), bv.sort))
          case (None, dv: DifferentialSymbol) =>
            Some(DifferentialSymbol(BaseVariable(dv.x.name, opt(snapshot.getOpt(dv.x.name)), dv.sort)))
          case _ => None
        }
      }
  )

  /** SSA translation of a term */
  def ssa(f: Term, snapshot: Snapshot): Term = { ExpressionTraversal.traverse(snapRenameETF(snapshot), f).getOrElse(f) }

  /**
   * SSA translation of a hybrid program/game. We assume for simplicity that the hybrid program does not bind any of the
   * variables subject to SSA, meaning we simply re-index free variable occurrences in [[hp]]
   */
  def ssa(hp: Program, snapshot: Snapshot): (Program, Snapshot) = {
    def getAngelLoop(p: Program): Option[(Compose, Option[Program])] = {
      p match {
        case (cmp @ Compose(a: Assign, dl @ Dual(Loop(_)))) => Some((cmp, None))
        case (cmp @ Compose(a: Assign, Compose(Dual(Loop(b)), rest))) => Some((Compose(a, Dual(Loop(b))), Some(rest)))
        case _ => None
      }
    }
    getAngelLoop(hp) match {
      // @TODO: Some soundness side condition needed on x := e
      case Some((Compose(Assign(x, e), Dual(Loop(child))), maybeRest)) =>
        val boundVars = StaticSemantics(child).bv.toSet.+(x)
        val g = ssa(e, snapshot)
        val headSnap = snapshot.addSet(boundVars.-(x))
        val preSnap = snapshot.addSet(boundVars)
        val (y, _snap) = snapshot.increment(x)
        val init = Assign(y, g)
        val (body, postSnap) = ssa(child, preSnap)
        val baseStutters = pstutters(snapshot, headSnap)
        val indStutters = pstutters(postSnap, preSnap)
        val loop = Dual(Loop(compose(body :: indStutters :: Nil)))
        maybeRest match {
          case None =>
            val res = compose(init :: baseStutters :: loop :: Nil)
            (res, preSnap)
          case Some(rest) =>
            val (theRest, restSnap) = ssa(rest, preSnap)
            val res = compose(init :: baseStutters :: loop :: theRest :: Nil)
            (res, restSnap)
        }
      // for loop special case
      case None => hp match {
          case Test(cond) =>
            val (fml, snap) = ssa(cond, snapshot)
            (Test(fml), snap)
          case Assign(x, f) =>
            val g = ssa(f, snapshot)
            val (y, snap) = snapshot.increment(x)
            (Assign(y, g), snap)
          case AssignAny(x) =>
            val (y, snap) = snapshot.increment(x)
            (AssignAny(y), snap)
          case Choice(left, right) =>
            val (leftS, leftSnap) = ssa(left, snapshot)
            val (rightS, rightSnap) = ssa(right, snapshot)
            val snap = leftSnap ++ rightSnap
            val leftStutters = pstutters(leftSnap, snap)
            val rightStutters = pstutters(rightSnap, snap)
            (Choice(compose(leftS :: leftStutters :: Nil), compose(rightS :: rightStutters :: Nil)), snap)
          case Loop(child) =>
            val boundVars = StaticSemantics(child).bv.toSet
            val preSnap = snapshot.addSet(boundVars)
            val (body, postSnap) = ssa(child, preSnap)
            val baseStutters = pstutters(snapshot, preSnap)
            val indStutters = pstutters(postSnap, preSnap)
            val loop = Loop(compose(body :: indStutters :: Nil))
            val res = compose(baseStutters :: loop :: Nil)
            (res, preSnap)
          case odes @ ODESystem(ode, constraint) =>
            val bound = StaticSemantics(odes).bv.toSet
            val snap = snapshot.addSet(bound)
            val ds1 = ssa(ode, snap)
            val (dc1, _dcSnap) = ssa(constraint, snap)
            val inStutter = pstutters(snapshot, snap)
            val outOde = ODESystem(ds1, dc1)
            (compose(inStutter :: outOde :: Nil), snap)
          case Dual(child) =>
            val (childS, snap) = ssa(child, snapshot)
            (Dual(childS), snap)
          case Compose(left, right) =>
            val (leftS, leftSnap) = ssa(left, snapshot)
            val (rightS, rightSnap) = ssa(right, leftSnap)
            (Compose(leftS, rightS), rightSnap)
          case _: AtomicDifferentialProgram | _: AtomicProgram | _: DifferentialProduct | _: CompositeProgram =>
            throw TransformationException(s"Unexpected or unsupported program $hp in SSA pass")
        }
    }
  }

  /**
   * SSA translation of a differential program We assume for simplicity that the program does not bind any of the
   * variables subject to SSA, meaning we simply re-index free variable occurrences
   */
  def ssa(dp: DifferentialProgram, snapshot: Snapshot): (DifferentialProgram) = {
    dp match {
      case AtomicODE(xp, e) =>
        val x = Variable(xp.name, opt(snapshot.getOpt(xp.name)), xp.sort)
        val dx = DifferentialSymbol(x)
        AtomicODE(dx, ssa(e, snapshot))
      case DifferentialProduct(l, r) => DifferentialProduct(ssa(l, snapshot), ssa(r, snapshot))
    }
  }

  /**
   * SSA translation of a formula We assume for simplicity that the formula does not bind any of the variables subject
   * to SSA, meaning we simply re-index free variable occurrences
   */
  def ssa(fml: Formula, snapshot: Snapshot): (Formula, Snapshot) = {
    fml match {
      case q: Quantified => {
        // Note: Results in backwards list, which is then reversed
        val (xxs, qSnap) = q
          .vars
          .foldLeft[(List[Variable], Snapshot)]((Nil, snapshot))({ case ((acc, accSnap), x) =>
            val (xx, snap) = accSnap.increment(x)
            (xx :: acc, snap)
          })
        val (finalChild, finalSnap) = ssa(q.child, qSnap)
        (q.reapply(xxs.reverse, finalChild), finalSnap)
      }
      case m: Modal => {
        val (finalProgram, programSnap) = ssa(m.program, snapshot)
        val (finalChild, finalSnap) = ssa(m.child, programSnap)
        (m.reapply(finalProgram, finalChild), finalSnap)
      }
      case PredOf(func, child) => (PredOf(func, ssa(child, snapshot)), snapshot)
      case PredicationalOf(func, child) =>
        val (finalChild, finalSnap) = ssa(child, snapshot)
        (PredicationalOf(func, finalChild), finalSnap)
      case cf: UnaryCompositeFormula =>
        val (finalChild, finalSnap) = ssa(cf.child, snapshot)
        (cf.reapply(finalChild), finalSnap)
      case bf: BinaryCompositeFormula =>
        val (lf, lSnap) = ssa(bf.left, snapshot)
        val (rf, rSnap) = ssa(bf.right, snapshot)
        val snap = lSnap ++ rSnap
        (bf.reapply(lf, rf), snap)
      case cmpF: ComparisonFormula => (cmpF.reapply(ssa(cmpF.left, snapshot), ssa(cmpF.right, snapshot)), snapshot)
      case af: AtomicFormula => (af, snapshot)
      case cf: CompositeFormula => throw TransformationException(
          "Expected all composite formulas to be implemented, this exception should be unreachable"
        )
    }
  }

  /** SSA translation of a hybrid program/game */
  def ssa(exp: Expression, snapshot: Snapshot): (Expression, Snapshot) = {
    exp match {
      case e: Term => (ssa(e, snapshot), snapshot)
      case e: Formula => ssa(e, snapshot)
      case e: DifferentialProgram => ssa(e, snapshot)
      case e: Program => ssa(e, snapshot)
      case _ => throw TransformationException("Expected all cases implemented in SSA, this line should be unreachable")
    }
  }

  /** SSA translation of a proof method */
  def ssa(m: Method, snapshot: Snapshot): Method = {
    val node = m match {
      case _: RCF | _: Auto | _: Prop | _: Solution | _: DiffInduction | _: Exhaustive | _: Hypothesis => m
      case GuardDone(Some(delta)) => GuardDone(Some(ssa(delta, snapshot)))
      case Using(sels, m) => Using(sels.map(ssa(_, snapshot)), ssa(m, snapshot))
      // @TODO: This means variable indices which are used in ss can be reused elsewhere. Is this what we want?
      case ByProof(ss) => ByProof(ssa(Block(ss), snapshot)._1.asInstanceOf[Block].ss)
      case _: GuardDone => throw TransformationException("Bad pattern match in SSA for GuardDone")
    }
    locate(node, m)
  }

  /** SSA translation of a fact selector */
  def ssa(sel: Selector, snapshot: Snapshot): Selector = {
    val node = sel match {
      case DefaultSelector | DefaultAssignmentSelector => sel
      /* @TODO: Revisit this once pattern selectors have really been used. It's arguably better for a pattern to select
       * facts regardless of which variable version/index is used. In that case, SSA renaming would be irrelevant here*/
      case PatternSelector(e) => PatternSelector(ssa(e, snapshot))
      case ForwardSelector(pt) => ForwardSelector(ssa(pt, snapshot))
    }
    locate(node, sel)
  }

  /** SSA transformation of a forward proof term */
  def ssa(pt: ProofTerm, snapshot: Snapshot): ProofTerm = {
    val node = pt match {
      /* SSA doesn't re-index fact variable names, just program variables */
      case ProofVar(x) => ProofVar(x)
      /* ProgramAssignments / ProgramVar(x) is used to search assignments of *all* versions of x, no re-index needed. */
      case ProgramAssignments(x, ssa) => ProgramAssignments(x, ssa)
      case ProgramVar(x) => ProgramVar(x)
      case ProofInstance(e) =>
        val (ee, _snap) = ssa(e, snapshot)
        ProofInstance(ee)
      case ProofApp(m, n) => ProofApp(ssa(m, snapshot), ssa(n, snapshot))
    }
    locate(node, pt)
  }

  /**
   * SSA translation of a [[Modify]] proof statement
   * @return
   *   Translated statement and snapshot of final state
   */
  def ssa(mod: Modify, snapshot: Snapshot): (Modify, Snapshot) = {
    val (asgns, snap) = mod
      .asgns
      .foldLeft[(List[(Option[Ident], Variable, Option[Term])], Snapshot)](Nil, snapshot)({
        case ((list, snapshot), (id, x, f)) =>
          val (xx, snap) = snapshot.increment(x)
          ((id, xx, f.map(ssa(_, snapshot))) :: list, snap)
      })
    val node = Modify(asgns.reverse)
    (locate(node, mod), snap)
  }

  /** Translate indices of label arguments */
  def ssa(ld: LabelDef, snapshot: Snapshot): LabelDef = {
    LabelDef(ld.label, ld.args.map(ssa(_, snapshot).asInstanceOf[Variable]))
  }

  /** @returns Translated statement and snapshot of final state */
  def ssa(s: Statement, snapshot: Snapshot): (Statement, Snapshot) = {
    val (node, snap) = s match {
      case mod: Modify => ssa(mod, snapshot)
      case Label(ld, _) => (Label(ssa(ld, snapshot), Some(snapshot)), snapshot)
      case Block(ss) =>
        val (ssRev, finalSnap) = ss
          .foldLeft[(List[Statement], Snapshot)]((Nil, snapshot))({ case ((acc, snapshot), s1) =>
            val (s2, snap) = ssa(s1, snapshot)
            (s2 :: acc, snap)
          })
        (KaisarProof.block(ssRev.reverse), finalSnap)
      case BoxChoice(left, right) =>
        val (leftS, leftSnap) = ssa(left, snapshot)
        val (rightS, rightSnap) = ssa(right, snapshot)
        val snap = leftSnap ++ rightSnap
        val leftStutters = stutters(leftSnap, snap, s)
        val rightStutters = stutters(rightSnap, snap, s)
        (
          BoxChoice(KaisarProof.block(leftS :: leftStutters :: Nil), KaisarProof.block(rightS :: rightStutters :: Nil)),
          snap,
        )
      case BoxLoop(inBody, ih) =>
        val boundVars = VariableSets(inBody).boundVars
        val preSnap = snapshot.addSet(boundVars)
        val (body, postSnap) = ssa(inBody, preSnap)
        val baseStutters = stutters(snapshot, preSnap, s)
        val indStutters = stutters(postSnap, preSnap, s)
        val loop = locate(BoxLoop(KaisarProof.block(body :: indStutters :: Nil), ih), s)
        val res = KaisarProof.block(baseStutters :: loop :: Nil)
        (res, preSnap)
      case While(x: Expression, j: Formula, inBody: Statement) =>
        val (body, bodySnap) = ssa(inBody, snapshot)
        val baseStutters = stutters(snapshot, bodySnap, s)
        val indStutters = stutters(bodySnap, snapshot, s)
        val (xx, (jj, _jjSnap)) = (ssa(x, bodySnap), ssa(j, bodySnap))
        val whilst = locate(While(xx, jj, KaisarProof.block(body :: indStutters :: Nil)), s)
        (KaisarProof.block(baseStutters :: whilst :: Nil), bodySnap)
      case For(metX, met0, metIncr, conv, guard, inBody, metGuard) =>
        val met00 = ssa(met0, snapshot)
        val (metXX, initSnap) = snapshot.increment(metX)
        val boundVars = VariableSets(inBody).boundVars
        val preSnap = snapshot.addSet(boundVars).revisit(metXX)
        val (body, postSnap) = ssa(inBody, preSnap)
        val baseStutters = stutters(snapshot, preSnap, s)
        val indStutters = stutters(postSnap, preSnap, s)
        // NB: SSA for for-loops is awkward because we SSA-assign the loop index variable and then assign it again as part
        // of the loop, but this might be preferable to leaving out its SSA assignment
        val metIncrr = ssa(metIncr, preSnap)
        val (guardd: Assume, _) = ssa(guard, preSnap)
        val convv = conv.map(ssa(_, preSnap)._1.asInstanceOf[Assert])
        val metGuardd: Option[Term] = metGuard.map(f => ssa(f, preSnap))
        val forth = locate(
          For(metXX, met00, metIncrr, convv, guardd, KaisarProof.block(body :: indStutters :: Nil), metGuardd),
          s,
        )
        (KaisarProof.block(baseStutters :: forth :: Nil), preSnap)
      // @TODO: switch case seems wrong, needs swap in the assignments
      case Switch(scrutinee: Option[Selector], pats: List[(Expression, Expression, Statement)]) =>
        val scrut = scrutinee.map(ssa(_, snapshot))
        val clauses = pats.map({
          case (x, f, s) => {
            val (ff, snap1) = ssa(f, snapshot)
            val (ss, snap2) = ssa(s, snap1)
            ((x, ff, ss), snap2)
          }
        })
        val maxSnap = clauses.map(_._2).reduce(_ ++ _)
        val stutterClauses = clauses.map({ case ((x, f, bs), clauseSnap) =>
          val asgns = stutters(clauseSnap, maxSnap, s)
          (x, f, KaisarProof.block(asgns :: bs :: Nil))
        })
        (Switch(scrut, stutterClauses), maxSnap)
      case Assume(pat, f) =>
        val (fml, _fmlSnap) = ssa(f, snapshot)
        (Assume(pat, fml), snapshot)
      case Assert(pat, f, m) =>
        val (ff, _fmlSnap) = ssa(f, snapshot)
        val mm = ssa(m, snapshot)
        (Assert(pat, ff, mm), snapshot)
      case Note(x, proof, annotation) =>
        val (ann, _annSnap) = annotation.map(ssa(_, snapshot)) match {
          case Some((l, r)) => (Some(l), r)
          case None => (None, snapshot)
        }
        (Note(x, ssa(proof, snapshot), ann), snapshot)
      case LetSym(f, args, e) => {
        // Don't SSA parameters, only state variables
        val bound = args.toSet
        val local = snapshot.filter({ case (k, v) => !bound.contains(Variable(k)) })
        val (loc, _locSnap) = ssa(e, local)
        (LetSym(f, args, loc), snapshot)
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
        val inStutter = stutters(snapshot, snap, s)
        val ode = locate(ProveODE(ds1, dc1), s)
        (KaisarProof.block(inStutter :: ode :: Nil), snap)
      case Was(now: Statement, was: Statement) =>
        val (now1, snap) = ssa(now, snapshot)
        (Was(now1, was), snap)
      /* @TODO: Decide intended semantics of Match patterns. Here I assume that bound variables are not shadowed in a pattern-match,
       * but that free variables may be introduced */
      case Match(pat: Expression, e: Expression) =>
        val snap = snapshot.addPattern(pat)
        val (ee, _eSnap) = ssa(e, snapshot)
        (Match(ssa(pat, snap), ee), snap)
      case Triv() => (Triv(), snapshot)
      case pr: Pragma => (pr, snapshot)
      case meta: MetaNode => throw TransformationException(s"Cannot apply SSA to context-only node $meta")
    }
    (locate(node, s), snap)
  }

  /**
   * In contrast to other ssa functions, differential equations do not update the snapshot as we go. instead,
   * [[snapshot]] should be the snapshot at the *end* of the ODE, which must be precomputed. this difference is due to
   * product ODEs having to assign variables in parallel
   */
  def ssa(ds: DiffStatement, snapshot: Snapshot): DiffStatement = {
    val node = ds match {
      case AtomicODEStatement(dp: AtomicODE, ident) =>
        val x = Variable(dp.xp.name, opt(snapshot.getOpt(dp.xp.name)), dp.xp.sort)
        val dx = DifferentialSymbol(x)
        AtomicODEStatement(AtomicODE(dx, ssa(dp.e, snapshot)), ident)
      case DiffProductStatement(l, r) => DiffProductStatement(ssa(l, snapshot), ssa(r, snapshot))
      case DiffGhostStatement(ds) => DiffGhostStatement(ssa(ds, snapshot))
      case InverseDiffGhostStatement(ds) => InverseDiffGhostStatement(ssa(ds, snapshot))
    }
    locate(node, ds)
  }

  /**
   * SSA translation of domain statement. [[DomModify]] might bind a duration variable, in which case [[snapshot]]
   * refers to the *final* state of the ODE.
   */
  def ssa(ds: DomainStatement, snapshot: Snapshot): DomainStatement = {
    val node = ds match {
      case DomAssume(x, f) =>
        val (fml, _fmlSnap) = ssa(f, snapshot)
        (DomAssume(ssa(x, snapshot), fml))
      case DomAssert(x, f, child) =>
        val (fml, _fmlSnap) = ssa(f, snapshot)
        (DomAssert(ssa(x, snapshot), fml, ssa(child, snapshot)))
      case DomWeak(dc) =>
        val dc1 = ssa(dc, snapshot)
        DomWeak(dc1)
      // note: final subscript of time variable t was already precomputed in snapshot. Don't use ssa(mod: Modify)
      // since it would doubly increment the subscript
      case DomModify(id, x, f) =>
        val xt = ssa(x, snapshot).asInstanceOf[Variable]
        DomModify(id, xt, ssa(f, snapshot))
      case DomAnd(l, r) =>
        val l1 = ssa(l, snapshot)
        val r1 = ssa(r, snapshot)
        DomAnd(l1, r1)
    }
    locate(node, ds)
  }

  /** Apply SSA translation pass to Kaisar statement */
  def apply(s: Statement): Statement = {
    val vs = VariableSets(s)
    val vars = vs.freeVars ++ vs.boundVars
    val snap = Snapshot.initial(vars)
    ssa(s, snap)._1
  }

  /**
   * Apply SSA translation pass to hybrid program. Make sure you don't actually want apply(Statement). Hybrid program
   * SSA is used, for example, to cross-check statements against CdGL theorem statements
   */
  def apply(hp: Program): Program = {
    val vs = StaticSemantics(hp)
    val vars = vs.fv.toSet ++ vs.bv.toSet
    val snap = Snapshot.initial(vars)
    ssa(hp, snap)._1
  }
}
