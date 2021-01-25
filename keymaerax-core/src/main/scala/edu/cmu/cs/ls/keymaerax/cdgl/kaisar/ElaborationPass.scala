/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * Reduces all other selectors to proof and program-variable selectors.
  * Proof-term selectors are translated to [[Note]]s. Variables, which are ambiguous
  * in the source syntax, are disambiguated to program variables or proof variables, and the "default"
  * selector is lowered as well.
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.ProofTraversal.TraversalFunction
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.Context._
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.{ElaborationException, Ident, IdentPat}
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.ASTNode._
import edu.cmu.cs.ls.keymaerax.core._

class ElaborationPass() {
  var ghostCon: Context = Context.empty.asElaborationContext

  /** Generous notion of free variables: include variables explicitly mentioned in proof term as well as program variables
    * mentioned in any fact used in the proof. */
  private def freeVarsPT(con: Context, pt: ProofTerm): Set[Variable] = {
    pt match {
      case ProgramVar(x) => Set(x)
      case ProofVar(x) =>
        val fml = con.get(x).getOrElse(True)
        val plainFml = KaisarProof.forgetAt(fml)
        StaticSemantics(plainFml).fv.toSet
      case ProofInstance(e: Formula) => StaticSemantics(e).fv.toSet
      case ProofInstance(e: Program) => StaticSemantics(e).fv.toSet
      case ProofInstance(e: Term) => StaticSemantics(e).toSet
      case ProofApp(m, n) => freeVarsPT(con, m) ++ freeVarsPT(con, n)
    }
  }
  private def freeVarsSel(con: Context, sel: Selector): Set[Variable] = {
    sel match {
      case ForwardSelector(pt) => freeVarsPT(con, pt)
      case _ => Set()
    }
  }

  /** Determine which variables in [[pt]] are fact variables vs. program variables when resolved in context [[kc]]. */
  private def collectPt(kc: Context, pt: ProofTerm): ProofTerm = {
    pt match {
      case ProofVar(x) if ForwardProofChecker.allBuiltins.contains(x.name) => ProofVar(x)
      case ProofVar(x) =>
        // If x is not found as a fact variable, assume it's a program variable
        val got = kc.get(x)
        got  match {
          case Some(_) => pt
          case None if VariableSets(kc).allVars.contains(x) =>
            locate(ProgramVar(x), pt)
          case _ =>
            throw ElaborationException(s"Tried to use unknown fact: $x. Typo?", node = pt)
        }
      case ProofApp(m, n) => locate(ProofApp(collectPt(kc, m), collectPt(kc, n)), pt)
      case _: ProofInstance => pt
      case ProgramVar(x) => throw ElaborationException("Did not expect program variable proof term in selector elimination pass.", node = pt)
    }
  }

  /** @return list of proof terms selected by selector. */
  private def collectPts(kc: Context, sel: Selector, goal: Formula): List[Selector] = {
    sel match {
      case ForwardSelector(pt) => ForwardSelector(collectPt(kc, pt)) :: Nil
      case PatternSelector(pat) => kc.unify(pat).flatMap({case (Some(x), _) => Some(locate(ForwardSelector(ProofVar(x)), sel)) case _ => None}).toList
      // Delay elaboration until after functions/labels are elaborated
      case DefaultAssignmentSelector | DefaultSelector => List(sel)
    }
  }

  /** @return list of assumption proof term for method, paired with underlying method  */
  private def collectPts(kc: Context, kce: Context, asrt: Assert, m: Method, goal: Formula): (List[Selector], Method) = {
    m match {
      case Using(use, m) =>
        val useAssms = use.flatMap(collectPts(kc, _, goal))
        val (assms, meth) = collectPts(kc, kce, asrt, m, goal)
        val combineAssms = useAssms ++ assms
        if(combineAssms.isEmpty && use != List(DefaultSelector) && use != List(DefaultAssignmentSelector))
          throw ElaborationException("Non-default selector should select at least one fact.", node = m)
        val allFree = combineAssms.map(freeVarsSel(kc, _)).foldLeft[Set[Variable]](Set())(_ ++ _)
        val freePtCandidates = allFree.toList.map(ProgramAssignments(_))
        val freePt = freePtCandidates.filter(x => kc.getAssignments(x.x).nonEmpty).map(ForwardSelector)
        (freePt ++ combineAssms, meth)
      case ByProof(pf) => (List(), locate(ByProof(apply(locate(Block(pf), m)) :: Nil), m))
      case _: ByProof | _: RCF | _: Auto | _: Prop | _: Solution | _: DiffInduction | _: Exhaustive | _: Hypothesis => (List(), m)
      case GuardDone(fOpt) =>
        val delta = fOpt match {
          case Some(delta) => delta
          case None => kce.inferGuardDelta(asrt)
        }
        val deltaElab = kce.elaborateFunctions(delta, m)
        // @TODO: Check this see if it works on not
        kc.sideEffect(Assert(asrt.pat, asrt.f, GuardDone(Some(deltaElab))))
        kce.sideEffect(Assert(asrt.pat, asrt.f, GuardDone(Some(deltaElab))))
        (List(), GuardDone(Some(deltaElab)))
    }
  }

  /** @return domain statement with proofvar and programvar resolved. Does not introduce notes. */
  private def collectPts(kc: Context, kce: Context, dc: DomainStatement): DomainStatement = {
    dc match {
      case DomAnd(l, r) =>
        val dsL = collectPts(kc, kce, l)
        // If left branch introduces domain constraint assumptions / assertions, then assertions in right half can mention.
        // @TODO: Add to kce or not?
        val dsR = collectPts(kc.:+(dsL.collect.constraints.s), kce:+(dsL.collect.constraints.s), r)
        locate(DomAnd(dsL, dsR), dc)
      case DomAssume(x, f) =>
        StandardLibrary.factBindings(x, kc.elaborateFunctions(f, dc), dc).map({case (x, y) => locate(DomAssume(IdentPat(x), y), dc)}).
          reduce[DomainStatement]({case (l, r) => locate(DomAnd(l, r), dc)})
      case DomAssert(x, f, m) =>
        if(x != Nothing && !x.isInstanceOf[Variable])
          throw ElaborationException(s"Non-scalar fact patterns not allowed in domain constraint assertion ${dc}", node = dc)
        val (assump, meth) = collectPts(kc, kce, Assert(x,f,m), m, f)
        locate(DomAssert(x, kc.elaborateFunctions(f, dc), Using(assump, meth)), dc)
      case DomModify(id, x, f) => locate(DomModify(id, x, kc.elaborateFunctions(f, dc)), dc)
      case DomWeak(dc) => locate(DomWeak(dc), dc)
    }
  }


  /** @return statement where advanced selectors have been elaborated to simple selectors */
  def apply(s: Statement): Statement = {
    ghostCon = ghostCon.reapply(s)
    val ret = ProofTraversal.traverse(Context.empty.asElaborationContext, Context.empty.asElaborationContext,s, new TraversalFunction {
      // Forward proof term conjoining input list of facts
      private def conjoin(xs: List[Ident]): ProofTerm = {
        xs.map(ProofVar).reduce[ProofTerm]{case (l, r) => ProofApp(ProofApp(ProofVar(Variable("andI")), l), r)}
      }

      // Throw an exception if we think the user is trying to write an invalid simultaneous assignment. We could just ignore
      // this and treat it as a sequential assignment, but we done't want to confuse them.
      private def checkAdmissibleAssignmentBlock(ss: List[Modify]): Unit = {
        val _ = ss.foldRight[Set[Variable]](Set())({case (mod, acc) =>
          val bv = mod.boundVars
          val fv = mod.freeVars
          if(acc.intersect(fv).nonEmpty)
            throw ElaborationException(s"Simultaneous vector assignments are not supported, but assignment $mod tries to use simultaneously-bound variable(s) ${acc.intersect(fv)}. " +
              s"To fix this, assign each variable separately, and if you wish to use a simultaneous assignment, introduce temporary variables for the old value(s) of ${acc.intersect(fv)}.",
              node = mod)
          acc.++(bv)
        })
      }

      // Elaborate vectorial modify into a block of single modifies
      private def elabVectorAssign(modify: Modify): Statement = {
        if(modify.mods.length == 1)
          modify
        // If the assignment *vector* has a single name, then ghost in the assignment facts and note their conjunction.
        else if (modify.ids.length == 1 && modify.mods.length > 1) {
          val (asgnIds, assignsRev) = modify.mods.foldLeft[List[(Option[Ident], Modify)]](Nil){
            // * assignments do not introduce facts
            case (xfs, (x, None)) =>
              (None, Modify(Nil, List((x, None)))) :: xfs
            case (xfs, (x, Some(f))) =>
              val id = ghostCon.fresh()
              val fml = Equal(x, f)
              ghostCon = ghostCon.ghost(fml)
              (Some(id), locate(Modify(List(id), List((x, Some(f)))), modify)) :: xfs
          }.unzip
          val assigns = assignsRev.reverse
          checkAdmissibleAssignmentBlock(assigns)
          val note = locate(Note(modify.ids.head, conjoin(asgnIds.filter(_.isDefined).map(_.get))), modify)
          // Assign individually and then note the conjoined assignment
          locate(KaisarProof.block(assigns :+ note), modify)
        }
        // If assignments are unannotated or individually annotated, just unpack them normally.
        else {
          val asgns = modify.asgns.map({case (id, x, f) => locate(Modify(id.toList, List((x, f))), modify)})
          checkAdmissibleAssignmentBlock(asgns)
          locate(KaisarProof.block(asgns), modify)
        }
      }

      private def coerceFormula(e: ProofTerm): ProofTerm = {
        e match {
          case ProofInstance(f: Formula) => ProofInstance(f)
          case ProofInstance(FuncOf(Function(name, index, domain, sort, interpreted), arg)) => ProofInstance(PredOf(Function(name, index, domain, Bool, interpreted), arg))
          case _ => throw new Exception(s"Expected formula, got $e")
        }
      }

      private def coerceTerm(e: ProofTerm): ProofTerm = {
        e match {
          case ProofInstance(f: Term) => ProofInstance(f)
          case ProofInstance(PredOf(Function(name, index, domain, sort, interpreted), arg)) => ProofInstance(FuncOf(Function(name, index, domain, Real, interpreted), arg))
          case _ => throw new Exception(s"Expected formula, got $e")
        }
      }

      private def coercePTSorts(pt: ProofTerm): ProofTerm = {
        pt match {
          case ProofApp(ProofApp(ProofVar(BaseVariable("orIL", _, _)), pt1), pt2: ProofInstance) => ProofApp(ProofApp(ProofVar(Variable("orIL")), coercePTSorts(pt1)), coerceFormula(pt2))
          case ProofApp(ProofApp(ProofVar(BaseVariable("orIR", _, _)), pt1: ProofInstance), pt2) => ProofApp(ProofApp(ProofVar(Variable("orIR")), coerceFormula(pt1)), coercePTSorts(pt2))
          case ProofApp(ProofApp(ProofVar(BaseVariable("falseE", _, _)), pt1), pt2:ProofInstance) => ProofApp(ProofApp(ProofVar(Variable("falseE")), coercePTSorts(pt1)), coerceFormula(pt2))
          case ProofApp(ProofApp(ProofVar(BaseVariable("implyW", _, _)), pt1: ProofInstance), pt2) => ProofApp(ProofApp(ProofVar(Variable("implyW")), coerceFormula(pt1)), coercePTSorts(pt2))
          case ProofApp(ProofApp(ProofVar(BaseVariable("allE", _, _)), pt1), pt2) => ProofApp(ProofApp(ProofVar(Variable("allE")), coercePTSorts(pt1)), coerceTerm(pt2))
          case ProofApp(ProofApp(ProofApp(ProofVar(BaseVariable("existsI", _, _)), pt1), pt2), pt3) =>ProofApp(ProofApp(ProofApp(ProofVar(Variable("existsI")), coercePTSorts(pt1)), coerceTerm(pt2)), coercePTSorts(pt3))
          case ProofApp(m, n) => ProofApp(coercePTSorts(m), coercePTSorts(n))
          case _ => pt
        }
      }

      override def preS(kc: Context, kce: Context, sel: Statement): Option[Statement] = {
        sel match {
          case mod: Modify =>
            // ProofTraversal can handle locations if we're translating statements one-to-one, but we should do it by hand
            // when we introduce "new" assignments.
            val elabFuncs = locate(Modify(mod.ids, mod.mods.map({case (x, fOpt) => (x, fOpt.map(x => kce.elaborateFunctions(x, mod)))})), sel)
            Some(elabVectorAssign(elabFuncs))
          case Assume(e, f) =>
            // @Note: Splitting up assumes would be bad because it breaks lastFact
            Some(locate(Assume(e, kce.elaborateFunctions(f, sel)), sel))
          case asrt@Assert(e, f, m) =>
            val (fullSels, meth) = collectPts(kc, kce, asrt, m, f)
            val finalMeth = locate(Using(fullSels, meth), meth)
            val assertion = locate(Assert(e, kce.elaborateFunctions(f, sel), finalMeth), sel)
            Some(locate(assertion, sel))
          case ProveODE(ds, dc) =>
            requireTimeVarForSolution(ds, ds.clocks)
            // Context should include ODE during collection, because we want to know about domain constraint fmls and we may
            // want to remember selectors of the ODE bound variables for later (e.g. remember Phi nodes during SSA)
            // @TODO: kce, kce or kc, kce
            val dom = collectPts(kce.:+(sel), kce.:+(sel), dc)
            Some(ProveODE(ds, dom))
          case Note(x, plainPt, ann) =>
            val pt = coercePTSorts(plainPt)
            val finalPt = locate(kce.elaborateFunctions(pt, pt), pt)
            Some(locate(Note(x, finalPt, ann), sel))
          case _ => None
        }
      }

      private def requireTimeVarForSolution(ds: DiffStatement, clocks: Set[Variable]): Unit = {
        ds match {
          case AtomicODEStatement(dp, Nothing) => ()
          case AtomicODEStatement(dp, solFact) if clocks.isEmpty => throw ElaborationException("ODE with solution label must have time variable")
          case AtomicODEStatement(dp, solFact)  => ()
          case DiffProductStatement(l, r) => requireTimeVarForSolution(l, clocks); requireTimeVarForSolution(r, clocks)
          case DiffGhostStatement(ds) => requireTimeVarForSolution(ds, clocks)
          case InverseDiffGhostStatement(ds) => requireTimeVarForSolution(ds, clocks)
        }
      }

      // Elaborate terms and formulas throughout an ODE proof
      private def elaborateODE(kc: Context, kce: Context,  ds: DiffStatement): DiffStatement = {
        ds match {
          case AtomicODEStatement(AtomicODE(xp, e), solFact) => AtomicODEStatement(AtomicODE(xp, kce.elaborateFunctions(e, ds)), solFact)
          case DiffProductStatement(l, r) => DiffProductStatement(elaborateODE(kc, kce, l), elaborateODE(kc, kce, r))
          case DiffGhostStatement(ds) => DiffGhostStatement(elaborateODE(kc, kce, ds))
          case InverseDiffGhostStatement(ds) => InverseDiffGhostStatement(elaborateODE(kc, kce, ds))
        }
      }

      // elaborate terms and formulas in all terms that mention them, Asserts which were handled earlier.
      override def postS(kc: Context, kce: Context, s: Statement): Statement = {
        s match {
          case Assume(pat, f) => locate(Assume(pat, kce.elaborateFunctions(f, s)),s)
          // Elaborate all functions that are defined *before* f
          case LetSym(f, args, e: Term) =>
            val rhs = kce.elaborateFunctions(e, s)
            locate(LetSym(f, args, rhs),s)
          case LetSym(f, args, e: Formula) => locate(LetSym(f, args, kce.elaborateFunctions(e, s)),s)
          case LetSym(_, _, _: Program) => throw ElaborationException("Lets of programs are only allowed in top-level declarations, not in proofs")
          case Match(pat, e: Term) => locate(Match(pat, kce.elaborateFunctions(e, s)),s)
          case While(x, j, body) => locate(While(x, kce.elaborateFunctions(j, s), body),s)
          case For(metX, metF, metIncr, guard, conv, body, metGuard) =>
            locate(For(metX, kce.elaborateFunctions(metF, s), kce.elaborateFunctions(metIncr, s), guard, conv, body, metGuard.map{f => kce.elaborateFunctions(f, s)}), s)
          case BoxLoop(body, Some((ihk, ihv, None))) =>
            locate(BoxLoop(body, Some((ihk, kce.elaborateFunctions(ihv, s), None))),s)
          // dc was elaborated in preS
          case ProveODE(ds, dc) => locate(ProveODE(elaborateODE(kc, kce, ds), dc), s)
          case Switch(scrut, pats) => locate(Switch(scrut, pats.map({case (x, f: Formula, b) => (x, kce.elaborateFunctions(f, s), b)})), s)
          case s => s
        }
      }
    })
    ghostCon = Context.empty.asElaborationContext
    ret
  }
}
