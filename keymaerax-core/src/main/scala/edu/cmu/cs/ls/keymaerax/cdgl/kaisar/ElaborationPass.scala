/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * Reduces all other selectors to proof and program-variable selectors.
  * Proof-term selectors are translated to [[Note]]s. Variables, which are armbiguous
  * in the source syntax, are disambiguated to program variables or proof variables, and the "default"
  * selector is lowered as well.
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.ProofTraversal.TraversalFunction
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.Context._
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.{ElaborationException, Ident}
import edu.cmu.cs.ls.keymaerax.core._

class ElaborationPass() {
  var ghostCon: Context = Context.empty.asElaborationContext

  /** Generous notion of free variables: include variables explicitly mentioned in proof term as well as program variables
    * mentioned in any fact used in the proof. */
  private def freeVarsPT(con: Context, pt: ProofTerm): Set[Variable] = {
    pt match {
      case ProgramVar(x) => Set(x)
      case ProofVar(x) => StaticSemantics(con.get(x).getOrElse(True)).fv.toSet
      case ProofInstance(e: Formula) => StaticSemantics(e).fv.toSet
      case ProofInstance(e: Program) => StaticSemantics(e).fv.toSet
      case ProofInstance(e: Term) => StaticSemantics(e).toSet
      case ProofApp(m, n) => freeVarsPT(con, m) ++ freeVarsPT(con, n)
    }
  }

  /** Determine which variables in [[pt]] are fact variables vs. program variables when resolved in context [[kc]]. */
  private def disambiguate(kc: Context, pt: ProofTerm): ProofTerm = {
    pt match {
      case ProofVar(x) =>
        // If x is not found as a fact variable, assume it's a program variable
        val got = kc.get(x)
        got  match {
          case Some(_) => pt
          case None if VariableSets(kc).allVars.contains(x) =>
            ProgramVar(x)
          case _ =>
            throw ElaborationException(s"Tried to use unknown fact: $x. Typo?")
        }
      case ProofApp(m, n) => ProofApp(disambiguate(kc, m), disambiguate(kc, n))
      case ProofInstance(e) => ProofInstance(e)
      case ProgramVar(x) => throw ElaborationException("Did not expect program variable proof term in selector elimination pass.")
    }
  }

  /** Return morally "the same" selector, but determine which variables are ProofVar vs. ProgramVar */
  private def disambiguate(kc: Context, sel: Selector, goal: Formula): List[Selector] = {
    sel match {
      case DefaultSelector =>
        val fv = StaticSemantics(goal).fv
        val candidates = fv.toSet.toList.map(ProgramVar)
        val allAssignments = candidates.map(x => kc.getAssignments(x.x))
        candidates.filter(x => kc.getAssignments(x.x).nonEmpty).map(ForwardSelector)
      case ForwardSelector(pt) => List(ForwardSelector(disambiguate(kc, pt)))
      case sel => List(sel)
    }
  }

  /** @return list of proof terms selected by selector. */
  private def collectPts(kc: Context, sel: Selector, goal: Formula): List[ProofTerm] = {
    sel match {
      case DefaultSelector =>
        val fv = StaticSemantics(goal).fv
        val candidates = fv.toSet.toList.map(ProgramVar)
        // Program is not yet SSA-form, so don't filter out program variables that get bound twice.
        val eachAssigns = candidates.map(x => (x, kc.getAssignments(x.x)))
        eachAssigns.filter(_._2.nonEmpty).map(_._1)
      case ForwardSelector(pt) => List(disambiguate(kc, pt))
      case PatternSelector(pat) =>
        kc.unify(pat).map({case (x, _) => ProofVar(x)}).toList
    }
  }

  /** Return morally "the same" method, but determine which variables are ProofVar vs. ProgramVar */
  private def disambiguate(kc: Context, m: Method, goal: Formula): Method = {
    m match {
      case Using(use, m) => Using(use.flatMap(disambiguate(kc, _, goal)), disambiguate(kc, m, goal))
      case m => m
    }
  }

  /** @return list of assumption proof term for method, paired with underlying method  */
  private def collectPts(kc: Context, m: Method, goal: Formula): (List[ProofTerm], Method) = {
    m match {
      case Using(use, m) =>
        val useAssms = use.flatMap(collectPts(kc, _, goal))
        val (assms, meth) = collectPts(kc, m, goal)
        val combineAssmsCandidates = useAssms ++ assms
        if(combineAssmsCandidates.isEmpty && use != List(DefaultSelector))
          throw ElaborationException("Non-default selector should select at least one fact.")
        val allFree = combineAssmsCandidates.map(freeVarsPT(kc, _)).foldLeft[Set[Variable]](Set())(_ ++ _)
        val freePtCandidates = allFree.toList.map(ProgramVar)
        val freePt = freePtCandidates.filter(x => kc.getAssignments(x.x).nonEmpty)
        val combineAssms = combineAssmsCandidates.filter(!_.isInstanceOf[ProgramVar])
        val dedupAssms = freePt ++ combineAssms
        (dedupAssms, meth)
      case ByProof(pf) => (List(), ByProof(apply(Block(pf)) :: Nil))
      case _: ByProof | _: RCF | _: Auto | _: Prop | _: Solution | _: DiffInduction | _: Exhaustive => (List(), m)
    }
  }

  /** @return domain statement with proofvar and programvar resolved. Does not introduce notes. */
  private def collectPts(kc: Context, dc: DomainStatement): DomainStatement = {
    dc match {
      case DomAnd(l, r) =>
        val dsL = collectPts(kc, l)
        // If left branch introduces domain constraint assumptions / assertions, then assertions in right half can mention.
        val dsR = collectPts(kc.:+(dsL.collect.constraints.s), r)
        (DomAnd(dsL, dsR))
      case DomAssume(x, f) => DomAssume(x, kc.elaborateFunctions(f))
      case DomAssert(x, f, m) =>
        val meth = disambiguate(kc, m, f)
        DomAssert(x, kc.elaborateFunctions(f), meth)
      case DomModify(x, f) => DomModify(x, kc.elaborateFunctions(f))
      case DomWeak(dc) => DomWeak(dc)
    }
  }

  /** @return statement where advanced selectors have been elaborated to simple selectors */
  def apply(s: Statement): Statement = {
    ghostCon = ghostCon.reapply(s)
    val ret = ProofTraversal.traverse(Context.empty.asElaborationContext, s, new TraversalFunction {

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
              s"To fix this, assign each variable separately, and if you wish to use a simultaneous assignment, introduce temporary variables for the old value(s) of ${acc.intersect(fv)}.")
          acc.++(bv)
        })
      }

      private def elabVectorAssign(modify: Modify): Statement = {
        if(modify.mods.length == 1)
          return modify
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
              (Some(id), Modify(List(id), List((x, Some(f))))) :: xfs
          }.unzip
          val assigns = assignsRev.reverse
          checkAdmissibleAssignmentBlock(assigns)
          val note = Note(modify.ids.head, conjoin(asgnIds.filter(_.isDefined).map(_.get)))
          // Assign individually and then note the conjoined assignment
          KaisarProof.block(assigns :+ note)
        }
        // If assignments are unannotated or individually annotated, just unpack them normally.
        else {
          val asgns = modify.asgns.map({case (id, x, f) => Modify(id.toList, List((x, f)))})
          checkAdmissibleAssignmentBlock(asgns)
          KaisarProof.block(asgns)
        }
      }

      override def preS(kc: Context, sel: Statement): Option[Statement] = {
        sel match {
          case mod: Modify =>
            val elabFuncs = Modify(mod.ids, mod.mods.map({case (x, fOpt) => (x, fOpt.map(kc.elaborateFunctions(_)))}))
            Some(elabVectorAssign(elabFuncs))
          case Assert(e, f, m) =>
            val (pts, meth) = collectPts(kc, m, f)
            val (keptPts, notePts) = pts.partition({case ProofVar(x) => true case _ => false})
            val notes: List[Ghost] =
              notePts.foldLeft[List[Ghost]]((List[Ghost]()))({case (acc: List[Ghost], pt) =>
                val id = ghostCon.fresh()
                ghostCon = ghostCon.ghost(KaisarProof.askLaterP)
                // notes should be ghosts since they did not appear in the user's intended proof/program.
                // proofchecking output after selector elimination should "look like" proofchecking the input
                Ghost(Note(id, pt)) :: acc})
            val noteSels = notes.map({case Ghost(Note(id, _, _)) => ForwardSelector(ProofVar(id))})
            val fullSels = keptPts.map(ForwardSelector) ++ noteSels
            val finalMeth = Using(fullSels, meth)
            Some(Block(notes.:+(Assert(e, kc.elaborateFunctions(f), finalMeth))))
          case ProveODE(ds, dc) =>
            val dom = collectPts(kc, dc)
            Some(ProveODE(ds, dom))
          case _ => None
        }
      }

      // Elaborate terms and formulas throughout an ODE proof
      private def elaborateODE(kc: Context, ds: DiffStatement): DiffStatement = {
        ds match {
          case AtomicODEStatement(AtomicODE(xp, e), solFact) => AtomicODEStatement(AtomicODE(xp, kc.elaborateFunctions(e)), solFact)
          case DiffProductStatement(l, r) => DiffProductStatement(elaborateODE(kc, l), elaborateODE(kc, r))
          case DiffGhostStatement(ds) => DiffGhostStatement(elaborateODE(kc, ds))
          case InverseDiffGhostStatement(ds) => InverseDiffGhostStatement(elaborateODE(kc, ds))
        }
      }

      // elaborate terms and formulas in all terms that mention them, Asserts which were handled earlier.
      override def postS(kc: Context, s: Statement): Statement = {
        s match {
          case Assume(pat, f) =>Assume(pat, kc.elaborateFunctions(f))
          // Elaborate all functions that are defined *before* f
          case LetFun(f, args, e: Term) => LetFun(f, args, kc.elaborateFunctions(e))
          case Match(pat, e: Term) => Match(pat, kc.elaborateFunctions(e))
          case While(x, j, s) => While(x, kc.elaborateFunctions(j), s)
          case BoxLoop(s, Some((ihk, ihv))) => BoxLoop(s, Some((ihk, kc.elaborateFunctions(ihv))))
          // dc was elaborated in preS
          case ProveODE(ds, dc) => ProveODE(elaborateODE(kc, ds), dc)
          case Switch(scrut, pats) => Switch(scrut, pats.map({case (x, f: Formula, b) => (x, kc.elaborateFunctions(f), b)}))
          case s => s
        }
      }
    })
    ghostCon = Context.empty.asElaborationContext
    ret
  }
}
