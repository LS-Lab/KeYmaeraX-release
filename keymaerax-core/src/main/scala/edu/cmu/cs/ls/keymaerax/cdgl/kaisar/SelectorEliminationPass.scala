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
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.ElaborationException
import edu.cmu.cs.ls.keymaerax.core._

class SelectorEliminationPass() {
  var ghostCon: Context = Context.empty

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
          case None => ProgramVar(x)
        }
      case ProofApp(m, n) => ProofApp(disambiguate(kc, m), disambiguate(kc, n))
      case ProofInstance(e) => ProofInstance(e)
      case ProgramVar(x) => throw new Exception("Did not expect program variable proof term in selector elimination pass.")
    }
  }

  private def disambiguate(kc: Context, sel: Selector, goal: Formula): List[Selector] = {
    sel match {
      case DefaultSelector =>
        val fv = StaticSemantics(goal).fv
        // @TODO: filter down only to bound variables of context.
        // But filtering is probably very slow.
        val candidates = fv.toSet.toList.map(ProgramVar)
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
        // @TODO: filter down only to bound variables of context.
        // But filtering is probably very slow.
        val candidates = fv.toSet.toList.map(ProgramVar)
        candidates.filter(x => kc.getAssignments(x.x).nonEmpty)
      case ForwardSelector(pt) => List(disambiguate(kc, pt))
      case PatternSelector(pat) =>
        kc.unify(pat).map({case (x, _) => ProofVar(x)}).toList
    }
  }

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
        val combineAssms = useAssms ++ assms
        if(combineAssms.isEmpty && use != List(DefaultSelector))
          throw ElaborationException("Non-default selector should select at least one fact.")
        val allFree = combineAssms.map(freeVarsPT(kc, _)).foldLeft[Set[Variable]](Set())(_ ++ _)
        val freePt = allFree.toList.map(ProgramVar)
        val dedupAssms = freePt ++ combineAssms.filter(!_.isInstanceOf[ProgramVar])
        (dedupAssms, meth)
      case _: ByProof | _: RCF | _: Auto | _: Prop | _: Solution | _: DiffInduction => (List(), m)
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
      case DomAssert(x, f, m) =>
        val meth = disambiguate(kc, m, f)
        DomAssert(x, f, meth)
        /*val notes: List[Note] =
          pts.foldLeft[List[Note]](List[Note]())({case (acc: List[Note], pt) =>
            // TODO: Hack: context doesnt say what conclusion is
            val id = ghostCon.fresh()
            ghostCon = ghostCon.ghost(True)
            Note(id, pt) :: acc})*/
        //val noteSels = notes.map({case Note(id, _, _) => ForwardSelector(ProofVar(id))})
        //val finalMeth = Using(noteSels, meth)
      case _: DomWeak | _: DomAssume | _: DomModify => dc
    }
  }

  /** @return statement where advanced selectors have been elaborated to simple selectors */
  def apply(s: Statement): Statement = {
    ghostCon = Context(s)
    val ret = ProofTraversal.traverse(Context.empty, s, new TraversalFunction {
      override def preS(kc: Context, sel: Statement): Option[Statement] = {
        sel match {
          case Assert(e, f, m) =>
            val (pts, meth) = collectPts(kc, m, f)
            val notes: List[Ghost] =
              pts.foldLeft[List[Ghost]]((List[Ghost]()))({case (acc: List[Ghost], pt) =>
                // TODO: Hack: context doesn't say what conclusion is
                val id = ghostCon.fresh()
                ghostCon = ghostCon.ghost(True)
                // notes should be ghosts since they did not appear in the user's intended proof/program.
                // proofchecking output after selector elimination should "look like" proofchecking the input
                Ghost(Note(id, pt)) :: acc})
            val noteSels = notes.map({case Ghost(Note(id, _, _)) => ForwardSelector(ProofVar(id))})
            val finalMeth = Using(noteSels, meth)
            Some(Block(notes.:+(Assert(e, f, finalMeth))))
          case ProveODE(ds, dc) =>
            val dom = collectPts(kc, dc)
            Some(ProveODE(ds, dom))
          case _ => None
        }
      }
    })
    ghostCon = Context.empty
    ret
  }
}
