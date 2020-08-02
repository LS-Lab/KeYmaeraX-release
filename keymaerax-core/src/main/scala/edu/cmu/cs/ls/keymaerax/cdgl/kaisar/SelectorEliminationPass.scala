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
import edu.cmu.cs.ls.keymaerax.core._

object SelectorEliminationPass {
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

  /** @return list of proof terms selected by selector. */
  private def collectPts(kc: Context, sel: Selector, goal: Formula): List[ProofTerm] = {
    sel match {
      case DefaultSelector =>
        val fv = StaticSemantics(goal).fv
        fv.toSet.toList.map(ProgramVar)
      case ForwardSelector(pt) => List(disambiguate(kc, pt))
      case PatternSelector(pat) =>
        kc.unify(pat).map({case (x, _) => ProofVar(x)}).toList
    }
  }

  /** @return list of assumption proof term for method, paired with underlying method  */
  private def collectPts(kc: Context, m: Method, goal: Formula): (List[ProofTerm], Method) = {
    m match {
      case Using(use, m) =>
        val useAssms = use.flatMap(collectPts(kc, _, goal))
        val (assms, meth) = collectPts(kc, m, goal)
        val combineAssms = useAssms ++ assms
        val allFree = combineAssms.map(freeVarsPT(kc, _)).reduce(_ ++ _)
        val freePt = allFree.toList.map(ProgramVar)
        val dedupAssms = freePt ++ combineAssms.filter(!_.isInstanceOf[ProgramVar])
        (dedupAssms, meth)
      case _: ByProof | _: RCF | _: Auto | _: Prop => (List(), m)
    }
  }

  /** @return list of note statements for proof assumptions, paired with elaborated statement. */
  private def collectPts(kc: Context, dc: DomainStatement): (List[Note], DomainStatement) = {
    dc match {
      case DomAnd(l, r) =>
        val (ptsL, dsL) = collectPts(kc, l)
        val (ptsR, dsR) = collectPts(kc, r)
        (ptsL ++ ptsR, DomAnd(dsL, dsR))
      case DomAssert(x, f, m) =>
        val (pts, meth) = collectPts(kc, m, f)
        val (_, notes: List[Note]) =
          pts.foldLeft[(Context, List[Note])]((kc, List[Note]()))({case ((kc, acc: List[Note]), pt) =>
            // TODO: Hack: context doesnt say what conclusion is
            val (id, c: Context) = (kc.fresh(), kc.ghost(True))
            (c, Note(id, pt) :: acc)})
        val noteSels = notes.map({case Note(id, _, _) => ForwardSelector(ProofVar(id))})
        val finalMeth = Using(noteSels, meth)
        (notes, DomAssert(x, f, finalMeth))
      case _: DomWeak | _: DomAssume | _: DomModify => (List(), dc)
    }
  }

  /** @return statement where advanced selectors have been elaborated to simple selectors */
  def apply(s: Statement): Statement = {
    ProofTraversal.traverse(Context.empty, s, new TraversalFunction {
      override def preS(kc: Context, sel: Statement): Option[Statement] = {
        sel match {
          case Assert(e, f, m) =>
            val (pts, meth) = collectPts(kc, m, f)
            val (_, notes: List[Ghost]) =
              pts.foldLeft[(Context, List[Ghost])]((kc, List[Ghost]()))({case ((kc, acc: List[Ghost]), pt) =>
                // TODO: Hack: context doesn't say what conclusion is
                val (id, c: Context) = (kc.fresh(), kc.ghost(True))
                // notes should be ghosts since they did not appear in the user's intended proof/program.
                // proofchecking output after selector elimination should "look like" proofchecking the input
                (c,  Ghost(Note(id, pt)) :: acc)})
            val noteSels = notes.map({case Ghost(Note(id, _, _)) => ForwardSelector(ProofVar(id))})
            val finalMeth = Using(noteSels, meth)
            Some(Block(notes.:+(Assert(e, f, finalMeth))))
          case ProveODE(ds, dc) =>
            val (notes, dom) = collectPts(kc, dc)
            Some(Block(notes.:+(ProveODE(ds, dom))))
          case _ => None
        }
      }
    })
  }
}
