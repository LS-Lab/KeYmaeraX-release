package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.ProofTraversal.TraversalFunction
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.Context._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.UnificationMatch

object SelectorEliminationPass {
  def collectPts(kc: Context, sel: Selector, goal: Formula): List[ProofTerm] = {
    sel match {
        // @TODO: Use different ProofVars/ProofTerms for fact assumptions vs fact assumptions
      case DefaultSelector =>
        val fv = StaticSemantics(goal).fv
        fv.toSet.toList.map(ProofVar)
      case ForwardSelector(pt) => List(pt)
      case PatternSelector(pat) =>
        Context.unify(kc, pat).map({case (x, _) => ProofVar(x)}).toList
    }
  }

  def collectPts(kc: Context, m: Method, goal: Formula): (List[ProofTerm], Method) = {
    m match {
      case Using(use, m) =>
        val useAssms = use.flatMap(collectPts(kc, _, goal))
        val (assms, meth) = collectPts(kc, m, goal)
        (useAssms ++ assms, meth)
      case _: ByProof | _: RCF | _: Auto | _: Prop => (List(), m)
    }
  }

  def collectPts(kc: Context, dc: DomainStatement): (List[Note], DomainStatement) = {
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
            val (id, c: Context) = (Context.fresh(kc), Context.ghost(kc, True))
            (c, Note(id, pt) :: acc)})
        val noteSels = notes.map({case Note(id, _, _) => ForwardSelector(ProofVar(id))})
        val finalMeth = Using(noteSels, meth)
        (notes, DomAssert(x, f, finalMeth))
      case _: DomWeak | _: DomAssume | _: DomModify => (List(), dc)
    }
  }

  def apply(s: Statement): Statement = {
    ProofTraversal.traverse(Context.empty, s, new TraversalFunction {
      override def preS(kc: Context, sel: Statement): Option[Statement] = {
        sel match {
          case Assert(e, f, m) =>
            val (pts, meth) = collectPts(kc, m, f)
            val (_, notes: List[Note]) =
              pts.foldLeft[(Context, List[Note])]((kc, List[Note]()))({case ((kc, acc: List[Note]), pt) =>
                // TODO: Hack: context doesnt say what conclusion is
                val (id, c: Context) = (Context.fresh(kc), Context.ghost(kc, True))
                (c, Note(id, pt) :: acc)})
            val noteSels = notes.map({case Note(id, _, _) => ForwardSelector(ProofVar(id))})
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
