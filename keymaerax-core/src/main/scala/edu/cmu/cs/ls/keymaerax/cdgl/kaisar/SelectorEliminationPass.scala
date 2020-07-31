package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.ProofTraversal.TraversalFunction
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.Context._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.UnificationMatch

object SelectorEliminationPass {
  private def freeVarsPT(con: Context, pt: ProofTerm): Set[Variable] = {
    pt match {
      case ProgramVar(x) => Set(x)
      case ProofVar(x) => StaticSemantics(Context.get(con, x).get).fv.toSet
      case ProofInstance(e: Formula) => StaticSemantics(e).fv.toSet
      case ProofInstance(e: Program) => StaticSemantics(e).fv.toSet
      case ProofInstance(e: Term) => StaticSemantics(e).toSet
      case ProofApp(m, n) => freeVarsPT(con, m) ++ freeVarsPT(con, n)
    }
  }

  // The parser uses the same syntax for fact variables and for program variable proof terms which refer to all assignments
  // of a given variable
  def disambiguate(kc: Context, pt: ProofTerm): ProofTerm = {
    pt match {
      case ProofVar(x) =>
        // If x is not found as a fact variable, assume it's a program variable
        Context.get(kc, x) match {
          case Some(_) => pt
          case None => ProgramVar(x)
        }
      case ProofApp(m, n) => ProofApp(disambiguate(kc, m), disambiguate(kc, n))
      case ProofInstance(e) => ProofInstance(e)
      case ProgramVar(x) => throw new Exception("Didn't expect program variable proof term in selector elimination pass.")
    }
  }

  def collectPts(kc: Context, sel: Selector, goal: Formula): List[ProofTerm] = {
    sel match {
      case DefaultSelector =>
        val fv = StaticSemantics(goal).fv
        fv.toSet.toList.map(ProgramVar)
      case ForwardSelector(pt) => List(disambiguate(kc, pt))
      case PatternSelector(pat) =>
        Context.unify(kc, pat).map({case (x, _) => ProofVar(x)}).toList
    }
  }

  def collectPts(kc: Context, m: Method, goal: Formula): (List[ProofTerm], Method) = {
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
