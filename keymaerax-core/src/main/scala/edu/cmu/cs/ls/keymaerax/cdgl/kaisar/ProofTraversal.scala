package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof._
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.Context._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.FTPG

object ProofTraversal {
  trait TraversalFunction {
    def preS(kc: Context, s: Statement): Option[Statement] = None
    def postS(kc: Context, s: Statement): Statement = s
    def preDomS(kc: Context, s: DomainStatement): Option[DomainStatement] = None
    def postDomS(kc: Context, s: DomainStatement):  DomainStatement = s
    def preDiffS(kc: Context, s: DiffStatement): Option[DiffStatement] = None
    def postDiffS(kc: Context, s: DiffStatement): DiffStatement = s
    def preSel(kc: Context, s: Selector): Option[Selector] = None
    def postSel(kc: Context, s: Selector):Selector  = s
    def preM(kc: Context, s: Method): Option[Method] = None
    def postM(kc: Context, s: Method): Method = s
    def prePT(kc: Context, s: ProofTerm): Option[ProofTerm] = None
    def postPT(kc: Context, s: ProofTerm): ProofTerm = s
    def preAP(kc: Context, s: AsgnPat): Option[AsgnPat] = None
    def postAP(kc: Context, s: AsgnPat): AsgnPat  = s
  }

  def traverse(kc: Context, s: Statement, tf: TraversalFunction): Statement = {
    tf.preS(kc, s) match {
      case Some(st) => st
      case None =>
        val mid =
        s match {
          case Was(now: Statement, was: Statement) =>
            Was(traverse(kc, now, tf), was)
          case Block(ss) =>
            val (conFinal, revSS) = ss.foldLeft[(Context, List[Statement])](kc, List()){case ((con, acc), s) =>
              (Context.:+(con, s), traverse(con, s, tf) :: acc)
            }
            Block(revSS.reverse)
          case Switch(sel, pats) =>
            Switch(sel, pats.map({case (v, pat, s) => (v, pat, (traverse(kc, s, tf)))}))
          case BoxChoice(left, right) =>
            BoxChoice(traverse(kc, left, tf), traverse(kc, right, tf))
          case While(x, j, ss) =>
            While(x, j, traverse(kc, ss, tf))
          case BoxLoop(s) =>
            BoxLoop(traverse(kc, s, tf))
          case Ghost(ss) =>
            Ghost(traverse(kc, ss, tf))
          case InverseGhost(ss) =>
            InverseGhost(traverse(kc, ss, tf))
          case ProveODE(ds, dc) =>
            ProveODE(traverse(kc, ds, tf), traverse(kc, dc, tf))
          case Assert(x, f, child) =>
            Assert(x, f, traverse(kc, child, tf))
          case e: PrintGoal => e
          case e: Assume => e
          case e: Modify => e
          case e: Label => e
        }
        tf.postS(kc, mid)
    }
  }

  def traverse(kc: Context, ds: DiffStatement, tf: TraversalFunction): DiffStatement = {
    tf.preDiffS(kc, ds) match {
      case Some(ds) => ds
      case None =>
        val mid = ds match {
          case AtomicODEStatement(dp) => AtomicODEStatement(dp)
          case DiffProductStatement(l, r) => DiffProductStatement(traverse(kc, l, tf), traverse(kc, r, tf))
          case DiffGhostStatement(ds) => DiffGhostStatement(traverse(kc, ds, tf))
          case InverseDiffGhostStatement(ds) => InverseDiffGhostStatement(traverse(kc, ds, tf))
        }
        tf.postDiffS(kc, mid)
    }
  }

  def traverse(kc: Context, ds: DomainStatement, tf: TraversalFunction): DomainStatement = {
    tf.preDomS(kc, ds) match {
      case Some(ds) => ds
      case None =>
        val mid =
          ds match {
            case DomAssume(x, f) => DomAssume(x, f)
            case DomAssert(x, f, child) => DomAssert(x, f, traverse(kc, child, tf))
            case DomWeak(dc) => DomWeak(traverse(kc, dc, tf))
            case DomModify(x, hp) => DomModify(traverse(kc, x, tf), hp)
            case DomAnd(l, r) => DomAnd(traverse(kc, l, tf), traverse(kc, r, tf))
          }
        tf.postDomS(kc, mid)
    }
  }

  def traverse(kc: Context, pt: ProofTerm, tf: TraversalFunction): ProofTerm = {
    tf.prePT(kc, pt) match {
      case Some(pt) => pt
      case None =>
        val mid = pt match {
          case ProofVar(x: Ident) => ProofVar(x)
          case ProofInstance(e) => ProofInstance(e)
          case ProofApp(m, n) => ProofApp(traverse(kc, m, tf), traverse(kc, m, tf))
        }
        tf.postPT(kc, mid)
    }
  }

  def traverse(kc: Context, m: Method, tf: TraversalFunction): Method = {
    tf.preM(kc, m) match {
      case Some(m) => m
      case None =>
        val mid = m match {
          case _ : RCF | _ : Auto | _ : Prop => m
          case Using(uses, m) => Using(uses.map(traverse(kc, _, tf)), traverse(kc, m, tf))
          case ByProof(pf) => ByProof(Proof(pf.ss.map(traverse(kc, _, tf))))
        }
        tf.postM(kc, mid)
    }
  }

  def traverse(kc: Context, s: Selector, tf: TraversalFunction): Selector = {
    tf.preSel(kc, s) match {
      case Some(sel) => sel
      case None =>
        val mid = s match {
          case ForwardSelector(pt) => ForwardSelector(traverse(kc, pt, tf))
          case PatternSelector(e) => PatternSelector(e)
        }
        tf.postSel(kc, mid)
    }
  }

  def traverse(kc: Context, ap: AsgnPat, tf: TraversalFunction): AsgnPat = {
    tf.preAP(kc, ap) match {
      case Some(ap) => ap
      case None =>
        val mid = ap match {
          case TuplePat(aps) => TuplePat(aps.map(traverse(kc, _, tf)))
          case _ : WildPat | _ : NoPat | _ : VarPat => ap
        }
        tf.postAP(kc, mid)
    }
  }
}