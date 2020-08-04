/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * Visitor pattern for Kaisar proofs, useful for implementing simple compiler passes.
  * Basic context management is performed. The preX functions allow the visitor to optionally modify the statement
  * instead of traversing it recursively, while the postX functions allow modifying the result of a recursive call.
  * @see [[edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.ExpressionTraversalFunction]]
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof._
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.Context._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.FTPG

object ProofTraversal {
  /** Interface for modifying some or all syntactic classes of Kaisar proofs. While Kaisar has many syntactic classes,
    * all follow the same pattern: 1) optionally modify the input of a recursive call. If you choose to do so, that
    * recursive call ends. Else, modify the result of applying the inductive hypotheses.
    *
    * If your desired output is of a different type, have your traversal function mutate a variable.
    * */
  trait TraversalFunction {
    /* pre-modify statement */
    def preS(kc: Context, s: Statement): Option[Statement] = None
    /* post-modify statement */
    def postS(kc: Context, s: Statement): Statement = s
    /* pre-modify ODE domain statement */
    def preDomS(kc: Context, s: DomainStatement): Option[DomainStatement] = None
    /* post-modify ODE domain statement */
    def postDomS(kc: Context, s: DomainStatement):  DomainStatement = s
    /* pre-modify ODE differential statement */
    def preDiffS(kc: Context, s: DiffStatement): Option[DiffStatement] = None
    /* post-modify ODE differential statement */
    def postDiffS(kc: Context, s: DiffStatement): DiffStatement = s
    /* pre-modify fact selector for proof step */
    def preSel(kc: Context, s: Selector): Option[Selector] = None
    /* post-modify fact selector for proof step */
    def postSel(kc: Context, s: Selector): Selector  = s
    /* pre-modify proof step method */
    def preM(kc: Context, s: Method): Option[Method] = None
    /* post-modify proof step method */
    def postM(kc: Context, s: Method): Method = s
    /* pre-modify forward proof term */
    def prePT(kc: Context, s: ProofTerm): Option[ProofTerm] = None
    /* post-modify forward proof term */
    def postPT(kc: Context, s: ProofTerm): ProofTerm = s
    /* pre-modify assignment pattern (pattern for LHS of an assignment statement) */
    def preAP(kc: Context, s: AsgnPat): Option[AsgnPat] = None
    /* post-modify assignment pattern (pattern for LHS of an assignment statement) */
    def postAP(kc: Context, s: AsgnPat): AsgnPat  = s
  }

  /* Traverse statement */
  def traverse(kc: Context, s: Statement, tf: TraversalFunction): Statement = {
    tf.preS(kc, s) match {
      case Some(st) => st
      case None =>
        val mid =
        s match {
          case BoxLoopProgress(bl, prog) => BoxLoopProgress(bl, traverse(kc, prog, tf))
          case Phi(asgns) => Phi(traverse(kc, asgns, tf))
          case Was(now: Statement, was: Statement) =>
            Was(traverse(kc, now, tf), was)
          case Block(ss) =>
            val (conFinal, revSS) = ss.foldLeft[(Context, List[Statement])](kc, List()){case ((con, acc), s) =>
              (con.:+(s), traverse(con, s, tf) :: acc)
            }
            Block(revSS.reverse)
          case Switch(sel, pats) =>
            Switch(sel, pats.map({case (v, pat, s) => (v, pat, (traverse(kc, s, tf)))}))
          case BoxChoice(left, right) =>
            BoxChoice(traverse(kc, left, tf), traverse(kc, right, tf))
          case While(x, j, ss) =>
            While(x, j, traverse(kc, ss, tf))
          case BoxLoop(s, ih) =>
            BoxLoop(traverse(kc, s, tf), ih)
          case Ghost(ss) =>
            Ghost(traverse(kc, ss, tf))
          case InverseGhost(ss) =>
            InverseGhost(traverse(kc, ss, tf))
          case ProveODE(ds, dc) =>
            ProveODE(traverse(kc, ds, tf), traverse(kc, dc, tf))
          case Assert(x, f, child) =>
            Assert(x, f, traverse(kc, child, tf))
          case Note(x, pt, ann) =>
            Note(x, traverse(kc, pt, tf), ann)
          case Modify(pat, rhs) => Modify(traverse(kc, pat, tf), rhs)
          case _: PrintGoal | _: Assume | _: Label | _: LetFun | _: Match | _: Triv => s
        }
        tf.postS(kc, mid)
    }
  }

  /** traverse a differential statement */
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

  /** traverse a domain statement */
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

  /** traverse a forward proof term */
  def traverse(kc: Context, pt: ProofTerm, tf: TraversalFunction): ProofTerm = {
    tf.prePT(kc, pt) match {
      case Some(pt) => pt
      case None =>
        val mid = pt match {
          case ProgramVar(x) => ProgramVar(x)
          case ProofVar(x: Ident) => ProofVar(x)
          case ProofInstance(e) => ProofInstance(e)
          case ProofApp(m, n) => ProofApp(traverse(kc, m, tf), traverse(kc, m, tf))
        }
        tf.postPT(kc, mid)
    }
  }

  /** traverse a proof step method */
  def traverse(kc: Context, m: Method, tf: TraversalFunction): Method = {
    tf.preM(kc, m) match {
      case Some(m) => m
      case None =>
        val mid = m match {
          case _ : RCF | _ : Auto | _ : Prop => m
          case Using(uses, m) => Using(uses.map(traverse(kc, _, tf)), traverse(kc, m, tf))
          case ByProof(ss) => ByProof(ss.map(traverse(kc, _, tf)))
        }
        tf.postM(kc, mid)
    }
  }

  /** Traverse a fact selector */
  def traverse(kc: Context, s: Selector, tf: TraversalFunction): Selector = {
    tf.preSel(kc, s) match {
      case Some(sel) => sel
      case None =>
        val mid = s match {
          case ForwardSelector(pt) => ForwardSelector(traverse(kc, pt, tf))
          case PatternSelector(e) => PatternSelector(e)
          case DefaultSelector => DefaultSelector
        }
        tf.postSel(kc, mid)
    }
  }

  /** Traverse an assignment pattern. */
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