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
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.ASTNode._
import edu.cmu.cs.ls.keymaerax.core._

object ProofTraversal {
  /** Interface for modifying some or all syntactic classes of Kaisar proofs. While Kaisar has many syntactic classes,
    * all follow the same pattern: 1) optionally modify the input of a recursive call. If you choose to do so, that
    * recursive call ends. Else, modify the result of applying the inductive hypotheses.
    * In each case, the context is available in two forms: raw and elaborated (i.e., containing results of past recursive calls).
    *
    * If your desired output is of a different type, have your traversal function mutate a variable.
    * */
  trait TraversalFunction {
    /* pre-modify statement */
    def preS(kc: Context, kce: Context, s: Statement): Option[Statement] = None
    /* post-modify statement */
    def postS(kc: Context, kce: Context, s: Statement): Statement = s
    /* pre-modify ODE domain statement */
    def preDomS(kc: Context, kce: Context, s: DomainStatement): Option[DomainStatement] = None
    /* post-modify ODE domain statement */
    def postDomS(kc: Context, kce: Context, s: DomainStatement):  DomainStatement = s
    /* pre-modify ODE differential statement */
    def preDiffS(kc: Context, kce: Context, s: DiffStatement): Option[DiffStatement] = None
    /* post-modify ODE differential statement */
    def postDiffS(kc: Context, kce: Context, s: DiffStatement): DiffStatement = s
    /* pre-modify fact selector for proof step */
    def preSel(kc: Context, kce: Context, s: Selector): Option[Selector] = None
    /* post-modify fact selector for proof step */
    def postSel(kc: Context, kce: Context, s: Selector): Selector  = s
    /* pre-modify proof step method */
    def preM(kc: Context, kce: Context, s: Method): Option[Method] = None
    /* post-modify proof step method */
    def postM(kc: Context, kce: Context, s: Method): Method = s
    /* pre-modify forward proof term */
    def prePT(kc: Context, kce: Context, s: ProofTerm): Option[ProofTerm] = None
    /* post-modify forward proof term */
    def postPT(kc: Context, kce: Context, s: ProofTerm): ProofTerm = s
    /* pre-modify assignment pattern (pattern for LHS of an assignment statement) */
    //def preAP(kc: Context, s: AsgnPat): Option[AsgnPat] = None
    /* post-modify assignment pattern (pattern for LHS of an assignment statement) */
    //def postAP(kc: Context, s: AsgnPat): AsgnPat  = s
  }

  /* Traverse statement */
  def traverse(kc: Context, kce: Context, s: Statement, tf: TraversalFunction): Statement = {
    tf.preS(kc, kce, s) match {
      case Some(st) => locate(st, s)
      case None =>
        val mid =
        s match {
          case SwitchProgress(switch, onBranch, progress) => SwitchProgress(switch, onBranch, traverse(kc, kce, progress, tf))
          case BoxChoiceProgress(bc, onBranch, progress) => BoxChoiceProgress(bc, onBranch, traverse(kc, kce, progress, tf))
          case BoxLoopProgress(bl, prog) => BoxLoopProgress(bl, traverse(kc, kce, prog, tf))
          case WhileProgress(wh, prog) => WhileProgress(wh, traverse(kc, kce, prog, tf))
          case ForProgress(fr, prog) => ForProgress(fr, traverse(kc, kce, prog, tf))
          case Phi(asgns) => Phi(traverse(kc, kce, asgns, tf))
          case Was(now: Statement, was: Statement) =>
            Was(traverse(kc, kce, now, tf), was)
          case Block(ss) =>
            val (conFinal, revSS) = ss.foldLeft[((Context, Context), List[Statement])]((kc, kce), List()){case (((con, cone), acc), s) =>
              val se = traverse(con, cone, s, tf)
              ((con.:+(s), cone.:+(se)), se :: acc)
            }
            Block(revSS.reverse)
          case switch@Switch(sel, pats) =>
            Switch(sel, pats.zipWithIndex.map({case ((v, pat: Formula, s), i) =>
              (v, pat, (traverse(kc.:+(SwitchProgress(switch, i, Triv())), kce.:+(SwitchProgress(switch, i, Triv())), s, tf)))}))
          case bc@BoxChoice(left, right) =>
            val (conL, conR) = (kc.:+(BoxChoiceProgress(bc, 0, Triv())), kc.:+(BoxChoiceProgress(bc, 1, Triv())))
            val (coneL, coneR) = (kce.:+(BoxChoiceProgress(bc, 0, Triv())), kce.:+(BoxChoiceProgress(bc, 1, Triv())))
            BoxChoice(traverse(conL, coneL, left, tf), traverse(conR, coneR, right, tf))
          case While(x, j, ss) =>
            While(x, j, traverse(kc, kce, ss, tf))
          case fr@For(metX, metF, metIncr, conv, guard, body, guardEps) =>
            val grd: Assume = traverse(kc, kce, guard, tf).asInstanceOf[Assume]
            val cnv: Option[Assert] = conv.map(as => traverse(kc, kce, as, tf).asInstanceOf[Assert])
            val prog = (ForProgress(fr, Triv()))
            // @TODO: if progress helps, use it in all constructors of traverse
            For(metX, metF, metIncr, cnv, grd, traverse(kc.:+(prog), kce.:+(prog), body, tf), guardEps)
          case BoxLoop(s, ih) =>
            BoxLoop(traverse(kc, kce, s, tf), ih)
          case Ghost(ss) =>
            Ghost(traverse(kc.withGhost, kce.withGhost, ss, tf))
          case InverseGhost(ss) =>
            InverseGhost(traverse(kc.withInverseGhost, kce.withInverseGhost, ss, tf))
          case ProveODE(ds, dc) =>
            ProveODE(traverse(kc, kce, ds, tf), traverse(kc, kce, dc, tf))
          case Assert(x, f, child) =>
            Assert(x, f, traverse(kc, kce, child, tf))
          case Note(x, pt, ann) =>
            Note(x, traverse(kc, kce, pt, tf), ann)
          case _: Modify | _: PrintGoal | _: Assume | _: Label | _: LetSym | _: Match | _: Triv | _: Pragma | _: Comment => s
        }
        locate(tf.postS(kc, kce, locate(mid, s)), s)
    }
  }

  /** traverse a differential statement */
  def traverse(kc: Context, kce: Context, ds: DiffStatement, tf: TraversalFunction): DiffStatement = {
    tf.preDiffS(kc, kce, ds) match {
      case Some(theDs) => locate(theDs, ds)
      case None =>
        val mid = ds match {
          case AtomicODEStatement(dp, ident) => AtomicODEStatement(dp, ident)
          case DiffProductStatement(l, r) => DiffProductStatement(traverse(kc, kce, l, tf), traverse(kc, kce, r, tf))
          case DiffGhostStatement(ds) => DiffGhostStatement(traverse(kc.withGhost, kce.withGhost, ds, tf))
          case InverseDiffGhostStatement(ds) => InverseDiffGhostStatement(traverse(kc.withInverseGhost, kce.withInverseGhost, ds, tf))
        }
        locate(tf.postDiffS(kc, kce, locate(mid, ds)), ds)
    }
  }

  /** traverse a domain statement */
  def traverse(kc: Context, kce: Context, ds: DomainStatement, tf: TraversalFunction): DomainStatement = {
    tf.preDomS(kc, kce, ds) match {
      case Some(theDs) => locate(theDs, ds)
      case None =>
        val mid =
          ds match {
            case DomAssume(x, f) => DomAssume(x, f)
            case DomAssert(x, f, child) => DomAssert(x, f, traverse(kc, kce, child, tf))
            case DomWeak(dc) => DomWeak(traverse(kc.withInverseGhost, kce.withInverseGhost, dc, tf))
            case DomModify(id, x, f) => DomModify(id, x, f)
            case DomAnd(l, r) => DomAnd(traverse(kc, kce, l, tf), traverse(kc, kce, r, tf))
          }
        locate(tf.postDomS(kc, kce, locate(mid, ds)), ds)
    }
  }

  /** traverse a forward proof term */
  def traverse(kc: Context, kce: Context, pt: ProofTerm, tf: TraversalFunction): ProofTerm = {
    tf.prePT(kc, kce, pt) match {
      case Some(outPt) => locate(outPt, pt)
      case None =>
        val mid = pt match {
          case ProgramVar(x) => ProgramVar(x)
          case ProgramAssignments(x, ssa) => ProgramAssignments(x, ssa)
          case ProofVar(x: Ident) => ProofVar(x)
          case ProofInstance(e) => ProofInstance(e)
          case ProofApp(m, n) => ProofApp(traverse(kc, kce, m, tf), traverse(kc, kce, n, tf))
        }
        locate(tf.postPT(kc, kce, locate(mid, pt)), pt)
    }
  }

  /** traverse a proof step method */
  def traverse(kc: Context, kce: Context, m: Method, tf: TraversalFunction): Method = {
    tf.preM(kc, kce, m) match {
      case Some(outM) => locate(outM, m)
      case None =>
        val mid = m match {
          case _ : RCF | _ : Auto | _ : Prop | _: Triv | _: Solution | _: DiffInduction | _: Exhaustive | _: Hypothesis | _: GuardDone => m
          case Using(uses, m) => Using(uses.map(traverse(kc, kce, _, tf)), traverse(kc, kce, m, tf))
          case ByProof(ss) => ByProof(ss.map(traverse(kc, kce, _, tf)))
        }
        locate(tf.postM(kc, kce, locate(mid, m)), m)
    }
  }

  /** Traverse a fact selector */
  def traverse(kc: Context, kce: Context, s: Selector, tf: TraversalFunction): Selector = {
    tf.preSel(kc, kce, s) match {
      case Some(outSel) => locate(outSel, s)
      case None =>
        val mid = s match {
          case ForwardSelector(pt) => ForwardSelector(traverse(kc, kce, pt, tf))
          case PatternSelector(e) => PatternSelector(e)
          case DefaultSelector => DefaultSelector
          case DefaultAssignmentSelector => DefaultAssignmentSelector
        }
        locate(tf.postSel(kc, kce, locate(mid, s)), s)
    }
  }
}