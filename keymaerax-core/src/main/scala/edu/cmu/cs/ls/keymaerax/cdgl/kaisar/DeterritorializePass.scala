/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * Remove line labels by rewriting
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.DeterritorializePass.TimeTable
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.{Ident, LabelDef, LabelRef, TimeIdent, TransformationException}
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.ProofTraversal.TraversalFunction
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.SubstitutionHelper

object DeterritorializePass {
  val DEBUG: Boolean = false
  type TimeTable = Map[TimeIdent, (Snapshot, Context, LabelDef)]

  /** Translate away labels in statement, which must be in SSA form. */
  def apply(s: Statement): Statement = {
    var times: TimeTable = Map()
    // Collect snapshot information of all labels. This information was populated during SSA.
    val collectSnapshots = new TraversalFunction {
      override def postS(kc: Context, s: Statement): Statement = {
        s match {
          case Label(ld, Some(snap: Snapshot)) => times = times.+(ld.label -> (snap, kc, ld))
          case Label(ld, None) => throw TransformationException("Expected label statement to contain snapshot", node = s)
          case _ => ()
        }
        s
      }
    }
    ProofTraversal.traverse(Context.empty, s, collectSnapshots)
    new DeterritorializePass(times).apply(s)
  }
}

case class DeterritorializePass(tt: TimeTable) {
  /** reindex f based on snapshot, except some set of variables */
  private def reindex(snapshot: Snapshot, f: Term, except: Set[Ident]): Term = {
    val reindexOne: Term => Option[Term] = ({case BaseVariable(name, _, sort) =>
      // rename program variables but not function arguments
      // Insert "stable" function to indicate that proofchecking should never change the index on this variable -
      // we already figured out the right index.
      if (!except.contains(Variable(name))) {
        Some(FuncOf(KaisarProof.stable, BaseVariable(name, snapshot.get(name), sort)))
      } else None
    case _ => None
    })
    SubstitutionHelper.replacesFree(f)(reindexOne)
  }


  /** Eliminate [[stable]] marker in terms */
  private def destabilize(f: Term): Term = SubstitutionHelper.replacesFree(f)(f => KaisarProof.getStable(f))
  /** Return a term equivalent to [[f@lr]] which only uses terms that are defined at the beginning of [[conDiff]] */
  private def rewind(conDiff: Context, labelSnap: Snapshot, lr: LabelRef, f: Term, except: Set[Ident], node: ASTNode): Term = {
    val (_, _, ld) = tt(lr.label)
    if (lr.args.length != ld.args.length) throw TransformationException(s"Label ${ld.label} referenced with arguments ${lr.args} but expects ${ld.args.length} arguments", node = node)
    val argMap = ld.args.zip(lr.args).foldLeft[Map[Variable, Term]](Map())({case (acc, (k, v)) => acc.+(k -> v)})
    val termAcc = destabilize(reindex(labelSnap, f, except))
    if (DeterritorializePass.DEBUG) println(s"Rewinding from ${termAcc.prettyString}")
    def fail = throw TransformationException(s"Value of $f@$lr is ill-defined", node = node)
    def traverse(s: Statement, f: Term): Term = {
      s match {
        case mod: Modify =>
          mod.mods.foldRight[Term](f){
            case ((x, Some(rhs)), acc) =>
              if (DeterritorializePass.DEBUG) println(s"Replace $x = $rhs in $acc")
              val res = SubstitutionHelper.replaceFree(acc)(x, rhs)
              if (DeterritorializePass.DEBUG) println(s"Replaced to: $res")
              res
            case ((x, None), acc) if argMap.contains(x) =>
              if (DeterritorializePass.DEBUG) println(s"Replace $x := * by ${argMap(x)} in $acc")
              val res = SubstitutionHelper.replaceFree(acc)(x, argMap(x))
              if (DeterritorializePass.DEBUG) println(s"Replaced to: $res")
              res
            case ((x, None), acc) if !argMap.contains(x) =>
              throw TransformationException(s"Cannot determine value of $f@$lr because variable $x is under-defined. " +
              s"To fix this, add a parameter to label ${lr.label}, e.g. ${LabelDef(ld.label, ld.args :+ x)}", node = node)}
        case proveODE@ProveODE(ds, dc) if proveODE.hasTrueSolution =>
          // solution RHS has label arguments pre-applied
          val solMap = proveODE.solutions.get.toMap.map({case (x, t) => (x, SubstitutionHelper.replacesFree(t)({case x: BaseVariable => argMap.get(x) case _ => None}))})
          val fullMap = argMap.foldLeft[Map[Variable, Term]](solMap)({case (acc, (k, v)) => acc.+(k -> v)})
          if (DeterritorializePass.DEBUG) println(s"Replacing solutions $fullMap in $f")
          val res = SubstitutionHelper.replacesFree(f)({case x: BaseVariable => fullMap.get(x) case _ => None})
          if (DeterritorializePass.DEBUG) println(s"Replacing to: $res")
          res
        case Block(ss) => ss.foldRight[Term](f)(traverse)
        case BoxChoice(l, r) =>
          // Note: This can lead to surprising behavior, this will allow a user to prove some p(x@l) and then
          // be disappointed that p(x@l) is a weaker statement than they had hoped.
          // If at most one branch binds the free variables of f, use that branch, else ill-defined
          val (ll, rr) = (traverse(l, f), traverse(r, f))
          if (ll == f) rr
          else if (rr == f) ll
          else fail
        case Phi(asgns) => traverse(asgns, f)
        case BoxLoop(s, ih) =>
          val ff = traverse(s, f)
          if (f == ff) f
          else
            throw TransformationException(s"Value of $f@$lr is under-defined because it depends on duration of loop ${BoxLoop(s, ih)}. " +
              s"Change the loop body or change $f so that $f does not mention any variables modified by the loop.", node = node)
        case _ => f
      }
    }
    val res = traverse(conDiff.s, termAcc)
    if (DeterritorializePass.DEBUG) println("Replaced to: " + res)
    res
  }

  /** Reindex [[f]] according to [[label]] if it is legal to do so. */
  private def renameAdmissible(kc: Context, label: LabelRef, f: Term, except: Set[Ident], node: ASTNode): Option[Term] = {
    tt.get(label.label) match {
      case None => throw TransformationException(s"Undefined line label: $label", node = node)
      case Some((labelSnap, labelCon, _labelDef)) =>
        // @TODO: This is slow
        val hereSnap = Snapshot.ofContext(kc)
        if (!(labelSnap <= hereSnap)) {
          val conDiff = labelCon -- kc
          val res = rewind(conDiff, labelSnap, label, f, except, node)
          Some(res)
        } else
          Some(reindex(labelSnap, f, except))
    }
  }

  // Rename individual atomic terms
  private def transHelper(kc: Context, local: Set[Ident], node: ASTNode = Triv()): Term => Option[Term] = (f: Term) =>
    KaisarProof.getAt(f, node) match {
      case Some((e, label)) => renameAdmissible(kc, label, e, local, node)
      case None => None
    }

  /** Translate a term [[t]], but leave parameters [[localVars]] intact */
  private def translate(kc: Context, t: Term, localVars: List[Ident] = Nil, node: ASTNode = Triv()): Term = {
    SubstitutionHelper.replacesFree(t)(transHelper(kc, localVars.toSet, node))
  }

  /** Translate a formula [[fml]] */
  private def translate(kc: Context, fml: Formula, node: ASTNode): Formula = {
    SubstitutionHelper.replacesFree(fml)(transHelper(kc, Set(), node))
  }

  /** Translate an expression [[e]] */
  private def translate(kc: Context, e: Expression, node: ASTNode): Expression = {
    SubstitutionHelper.replacesFree(e)(transHelper(kc, Set(), node))
  }

  /** Translate an expression pattern [[pat]], where already-bound variables are not renamed */
  private def translatePat(kc: Context, pat: Term, node: ASTNode): Term = {
    val boundVars = VariableSets(kc).boundVars
    SubstitutionHelper.replacesFree(pat)(transHelper(kc, boundVars, node))
  }

  private def translatePat(kc: Context, pat: Formula, node: ASTNode): Formula = {
    val boundVars = VariableSets(kc).boundVars
    SubstitutionHelper.replacesFree(pat)(transHelper(kc, boundVars, node))
  }

  /** Translate away label references in a statement which must be in SSA form. */
  def apply(s: Statement): Statement = {
    val pass = new TraversalFunction {
      /* delete labels now. We already got all the info we need from them in [[tt]] */
      override def preS(kc: Context, s: Statement): Option[Statement] = {
        s match {
          case _: Label => Some(Ghost(Triv()))
          case _ => None
        }
      }

      // translate named references in atoms
      override def postPT(kc: Context, pt: ProofTerm): ProofTerm = {
        pt match {
          case ProofInstance(e) => ProofInstance(translate(kc, e, pt))
          case _ => pt
        }
      }

      override def postSel(kc: Context, sel: Selector): Selector = {
        sel match {
          case PatternSelector(e) => PatternSelector(translatePat(kc, e, sel))
          case _ => sel
        }
      }

      override def postDomS(kc: Context, ds: DomainStatement): DomainStatement = {
        ds match {
          case DomAssume(x, f) =>  DomAssume(x, translate(kc, f, ds))
          case DomAssert(x, f, child) => DomAssert(x, translate(kc, f, ds), child)
          case DomModify(x, f) => DomModify(x, translate(kc, f, node = ds))
          case _: DomAnd | _: DomWeak => ds
        }
      }

      override def postDiffS(kc: Context, ds: DiffStatement): DiffStatement = {
        ds match {
          case AtomicODEStatement(dp, ident) => AtomicODEStatement(AtomicODE(dp.xp, translate(kc, dp.e, node = ds)), ident)
          case _ => ds
        }
      }

      // translate named references in atoms
      override def postS(kc: Context, s: Statement): Statement = {
        s match {
          case Assume(pat, f) => Assume(pat, translate(kc, f, s))
          case Assert(pat, f, m) => Assert(pat, translate(kc, f, s), m)
          case mod: Modify => Modify(mod.ids, mod.mods.map({case (x, f) => (x, f.map(z => translate(kc, z, Nil)))}))
          case Note(x, proof, Some(annotation)) => Note(x, proof, Some(translate(kc, annotation, s)))
          case LetSym(f, args, e: Term) => LetSym(f, args, translate(kc, e, localVars = args))
          case Match(pat, e) => Match(translatePat(kc, pat, s), translate(kc, e, s))
          case Switch(scrutinee, pats) => Switch(scrutinee, pats.map({case (e1, e2, bs) => (e1, translatePat(kc, e2, s), bs)}))
          case While(x, j, bs) => While(x, translate(kc, j, s), bs)
          // Filter out no-op'd labels
          case BoxChoice(Ghost(Triv()), right) => right
          case BoxChoice(left, Ghost(Triv())) => left
          case Block(ss) => KaisarProof.block(ss.filter({case Ghost(Triv()) => false case _ => true}))
          case s => s
        }
      }
    }
    ProofTraversal.traverse(Context.empty, s, pass)
  }
}