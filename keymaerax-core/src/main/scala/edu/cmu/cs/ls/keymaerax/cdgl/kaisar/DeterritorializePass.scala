/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * Remove line labels by rewriting
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.DeterritorializePass.TimeTable
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.{Ident, TimeIdent, TransformationException}
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.ProofTraversal.TraversalFunction
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.SubstitutionHelper

object DeterritorializePass {
  type TimeTable = Map[TimeIdent, (Snapshot, Context)]

  /** Translate away labels in statement, which must be in SSA form. */
  def apply(s: Statement): Statement = {
    var times: TimeTable = Map()
    // Collect snapshot information of all labels. This information was populated during SSA.
    val collectSnapshots = new TraversalFunction {
      override def postS(kc: Context, s: Statement): Statement = {
        s match {
          case Label(lr, Some(snap: Snapshot)) => times = times.+(lr.label -> (snap, kc))
          case Label(lr, None) => throw TransformationException("Expected label statement to contain snapshot")
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


  private def renameAdmissible(kc: Context, label: TimeIdent, f: Term, except: Set[Ident]): Option[Term] = {
    tt.get(label) match {
      case None => throw TransformationException(s"Undefined line label: $label")
      case Some((labelSnap, labelCon)) =>
        // @TODO: This is slow
        val hereSnap = Snapshot.ofContext(kc)
        // @TODO: Implement forward label references
        // @TODO: Check is only correct if different branches a ++ b reuse same indices.
        // For now, only allow label translation if the reference appears after definition.
        // We do not check whether any of the referenced variables have gone out of scope - omitting this check
        // should be sound, but just allows us to reference things that are somewhat useless.
        if (!(labelSnap <= hereSnap)) {
          throw TransformationException(s"Label $label can only must be defined before use")
        }
        Some(reindex(labelSnap, f, except))
    }
  }

  private def transHelper(kc: Context, local: Set[Ident]): Term => Option[Term] = (f: Term) =>
    KaisarProof.getAt(f) match {
      case Some((e, label)) => renameAdmissible(kc, label.label, e, local)
      case None => None
    }

  private def translate(kc: Context, t: Term, localVars: List[Ident] = Nil): Term = {
    SubstitutionHelper.replacesFree(t)(transHelper(kc, localVars.toSet))
  }

  private def translate(kc: Context, fml: Formula): Formula = {
    SubstitutionHelper.replacesFree(fml)(transHelper(kc, Set()))
  }

  private def translate(kc: Context, e: Expression): Expression = {
    SubstitutionHelper.replacesFree(e)(transHelper(kc, Set()))
  }

  private def translatePat(kc: Context, pat: Expression): Expression = {
    val boundVars = VariableSets(kc).boundVars
    SubstitutionHelper.replacesFree(pat)(transHelper(kc, boundVars))
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
          case ProofInstance(e) => ProofInstance(translate(kc, e))
          case _ => pt
        }
      }

      override def postSel(kc: Context, sel: Selector): Selector = {
        sel match {
          case PatternSelector(e) => PatternSelector(translatePat(kc, e))
          case _ => sel
        }
      }

      override def postDomS(kc: Context, ds: DomainStatement): DomainStatement = {
        ds match {
          case DomAssume(x, f) =>  DomAssume(x, translate(kc, f))
          case DomAssert(x, f, child) => DomAssert(x, translate(kc, f), child)
          case DomModify(x, f) => DomModify(x, translate(kc, f))
          case _: DomAnd | _: DomWeak => ds
        }
      }

      override def postDiffS(kc: Context, ds: DiffStatement): DiffStatement = {
        ds match {
          case AtomicODEStatement(dp) => AtomicODEStatement(AtomicODE(dp.xp, translate(kc, dp.e)))
          case _ => ds
        }
      }

      // translate named references in atoms
      override def postS(kc: Context, s: Statement): Statement = {
        s match {
          case Assume(pat, f) => Assume(pat, translate(kc, f))
          case Assert(pat, f, m) => Assert(pat, translate(kc, f), m)
          case Modify(pat, Left(f)) => Modify(pat, Left(translate(kc, f)))
          case Note(x, proof, Some(annotation)) => Note(x, proof, Some(translate(kc, annotation)))
          case LetFun(f, args, e: Term) => LetFun(f, args, translate(kc, e, localVars = args))
          case Match(pat, e: Term) => Match(translatePat(kc, pat), translate(kc, e))
          case Switch(scrutinee, pats) => Switch(scrutinee, pats.map({case (e1, e2, s) => (e1, translatePat(kc, e2), s)}))
          case While(x, j, s) => While(x, translate(kc, j), s)
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