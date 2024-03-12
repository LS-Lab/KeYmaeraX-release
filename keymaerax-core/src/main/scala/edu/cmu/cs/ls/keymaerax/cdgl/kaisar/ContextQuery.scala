/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * The ContextQuery trait gives a query language for inspecting the proof context for facts and assignments. A
 * query-language approach provides compositionality and is especially useful for bulk queries. In turn, support for
 * bulk queries is important both for performance and convenience. For performance, it is important that we do not
 * unintentionally select the same fact twice, and the language approach simplifies fact selection deduplication. Bulk
 * queries also provide convenience when lookup up two facts A and B which are each doubly defined on disjoint proof
 * branches C and D. Naive lookups would yield a weaker result (A_C | A_D) & (B_C | B_D), while we can support the more
 * precise (A_C & B_C) | (A_D & B_D). This need arises frequently in safety proofs of branching controllers. Queries
 * arise both from the selectors written in a proof (e.g. "x" or "fact") as well as Kaisar's own heuristics. As the
 * scenario warrants, default selectors can look up facts, or assignments which are likely to be relevant.
 * @author
 *   Brandon Bohrer
 * @see
 *   [[edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof]]
 */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.UnificationMatch

sealed trait ContextQuery {

  /**
   * Required operation.
   * @param x
   *   optional fact identifier
   * @param f
   *   fact formula,
   * @param isAssignment
   *   flag indicating whether the fact was induced by an assignment
   * @return
   *   whether this query is looking for the given fact
   */
  def matches(x: Option[Ident], f: Formula, isAssignment: Boolean): Boolean

  /** Optionally elaborate or otherwise post-process only the successful matches */
  def elaborate(kc: Context, f: Formula): Formula = f

  /** Optionally elaborate or otherwise post-process only the successful matches */
  def elaborate(kc: Context, f: Term): Term = f

  def partitionPt: (List[ProofTerm], ContextQuery) = {
    this match {
      case QProofTerm(pt) => (List(pt), QNil())
      case QElaborate(cq) =>
        val (pts, cqq) = cq.partitionPt
        (pts, QElaborate(cqq))
      case QPhi(phi, cq) =>
        val (pts, cqq) = cq.partitionPt
        (pts, QPhi(phi, cqq))
      case QUnion(l, r) =>
        val (ptsL, cqL) = l.partitionPt
        val (ptsR, cqR) = r.partitionPt
        (ptsL ++ ptsR, QUnion(l, r))
      case _: QNil | _: QUnify | _: QProofVar | _: QAssignments | _: QProgramVar => (Nil, this)
    }
  }
}

/**
 * [[QElaborate]] instructs the context to execute query [[cq]] normally, then fully elaborate all (user-defined and
 * internal) function symbols appearing in the result.
 */
case class QElaborate(cq: ContextQuery) extends ContextQuery {
  override def matches(x: Option[Ident], f: Formula, isAssignment: Boolean): Boolean = cq
    .matches(x, f, isAssignment = isAssignment)
  override def elaborate(kc: Context, f: Formula): Formula = kc.elaborateStable(kc.elaborateFunctions(f, Triv()))
  override def elaborate(kc: Context, f: Term): Term = kc.elaborateStable(kc.elaborateFunctions(f, Triv()))
}

/** Matches nothing. Algebraic unit of query language. */
case class QNil() extends ContextQuery {
  override def matches(x: Option[Ident], f: Formula, isAssignment: Boolean): Boolean = false
}

/** Matches all facts which mention a given program variable */
case class QProgramVar(x: Variable) extends ContextQuery {
  override def matches(yOpt: Option[Ident], fml: Formula, isAssignment: Boolean): Boolean = {
    val vars = StaticSemantics(fml)
    val allVars: Set[Variable] = (vars.fv ++ vars.bv).toSet // .++(yOpt.toSet)
    allVars.exists(y => x.name == y.name)
  }
}

/**
 * Matches all assignments which assign a given variable [[x]]. The subscript of [[x]] is ignored so that a simple
 * search for [[x]] will capture its SSA-variants such as [[x_1]].
 */
// @TODO: onlySSA flag not fully implemented
case class QAssignments(x: Variable, onlySSA: Boolean) extends ContextQuery {
  override def matches(y: Option[Ident], fml: Formula, isAssignment: Boolean): Boolean = {
    isAssignment &&
    (fml match {
      case Equal(z: Variable, _) => x.name == z.name
      case _ => false
    })
  }
}

object QUnion {

  /** Smart constructor for union queries. Only effect is simpler representation for debugger output. */
  def apply(l: ContextQuery, r: ContextQuery): ContextQuery = {
    (l, r) match {
      case (QNil(), _) => r
      case (_, QNil()) => l
      case _ => new QUnion(l, r)
    }
  }
}

/** Matches all facts matched by at least one of [[l]] and [[r]] */
case class QUnion private (l: ContextQuery, r: ContextQuery) extends ContextQuery {
  override def matches(x: Option[Ident], fml: Formula, isAssignment: Boolean): Boolean = l
    .matches(x, fml, isAssignment) || r.matches(x, fml, isAssignment)
}

/**
 * Matches only facts which are bound to fact name [[x]]. In the case that [[x]] is bound to different facts on
 * different branches, both facts are returned so that they may be (soundly) disjoined.
 */
case class QProofVar(x: Variable) extends ContextQuery {
  // @TODO: Make interface clear for assignments with or without identifiers
  override def matches(y: Option[Ident], fml: Formula, isAssignment: Boolean): Boolean = y.contains(x) && !isAssignment
}

/**
 * Query corresponding to a proof term selector. Presently, the effect is the same as [[note]]ing a proof term and
 * selecting the [[note]]d fact variable. However, having a ProofTerm query would allow us in principle to manage proof
 * terms whose arguments differ across branches.
 */
case class QProofTerm(pt: ProofTerm) extends ContextQuery {
  override def matches(x: Option[Ident], fml: Formula, isAssignment: Boolean): Boolean = false
}

/** Not to be confused with [[QUnion]]. Matches all formulas which unify with a given pattern. */
case class QUnify(pat: Expression) extends ContextQuery {
  override def matches(maybeX: Option[Ident], f: Formula, isAssignment: Boolean): Boolean = {
    maybeX match {
      case Some(x) =>
        try {
          UnificationMatch(pat, f)
          true
        } catch { case _: ProverException => false }
      case None => false
    }
  }
}

/**
 * Applies a query [[cq]] under an assignment. Assuming queries are applied to (light) SSA-form contexts, the QPhi is
 * only needed for (inlined) Phi assignments, as they are the only assignments which ever shadow another.
 */
case class QPhi(phi: Phi, cq: ContextQuery) extends ContextQuery {
  override def matches(x: Option[Ident], fml: Formula, isAssignment: Boolean): Boolean = cq
    .matches(x, Context.substPhi(phi, fml), isAssignment)

  override def elaborate(kc: Context, f: Formula): Formula = cq.elaborate(kc, f)
}
