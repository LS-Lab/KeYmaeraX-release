/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Structured result of a context lookup. Successful queries can return facts and assignments, while failures are
 * distinguished between those that should propagate or those that should not. When the result differs by which proof
 * branch is "executed," both branches are given.
 *
 * @author
 *   Brandon Bohrer
 * @see
 *   [[edu.cmu.cs.ls.keymaerax.cdgl.kaisar.ContextQuery]]
 * @see
 *   [[edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof]]
 */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof._
import edu.cmu.cs.ls.keymaerax.core._

sealed trait ContextResult {

  /** (optional identifier, fact, whether fact corresponds to an assignment) */
  type Item = (Option[Ident], Formula, Boolean)

  /** @return whether result contains no facts/assignments */
  def isEmpty: Boolean = {
    this match {
      case RBranch(l, r) => l.isEmpty && r.isEmpty
      case RWeakFailure(msg) => true
      case RStrongFailure(msg) => true
      case RSuccess(facts, assigns) => facts.isEmpty && assigns.isEmpty
    }
  }

  /** @return whether result contains facts/assignments */
  def nonEmpty: Boolean = !isEmpty

  /** @return fact corresponding to assignment */
  def assignFact(as: Assign): Formula = Equal(as.x, as.e)

  /** @return fact identifier corresponding to assignment */
  def assignId(as: Assign): Option[Ident] = None

  /** @return context result where successful results are filtered by [[p]] */
  def filter(p: Item => Boolean): ContextResult = {
    this match {
      case RWeakFailure(msg) => RStrongFailure(msg)
      case RStrongFailure(msg) => RStrongFailure(msg)
      case RSuccess(facts, assigns) => RSuccess(
          facts.filter({ case (id, fml) => p(id, fml, false) }),
          assigns.filter(asgn => p(assignId(asgn), assignFact(asgn), true)),
        )
    }
  }

  /** Apply [[p]] for side effects to every successful result and ignore values. */
  def foreach(p: Item => Unit): Unit = {
    this match {
      case RWeakFailure(msg) => ()
      case RStrongFailure(msg) => ()
      case RBranch(l, r) => l.foreach(p); r.foreach(p)
      case RSuccess(facts, assigns) =>
        facts.foreach({ case (id, fml) => p(id, fml, false) })
        assigns.foreach(asgn => p(assignId(asgn), assignFact(asgn), true))
    }
  }

  /**
   * @return
   *   only those results which can soundly be accessed in the given context, assuming a given set of taboo variables
   *   (i.e. variables which were bound after the context and before the reference site)
   */
  def admissiblePart(inContext: Context, tabooProgramVars: Set[Variable], tabooFactVars: Set[Ident]): ContextResult =
    this match {
      case _: RStrongFailure => this
      case _: RWeakFailure => this
      case RSuccess(facts, assigns) =>
        def factFilter(id: Option[Ident], fml: Formula): Boolean = {
          val free = StaticSemantics(KaisarProof.forgetAt(fml)).fv
          (id.forall(!tabooFactVars.contains(_))) &&
          (inContext.isElaborationContext || free.toSet.intersect(tabooProgramVars).isEmpty)
        }
        def assignFilter(as: Assign): Boolean = factFilter(assignId(as), assignFact(as))
        val filteredFacts = facts.filter({ case (x, y) => factFilter(x, y) })
        val filteredAssigns = assigns.filter(assignFilter)
        RSuccess(filteredFacts, filteredAssigns)
    }

  // @TODO: Better data structure for assignments that might also have names. matchesAssign vs matchesFact
  /** @return only the portion which satisfies the given query */
  def matchingPart(cq: ContextQuery): ContextResult = {
    this match {
      case _: RStrongFailure => this
      case _: RWeakFailure => this
      case RSuccess(facts, assigns) => RSuccess(
          facts.filter({ case (id, fml) => cq.matches(id, fml, isAssignment = false) }),
          assigns.filter({ case (asgn: Assign) => cq.matches(Some(asgn.x), assignFact(asgn), isAssignment = true) }),
        )
    }
  }

  /** @return "same" result with (user-defined and internal) function symbols fully elaborated */
  def elaborated(kc: Context, cq: ContextQuery): ContextResult = {
    this match {
      case RSuccess(fmls, assigns) =>
        val elabFmls = fmls.map(idFml => (idFml._1, cq.elaborate(kc.outer, idFml._2)))
        val elabAssigns = assigns.map(asgn => Assign(asgn.x, cq.elaborate(kc.outer, asgn.e)))
        RSuccess(elabFmls, elabAssigns)
      case _ => this
    }
  }

  /** @return association list of results */
  def asList: List[(Option[Ident], Formula)]

  /** @return formulas for each fact and assignment */
  def formulas: List[Formula] = asList.map(_._2)

  /** @return all identifiers found */
  def idents: List[Ident] = asList.map(_._1).flatMap(_.toList)

  /** @return results of both contexts, swallowing weak errors */
  def ++(other: ContextResult): ContextResult = (this, other) match {
    case (RSuccess(factsL, assignL), RSuccess(factsR, assignR)) => RSuccess(factsL ++ factsR, assignL ++ assignR)
    // @TODO: Do we want to allow strong failures with a list of error messages?
    case (_: RStrongFailure, _) => this
    case (_, _: RStrongFailure) => other
    // Only swallow weak errors when other branch found something. Otherwise, weak error may help explain why no
    // result was found.
    case (_: RWeakFailure, _) if other.nonEmpty => other
    case (_, _: RWeakFailure) if other.nonEmpty => this
    case (_: RWeakFailure, _) => this
    case (_, _: RWeakFailure) => other
    case (l, r) if r.isEmpty => l
    case (l, r) if l.isEmpty => r
    case (x, RBranch(l, r)) => RBranch(l.++(x), r.++(x))
    case (RBranch(l, r), x) => RBranch(l.++(x), r.++(x))
    case _ => throw ProofCheckException(s"Could not compute union of results: $this and $other")
  }
}

/** Collection of facts with optional names, as well as assignments */
case class RSuccess(facts: Set[(Option[Ident], Formula)], assigns: Set[Assign] = Set()) extends ContextResult {
  override def asList: List[(Option[Ident], Formula)] = facts.toList ++
    assigns.map((as: Assign) => (None, Equal(as.x, as.e))).toList
}

/** Strong failures represent an issue that must be reported regardless of what happens on other branches */
case class RStrongFailure(msg: String) extends ContextResult {
  override def asList: List[(Option[Ident], Formula)] = Nil
}

/** Weak failures only represent that one branch has failed, and so long as some other branch succeeds, we're ok */
case class RWeakFailure(msg: String) extends ContextResult {
  override def asList: List[(Option[Ident], Formula)] = Nil
}

/** When results differed for two parallel branches of a proof, return each branch, distinguished */
case class RBranch(l: ContextResult, r: ContextResult) extends ContextResult {
  // Combine each branch in set fashion. Facts which appear on both branches are kept.
  // We then disjoin the branches where the facts/assignments of each branch are conjunctive.
  // This operation erases naming information. However, naming information should be non-essential in the
  // *result* of a query.
  override def asList: List[(Option[Ident], Formula)] = {
    def conjoin(fmls: List[Formula]): Formula = fmls match {
      case Nil => True
      case _ => fmls.reduce(And)
    }
    def setted(lst: List[(Option[Ident], Formula)]): Set[Formula] = lst.foldLeft[Set[Formula]](Set())({ case (acc, x) =>
      acc.+(x._2)
    })
    val (llst, rlst) = (l.asList, r.asList)
    if (llst == rlst) llst
    else {
      val (lSet, rSet) = (setted(llst), setted(rlst))
      val (inter, lDiff, rDiff) = (lSet.intersect(rSet), lSet.--(rSet), rSet.--(lSet))
      val (lBranch, rBranch) = (conjoin(lDiff.toList), conjoin(rDiff.toList))
      val fmls = (lBranch, rBranch) match {
        // if either branch is true, then P | true simplifies to True
        case (True, _) | (_, True) => inter.toList
        case _ => Or(lBranch, rBranch) :: inter.toList
      }
      fmls.map(x => (None, x))
    }
  }
}

object ContextResult {

  /** Found nothing. */
  def unit: ContextResult = RSuccess(Set(), Set())
}
