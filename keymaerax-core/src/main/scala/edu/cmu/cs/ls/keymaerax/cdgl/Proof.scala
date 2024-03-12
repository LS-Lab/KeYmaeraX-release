/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Forward natural deduction proof terms for CdGL. Proof variables for assumptions are represented with de Bruijn
 * indices. The conclusion of a proof term is an output of the proof checker, which often requires formula (and program)
 * annotations in proof terms. To promote lexical scope, binding connectives rename in the context rather than
 * weakening. Variables used for renaming are optional arguments to proof terms, which can be inferred if not given
 * explicitly. In typical natural-deduction style, premisses mention as few connectives as possible
 * @note
 *   Soundness-critical
 * @author
 *   Brandon Bohrer
 */
package edu.cmu.cs.ls.keymaerax.cdgl

import edu.cmu.cs.ls.keymaerax.cdgl.Proof._
import edu.cmu.cs.ls.keymaerax.core._
import scala.collection.immutable

object Proof {
  // de Bruijn indices
  type ProofVariable = Int
}

/**
 * A context is a conjunction of assumption formulas. Variable references proceed from the head of the list and binding
 * rules introduce assumptions at the head, i.e., assumption 0 is the first element and the most recently added.
 * @param c
 *   List of assumptions
 */
final case class Context(c: List[Formula]) {
  override def toString: String = {
    val s = c.map(_.prettyString).foldRight("")((s, acc) => s + "," + acc)
    s
  }

  /** Returns whether context contains proof variable */
  def contains(x: ProofVariable): Boolean = c.length > x

  /** returns IndexedSeq containing same elements */
  def asIndexedSeq: immutable.IndexedSeq[Formula] = c.toIndexedSeq

  /** returns List containing same elements */
  def asList: List[Formula] = c

  /** returns Sequent with same assumptions and empty succedent */
  def asSequent: Sequent = Sequent(this.asIndexedSeq, immutable.IndexedSeq())

  /** returns Sequent with same assumptions and given succedent */
  def entails(f: Formula): Sequent = { Sequent(c.toIndexedSeq, immutable.IndexedSeq(f)) }

  /** Apply single renaming to all assumptions */
  def rename(what: Variable, repl: Variable): Context = {
    Context.ofSequent(UniformRenaming(what, repl)(this.asSequent).head)
  }

  /** Apply all renamings to all assumptions */
  def renames(whats: List[Variable], repls: List[Variable]): Context = {
    whats.zip(repls).foldLeft[Context](this)({ case (acc, (x, y)) => acc.rename(x, y) })
  }

  /** Add assumption P to context */
  def extend(P: Formula): Context = { Context(P :: c) }

  /** All variables which appear free in some assumption */
  def freevars: SetLattice[Variable] = c
    .map(StaticSemantics(_).fv)
    .foldLeft[SetLattice[Variable]](SetLattice.bottom)({ case (acc, fv) => fv ++ acc })

  /** Retrieve assumption formula for given variable index */
  def apply(p: ProofVariable): Formula = c(p)
}

object Context {

  /** Returns true iff context contains no assumptions */
  def empty: Context = Context(List())

  /** Context corresponding to antecedent of sequent */
  def ofSequent(seq: Sequent): Context = { Context(seq.ante.toList) }

}

/** Judgement G |- P  is a context G with a single succedent formula P */
final case class Judgement(ante: Context, succ: Formula) {}

/** An effectively-well-found convergence metric used for Angelic loop convergence reasoning <*> */
sealed trait Metric {

  /** Witness of admissibility */
  def witness: Proof

  /** @param fact Result of checking witness. */
  def setFact(fact: Formula): Unit

  /**
   * @param boundTaboo
   *   bound variables of loop body
   * @param freeTaboo
   *   Free variables of context, variant, and postcondition
   * @return
   *   true if metric is admissible
   */
  def isAdmissible(boundTaboo: Set[Variable], freeTaboo: Set[Variable]): Boolean

  /** Formula which holds when the metric has converged */
  def isZero: Formula

  /** Formula which holds when the metric has not converged */
  def nonZero: Formula

  /** Formula which expresses that the metric has decreased in the given iteration */
  def decreased: Formula

  /** Formula which remembers initial metric value in ghost variable(s) */
  def ghost: Formula
}

/**
 * Constant metric requires real scalar term [[t]] to decrease by at least positive constant [[n]] each iteration, and
 * stores previous metric value in [[theGhost]]. Termination condition [[isZero]] is inequational because [[t]] is
 * permitted to become negative
 */
case class ConstantMetric(t: Term, theGhost: Variable, child: Proof) extends Metric {
  var n: Option[Term] = None
  def witness: Proof = child
  def setFact(fact: Formula): Unit = fact match {
    case Greater(theN, nz: Number) =>
      if (nz.value != 0) throw ProofException("Metric witness conclusion must have shape k>0")
      n = Some(theN)
    case p => throw ProofException("Metric witness conclusion must have shape k>0")
  }
  def isAdmissible(boundTaboo: Set[Variable], freeTaboo: Set[Variable]): Boolean = StaticSemantics(n.get)
    .intersect(boundTaboo)
    .isEmpty && !freeTaboo.contains(theGhost)
  def nonZero: Formula = Greater(t, Number(0))
  def isZero: Formula = LessEqual(t, Number(0))
  def decreased: Formula = GreaterEqual(theGhost, Plus(t, n.get))
  def ghost: Formula = Equal(theGhost, t)
}

/** CdGL forward proof terms */
sealed trait Proof {}

/*                 *
 *  -------------------------------
 *   G |-  (): True
 */
case class Triv() extends Proof {}

/* G |- M: P   G |- N: Q
 * ----------------------------------------------
 * G |- <M, N>: <?P>Q
 */
case class DTestI(left: Proof, right: Proof) extends Proof {}

/* G |- M: <?P>Q
 * ----------------------------------------------
 * G |- piL(M): P
 */
case class DTestEL(child: Proof) extends Proof {}

/* G |- M: <?P>Q
 * ----------------------------------------------
 * G |- piR(M): Q
 */
case class DTestER(child: Proof) extends Proof {}

/* G_x^y, p: (x=f_x^y) |- M: P
 * ----------------------------------------------
 * G |- <x: =f_x^y in p. M> : <x: =f>P
 */
case class DAssignI(e: Assign, child: Proof, y: Option[Variable] = None) extends Proof {}

/* G |- M: <x: =f>p(x)
 * ----------------------------------------------
 * G |- <: =^-1>(M): p(f)
 */
case class DAssignE(child: Proof) extends Proof {}

/* G_x^y, p: (x=f_x^y) |- M: P
 * ----------------------------------------------
 * G |- <x : * f_x^y in p. M> : <x: =*>P
 */
case class DRandomI(e: Assign, child: Proof, y: Option[Variable] = None) extends Proof {}

/* G |- M: <x: =f>p(x)   G_x^y, p(x) |- N: Q
 * ----------------------------------------------
 * G |-  (unpack_x^y = M in N) : Q
 */
case class DRandomE(left: Proof, right: Proof, y: Option[Variable] = None) extends Proof {}

/* G |- M: <a><b>P
 * ----------------------------------------------
 * G |- <i M>: <a;b>P
 */
case class DComposeI(child: Proof) extends Proof {}

/* G |- M: <a;b>P
 * ----------------------------------------------
 * G |- <i^-1 M>: <a><b>P
 */
case class DComposeE(child: Proof) extends Proof {}

/* G |- M: <a>P
 * ----------------------------------------------
 * G |- injL[b](M): <a++b>P
 */
case class DChoiceIL(other: Program, child: Proof) extends Proof {}

/* G |- M: <b>P
 * ----------------------------------------------
 * G |- injR[a](M): <a++b>P
 */
case class DChoiceIR(other: Program, child: Proof) extends Proof {}

/* G |- A: <a++b>P   G, l: <a>P |- B: Q   G, r: <b>P |- C: Q
 * ----------------------------------------------
 * G |- (case A of l=>B | r=>C): Q
 */
case class DChoiceE(child: Proof, left: Proof, right: Proof) extends Proof {}

/* G |- M: P
 * ----------------------------------------------
 * G |- stop[a](M): <a*>P
 */
case class DStop(child: Proof, other: Program) extends Proof {}

/* G |- M: <a><a*>P
 * ----------------------------------------------
 * G |- (go M): <a*>P
 */
case class DGo(child: Proof) extends Proof {}

/* G |- A: J   m: mx=met>metz, v: J |- <a>(J & mx>met)  m: met=metz, v: J |- Q
 * ------------------------------------------------------------------------
 * G |- for_{met, metz}(A;mv.B;C): <a*>Q
 */
// etric: Term, metz: Term, mx: BaseVariable
case class DRepeatI(m: Metric, init: Proof, step: Proof, post: Proof) extends Proof {}

/* G |- A: <a*>P   x: P |- B: Q   x: <a>Q |- C: Q
 * ----------------------------------------------
 * G |- FP(A, x.B, x.C): Q
 */
case class DRepeatE(child: Proof, post: Proof, step: Proof) extends Proof {}

/* G |- M: [a]P
 * ----------------------------------------------
 * G |- yield M: <a^d>P
 */
case class DDualI(child: Proof) extends Proof {}

/* G |- M: <a^d>P
 * ----------------------------------------------
 * G |- (yield^-1 M): [a]P
 */
case class DDualE(child: Proof) extends Proof {}

/* G |- dur >= 0   G_xs^ys, 0<=s<=dur |- M: Q_xs^sol(s)   G_xs^ys |- N: P_xs^sol(dur)
 * ----------------------------------------------  sol solves x'=f&Q on [0, dur], s and t fresh
 * G |- DS[x'=f&Q, ys, sol, dur, s](M, N): <x'=f&Q>P
 */
case class DSolve(
    ode: ODESystem,
    post: Formula,
    durPos: Proof,
    dc: Proof,
    child: Proof,
    s: Variable = Variable("s"),
    t: Variable = Variable("t"),
    ys: Option[List[Variable]] = None,
) extends Proof {}

/* G, t=0 |- A: d>=0 & f >= -dv
 * G, t=0 |- B: <x'=f, t'=1&Q>t>=d
 * G |- C: [x'=f&Q](f' >= v)
 * G_xs^ys, f>=0 |- D: P
 * ---------------------------------------------- d, v constant, t, ys fresh
 * G |- DV[f, g, d, eps, v](A, B, C, D): <x'=f&Q>P
 */
case class DV(
    const: Proof,
    dur: Proof,
    rate: Proof,
    post: Proof,
    t: Variable = Variable("t"),
    ys: Option[List[Variable]] = None,
) extends Proof {}

/* G, x: P |- M: Q
 * ----------------------------------------------
 * G |- (fn x: P => M): [?P]Q
 */
case class BTestI(fml: Formula, child: Proof) extends Proof {}

/* G |- M: [?P]Q   G|- N: P
 * ----------------------------------------------
 * G |- (M N): Q
 */
case class BTestE(left: Proof, right: Proof) extends Proof {}

/* G_x^y, p: (x=f_x^y) |- M: P
 * ----------------------------------------------
 * G |- [x: =f_x^y in p. M] : [x: =f]P
 */
case class BAssignI(e: Assign, child: Proof, y: Option[Variable] = None) extends Proof {}

/* G |- M: [x: =f]p(x)
 * ----------------------------------------------
 * G |- [: =^-1](M): p(f)
 */
case class BAssignE(child: Proof) extends Proof {}

/* G |- G_x^y |- M: P
 * ----------------------------------------------
 * G |- (fn x^y => M): [x: =*]P
 */
case class BRandomI(x: Variable, child: Proof, y: Option[Variable] = None) extends Proof {}

/* G |- M: [x: =*]p(x)
 * ----------------------------------------------
 * G |- (M f): p(f)
 */
case class BRandomE(child: Proof, f: Term) extends Proof {}

/* G |- M: [a][b]P
 * ----------------------------------------------
 * G |- [i M]: [a;b]P
 */
case class BComposeI(child: Proof) extends Proof {}

/* G |- M: [a;b]P
 * ----------------------------------------------
 * G |- [i M]: [a][b]P
 */
case class BComposeE(child: Proof) extends Proof {}

/* G |- M: [a]P   G |- N: [b]P
 * ----------------------------------------------
 * G |- [M, N]: [a++b]P
 */
case class BChoiceI(left: Proof, right: Proof) extends Proof {}

/* G |- M: [a++b]P
 * ----------------------------------------------
 * G |- projL(M): [a]P
 */
case class BChoiceEL(child: Proof) extends Proof {}

/* G |- M: [a++b]P
 * ----------------------------------------------
 * G |- projR(M): [b]P
 */
case class BChoiceER(child: Proof) extends Proof {}

/* G |- A: J   G_xs^ys, x: J |- B: [a]J   G_xs^ys, x: J |- C: Q
 * ---------------------------------------------------------
 * G |- (A rep[ys] x: J. B in C): [a*]Q
 */
case class BRepeatI(pre: Proof, step: Proof, post: Proof, a: Program, ys: Option[List[Variable]] = None)
    extends Proof {}

/* G |- M: [a*]P
 * ----------------------------------------------
 * G |- projL(M): P
 */
case class BRepeatEL(child: Proof) extends Proof {}

/* G |- M: [a*]P
 * ----------------------------------------------
 * G |- projR(M): [a][a*]P
 */
case class BRepeatER(child: Proof) extends Proof {}

/* G |- M: <a>P
 * ----------------------------------------------
 * G |- [yield M]: [a^d]P
 */
case class BDualI(child: Proof) extends Proof {}

/* G |- M: [a^d]P
 * ----------------------------------------------
 * G |- [yield^-1 M]: <a>P
 */
case class BDualE(child: Proof) extends Proof {}

/*  G_xs^ys, 0<=t, (\forall 0<=s<=t, Q_xs^sol(dur)) |- N: P_xs^sol(dur)
 * --------------------------------------------------------------------  sol solves x'=f&Q on [0, dur], s and t fresh
 * G |- BS[x'=f&Q, ys, sol, t, s](M, N): [x'=f&Q]P
 */
case class BSolve(
    ode: ODESystem,
    post: Formula,
    child: Proof,
    s: Variable = Variable("s"),
    t: Variable = Variable("t"),
    ys: Option[List[Variable]] = None,
) extends Proof {}

/* G_xs^ys, x: Q |- M: P
 * ----------------------------------------------
 * G |- DW[ys](x.M): [x'=f & Q]P
 */
case class DW(ode: ODESystem, child: Proof, ys: Option[List[Variable]] = None) extends Proof {}

/* G |- M: [x'=f&Q]R   G |- N: [x'=f&(Q&R)]P
 * ----------------------------------------------
 * G |- DC(M, N): [x'=f&Q]P
 */
case class DC(left: Proof, right: Proof) extends Proof {}

/* G |- M: P   G_xs^ys |- N: (P)'_x'^f
 * ----------------------------------------------
 * G |- DI(M, N): [x'=f & Q]P
 */
case class DI(ode: ODESystem, pre: Proof, step: Proof, ys: Option[List[Variable]] = None) extends Proof {}

/* G, y=y0 |- M: [x'=f, y'=a(y)+b&Q]P
 * ----------------------------------------------
 * G |- DG[y, y0, a, b](M): [x'=f]P
 */
case class DG(init: Assign, rhs: Plus, child: Proof) extends Proof {}

/* G_x^y |- M: P
 * ----------------------------------------------
 * G |- (fn x^y => M): (\forall x, P)
 */
case class ForallI(x: Variable, child: Proof, y: Option[Variable] = None) extends Proof {}

/* G |- M: (\forall x, p(x))
 * ----------------------------------------------
 * G |- (M f): p(f)
 */
case class ForallE(child: Proof, f: Term) extends Proof {}

/* G_x^y, p: (x=f_x^y) |- M: P
 * ----------------------------------------------
 * G |- <x = f_x^y in p. M> : \exists x, P
 */
case class ExistsI(e: Assign, child: Proof, y: Option[Variable] = None) extends Proof {}

/* G |- M: (exists x, p(x))   G_x^y, p(x) |- N: Q
 * ----------------------------------------------
 * G |- (unpack_x^y = M in N) : Q
 */
case class ExistsE(left: Proof, right: Proof, y: Option[Variable] = None) extends Proof {}

/* G |- M: P   G |- N: Q
 * ----------------------------------------------
 * G |- (M, N): P & Q
 */
case class AndI(left: Proof, right: Proof) extends Proof {}

/* G |- M: P & Q
 * ----------------------------------------------
 * G |- projL(M): P
 */
case class AndEL(child: Proof) extends Proof {}

/* G |- M: P & Q
 * ----------------------------------------------
 * G |- projR(M): Q
 */
case class AndER(child: Proof) extends Proof {}

/* G |- M: P
 * ----------------------------------------------
 * G |- injL[Q](M): P | Q
 */
case class OrIL(other: Formula, child: Proof) extends Proof {}

/* G |- M: Q
 * ----------------------------------------------
 * G |- injR[P](M): P | Q
 */
case class OrIR(other: Formula, child: Proof) extends Proof {}

/* G |- A: (P|Q)   G, l: P |- B: R    G, r: Q |- C: R
 * ----------------------------------------------
 * G |- (case A of l=>B | r=>C): R
 */
case class OrE(child: Proof, left: Proof, right: Proof) extends Proof {}

/* G, x: P |- M: Q
 * ----------------------------------------------
 * G |- (fn x: P => M): (P -> Q)
 */
case class ImplyI(fml: Formula, child: Proof) extends Proof {}

/* G |- M: (P -> Q)   G |- N: P
 * ----------------------------------------------
 * G |- (M N): Q
 */
case class ImplyE(left: Proof, right: Proof) extends Proof {}

/* G, x: P |- M: Q   G, x: Q |- N: P
 * ----------------------------------------------
 * G |- (M, N)[x: P, Q]
 */
case class EquivI(fml: Equiv, left: Proof, right: Proof) extends Proof {}

/* G |- M: (P <-> Q)   G |- N: P
 * ----------------------------------------------
 * G |- (projL(M) N): Q
 */
case class EquivEL(child: Proof, assump: Proof) extends Proof {}

/* G |- M: (P <-> Q)   G |- N: Q
 * ----------------------------------------------
 * G |- (projR(M) N): P
 */
case class EquivER(child: Proof, assump: Proof) extends Proof {}

/* G, x: P |- M: False
 * ----------------------------------------------
 * G |- (fn x: P => M): !P
 */
case class NotI(p: Formula, child: Proof) extends Proof {}

/* G |- M: !P   G |- N: P
 * ----------------------------------------------
 * G |- (M N): False
 */
case class NotE(left: Proof, right: Proof) extends Proof {}

/* G |- M: False
 * ----------------------------------------------
 * G |- abort[P] M: P
 */
case class FalseE(child: Proof, fml: Formula) extends Proof {}

/*       *
 * ----------------------------------------------
 * G, x: P |- x: P
 */
case class Hyp(p: ProofVariable) extends Proof {}

/* G |- M: [a]J   G_xs^ys, x: J |- N: Q
 * ----------------------------------------------
 * G |-  (M o x: J. N)[ys] : [a]Q
 */
case class Mon(left: Proof, right: Proof, ys: Option[List[Variable]] = None) extends Proof {}

/* G |- M: Q
 * ---------------------------------------------- (Q -> P is valid first-order arithmetic)
 * G |- QE[P](M) : P
 */
case class QE(p: Formula, child: Proof) extends Proof {}

/*           G |- k > 0
 * ------------------------------  (k > 0)
 * G |-  f > g \/ f < g + k
 */
case class Compare(f: Term, g: Term, kPos: Proof) extends Proof {}
