package edu.cmu.cs.ls.keymaerax.cli

import edu.cmu.cs.ls.keymaerax.bellerophon.OnAll
import edu.cmu.cs.ls.keymaerax.btactics.PolynomialArithV2
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.collection.immutable.IndexedSeq

/** Assesses dL formulas for equivalence, implication etc. with restricted automation. */
object AssessmentProver {
  /** Proves equivalence of `a` and `b` by QE. */
  def qeEquivalence(a: Formula, b: Formula): ProvableSig = {
    KeYmaeraXProofChecker(5000)(QE)(Sequent(IndexedSeq.empty, IndexedSeq(Equiv(a, b))))
  }

  /** Proves polynomial equality of `a` and `b`. */
  def polynomialEquality(a: Term, b: Term): ProvableSig = {
    KeYmaeraXProofChecker(5000)(PolynomialArithV2.equate(1))(Sequent(IndexedSeq.empty, IndexedSeq(Equal(a, b))))
  }
  /** Proves polynomial equality between the terms resulting from chasing simple programs in `a` and `b`. */
  def polynomialEquality(a: ComparisonFormula, b: ComparisonFormula): ProvableSig = {
    require(a.reapply(b.left, b.right) == b, "Same comparison operator expected, but got " + a.getClass.getSimpleName + " vs. " + b.getClass.getSimpleName)
    KeYmaeraXProofChecker(1500)(PolynomialArithV2.equate(1))(Sequent(IndexedSeq.empty,
      IndexedSeq(Equal(Minus(a.left, a.right), Minus(b.left, b.right)))))
  }
  /** Proves polynomial equality between the terms resulting from chasing simple programs in `a` and `b`. */
  def polynomialEquality(a: Sequent, b: Sequent): ProvableSig = {
    require(a.ante.isEmpty && a.succ.size == 1 && b.ante.isEmpty && b.succ.size == 1)
    val ap: ProvableSig = KeYmaeraXProofChecker(1000)(chase(1))(a)
    val bp: ProvableSig = KeYmaeraXProofChecker(1000)(chase(1))(b)
    assert(ap.subgoals.size == 1 && ap.subgoals.head.isFOL && ap.subgoals.head.ante.isEmpty && ap.subgoals.head.succ.size == 1 &&
      bp.subgoals.size == 1 && bp.subgoals.head.isFOL && bp.subgoals.head.ante.isEmpty && bp.subgoals.head.succ.size == 1)
    //@todo allow more liberal equality? normalize? compound formulas?
    (ap.subgoals.head.succ.head, bp.subgoals.head.succ.head) match {
      case (ac: ComparisonFormula, bc: ComparisonFormula) => polynomialEquality(ac, bc)
      case (aps, bps) => throw new IllegalArgumentException("Atomic comparison formulas expected, but got " + aps.prettyString + ", " + bps.prettyString)
    }
  }

  /** Compares expressions for equality. */
  def syntacticEquality(a: Expression, b: Expression): Boolean = {
    a == b
  }
  /** Compares sequents for equality. */
  def syntacticEquality(a: List[Sequent], b: List[Sequent]): Boolean = {
    a.zip(b).forall({ case (a, b) =>
      a.ante.toSet == b.ante.toSet && a.succ.toSet == b.succ.toSet
    })
  }

  /** Checks `inv` for being a loop invariant of `loop`. */
  def loopInvCheck(seq: Sequent, inv: Formula): ProvableSig = {
    KeYmaeraXProofChecker(5000)(implyR(1) & loop(inv)(1) & OnAll(auto & done) & done)(seq)
  }

  /** Checks `inv` for being a differential invariant of `ode`. */
  def dICheck(ode: ODESystem, inv: Formula): ProvableSig = {
    KeYmaeraXProofChecker(5000)(dI(auto='cex)(1))(Sequent(IndexedSeq(inv), IndexedSeq(Box(ode, inv))))
  }

}
