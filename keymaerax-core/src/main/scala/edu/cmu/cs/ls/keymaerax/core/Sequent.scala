/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Sequents and positioning.
 * @note
 *   Code Review: 2020-02-17
 */
package edu.cmu.cs.ls.keymaerax.core

import scala.collection.immutable

/**
 * Position of a formula in a sequent, i.e. antecedent or succedent positions.
 *
 * @see
 *   [[SeqPos$.apply(signedPos:Int):edu\.cmu\.cs\.ls\.keymaerax\.core\.SeqPos*]]
 * @see
 *   [[Sequent.apply(pos:edu\.cmu\.cs\.ls\.keymaerax\.core\.SeqPos):edu\.cmu\.cs\.ls\.keymaerax\.core\.Formula*]]
 * @see
 *   [[AntePos]]
 * @see
 *   [[SuccPos]]
 */
sealed trait SeqPos {

  /** Whether this position is in the antecedent on the left of the sequent arrow */
  val isAnte: Boolean

  /** Whether this position is in the succedent on the right of the sequent arrow */
  val isSucc: Boolean

  /** The '''unsigned''' index into the antecedent or succedent list, respectively, '''0-indexed'''. */
  private[keymaerax] val getIndex: Int

  /**
   * The '''signed''' position for the antecedent or succedent list, respectively, '''1-indexed'''. Negative numbers
   * indicate antecedent positions, -1, -2, -3, .... Positive numbers indicate succedent positions, 1, 2, 3. Zero is
   * unused.
   * @see
   *   [[SeqPos.apply(signedPos:Int):edu\.cmu\.cs\.ls\.keymaerax\.core\.SeqPos*]]
   */
  final lazy val getPos: Int =
    if (isSucc) { assert(!isAnte); getIndex + 1 }
    else { assert(isAnte); -(getIndex + 1) }

  override def toString: String = getPos.toString
}

/**
 * Antecedent Positions of formulas in a sequent, i.e. in the assumptions on the left of the sequent arrow.
 *
 * @param index
 *   the position 0-indexed in antecedent.
 */
case class AntePos private[ls] (private[core] val index: Int) extends SeqPos {
  val isAnte: Boolean = true
  val isSucc: Boolean = !isAnte

  /** The position 0-indexed in antecedent. */
  private[keymaerax] val getIndex: Int = index
}

/**
 * Antecedent Positions of formulas in a sequent, i.e. on the right of the sequent arrow.
 *
 * @param index
 *   the position 0-indexed in succedent.
 */
case class SuccPos private[ls] (private[core] val index: Int) extends SeqPos {
  val isAnte: Boolean = false
  val isSucc: Boolean = !isAnte

  /** The position 0-indexed in succedent. */
  private[keymaerax] val getIndex: Int = index
}

object SeqPos {

  /**
   * Sequent position of signed index `signedPos` where positive is succedent and negative antecedent.
   *
   * @param signedPos
   *   the signed integer position of the formula in the antecedent or succedent, respectively. Negative numbers
   *   indicate antecedent positions, -1, -2, -3, .... Positive numbers indicate succedent positions, 1, 2, 3.
   * @see
   *   [[SeqPos.getPos]]
   */
  def apply(signedPos: Int): SeqPos =
    if (signedPos > 0) { SuccPos(signedPos - 1) }
    else { require(signedPos < 0, "nonzero positions"); AntePos(-(signedPos + 1)) }

}

/**
 * Sequent `ante |- succ` with antecedent ante and succedent succ.
 * {{{
 *   ante(0),ante(1),...,ante(n) |- succ(0),succ(1),...,succ(m)
 * }}}
 * This sequent is often pretty-printed with signed line numbers:
 * {{{
 *     -1: ante(0)
 *     -2: ante(1)
 *         ...
 * -(n+1): ante(n)
 *  ==> 1: succ(0)
 *      2: succ(1)
 *         ...
 *  (m+1): succ(m)
 * }}}
 * The semantics of sequent `ante |- succ` is the conjunction of the formulas in `ante` implying the disjunction of the
 * formulas in `succ`.
 *
 * @param ante
 *   The ordered list of antecedents of this sequent whose conjunction is assumed.
 * @param succ
 *   The ordered list of succedents of this sequent whose disjunction needs to be shown.
 * @author
 *   Andre Platzer
 * @see
 *   Andre Platzer. [[https://doi.org/10.1007/s10817-008-9103-8 Differential dynamic logic for hybrid systems]]. Journal
 *   of Automated Reasoning, 41(2), pages 143-189, 2008.
 */
final case class Sequent(ante: immutable.IndexedSeq[Formula], succ: immutable.IndexedSeq[Formula]) {

  /**
   * Retrieves the formula in sequent at a given position.
   *
   * @param pos
   *   the position of the formula
   * @return
   *   the formula at the given position either from the antecedent or the succedent
   */
  def apply(pos: SeqPos): Formula = pos match {
    case ap: AntePos => apply(ap)
    case sp: SuccPos => apply(sp)
  }

  /**
   * Retrieves the formula in sequent at a given succedent position.
   * @param pos
   *   the succedent position of the formula
   * @return
   *   the formula at the given position from the succedent
   * @note
   *   slightly faster version with the same result as
   *   [[Sequent.apply(pos:edu\.cmu\.cs\.ls\.keymaerax\.core\.SeqPos):edu\.cmu\.cs\.ls\.keymaerax\.core\.Formula*]]
   */
  def apply(pos: AntePos): Formula = ante(pos.getIndex)

  /**
   * Retrieves the formula in sequent at a given antecedent position.
   * @param pos
   *   the antecedent position of the formula
   * @return
   *   the formula at the given position from the antecedent
   * @note
   *   slightly faster version with the same result as
   *   [[Sequent.apply(pos:edu\.cmu\.cs\.ls\.keymaerax\.core\.SeqPos):edu\.cmu\.cs\.ls\.keymaerax\.core\.Formula*]]
   */
  def apply(pos: SuccPos): Formula = succ(pos.getIndex)

  // transformations giving copies of sequents

  /**
   * A copy of this sequent concatenated with given sequent s. Sequent(A,S) glue Sequent(B,T) == Sequent(A++B, S++T)
   *
   * @param s
   *   the sequent whose antecedent to append to ours and whose succedent to append to ours.
   * @return
   *   a copy of this sequent concatenated with s. Results in a least upper bound with respect to subsets of this and s.
   */
  def glue(s: Sequent): Sequent = {
    Sequent(ante ++ s.ante, succ ++ s.succ)
  } ensures
    (
      r =>
        this.subsequentOf(r) && s.subsequentOf(r) && r.ante.forall(f => this.ante.contains(f) || s.ante.contains(f)) &&
          r.succ.forall(f => this.succ.contains(f) || s.succ.contains(f)),
      "result is a supersequent of its pieces and all formulas in result come from either one",
    )

  /**
   * A copy of this sequent with the indicated position replaced by the formula f.
   *
   * @param p
   *   the position of the replacement
   * @param f
   *   the replacing formula
   * @return
   *   a copy of this sequent with the formula at position p replaced by f.
   */
  def updated(p: SeqPos, f: Formula): Sequent = p match {
    case sp: SuccPos => updated(sp, f)
    case ap: AntePos => updated(ap, f)
  }

  /**
   * A copy of this sequent with the indicated antecedent position replaced by the formula f, same as
   * [[Sequent.updated(p:edu\.cmu\.cs\.ls\.keymaerax\.core\.SeqPos,f:edu\.cmu\.cs\.ls\.keymaerax\.core\.Formula):edu\.cmu\.cs\.ls\.keymaerax\.core\.Sequent*]].
   */
  def updated(p: AntePos, f: Formula): Sequent = Sequent(ante.updated(p.getIndex, f), succ)

  /**
   * A copy of this sequent with the indicated succedent position replaced by the formula f, same as
   * [[Sequent.updated(p:edu\.cmu\.cs\.ls\.keymaerax\.core\.SeqPos,f:edu\.cmu\.cs\.ls\.keymaerax\.core\.Formula):edu\.cmu\.cs\.ls\.keymaerax\.core\.Sequent*]].
   */
  def updated(p: SuccPos, f: Formula): Sequent = Sequent(ante, succ.updated(p.getIndex, f))

  /**
   * A copy of this sequent with the indicated position replaced by gluing the sequent s.
   *
   * @param p
   *   the position of the replacement
   * @param s
   *   the sequent glued / concatenated to this sequent after dropping p.
   * @return
   *   a copy of this sequent with the formula at position p removed and the sequent s appended.
   * @see
   *   [[Sequent.updated(p:edu\.cmu\.cs\.ls\.keymaerax\.core\.SeqPos,f:edu\.cmu\.cs\.ls\.keymaerax\.core\.Formula):edu\.cmu\.cs\.ls\.keymaerax\.core\.Sequent*]]
   * @see
   *   [[Sequent.glue(s:edu\.cmu\.cs\.ls\.keymaerax\.core\.Sequent):edu\.cmu\.cs\.ls\.keymaerax\.core\.Sequent*]]
   */
  def updated(p: SeqPos, s: Sequent): Sequent = p match {
    case sp: SuccPos => updated(sp, s)
    case ap: AntePos => updated(ap, s)
  }

  /**
   * A copy of this sequent with the indicated antecedent position replaced by gluing the sequent s, same as
   * [[updated(p:edu\.cmu\.cs\.ls\.keymaerax\.core\.SeqPos,s:edu\.cmu\.cs\.ls\.keymaerax\.core\.Sequent):edu\.cmu\.cs\.ls\.keymaerax\.core\.Sequent*]]
   */
  def updated(p: AntePos, s: Sequent): Sequent = {
    Sequent(ante.patch(p.getIndex, Nil, 1), succ).glue(s)
  } ensures
    (
      r => r.glue(Sequent(immutable.IndexedSeq(this(p)), immutable.IndexedSeq())).sameSequentAs(this.glue(s)),
      "result after re-including updated formula is equivalent to " + this + " glue " + s,
    )

  /**
   * A copy of this sequent with the indicated succedent position replaced by gluing the sequent s, same as
   * [[updated(p:edu\.cmu\.cs\.ls\.keymaerax\.core\.SeqPos,s:edu\.cmu\.cs\.ls\.keymaerax\.core\.Sequent):edu\.cmu\.cs\.ls\.keymaerax\.core\.Sequent*]]
   */
  def updated(p: SuccPos, s: Sequent): Sequent = {
    Sequent(ante, succ.patch(p.getIndex, Nil, 1)).glue(s)
  } ensures
    (
      r => r.glue(Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(this(p)))).sameSequentAs(this.glue(s)),
      "result after re-including updated formula is equivalent to " + this + " glue " + s,
    )

  /**
   * Check whether this sequent is a subsequent of the given sequent r (considered as sets)
   * @note
   *   Used for contracts in the core.
   */
  def subsequentOf(r: Sequent): Boolean = ante.toSet.subsetOf(r.ante.toSet) && succ.toSet.subsetOf(r.succ.toSet)

  /**
   * Check whether this sequent is the same as the given sequent r (considered as sets)
   * @note
   *   Used for contracts in the core.
   */
  def sameSequentAs(r: Sequent): Boolean = this.subsequentOf(r) && r.subsequentOf(this)

  override def toString: String = ante.map(_.prettyString).mkString(", ") +
    (if (ante.isEmpty) "  ==>  " else "\n  ==>  ") + succ.map(_.prettyString).mkString(", ")

  /** Pretty-print sequent */
  def prettyString: String = {
    val anteLines = this
      .ante
      .zipWithIndex
      .map { case (formula, i) =>
        val prefix = "   "
        s"$prefix${-(i + 1)}:  ${formula.prettyString}\t${formula.getClass.getSimpleName}"
      }

    val succLines = this
      .succ
      .zipWithIndex
      .map({ case (formula, i) =>
        val prefix = if (i == 0) "==> " else "    "
        s"$prefix${i + 1}:  ${formula.prettyString}\t${formula.getClass.getSimpleName}"
      })

    anteLines.concat(succLines).mkString("\n")
  }

}
