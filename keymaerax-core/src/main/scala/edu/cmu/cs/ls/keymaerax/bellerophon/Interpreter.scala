package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core.USubst
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.annotation.tailrec

/**
  * Interpreter for Bellerophon tactic expressions that transforms [[BelleValue Bellerophon values]] using
  * [[BelleExpr Bellerophon tactic language expressions]] to ultimately produce [[ProvableSig]].
  * {{{
  *   Interpreter : BelleExpr * BelleValue => BelleValue
  * }}}
 *
  * @author Nathan Fulton
  * @see [[SequentialInterpreter]]
  */
trait Interpreter {
  /** Returns the result of applying tactic `expr` to the proof value `v` (usually a provable). */
  def apply(expr: BelleExpr, v: BelleValue): BelleValue

  /** Stops the interpreter and kills all its tactic executions. */
  def kill(): Unit

  /** Indicates whether the interpreter is still operational. A dead interpreter refuses to run tactics. */
  def isDead: Boolean

  /** Registered listeners. */
  def listeners: scala.collection.immutable.Seq[IOListener]

  /**
    * Replaces the nth subgoal of `original` with the remaining subgoals of `subderivation`.
    *
    * @param original A Provable whose nth subgoal is equal to the conclusion of `subderivation` (modulo substitution).
    * @param n The numerical index of the subgoal of original to rewrite (Seqs are zero-indexed)
    * @param subderivation The provable to replace the original subgoal.
    * @return A pair of:
    *         * A new provable that is identical to `original`, except that the nth subgoal is replaced with the
    *           remaining subgoals of `subderivation`; and
    *         * The next index for the interpreter to continue, n if `subderivation` is proved (i.e., all later
    *           subgoals move up by 1), or (n+1) if subderivation is not proved.
    */
  protected def replaceConclusion(original: ProvableSig, n: Int, subderivation: ProvableSig, subst: Option[USubst]): (ProvableSig, Int) = {
    assert(original.subgoals.length > n, s"$n is a bad index for Provable with ${original.subgoals.length} subgoals: $original")
    val substituted =
      if (original.subgoals(n) == subderivation.conclusion) original
      else subst.map(exhaustiveSubst(original, _)).getOrElse(original)
    if (substituted.subgoals(n) != subderivation.conclusion)
      throw new BelleUnexpectedProofStateError(s"Subgoal #$n of the original provable (${substituted.subgoals(n)}})\nshould be equal to the conclusion of the subderivation\n(${subderivation.conclusion}}),\nbut is not despite substitution $subst", subderivation.underlyingProvable)
    val newProvable = substituted(subderivation, n)
    val nextIdx = if (subderivation.isProved) n else n + 1
    (newProvable, nextIdx)
  }

  /** Applies substitutions `s` to provable `p` exhaustively. */
  @tailrec
  protected final def exhaustiveSubst(p: ProvableSig, s: USubst): ProvableSig = {
    val substituted = p(s)
    if (substituted != p) exhaustiveSubst(substituted, s)
    else substituted
  }
}

/**
  * Listeners for input/output results during the [[Interpreter interpretation]] of Bellerophon tactic expressions.
  */
trait IOListener {
  def begin(input: BelleValue, expr: BelleExpr): Unit
  def end(input: BelleValue, expr: BelleExpr, output: Either[BelleValue, Throwable]): Unit
  def kill(): Unit
}