package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core.USubst
import edu.cmu.cs.ls.keymaerax.infrastruct.UnificationMatch
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.annotation.tailrec
import scala.util.Try

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
  /** Starts the interpreter. */
  def start(): Unit

  /** Returns the result of applying tactic `expr` to the proof value `v` (usually a provable).
    * Interpreter must be started before executing tactics. */
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
  protected def replaceConclusion(original: ProvableSig, n: Int, subderivation: ProvableSig, subst: USubst): (ProvableSig, Int) = {
    assert(original.subgoals.length > n, s"$n is a bad index for Provable with ${original.subgoals.length} subgoals: $original")
    val (substParent, substChild) =
      if (original.subgoals(n) == subderivation.conclusion) (original, subderivation)
      else if (subderivation.isProved) {
        val substOrig = exhaustiveSubst(original, subst)
        (substOrig, exhaustiveSubst(subderivation,
          Try(UnificationMatch(subderivation.conclusion, substOrig.subgoals(n))).toOption.getOrElse(
            UnificationMatch(substOrig.subgoals(n), subderivation.conclusion)).usubst))
      } else (exhaustiveSubst(original, subst), subderivation)
    if (substParent.subgoals(n) != substChild.conclusion)
      throw new BelleUnexpectedProofStateError(s"Subgoal #$n of the original provable (${substParent.subgoals(n)}})\nshould be equal to the conclusion of the subderivation\n(${subderivation.conclusion}}),\nbut is not despite substitution $subst", subderivation.underlyingProvable)
    val newProvable = substParent(substChild, n)
    val nextIdx = if (substChild.isProved) n else n + 1
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