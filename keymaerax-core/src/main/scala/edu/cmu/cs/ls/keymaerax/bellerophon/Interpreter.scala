package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core.{Ensures, FuncOf, Function, Nothing, Real, Sequent, SubstitutionPair, USubst, Unit, Variable}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.SequentAugmentor
import edu.cmu.cs.ls.keymaerax.infrastruct.{SubstitutionHelper, UnificationMatch, UnificationTools}
import edu.cmu.cs.ls.keymaerax.parser.Declaration
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

  /** Collects substitutions (of `defs`) that are needed to make `sub` fit the `i`-th subgoal of `goal`. */
  protected def collectSubst(goal: ProvableSig, i: Int, sub: ProvableSig, defs: Declaration): USubst =
    UnificationTools.collectSubst(goal.underlyingProvable, i, sub.underlyingProvable, defs)


  /** Applies substitutions `s` to provable `p` exhaustively. */
  protected def exhaustiveSubst(p: ProvableSig, s: USubst): ProvableSig =
    p.reapply(SubstitutionHelper.exhaustiveSubst(p.underlyingProvable, s))

  /**
    * Replaces the nth subgoal of `original` with the remaining subgoals of `subderivation`.
    *
    * @param original A Provable whose nth subgoal is equal to the conclusion of `subderivation` (modulo substitution).
    * @param n The numerical index of the subgoal of original to rewrite (Seqs are zero-indexed)
    * @param subderivation The provable to replace the original subgoal.
    * @return A tuple of:
    *         * Indicator whether `original` and `subderivation` were merged.
    *         * A new provable that is identical to `original`, except that the nth subgoal is replaced with the
    *           remaining subgoals of `subderivation`; and
    *         * The next index for the interpreter to continue, n if `subderivation` is proved (i.e., all later
    *           subgoals move up by 1), or (n+1) if subderivation is not proved.
    */
  protected def applySubDerivation(original: ProvableSig, n: Int, subderivation: ProvableSig, subst: USubst): (Boolean, ProvableSig, Int) = {
    assert(original.subgoals.length > n, s"$n is a bad index for Provable with ${original.subgoals.length} subgoals: $original")
    val (substParent, substChild) =
      if (original.subgoals(n) == subderivation.conclusion) (original, subderivation)
      else if (subderivation.isProved) {
        val substOrig = exhaustiveSubst(original, subst)
        val substSubDeriv = exhaustiveSubst(subderivation, subst)
        //@todo may no longer need unification now that inner sequential interpreter returns delayed substitutions
        val unified = Try(UnificationMatch(substSubDeriv.conclusion, substOrig.subgoals(n))).toEither match {
          case Left(_) =>
            Try(UnificationMatch(substOrig.subgoals(n), substSubDeriv.conclusion)).toEither match {
              case Left(ex) => throw ex
              case Right(s) => s
            }
          case Right(s) => s
        }
        val substSubderivation = exhaustiveSubst(substSubDeriv, unified.usubst)
        (substOrig, substSubderivation)
      } else {
        (exhaustiveSubst(original, subst), subderivation)
      }
    if (substParent.subgoals(n) == substChild.conclusion) {
      val merged = substParent(substChild, n)
      val nextIdx = if (substChild.isProved) n else n + 1
      (true, merged, nextIdx)
    } else {
      assertSubMatchesModuloConstification(substParent, subderivation, n, subst)
      //@todo substParent may have more subgoals than subderivation
      (false, subderivation, if (substChild.isProved) n else n + 1)
    }
  } ensures(r => r match {
    case (rmerged: Boolean, rp: ProvableSig, rn: Int) =>
      (rn == n || rn == n+1) &&
      ((!rmerged && rp==subderivation) ||
       ( rmerged && exhaustiveSubst(rp, subst).conclusion == exhaustiveSubst(original, subst).conclusion &&
         (if (subderivation.isProved) {
           rp.subgoals.size == original.subgoals.size - 1
         } else {
           rp.subgoals(n) == subderivation.subgoals(0) &&
             rp.subgoals.takeRight(subderivation.subgoals.size - 1) == subderivation.subgoals.tail
         })
       )
      )
  })

  /** Assert that the conclusion of provable `sub` matches the subgoal `n` of provable `parent` either verbatim or
    * modulo constification renaming that is assumed to be applied in the future. Constification renaming requires
    * `parent` to have exactly one single subgoal. */
  protected def assertSubMatchesModuloConstification(parent: ProvableSig, sub: ProvableSig, n: Int, subst: USubst): Unit = {
    if (SubstitutionHelper.exhaustiveSubst(parent.underlyingProvable, subst).subgoals(n) != Try(SubstitutionHelper.exhaustiveSubst(sub.underlyingProvable, subst)).toOption.getOrElse(sub.underlyingProvable).conclusion &&
        !subMatchesModuloConstification(parent.subgoals(n), sub.conclusion, subst)) {
      throw new BelleUnexpectedProofStateError(s"Subgoal #$n of the original provable (${parent.subgoals(n)}})\nshould be equal to the conclusion of the subderivation\n(${sub.conclusion}}),\nbut is not despite substitution $subst", sub.underlyingProvable)
    }
  }

  /** Assert that the conclusion of provable `sub` matches the conclusion of provable `parent` either verbatim or
    * modulo constification renaming that is assumed to be applied in the future. */
  protected def assertConclusionsMatchModuloConstification(parent: ProvableSig, sub: ProvableSig, subst: USubst): Unit = {
    if (!subMatchesModuloConstification(parent.conclusion, sub.conclusion, subst)) throw new BelleUnexpectedProofStateError(s"Conclusion of the original provable (${parent.conclusion}})\nshould be equal to the conclusion of the subderivation\n(${sub.conclusion}}),\nbut is not despite substitution $subst", sub.underlyingProvable)
  }

  /** Returns true if `sub` matches `parent` either verbatim or modulo constification renaming of `subst`. */
  private def subMatchesModuloConstification(parent: Sequent, sub: Sequent, subst: USubst): Boolean = {
    if (subst(parent) != subst(sub)) {
      // support for spoonfeeding constification (dIRule); will only work if the remaining
      // tactics are closing the open goals of substChild since outer interpreter will
      // try to plug conclusion of substChild into unconstified open goal of substParent
      val constifications = subst.subsDefsInput.flatMap({
        case SubstitutionPair(f@FuncOf(Function(fn, fi, Unit, Real, _), Nothing), v: Variable) if fn == v.name && fi == v.index => Some(f -> v)
        case _ => None
      })
      val backSubstSubConclusion = constifications.foldRight(sub)({ case ((fn, v), s) => s.replaceAll(fn, v) })
      parent == backSubstSubConclusion
    } else true
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