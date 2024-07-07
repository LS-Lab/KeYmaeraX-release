/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.infrastruct

import org.keymaerax.core._
import org.keymaerax.pt.ProvableSig
import org.keymaerax.bellerophon.BelleExpr
import org.keymaerax.btactics.{Idioms, TactixLibrary}

import scala.collection.immutable
import scala.collection.immutable._

object RenUSubst {
  // @note semanticRenaming=false: to disallow renaming within semantic constructs as in the core.
  @inline
  private[keymaerax] val semanticRenaming = false /*&& (try {
    URename(Variable("quark"), Variable("quark", Some(5)))(ProgramConst("quarky")) == ProgramConst("quarky")
  } catch { case e: RenamingClashException => false })*/

  /** Create a renaming uniform substitution from the given list of replacements. */
  def apply(subsDefsInput: immutable.Seq[(Expression, Expression)]) /*: RenUSubst*/ =
    // if (semanticRenaming) new URenAboveUSubst(subsDefsInput) else
    // new DirectUSubstAboveURen(subsDefsInput)
    new FastUSubstAboveURen(subsDefsInput)
  // new FastUSubstAboveURen(subsDefsInput.filter(sp=>sp._1!=sp._2).distinct)
  //  new USubstAboveURen(subsDefsInput)

  /** Create a (non-)renaming uniform substitution corresponding to the given ordinary uniform substitution. */
  def apply(us: USubst): RenUSubst = apply(us.subsDefsInput.map(sp => (sp.what, sp.repl)))

  /** Create a renaming (non-)substitution corresponding to the given ordinary uniform renaming. */
  def apply(us: URename): RenUSubst = apply(List((us.what, us.repl)))

  /**
   * Apply uniform renaming what~>repl to provable forward in Hilbert-style (convenience). Supports semantic renaming on
   * proved provables; renames conclusion but keeps subgoals of unproved provables unrenamed to simplify forward proofs.
   */
  def UniformRenamingForward(provable: ProvableSig, what: Variable, repl: Variable): ProvableSig = {
    if (provable.isProved) provable(URename(what, repl, semantic = true))
    else provable(URename(what, repl)(provable.conclusion), UniformRenaming(what, repl))
  }

  private[infrastruct] def renamingPartOnly(
      subsDefsInput: immutable.Seq[(Expression, Expression)]
  ): immutable.Seq[(Variable, Variable)] = subsDefsInput
    .filter(sp => sp._1.isInstanceOf[Variable] && sp._2 != sp._1)
    .map(
      sp =>
        { // Predef.assert(sp._2.isInstanceOf[Variable], "Variable renaming expected " + sp + " in " + subsDefsInput);
          (sp._1.asInstanceOf[Variable], sp._2.asInstanceOf[Variable])
        }
    )
  private[infrastruct] def renamingPartOnly(
      subsDefsInput: immutable.List[(Expression, Expression)]
  ): immutable.List[(Variable, Variable)] = subsDefsInput
    .filter(sp => sp._1.isInstanceOf[Variable] && sp._2 != sp._1)
    .map(
      sp =>
        { // Predef.assert(sp._2.isInstanceOf[Variable], "Variable renaming expected " + sp + " in " + subsDefsInput);
          (sp._1.asInstanceOf[Variable], sp._2.asInstanceOf[Variable])
        }
    )
  private[infrastruct] def renamingPart(subsDefsInput: immutable.Seq[(Expression, Expression)]): RenUSubst =
    apply(renamingPartOnly(subsDefsInput))

  /**
   * Occurrences of what symbol the generalized SubstitutionPair sp will be replacing.
   * @return
   *   Function/predicate/predicational or DotTerm or (Differential)ProgramConst whose occurrences we will replace.
   */
  private[infrastruct] def matchKey(sp: (Expression, Expression)): NamedSymbol = sp._1 match {
    case d: DotTerm => d
    // case Nothing => {assert(sp._2 == Nothing, "can replace Nothing only by Nothing, and nothing else"); Nothing} // it makes no sense to substitute Nothing
    case a: DifferentialProgramConst => a
    case a: ProgramConst => a
    case DotFormula => DotFormula
    case PredicationalOf(p: Function, _) => p
    // RenUSubst generalization
    case FuncOf(f: Function, _) => f
    case PredOf(p: Function, _) => p
    case x: Variable => x
    case p: UnitPredicational => p
    case f: UnitFunctional => f
    case _ => throw new ProverException("Nonsubstitutable expression " + sp)
  }

  /**
   * The key characteristic expression constituents that this Substitution is matching on.
   * @return
   *   union of the matchKeys of all our substitution pairs.
   */
  private[infrastruct] def matchKeys(
      subsDefsInput: immutable.Seq[(Expression, Expression)]
  ): immutable.List[NamedSymbol] = {
    subsDefsInput.foldLeft(immutable.List[NamedSymbol]())((a, b) => a ++ immutable.List(matchKey(b)))
  }

}

/**
 * Renaming Uniform Substitution, combining [[URename]] and [[USubst]] in a way that has both a direct application like
 * apply functions of [[USubstRen]] as well as a translation to equivalent tactical/core prover operations.
 *
 * Liberal list of SubstitutionPair represented as merely a list of Pair, where the `Variable~>Variable` replacements
 * are by uniform renaming, and the other replacements are by uniform substitution.
 *
 * @author
 *   Andre Platzer
 * @see
 *   [[org.keymaerax.core.URename]]
 * @see
 *   [[org.keymaerax.core.USubst]]
 * @see
 *   [[USubstRen]]
 * @see
 *   [[org.keymaerax.infrastruct.Augmentors.TermAugmentor.~>()]]
 * @see
 *   [[org.keymaerax.infrastruct.Augmentors.FormulaAugmentor.~>()]]
 * @see
 *   [[org.keymaerax.infrastruct.Augmentors.ProgramAugmentor.~>()]]
 */
sealed trait RenUSubst extends (Expression => Expression) {

  /**
   * The (distinct) list of replacements that this RenUSubst performs by uniform renaming or uniform substitution,
   * respectively.
   */
  private[infrastruct] def subsDefsInput: immutable.Seq[(Expression, Expression)]

  /** Returns true if there is no replacement. */
  def isEmpty = subsDefsInput.isEmpty

  /** Create a similar RenUSubst of the same class with the alternative list of replacements */
  private[infrastruct] def reapply(subsDefs: immutable.Seq[(Expression, Expression)]): RenUSubst

  /** Union of renaming uniform substitutions, i.e., both replacement lists merged. */
  // @todo optimizable like UniformMatching.join
  def ++(other: RenUSubst): RenUSubst = reapply((this.subsDefsInput ++ other.subsDefsInput).distinct)

  /**
   * A renaming substitution pair for a renaming uniform substitution.
   * @see
   *   [[org.keymaerax.core.SubstitutionPair]]
   * @see
   *   [[org.keymaerax.infrastruct.Augmentors.TermAugmentor.~>()]]
   * @see
   *   [[org.keymaerax.infrastruct.Augmentors.FormulaAugmentor.~>()]]
   * @see
   *   [[org.keymaerax.infrastruct.Augmentors.ProgramAugmentor.~>()]]
   */
  type RenUSubstRepl = (Expression, Expression)

  // projections

  /**
   * The uniform substitution part of this renaming uniform substitution as a USubst
   * @see
   *   [[substitution]]
   */
  def usubst: USubst

  /**
   * The uniform substitution part of this renaming uniform substitution as a RenUSubst
   * @see
   *   [[usubst]]
   */
  def substitution: RenUSubst

  /** The uniform renaming part of this renaming uniform substitution */
  def renaming: RenUSubst

  // tactical / prover core application mechanism

  /** Get the renaming tactic part that performs this renaming */
  def getRenamingTactic: BelleExpr

  /**
   * Central operation to convert to forward tactic using the core's respective uniform renaming and uniform
   * substitution rules.
   */
  def toForward: ProvableSig => ProvableSig

  /**
   * This RenUSubst implemented strictly from the core.
   * @note
   *   For contract purposes
   */
  def toCore: Expression => Expression

  // direct application mechanism such as via [[USubstRen.apply]]

  def apply(e: Expression): Expression = e match {
    case t: Term => apply(t)
    case f: Formula => apply(f)
    case p: DifferentialProgram => apply(p)
    case p: Program => apply(p)
    case f: Function => throw new SubstitutionClashException(
        toString,
        "",
        "" + e,
        "",
        "",
        "substitutions are not defined on an isolated Function that is not applied to arguments.",
      )
  }

  def apply(t: Term): Term
  def apply(f: Formula): Formula
  def apply(p: Program): Program
  def apply(p: DifferentialProgram): DifferentialProgram

  /** Apply everywhere in the sequent. */
  def apply(s: Sequent): Sequent = {
    try {
      // @note mapping apply instead of the equivalent usubst makes sure the exceptions are augmented and the ensures contracts checked.
      Sequent(s.ante.map(apply), s.succ.map(apply))
    } catch {
      case ex: ProverException => throw ex.inContext(s.toString)
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(toString, "undef", "undef", s.toString, "undef", ex.getMessage)
          .initCause(ex)
    }
  }
}

/**
 * Fast implementation of: Renaming Uniform Substitution that, in goal-directed backwards Sequent direction, first runs
 * a uniform renaming below and on the result subsequently the uniform substitution above it.
 * {{{
 *   s(RG) |- s(RD)
 *   -------------- USubst
 *     RG  |- RD
 *   -------------- URen
 *      G  |- D
 * }}}
 * The direct application mechanism via [[apply()]] fast-forwards to the fast joint [[USubstRen]] infrastructure. Its
 * tactical / prover core implementation works in sync using prover core operations by scheduling separate uniform
 * substitutions and uniform renamings to the core when asked.
 *
 * @param subsDefsInput
 * @note
 *   reading in Hilbert direction from top to bottom, the uniform substitution comes first to ensure the subsequent
 *   uniform renaming no longer has nonrenamable program constants since no semantic renaming.
 * @author
 *   Andre Platzer
 * @see
 *   [[USubstRen]]
 * @see
 *   [[DirectUSubstAboveURen]]
 * @invariant
 *   subsDefsInput==subsDefsInput.distinct preserved if initially true
 */
// US: uniform substitution to instantiate all symbols especially program constants to become renamable
// UR: uniform renaming to rename preexisting variables to the present axioms
final class FastUSubstAboveURen(private[infrastruct] val subsDefsInput: immutable.Seq[(Expression, Expression)])
    extends RenUSubst {
  // @note explicit implementation to make RenUSubst equality independent of rens/subsDefs order
  override def equals(e: Any): Boolean = e match {
    case a: FastUSubstAboveURen => subsDefsInput.toSet == a.subsDefsInput.toSet
    case _ => false
  }

  override def hashCode: Int = 199 * subsDefsInput.hashCode()

  // @todo .distinct?
  override def reapply(subs: immutable.Seq[(Expression, Expression)]) = new FastUSubstAboveURen(subs)

  /** Renaming part, with identity renaming no-ops filtered out. */
  private val rens: immutable.Seq[(Variable, Variable)] = RenUSubst.renamingPartOnly(subsDefsInput)

  /** Substitution part, with identity substitution no-ops filtered out later in USubst(...). */
  private val subsDefs: immutable.Seq[SubstitutionPair] =
    try {
      subsDefsInput
        .filterNot(sp => sp._1.isInstanceOf[Variable])
        .map(sp =>
          try { SubstitutionPair(sp._1, sp._2) }
          catch { case ex: ProverException => throw ex.inContext("(" + sp._1 + "~>" + sp._2 + ")") }
        )
    } catch {
      case ex: ProverException => throw ex.inContext("FastUSubstAboveURen{" + subsDefsInput.mkString(", ") + "}")
    }

  /**
   * The effective USubstRen consisting of the renaming and the renamed substitution, since the core substitution will
   * be above the core renaming in the end.
   */
  private val effective: USubstRen =
    try { USubstRen(rens ++ subsDefs.map(sp => (sp.what, renall(sp.repl)))) }
    catch {
      case ex: ProverException => throw ex.inContext("FastUSubstAboveURen{" + subsDefsInput.mkString(", ") + "}")
    }

  /** All renamings at once */
  private lazy val renall: MultiRename = MultiRename(rens)

  override lazy val usubst: USubst = USubst(subsDefs)
  override lazy val renaming: RenUSubst = reapply(rens)
  override lazy val getRenamingTactic: BelleExpr = rens.foldLeft[BelleExpr](Idioms.ident)((t, sp) =>
    t &
      // @note for tableaux backward style, the renamings have to be reversed to get from (already renamed) conclusion back to (prerenamed) origin
      // @note permutations would help simplify matters here since they are their own inverse.
      TactixLibrary.uniformRename(sp._2, sp._1)
  )
  override lazy val substitution: RenUSubst = reapply(subsDefs.map(sp => (sp.what, sp.repl)))

  override lazy val toForward: ProvableSig => ProvableSig = {
    Predef.assert(rens.toMap.keySet.intersect(rens.toMap.values.toSet).isEmpty, "no cyclic renaming")
    fact => {
      val replaced = fact(usubst)
      // forward style: first US fact to get rid of program constants, then uniformly rename variables in the result
      rens.foldLeft(replaced)((pr, sp) => RenUSubst.UniformRenamingForward(pr, sp._1, sp._2))
    }
  }

  override lazy val toCore: Expression => Expression = e => {
    val replaced = usubst(e)
    Predef.assert(rens.toMap.keySet.intersect(rens.toMap.values.toSet).isEmpty, "no cyclic renaming")
    // forward style: first US fact to get rid of program constants, then uniformly rename variables in the result
    // rens.foldLeft(replaced)((expr,sp)=>URename(sp._1,sp._2)(expr))
    renall.toCore(replaced)
  }

  override def toString: String = "FastUSubstAboveRen{" + subsDefs.mkString(", ") + ";" +
    rens.map(sp => sp._1.prettyString + "~~>" + sp._2.prettyString).mkString(", ") + "}"

  // direct application mechanism literally via [[USubstRen.apply]]

  // @todo could optimize empty usubst or empty rens to be just identity application right away
  override def apply(t: Term): Term = new Ensures({ effective(t) }) ensures
    (
      r => sameAsCore(t, r),
      "fast tactical renaming substitution has same result as slower core, if defined: " + this + " on " + t,
    )

  override def apply(f: Formula): Formula = new Ensures({ effective(f) }) ensures
    (
      r => sameAsCore(f, r),
      "fast tactical renaming substitution has same result as slower core, if defined: " + this + " on " + f,
    )

  override def apply(p: Program): Program = new Ensures({ effective(p) }) ensures
    (
      r => sameAsCore(p, r),
      "fast tactical renaming substitution has same result as slower core, if defined: " + this + " on " + p,
    )

  override def apply(p: DifferentialProgram): DifferentialProgram = new Ensures({ effective(p) }) ensures
    (
      r => sameAsCore(p, r),
      "fast tactical renaming substitution has same result as slower core, if defined: " + this + " on " + p,
    )

  /** Check that same result as from core if both defined */
  private def sameAsCore(e: Expression, r: Expression): Boolean = {
    if (Matcher.REVERIFY)
      try {
        if (r == toCore(e)) true
        else {
          Predef.print(
            "fast result: " + r + "\ncore result: " + toCore(e) + "\nrenusubst:   " + this + "\neffective:   " +
              effective + "\napplied to:  " + e
          )
          false
        }
      } catch {
        // the core refuses semantic renaming so cannot compare
        case ignore: RenamingClashException => true
      }
    else true
  }
}

/**
 * Base class for many common Renaming Uniform Substitution, combining [[URename]] and [[USubst]]. Liberal list of
 * SubstitutionPair represented as merely a list of Pair, where the `Variable~>Variable` replacements are by uniform
 * renaming, and the other replacements are by uniform substitution.
 * @author
 *   Andre Platzer
 * @see
 *   [[org.keymaerax.core.URename]]
 * @see
 *   [[org.keymaerax.core.USubst]]
 * @see
 *   [[org.keymaerax.infrastruct.Augmentors.TermAugmentor.~>()]]
 * @see
 *   [[org.keymaerax.infrastruct.Augmentors.FormulaAugmentor.~>()]]
 * @see
 *   [[org.keymaerax.infrastruct.Augmentors.ProgramAugmentor.~>()]]
 */
abstract class RenUSubstBase(private[infrastruct] val subsDefsInput: immutable.Seq[(Expression, Expression)])
    extends RenUSubst {

  /** Renaming part, with identity renaming no-ops filtered out. */
  protected final val rens: immutable.Seq[(Variable, Variable)] = RenUSubst.renamingPartOnly(subsDefsInput)

  /** Substitution part, with identity substitution no-ops filtered out. */
  protected final val subsDefs: immutable.Seq[SubstitutionPair] =
    try {
      subsDefsInput
        .filterNot(sp => sp._1.isInstanceOf[Variable])
        .map(sp =>
          try { SubstitutionPair(sp._1, sp._2) }
          catch { case ex: ProverException => throw ex.inContext("(" + sp._1 + "~>" + sp._2 + ")") }
        )
    } catch { case ex: ProverException => throw ex.inContext("RenUSubst{" + subsDefsInput.mkString(", ") + "}") }

  // @note order to ensure toString already works in error message
  // @todo mostly superfluous by construction. May be able to optimize.
  applicable()

  /** unique left hand sides in subsDefs */
  private def applicable(): Unit = {
    // check that we never replace n by something and then again replacing the same n by something
    val lefts: List[Expression] = subsDefsInput.map(_._1).toList
    if (lefts.distinct.size != lefts.size) throw new ProverException(
      "conflict: no duplicate substitutions for the same substitutee\n" + "RenUSubst(" + subsDefsInput + ")\n" + this +
        "\nreplaces: " + lefts
    )
  }

  /**
   * The uniform substitution part of this renaming uniform substitution
   * @see
   *   [[substitution]]
   * @note
   *   lazy val and postponing applicable() until actual use case would make it possible for useAt(inst) to modify
   *   before exception. Not sure that's worth it though.
   */
  lazy final val usubst = USubst(subsDefs)

  private[infrastruct] def reapply(subsDefs: immutable.Seq[(Expression, Expression)]): RenUSubst

  /**
   * Convert to tactic to reduce to `form` by successively using the respective uniform renaming and uniform
   * substitution rules
   */
  def toTactic(form: Sequent): BelleExpr

  /** The uniform renaming part of this renaming uniform substitution */
  def renaming: RenUSubst = reapply(rens)

  /** Get the renaming tactic part */
  def getRenamingTactic: BelleExpr = rens.foldLeft[BelleExpr](Idioms.ident)((t, sp) =>
    t &
      // @note for tableaux backward style, the renamings have to be reversed to get from (already renamed) conclusion back to (prerenamed) origin
      // @note permutations would help simplify matters here since they are their own inverse.
      TactixLibrary.uniformRename(sp._2, sp._1)
  )

  /**
   * The uniform substitution part of this renaming uniform substitution
   * @see
   *   [[usubst]]
   */
  def substitution: RenUSubst = reapply(subsDefs.map(sp => (sp.what, sp.repl)))

  /** The first step that will be performed first toward the bottom of the proof. */
  private[infrastruct] def firstFlush: RenUSubst

  override def toString: String = "RenUSubst{" +
    rens.map(sp => sp._1.prettyString + "~~>" + sp._2.prettyString).mkString(", ") + " ; " + subsDefs.mkString(", ") +
    "}"
}

/**
 * Renaming Uniform Substitution that, in Sequent direction, first runs a uniform renaming and on the result
 * subsequently the uniform substituion.
 * {{{
 *   s(RG) |- s(RD)
 *   -------------- USubst
 *     RG  |- RD
 *   -------------- URen
 *      G  |- D
 * }}}
 * @param subsDefsInput
 * @note
 *   reading in Hilbert direction from top to bottom, the uniform substitution comes first to ensure the subsequent
 *   uniform renaming no longer has nonrenamable program constants since no semantic renaming.
 * @author
 *   Andre Platzer
 */
// US: uniform substitution to instantiate all symbols especially program constants to become renamable
// UR: uniform renaming to rename preexisting variables to the present axioms
final class USubstAboveURen(private[infrastruct] override val subsDefsInput: immutable.Seq[(Expression, Expression)])
    extends RenUSubstBase(subsDefsInput) {
  // @note explicit implementation to make RenUSubst equality independent of rens/subsDefs order
  override def equals(e: Any): Boolean = e match {
    case a: USubstAboveURen => rens.toSet == a.rens.toSet && subsDefs.toSet == a.subsDefs.toSet
    // rens == a.rens && subsDefs == a.subsDefs
    case _ => false
  }

  override def hashCode: Int = 47 * rens.hashCode() + subsDefs.hashCode()

  def reapply(subs: immutable.Seq[(Expression, Expression)]) = new USubstAboveURen(subs)

  // backwards style: compose US after renaming to get the same Hilbert proof order as in toForward: US above UR
  // rens.foldLeft(replaced)((pr,sp)=>UniformRenaming.UniformRenamingForward(pr, sp._1,sp._2))
  def toTactic(form: Sequent): BelleExpr =
    throw new UnsupportedOperationException(
      "not implemented"
    ) // @todo getRenamingTactic & ProofRuleTactics.US(usubst, form)

  def toForward: ProvableSig => ProvableSig = fact => {
    val replaced = fact(usubst) // UniformSubstitutionRule.UniformSubstitutionRuleForward(fact, usubst)
    // forward style: first US fact to get rid of program constants, then uniformly rename variables in the result
    rens.foldLeft(replaced)((pr, sp) => RenUSubst.UniformRenamingForward(pr, sp._1, sp._2))
  }

  val toCore = (e: Expression) => throw new UnsupportedOperationException("not yet implemented. @todo")

  private[infrastruct] def firstFlush: RenUSubst = renaming

  override def toString: String = super.toString + "USubstAboveRen"

  // @todo could optimize empty usubst or empty rens to be just identity application right away
  def apply(t: Term): Term =
    try { rens.foldLeft(usubst(t))((e, sp) => URename(sp._1, sp._2)(e)) }
    catch { case ex: ProverException => throw ex.inContext(t.prettyString, "with " + this) }

  def apply(f: Formula): Formula =
    try { rens.foldLeft(usubst(f))((e, sp) => URename(sp._1, sp._2)(e)) }
    catch { case ex: ProverException => throw ex.inContext(f.prettyString, "with " + this) }

  def apply(p: Program): Program =
    try { rens.foldLeft(usubst(p))((e, sp) => URename(sp._1, sp._2)(e)) }
    catch { case ex: ProverException => throw ex.inContext(p.prettyString, "with " + this) }

  def apply(p: DifferentialProgram): DifferentialProgram =
    try { rens.foldLeft(usubst(p))((e, sp) => URename(sp._1, sp._2)(e)) }
    catch { case ex: ProverException => throw ex.inContext(p.prettyString, "with " + this) }
}

/**
 * Direct implementation of: Renaming Uniform Substitution that, in Sequent direction, first runs a uniform renaming and
 * on the result subsequently the uniform substitution.
 * {{{
 *   s(RG) |- s(RD)
 *   -------------- USubst
 *     RG  |- RD
 *   -------------- URen
 *      G  |- D
 * }}}
 * Semantic renaming may be supported if need be.
 *
 * DirectUSubstAboveURen is a direct implementation in tactics land of a joint renaming and substitution algorithm. It
 * uses a single direct fast [[USubstRen]] for direct internal applications via [[DirectUSubstAboveURen.apply()]] but
 * schedules separate uniform substitutions and uniform renamings to the core when asked. The first fast pass supports
 * semantic renaming, which is useful during unification to "apply" renamings already to predicationals without clash.
 * The final core pass does not support semantic renaming, but is only needed for the final unifier.
 *
 * @param subsDefsInput
 * @note
 *   reading in Hilbert direction from top to bottom, the uniform substitution comes first to ensure the subsequent
 *   uniform renaming no longer has nonrenamable program constants since no semantic renaming.
 * @see
 *   [[FastUSubstAboveURen]]
 * @author
 *   Andre Platzer
 */
// US: uniform substitution to instantiate all symbols especially program constants to become renamable
// UR: uniform renaming to rename preexisting variables to the present axioms
final class DirectUSubstAboveURen(
    private[infrastruct] override val subsDefsInput: immutable.Seq[(Expression, Expression)]
) extends RenUSubstBase(subsDefsInput) {
  // @note explicit implementation to make RenUSubst equality independent of rens/subsDefs order
  override def equals(e: Any): Boolean = e match {
    case a: DirectUSubstAboveURen => rens.toSet == a.rens.toSet && subsDefs.toSet == a.subsDefs.toSet
    // rens == a.rens && subsDefs == a.subsDefs
    case _ => false
  }

  override def hashCode: Int = 67 * rens.hashCode() + subsDefs.hashCode()

  def reapply(subs: immutable.Seq[(Expression, Expression)]) = new DirectUSubstAboveURen(subs)

  /** All renamings at once */
  private val renall = MultiRename(rens)

  /**
   * The effective USubstRen consisting of the renaming and the renamed substitution, since the core substitution will
   * be above the core renaming in the end.
   */
  protected val effective: USubstRen =
    try {
      USubstRen(
        rens ++ subsDefs.map(sp =>
          try {
            Predef.assert(!(sp.what.isInstanceOf[Variable]), "already filtered renaming part elsewhere")
            (sp.what, renall(sp.repl))
          } catch { case ex: ProverException => throw ex.inContext("(" + sp + ")") }
        )
      )
    } catch {
      case ex: ProverException => throw ex.inContext("DirectUSubstAboveURen{" + subsDefsInput.mkString(", ") + "}")
    }

  // backwards style: compose US after renaming to get the same Hilbert proof order as in toForward: US above UR
  // rens.foldLeft(replaced)((pr,sp)=>UniformRenaming.UniformRenamingForward(pr, sp._1,sp._2))
  def toTactic(form: Sequent): BelleExpr =
    throw new UnsupportedOperationException(
      "not implemented"
    ) // @todo getRenamingTactic & ProofRuleTactics.US(usubst, form)

  val toForward: ProvableSig => ProvableSig = fact => {
    val replaced = fact(usubst)
    Predef.assert(rens.toMap.keySet.intersect(rens.toMap.values.toSet).isEmpty, "no cyclic renaming")
    // forward style: first US fact to get rid of program constants, then uniformly rename variables in the result
    rens.foldLeft(replaced)((pr, sp) => RenUSubst.UniformRenamingForward(pr, sp._1, sp._2))
  }

  val toCore: Expression => Expression = e => {
    val replaced = usubst(e)
    Predef.assert(rens.toMap.keySet.intersect(rens.toMap.values.toSet).isEmpty, "no cyclic renaming")
    // forward style: first US fact to get rid of program constants, then uniformly rename variables in the result
    // rens.foldLeft(replaced)((expr,sp)=>URename(sp._1,sp._2)(expr))
    renall.toCore(replaced)
  }

  private[infrastruct] def firstFlush: RenUSubst = renaming

  override def toString: String = "DirectUSubstAboveRen{" + subsDefs.mkString(", ") + ";" +
    rens.map(sp => sp._1.prettyString + "~~>" + sp._2.prettyString).mkString(", ") + "}"

  // @todo could optimize empty usubst or empty rens to be just identity application right away
  def apply(t: Term): Term = new Ensures({ effective(t) }) ensures
    (
      r => sameAsCore(t, r),
      "fast tactical renaming substitution has same result as slower core, if defined: " + this + " on " + t,
    )

  def apply(f: Formula): Formula = new Ensures({ effective(f) }) ensures
    (
      r => sameAsCore(f, r),
      "fast tactical renaming substitution has same result as slower core, if defined: " + this + " on " + f,
    )

  def apply(p: Program): Program = new Ensures({ effective(p) }) ensures
    (
      r => sameAsCore(p, r),
      "fast tactical renaming substitution has same result as slower core, if defined: " + this + " on " + p,
    )

  def apply(p: DifferentialProgram): DifferentialProgram = new Ensures({ effective(p) }) ensures
    (
      r => sameAsCore(p, r),
      "fast tactical renaming substitution has same result as slower core, if defined: " + this + " on " + p,
    )

  /** Check that same result as from core if both defined */
  private def sameAsCore(e: Expression, r: Expression): Boolean = {
    if (Matcher.REVERIFY)
      try {
        if (r == toCore(e)) true
        else {
          Predef.print(
            "fast result: " + r + "\ncore result: " + toCore(e) + "\nrenusubst:   " + this + "\neffective:   " +
              effective + "\napplied to:  " + e
          )
          false
        }
      } catch {
        // the core refuses semantic renaming so cannot compare
        case ignore: RenamingClashException => true
      }
    else true
  }
}

/**
 * Renaming Uniform Substitution that, in Sequent direction, first runs a uniform substitution and on the result
 * subsequently the uniform renaming.
 * {{{
 *   R(s(G)) |- R(s(D))
 *   ------------------ URen
 *      s(G) |- s(D)
 *   ------------------ USubst
 *        G  |- D
 * }}}
 * @param subsDefsInput
 * @author
 *   Andre Platzer
 */
private final class URenAboveUSubst(
    private[infrastruct] override val subsDefsInput: immutable.Seq[(Expression, Expression)]
) extends RenUSubstBase(subsDefsInput) {

  /** whether to use semantic renaming */
  private val semantic: Boolean = true // @todo check impact
  // @note explicit implementation to make RenUSubst equality independent of rens/subsDefs order
  override def equals(e: Any): Boolean = e match {
    case a: URenAboveUSubst => rens.toSet == a.rens.toSet && subsDefs.toSet == a.subsDefs.toSet
    // rens == a.rens && subsDefs == a.subsDefs
    case _ => false
  }

  override def hashCode: Int = 61 * rens.hashCode() + subsDefs.hashCode()

  def reapply(subs: immutable.Seq[(Expression, Expression)]) = new URenAboveUSubst(subs)

  // backwards style: compose US after renaming to get the same Hilbert proof order as in toForward: US above UR
  // rens.foldLeft(replaced)((pr,sp)=>UniformRenaming.UniformRenamingForward(pr, sp._1,sp._2))
  def toTactic(form: Sequent): BelleExpr =
    throw new UnsupportedOperationException(
      "not implemented"
    ) // @todo ProofRuleTactics.US(usubst, RenUSubst(rens)(form)) & getRenamingTactic

  /** Convert to forward tactic using the respective uniform renaming and uniform substitution rules */
  def toForward: ProvableSig => ProvableSig = fact => {
    /*UniformSubstitutionRule.UniformSubstitutionRuleForward*/
    (rens.foldLeft(fact)((pr, sp) => RenUSubst.UniformRenamingForward(pr, sp._1, sp._2)))(usubst)
  }

  val toCore = (e: Expression) => throw new UnsupportedOperationException("not yet implemented. @todo")

  private[infrastruct] def firstFlush: RenUSubst = substitution

  override def toString: String = super.toString + "URenAboveUSubst"

  // @todo could optimize empty usubst or empty rens to be just identity application right away
  def apply(t: Term): Term =
    try { usubst(rens.foldLeft(t)((e, sp) => URename(sp._1, sp._2, semantic)(e))) }
    catch { case ex: ProverException => throw ex.inContext(t.prettyString) }

  def apply(f: Formula): Formula =
    try { usubst(rens.foldLeft(f)((e, sp) => URename(sp._1, sp._2, semantic)(e))) }
    catch { case ex: ProverException => throw ex.inContext(f.prettyString) }

  def apply(p: Program): Program =
    try { usubst(rens.foldLeft(p)((e, sp) => URename(sp._1, sp._2, semantic)(e))) }
    catch { case ex: ProverException => throw ex.inContext(p.prettyString) }

  def apply(p: DifferentialProgram): DifferentialProgram =
    try { usubst(rens.foldLeft(p)((e, sp) => URename(sp._1, sp._2, semantic)(e))) }
    catch { case ex: ProverException => throw ex.inContext(p.prettyString) }
}

/**
 * Fast implementation of: Renaming Uniform Substitution that, in goal-directed backwards Sequent direction, first runs
 * a uniform substitution below and on the result subsequently the uniform renaming above it.
 * {{{
 *   R(s(G)) |- R(s(D))
 *   ------------------ URen
 *      s(G) |- s(D)
 *   ------------------ USubst
 *        G  |- D
 * }}}
 * The direct application mechanism via [[apply()]] fast-forwards to the fast joint [[USubstRen]] infrastructure. Its
 * tactical / prover core implementation works in sync using prover core operations by scheduling separate uniform
 * substitutions and uniform renamings to the core when asked.
 *
 * Cleverly exploits semantic renaming on Provables on demand (although not in full generality yet).
 *
 * @param subsDefsInput
 * @note
 *   reading in Hilbert direction from top to bottom, the uniform renaming comes abiove first then the subsequent
 *   uniform substitution comes below as second.
 * @see
 *   [[USubstRen]]
 * @invariant
 *   subsDefsInput==subsDefsInput.distinct preserved if initially true
 * @author
 *   Andre Platzer
 */
// US: uniform substitution to instantiate all symbols especially program constants to become renamable
// UR: uniform renaming to rename preexisting variables to the present axioms
final class FastURenAboveUSubst(private[infrastruct] val subsDefsInput: immutable.Seq[(Expression, Expression)])
    extends RenUSubst {
  // @note explicit implementation to make RenUSubst equality independent of rens/subsDefs order
  override def equals(e: Any): Boolean = e match {
    case a: FastURenAboveUSubst => subsDefsInput.toSet == a.subsDefsInput.toSet
    case _ => false
  }

  override def hashCode: Int = 271 * subsDefsInput.hashCode()

  override def reapply(subs: immutable.Seq[(Expression, Expression)]) = new FastURenAboveUSubst(subs)

  /** The effective USubstRen for subsDefsInput. */
  private val effective: USubstRen = USubstRen(subsDefsInput)

  /** Renaming part, with identity renaming no-ops filtered out. */
  private lazy val rens: immutable.Seq[(Variable, Variable)] = RenUSubst.renamingPartOnly(subsDefsInput)

  /** Substitution part, with identity substitution no-ops filtered out later in USubst(...). */
  private lazy val subsDefs: immutable.Seq[SubstitutionPair] =
    try {
      subsDefsInput
        .filterNot(sp => sp._1.isInstanceOf[Variable])
        .map(sp =>
          try { SubstitutionPair(sp._1, sp._2) }
          catch { case ex: ProverException => throw ex.inContext("(" + sp._1 + "~>" + sp._2 + ")") }
        )
    } catch {
      case ex: ProverException => throw ex.inContext("FastURenAboveUSubst{" + subsDefsInput.mkString(", ") + "}")
    }

  /** All renamings at once */
  private lazy val renall: MultiRename = MultiRename(rens)

  override lazy val usubst: USubst = USubst(subsDefs)
  override lazy val renaming: RenUSubst = reapply(rens)
  override lazy val getRenamingTactic: BelleExpr =
    throw new Error("not implemented") /*rens.foldLeft[BelleExpr](Idioms.ident)((t,sp)=> t &
    //@note for tableaux backward style, the renamings have to be reversed to get from (already renamed) conclusion back to (prerenamed) origin
    //@note permutations would help simplify matters here since they are their own inverse.
    TactixLibrary.uniformRename(sp._2, sp._1))*/
  override lazy val substitution: RenUSubst = reapply(subsDefs.map(sp => (sp.what, sp.repl)))

  /*
   * {{{
   *   R(s(G)) |- R(s(D))
   *   ------------------ URen
   *      s(G) |- s(D)
   *   ------------------ USubst
   *        G  |- D
   * }}}
   */
  override lazy val toForward: ProvableSig => ProvableSig = {
    Predef.assert(rens.toMap.keySet.intersect(rens.toMap.values.toSet).isEmpty, "no cyclic renaming")
    fact => {
      val renamedFact =
        if (fact.isProved) rens.foldLeft(fact)((pr, sp) => pr(URename(sp._1, sp._2, true)))
        else rens.foldLeft(fact)((pr, sp) => RenUSubst.UniformRenamingForward(pr, sp._1, sp._2))
      // @note renall not needed in usubst replacements, because simultaneous effect comes after having renamed above
      renamedFact(usubst)
    }
  }

  override lazy val toCore: Expression => Expression = e => {
    val replaced = usubst(e)
    Predef.assert(rens.toMap.keySet.intersect(rens.toMap.values.toSet).isEmpty, "no cyclic renaming")
    // forward style: first US fact to get rid of program constants, then uniformly rename variables in the result
    // rens.foldLeft(replaced)((expr,sp)=>URename(sp._1,sp._2)(expr))
    renall.toCore(replaced)
  }

  override def toString: String = "FastUSubstAboveRen{" + subsDefs.mkString(", ") + ";" +
    rens.map(sp => sp._1.prettyString + "~~>" + sp._2.prettyString).mkString(", ") + "}"

  // direct application mechanism literally via [[USubstRen.apply]]

  // @todo could optimize empty subsDefsInput to be just identity application right away
  override def apply(t: Term): Term = new Ensures({ effective(t) }) ensures
    (
      r => sameAsCore(t, r),
      "fast tactical renaming substitution has same result as slower core, if defined: " + this + " on " + t,
    )

  override def apply(f: Formula): Formula = new Ensures({ effective(f) }) ensures
    (
      r => sameAsCore(f, r),
      "fast tactical renaming substitution has same result as slower core, if defined: " + this + " on " + f,
    )

  override def apply(p: Program): Program = new Ensures({ effective(p) }) ensures
    (
      r => sameAsCore(p, r),
      "fast tactical renaming substitution has same result as slower core, if defined: " + this + " on " + p,
    )

  override def apply(p: DifferentialProgram): DifferentialProgram = new Ensures({ effective(p) }) ensures
    (
      r => sameAsCore(p, r),
      "fast tactical renaming substitution has same result as slower core, if defined: " + this + " on " + p,
    )

  /** Check that same result as from core if both defined */
  private def sameAsCore(e: Expression, r: Expression): Boolean = {
    if (Matcher.REVERIFY)
      try {
        if (r == toCore(e)) true
        else {
          Predef.print(
            "fast result: " + r + "\ncore result: " + toCore(e) + "\nrenusubst:   " + this + "\neffective:   " +
              effective + "\napplied to:  " + e
          )
          false
        }
      } catch {
        // the core refuses semantic renaming so cannot compare
        case ignore: RenamingClashException => true
      }
    else true
  }
}
