/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.btactics.{Idioms, ProofRuleTactics}
import edu.cmu.cs.ls.keymaerax.core._

import scala.Predef.Pair
import scala.collection.immutable
import scala.collection.immutable._

object RenUSubst {
  //@note See UniformRenaming.semanticRenaming: This should be false to disallow renaming within semantic constructs. Change to false after adapting tactics.
  private[keymaerax] val semanticRenaming = false && (try {
    URename(Variable("quark"), Variable("quark", Some(5)))(ProgramConst("quarky")) == ProgramConst("quarky")
  } catch { case e: RenamingClashException => false })

  private[bellerophon] val TRANSPOSITION = try {
    URename(Variable("quark"), Variable("quark", Some(5)))(Variable("quark", Some(5))) == Variable("quark")
  } catch { case e: RenamingClashException => false }

  def apply(subsDefsInput: immutable.Seq[(Expression,Expression)]) = if (semanticRenaming)
      new URenAboveUSubst(subsDefsInput)
    else
      new DirectUSubstAboveURen(subsDefsInput)
    //  new USubstAboveURen(subsDefsInput)

  def apply(us: USubst): RenUSubst = apply(us.subsDefsInput.
      map(sp=>(sp.what,sp.repl)))
    def apply(us: URename): RenUSubst = apply(List((us.what,us.repl)))

  private def renamingPartOnly(subsDefsInput: immutable.Seq[(Expression,Expression)]): immutable.Seq[(Variable,Variable)] =
      subsDefsInput.filter(sp => sp._1.isInstanceOf[Variable] && sp._2!=sp._1).
        map(sp => {Predef.assert(sp._2.isInstanceOf[Variable], "Variable renaming expected " + sp + " in " + subsDefsInput);
          (sp._1.asInstanceOf[Variable],sp._2.asInstanceOf[Variable])})
  private[bellerophon] def renamingPart(subsDefsInput: immutable.Seq[(Expression,Expression)]): RenUSubst =
    apply(renamingPartOnly(subsDefsInput))

  /**
   * Occurrences of what symbol the generalized SubstitutionPair sp will be replacing.
   * @return Function/predicate/predicational or DotTerm or (Differential)ProgramConst whose occurrences we will replace.
   */
  private[bellerophon] def matchKey(sp: (Expression,Expression)): NamedSymbol = sp._1 match {
    case DotTerm => DotTerm
    //case Nothing => {assert(sp._2 == Nothing, "can replace Nothing only by Nothing, and nothing else"); Nothing} // it makes no sense to substitute Nothing
    case a: DifferentialProgramConst => a
    case a: ProgramConst             => a
    case DotFormula                  => DotFormula
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
   * @return union of the matchKeys of all our substitution pairs.
   */
  private[bellerophon] def matchKeys(subsDefsInput: immutable.Seq[(Expression,Expression)]): immutable.List[NamedSymbol] = {
    subsDefsInput.foldLeft(immutable.List[NamedSymbol]())((a,b)=>a ++ immutable.List(matchKey(b)))
  }

}


/**
  * Renaming Uniform Substitution, combining URename and USubst.
  * Liberal list of SubstitutionPair represented as merely a list of Pair,
  * where the Variable~>Variable replacements are by uniform renaming,
  * and the other replacements are by uniform substitution.
  * @author Andre Platzer
  * @see [[edu.cmu.cs.ls.keymaerax.core.URename]]
  * @see [[edu.cmu.cs.ls.keymaerax.core.USubst]]
  */
sealed abstract class RenUSubst(private[bellerophon] val subsDefsInput: immutable.Seq[(Expression,Expression)]) extends (Expression => Expression) {
  /** Returns true if there is no replacement. */
  def isEmpty = subsDefsNonId.isEmpty

  /** Identity replaement no-ops filtered out. */
  private[bellerophon] final val subsDefsNonId: immutable.Seq[(Expression,Expression)] = subsDefsInput.filter(sp => sp._1!=sp._2  )
  /** Renaming part, with identity renaming no-ops filtered out. */
  protected final val rens: immutable.Seq[(Variable,Variable)] = RenUSubst.renamingPartOnly(subsDefsNonId)
  /** Substitution part, with identity substitution no-ops filtered out. */
  protected final val subsDefs: immutable.Seq[SubstitutionPair] = try {subsDefsNonId.filterNot(sp => sp._1.isInstanceOf[Variable]).
    map(sp => try {SubstitutionPair(sp._1, sp._2)} catch {case ex: ProverException => throw ex.inContext("(" + sp._1 + "~>" + sp._2 + ")")})
  } catch {case ex: ProverException => throw ex.inContext("RenUSubst{" + subsDefsInput.mkString(", ") + "}")}

  //@note order to ensure toString already works in error message
  applicable()
  /** unique left hand sides in subsDefs */
  private def applicable(): Unit = {
    // check that we never replace n by something and then again replacing the same n by something
    val lefts: List[Expression] = subsDefsInput.map(_._1).toList
    if (lefts.distinct.size != lefts.size) throw new ProverException("conflict: no duplicate substitutions for the same substitutee\n" + "RenUSubst(" + subsDefsInput + ")\n" + this + "\nreplaces: " + lefts)
  }

  /**
    * The uniform substitution part of this renaming uniform substitution
    * @see [[substitution]]
    * @note lazy val and postponing applicable() until actual use case would make it possible for useAt(inst) to modify before exception. Not sure that's worth it though.
    */
  lazy final val usubst = USubst(subsDefs)

  private[bellerophon] def reapply(subsDefs: immutable.Seq[(Expression,Expression)]): RenUSubst


  /** Union of renaming uniform substitutions, i.e., both replacement lists merged. */
  def ++(other: RenUSubst): RenUSubst = reapply((this.subsDefsInput ++ other.subsDefsInput).distinct)


  type RenUSubstRepl = (Expression,Expression)

  /** The uniform renaming part of this renaming uniform substitution */
  def renaming: RenUSubst = reapply(rens)

  /** Get the renaming tactic part */
  def getRenamingTactic: BelleExpr = rens.foldLeft[BelleExpr](Idioms.ident)((t,sp)=> t &
    //@note for tableaux backward style, the renamings have to be reversed to get from (already renamed) conclusion back to (prerenamed) origin
    //@note permutations would help simplify matters here since they are their own inverse.
    ProofRuleTactics.uniformRenaming(sp._2, sp._1))


  /**
    * The uniform substitution part of this renaming uniform substitution
    * @see [[usubst]]
    */
  def substitution: RenUSubst = reapply(subsDefs.map(sp => Pair(sp.what, sp.repl)))

  /** Convert to tactic to reduce to `form` by successively using the respective uniform renaming and uniform substitution rules */
  def toTactic(form: Sequent): SeqTactic

  /** Convert to forward tactic using the respective uniform renaming and uniform substitution rules */
  def toForward: Provable => Provable

  /** This RenUSubst implemented strictly from the core. */
  def toCore: Expression => Expression

  /** The first step that will be performed first toward the bottom of the proof. */
  private[bellerophon] def firstFlush: RenUSubst

  override def toString: String = "RenUSubst{" + rens.map(sp=>sp._1.prettyString + "~~>" + sp._2.prettyString).mkString(", ") + " ; " + subsDefs.mkString(", ") + "}"

  def apply(e: Expression): Expression = e match {
    case t: Term => apply(t)
    case f: Formula => apply(f)
    case p: DifferentialProgram => apply(p)
    case p: Program => apply(p)
  }

  def apply(t: Term): Term
  def apply(f: Formula): Formula
  def apply(p: Program): Program
  def apply(p: DifferentialProgram): DifferentialProgram
  /** Apply everywhere in the sequent. */
  def apply(s: Sequent): Sequent = {
    try {
      //@note mapping apply instead of the equivalent usubst makes sure the exceptions are augmented and the ensuring contracts checked.
      Sequent(s.ante.map(apply), s.succ.map(apply))
    } catch {
      case ex: ProverException => throw ex.inContext(s.toString)
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(toString, "undef", "undef", s.toString, "undef", ex.getMessage).initCause(ex)
    }
  }
}

/**
  * Renaming Uniform Substitution that, in Sequent direction, first runs a uniform renaming and on the result subsequently the uniform substituion.
  * {{{
  *   s(RG) |- s(RD)
  *   -------------- USubst
  *     RG  |- RD
  *   -------------- URen
  *      G  |- D
  * }}}
  * @param subsDefsInput
  * @note reading in Hilbert direction from top to bottom, the uniform substitution comes first to ensure the subsequent uniform renaming no longer has nonrenamable program constants since no semantic renaming.
  */
// US: uniform substitution to instantiate all symbols especially program constants to become renamable
// UR: uniform renaming to rename preexisting variables to the present axioms
final class USubstAboveURen(private[bellerophon] override val subsDefsInput: immutable.Seq[(Expression,Expression)]) extends RenUSubst(subsDefsInput) {
  //@note explicit implementation to make RenUSubst equality independent of rens/subsDefs order
  override def equals(e: Any): Boolean = e match {
    case a: USubstAboveURen => rens.toSet == a.rens.toSet && subsDefs.toSet == a.subsDefs.toSet
      //rens == a.rens && subsDefs == a.subsDefs
    case _ => false
  }

  override def hashCode: Int = 47 * rens.hashCode() + subsDefs.hashCode()

  def reapply(subs: immutable.Seq[(Expression,Expression)]) = new USubstAboveURen(subs)


  // backwards style: compose US after renaming to get the same Hilbert proof order as in toForward: US above UR
  // rens.foldLeft(replaced)((pr,sp)=>UniformRenaming.UniformRenamingForward(pr, sp._1,sp._2))
  def toTactic(form: Sequent): SeqTactic = throw new UnsupportedOperationException("not implemented") //@todo getRenamingTactic & ProofRuleTactics.US(usubst, form)

  def toForward: Provable => Provable = fact => {
    val replaced = fact(usubst)  //UniformSubstitutionRule.UniformSubstitutionRuleForward(fact, usubst)
    // forward style: first US fact to get rid of program constants, then uniformly rename variables in the result
    rens.foldLeft(replaced)((pr,sp)=>UniformRenaming.UniformRenamingForward(pr, sp._1,sp._2))
  }

  def toCore = throw new UnsupportedOperationException("not yet implemented. @todo")

  private[bellerophon] def firstFlush: RenUSubst = renaming

  override def toString: String = super.toString + "USubstAboveRen"

  //@todo could optimize empty usubst or empty rens to be just identity application right away
  def apply(t: Term): Term = try {rens.foldLeft(usubst(t))((e,sp)=>URename(sp._1,sp._2)(e))} catch {case ex: ProverException => throw ex.inContext(t.prettyString, "with " + this)}

  def apply(f: Formula): Formula = try {rens.foldLeft(usubst(f))((e,sp)=>URename(sp._1,sp._2)(e))} catch {case ex: ProverException => throw ex.inContext(f.prettyString, "with " + this)}

  def apply(p: Program): Program = try {rens.foldLeft(usubst(p))((e,sp)=>URename(sp._1,sp._2)(e))} catch {case ex: ProverException => throw ex.inContext(p.prettyString, "with " + this)}

  def apply(p: DifferentialProgram): DifferentialProgram = try {rens.foldLeft(usubst(p))((e,sp)=>URename(sp._1,sp._2)(e))} catch {case ex: ProverException => throw ex.inContext(p.prettyString, "with " + this)}
}

/**
  * Direct implementation of: Renaming Uniform Substitution that, in Sequent direction, first runs a uniform renaming and on the result subsequently the uniform substituion.
  * {{{
  *   s(RG) |- s(RD)
  *   -------------- USubst
  *     RG  |- RD
  *   -------------- URen
  *      G  |- D
  * }}}
  * Semantic renaming may be supported if need be.
  *
  * DirectUSubstAboveURen is a direct implementation in tactics land of a joint renaming and substitution algorithm.
  * It uses a single direct fast [[USubstRen]] for internal applications via [[DirectUSubstAboveURen.apply()]]
  * but schedules separate uniform substitutions and uniform renamings to the core when asked.
  * The first fast pass supports semantic renaming, which is useful during unification to "apply" renamings already to predicationals without clash.
  * The final core pass does not support semantic renaming, but is only needed for the final unifier.
  *
  * @param subsDefsInput
  * @note reading in Hilbert direction from top to bottom, the uniform substitution comes first to ensure the subsequent uniform renaming no longer has nonrenamable program constants since no semantic renaming.
  */
// US: uniform substitution to instantiate all symbols especially program constants to become renamable
// UR: uniform renaming to rename preexisting variables to the present axioms
final class DirectUSubstAboveURen(private[bellerophon] override val subsDefsInput: immutable.Seq[(Expression,Expression)]) extends RenUSubst(subsDefsInput) {
  //@note explicit implementation to make RenUSubst equality independent of rens/subsDefs order
  override def equals(e: Any): Boolean = e match {
    case a: DirectUSubstAboveURen => rens.toSet == a.rens.toSet && subsDefs.toSet == a.subsDefs.toSet
    //rens == a.rens && subsDefs == a.subsDefs
    case _ => false
  }

  override def hashCode: Int = 67 * rens.hashCode() + subsDefs.hashCode()

  def reapply(subs: immutable.Seq[(Expression,Expression)]) = new DirectUSubstAboveURen(subs)


  /** All renamings at once */
  private val renall = MultiRename(rens)
  /** The effective USubstRen consisting of the renaming and the renamed substitution,
    * since the core substitution will be above the core renaming in the end. */
  protected val effective: USubstRen = try {
    USubstRen(rens ++
      (subsDefs.map(sp => try {(sp.what, renall(sp.repl))} catch {case ex: ProverException => throw ex.inContext("(" + sp + ")")}))
    )
  } catch {case ex: ProverException => throw ex.inContext("DirectUSubstAboveURen{" + subsDefsInput.mkString(", ") + "}")}


  // backwards style: compose US after renaming to get the same Hilbert proof order as in toForward: US above UR
  // rens.foldLeft(replaced)((pr,sp)=>UniformRenaming.UniformRenamingForward(pr, sp._1,sp._2))
  def toTactic(form: Sequent): SeqTactic = throw new UnsupportedOperationException("not implemented") //@todo getRenamingTactic & ProofRuleTactics.US(usubst, form)

  def toForward: Provable => Provable = fact => {
    val replaced = fact(usubst)
    // forward style: first US fact to get rid of program constants, then uniformly rename variables in the result
    rens.foldLeft(replaced)((pr,sp)=>UniformRenaming.UniformRenamingForward(pr, sp._1,sp._2))
  }

  def toCore: Expression => Expression = e => {
    val replaced = usubst(e)
    // forward style: first US fact to get rid of program constants, then uniformly rename variables in the result
    rens.foldLeft(replaced)((expr,sp)=>URename(sp._1,sp._2)(expr))
  }

  private[bellerophon] def firstFlush: RenUSubst = renaming

  override def toString: String = super.toString + "DirectUSubstAboveRen"

  //@todo could optimize empty usubst or empty rens to be just identity application right away
  def apply(t: Term): Term = effective(t)

  def apply(f: Formula): Formula = effective(f)

  def apply(p: Program): Program = effective(p)

  def apply(p: DifferentialProgram): DifferentialProgram = effective(p)
}


/**
  * Renaming Uniform Substitution that, in Sequent direction, first runs a uniform substitution and on the result subsequently the uniform renaming.
  * {{{
  *   R(s(G)) |- R(s(D))
  *   ------------------ URen
  *      s(G) |- s(D)
  *   ------------------ USubst
  *        G  |- D
  * }}}
  * @param subsDefsInput
  */
final class URenAboveUSubst(private[bellerophon] override val subsDefsInput: immutable.Seq[(Expression,Expression)]) extends RenUSubst(subsDefsInput) {
  //@note explicit implementation to make RenUSubst equality independent of rens/subsDefs order
  override def equals(e: Any): Boolean = e match {
    case a: URenAboveUSubst => rens.toSet == a.rens.toSet && subsDefs.toSet == a.subsDefs.toSet
      // rens == a.rens && subsDefs == a.subsDefs
    case _ => false
  }

  override def hashCode: Int = 61 * rens.hashCode() + subsDefs.hashCode()

  def reapply(subs: immutable.Seq[(Expression,Expression)]) = new URenAboveUSubst(subs)


  // backwards style: compose US after renaming to get the same Hilbert proof order as in toForward: US above UR
  // rens.foldLeft(replaced)((pr,sp)=>UniformRenaming.UniformRenamingForward(pr, sp._1,sp._2))
  def toTactic(form: Sequent): SeqTactic = throw new UnsupportedOperationException("not implemented") //@todo ProofRuleTactics.US(usubst, RenUSubst(rens)(form)) & getRenamingTactic

  /** Convert to forward tactic using the respective uniform renaming and uniform substitution rules */
  def toForward: Provable => Provable = fact => {
    /*UniformSubstitutionRule.UniformSubstitutionRuleForward*/
      (rens.foldLeft(fact)((pr,sp)=>UniformRenaming.UniformRenamingForward(pr, sp._1,sp._2))) (usubst)
  }

  def toCore = throw new UnsupportedOperationException("not yet implemented. @todo")

  private[bellerophon] def firstFlush: RenUSubst = substitution

  override def toString: String = super.toString + "URenAboveUSubst"

  //@todo could optimize empty usubst or empty rens to be just identity application right away
  def apply(t: Term): Term = try {usubst(rens.foldLeft(t)((e,sp)=>URename(sp._1,sp._2)(e)))} catch {case ex: ProverException => throw ex.inContext(t.prettyString)}

  def apply(f: Formula): Formula = try {usubst(rens.foldLeft(f)((e,sp)=>URename(sp._1,sp._2)(e)))} catch {case ex: ProverException => throw ex.inContext(f.prettyString)}

  def apply(p: Program): Program = try {usubst(rens.foldLeft(p)((e,sp)=>URename(sp._1,sp._2)(e)))} catch {case ex: ProverException => throw ex.inContext(p.prettyString)}

  def apply(p: DifferentialProgram): DifferentialProgram = try {usubst(rens.foldLeft(p)((e,sp)=>URename(sp._1,sp._2)(e)))} catch {case ex: ProverException => throw ex.inContext(p.prettyString)}
}

