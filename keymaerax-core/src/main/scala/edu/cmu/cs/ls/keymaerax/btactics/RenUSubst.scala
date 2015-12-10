/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, SeqTactic}
import edu.cmu.cs.ls.keymaerax.core._

import scala.Predef.Pair
import scala.collection.immutable
import scala.collection.immutable._

object RenUSubst {
  def apply(subsDefsInput: immutable.Seq[(Expression,Expression)]) = new RenUSubst(subsDefsInput)
  def apply(us: USubst): RenUSubst = new RenUSubst(us.subsDefsInput.
    map(sp=>(sp.what,sp.repl)))
  def apply(us: URename): RenUSubst = new RenUSubst(List((us.what,us.repl)))

  private def renamingPartOnly(subsDefsInput: immutable.Seq[(Expression,Expression)]): immutable.Seq[(Variable,Variable)] =
    subsDefsInput.filter(sp => sp._1.isInstanceOf[Variable]).
      map(sp => (sp._1.asInstanceOf[Variable],sp._2.asInstanceOf[Variable]))
  private[btactics] def renamingPart(subsDefsInput: immutable.Seq[(Expression,Expression)]): RenUSubst =
    new RenUSubst(renamingPartOnly(subsDefsInput))

  /**
   * Occurrences of what symbol the generalized SubstitutionPair sp will be replacing.
   * @return Function/predicate/predicational or DotTerm or (Differential)ProgramConst whose occurrences we will replace.
   */
  private[btactics] def matchKey(sp: (Expression,Expression)): NamedSymbol = sp._1 match {
    case DotTerm => DotTerm
    case Anything => Anything
    //case Nothing => {assert(sp._2 == Nothing, "can replace Nothing only by Nothing, and nothing else"); Nothing} // it makes no sense to substitute Nothing
    case a: DifferentialProgramConst => a
    case a: ProgramConst             => a
    case DotFormula                  => DotFormula
    case PredicationalOf(p: Function, _) => p
    // RenUSubst generalization
    case FuncOf(f: Function, _) => f
    case PredOf(p: Function, _) => p
    case x: Variable => x
    case _ => throw new ProverException("Nonsubstitutable expression " + sp)
  }
  /**
   * The key characteristic expression constituents that this Substitution is matching on.
   * @return union of the matchKeys of all our substitution pairs.
   */
  private[btactics] def matchKeys(subsDefsInput: immutable.Seq[(Expression,Expression)]): immutable.List[NamedSymbol] = {
    subsDefsInput.foldLeft(immutable.List[NamedSymbol]())((a,b)=>a ++ immutable.List(matchKey(b)))
  }

}

/**
 * Renaming Uniform Substitution, combining URename and USubst.
 * Liberal list of SubstitutionPair represented as merely a list of Pair,
 * where the Variable~>Variable replacements are by uniform renaming,
 * followed by the other replacements by uniform substitution.
 * @author Andre Platzer
 * @see [[edu.cmu.cs.ls.keymaerax.core.URename]]
 * @see [[edu.cmu.cs.ls.keymaerax.core.USubst]]
 */
final class RenUSubst(private[btactics] val subsDefsInput: immutable.Seq[(Expression,Expression)]) extends (Expression => Expression) {
  /** automatically filter out identity substitution no-ops */
  private val rens: immutable.Seq[(Variable,Variable)] = RenUSubst.renamingPartOnly(subsDefsInput)
  private val subsDefs: immutable.Seq[SubstitutionPair] = try {subsDefsInput.filterNot(sp => sp._1.isInstanceOf[Variable]).
    map(sp => try {SubstitutionPair(sp._1, sp._2)} catch {case ex: ProverException => throw ex.inContext("(" + sp._1 + "~>" + sp._2 + ")")})
  } catch {case ex: ProverException => throw ex.inContext("RenUSubst{" + subsDefsInput.mkString(", ") + "}")}

  //@note order to ensure toString already works in error message
  applicable()
  /** unique left hand sides in subsDefs */
  private def applicable(): Unit = {
    // check that we never replace n by something and then again replacing the same n by something
    val lefts: List[Expression] = subsDefsInput.map(_._1).toList
    if (lefts.distinct.size != lefts.size) throw new ProverException("no duplicate substitutions with same substitutees\n" + this)
  }

  //@note explicit implementation to make RenUSubst equality independent of rens/subsDefs order
  override def equals(e: Any): Boolean = e match {
    case a: RenUSubst => rens == a.rens && subsDefs == a.subsDefs
    case _ => false
  }

  override def hashCode: Int = 47 * rens.hashCode() + subsDefs.hashCode()

  /**
   * The uniform substitution part of this renaming uniform substitution
   * @see [[substitution]]
   * @note lazy val and postponing applicable() until actual use case would make it possible for useAt(inst) to modify before exception. Not sure that's worth it though.
   */
  lazy val usubst = USubst(subsDefs)

  /** Union of renaming uniform substitutions, i.e., both replacement lists merged. */
  def ++(other: RenUSubst): RenUSubst = RenUSubst(this.subsDefsInput ++ other.subsDefsInput)


  type RenUSubstRepl = (Expression,Expression)

  /** The uniform renaming part of this renaming uniform substitution */
  def renaming: RenUSubst = RenUSubst(rens)

  /**
   * The uniform substitution part of this renaming uniform substitution
   * @see [[usubst]]
   */
  def substitution: RenUSubst = RenUSubst(subsDefs.map(sp => Pair(sp.what, sp.repl)))

  /** Convert to tactic to reduce to form by successively using the respective uniform renaming and uniform substitution rules */
  // backwards style: first schedule US and then schedule rename on its result
  def toTactic(form: Sequent): SeqTactic = ProofRuleTactics.US(usubst, RenUSubst(rens)(form)) & getRenamingTactic

  /** Convert to forward tactic using the respective uniform renaming and uniform substitution rules */
  def toForward: Provable => Provable = fact => {
    //Predef.require(rens.isEmpty, "renaming conversion not yet implemented")
    // forward style: first rename fact, then US the result
    UniformSubstitutionRule.UniformSubstitutionRuleForward(
      rens.foldLeft(fact)((pr,sp)=>UniformRenaming.UniformRenamingForward(pr, sp._1,sp._2))
      ,
      usubst)
  }

  /** Get the renaming tactic part */
  def getRenamingTactic: BelleExpr = rens.foldLeft[BelleExpr](Idioms.ident)((t,sp)=> t &
    //@note for tableaux backward style, the renamings have to be reversed to get from (already renamed) conclusion back to (prerenamed) origin
    //@note permutations would help simplify matters here since they are their own inverse.
    ProofRuleTactics.uniformRenaming(sp._2, sp._1))

  override def toString: String = "RenUSubst{" + rens.map(sp=>sp._1.prettyString + "~~>" + sp._2.prettyString).mkString(", ") + " ; " + subsDefs.mkString(", ") + "}"

  def apply(e: Expression): Expression = e match {
    case t: Term => apply(t)
    case f: Formula => apply(f)
    case p: Program => apply(p)
  }

  def apply(t: Term): Term = try {usubst(rens.foldLeft(t)((e,sp)=>URename(sp._1,sp._2)(e)))} catch {case ex: ProverException => throw ex.inContext(t.prettyString)}

  def apply(f: Formula): Formula = try {usubst(rens.foldLeft(f)((e,sp)=>URename(sp._1,sp._2)(e)))} catch {case ex: ProverException => throw ex.inContext(f.prettyString)}

  def apply(p: Program): Program = try {usubst(rens.foldLeft(p)((e,sp)=>URename(sp._1,sp._2)(e)))} catch {case ex: ProverException => throw ex.inContext(p.prettyString)}

  /**
   * Apply uniform substitution everywhere in the sequent.
   */
  def apply(s: Sequent): Sequent = {
    try {
      //@note mapping apply instead of the equivalent usubst makes sure the exceptions are augmented and the ensuring contracts checked.
      Sequent(s.pref, s.ante.map(apply), s.succ.map(apply))
    } catch {
      case ex: ProverException => throw ex.inContext(s.toString)
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(toString, "undef", "undef", s.toString, "undef", ex.getMessage).initCause(ex)
    }
  }

}
