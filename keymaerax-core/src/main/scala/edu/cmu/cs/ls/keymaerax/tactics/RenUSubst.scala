/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.tactics.Tactics.Tactic

import scala.Predef.Pair
import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.immutable
import scala.collection.immutable._

/**
 * Renaming Uniform Substitution, combining URename and USubst.
 * Liberal list of SubstitutionPair represented as merely a list of Pair,
 * where the Variable~>Variable replacements are by uniform renaming,
 * followed by the other replacements by uniform substitution.
 * @author Andre Platzer
 * @see [[edu.cmu.cs.ls.keymaerax.core.URename]]
 * @see [[edu.cmu.cs.ls.keymaerax.core.USubst]]
 */
final case class RenUSubst(subsDefsInput: immutable.Seq[Pair[Expression,Expression]]) extends (Expression => Expression) {
  /** automatically filter out identity substitution no-ops */
  private val rens: immutable.Seq[Pair[Variable,Variable]] = subsDefsInput.filter(sp => sp._1.isInstanceOf[Variable]).
    map(sp => (sp._1.asInstanceOf[Variable],sp._2.asInstanceOf[Variable]))
  private val subsDefs: immutable.Seq[SubstitutionPair] = subsDefsInput.filterNot(sp => sp._1.isInstanceOf[Variable]).
    map(sp => SubstitutionPair(sp._1, sp._2))
  /**
   * The uniform substitution part of this renaming uniform substitution
   * @see [[substitution]]
   */
  val usubst = USubst(subsDefs)

  type RenUSubstRepl = Pair[Expression,Expression]

  /** The uniform renaming part of this renaming uniform substitution */
  def renaming: RenUSubst = RenUSubst(rens)

  /**
   * The uniform substitution part of this renaming uniform substitution
   * @see [[usubst]]
   */
  def substitution: RenUSubst = RenUSubst(subsDefs.map(sp => Pair(sp.what, sp.repl)))

  /** Convert to tactic to reduce to form by successively using the respective uniform renaming and uniform substitution rules */
  def toTactic(form: Sequent): Tactic = getUSubstTactic(RenUSubst(rens)(form)) & getRenamingTactic

  /** Get the renaming tactic part */
  def getRenamingTactic: Tactic = rens.foldLeft(TactixLibrary.skip)((t,sp)=> t &
    //@note for tableaux backward style, the renamings have to be reversed to get from (already renamed) conclusion back to (prerenamed) origin
    //@note permutations would help simplify matters here since they are their own inverse.
    new Tactics.ApplyRule(UniformRenaming(sp._2, sp._1)) {
      override def applicable(node: ProofNode): Boolean = true
    })

  /** Get the uniform substitution tactic part to reduce to form */
  def getUSubstTactic(form: Sequent): Tactic = new Tactics.ApplyRule(UniformSubstitutionRule(usubst, form)) {
    override def applicable(node: ProofNode): Boolean = true
  }

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
