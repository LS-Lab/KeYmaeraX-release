/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.pt

import edu.cmu.cs.ls.keymaerax.core.{Provable, Rule, Sequent, USubst}

import scala.collection.immutable
import scala.collection.immutable.IndexedSeq

/**
  * A common signature for [[edu.cmu.cs.ls.keymaerax.core.Provable]]'s and [[PTProvable]]'s for use in the [[btactics]] package.
  * This allows for tactics to construct proof terms or not.
  * @author Nathan Fulton
  */
trait ProvableSig {
  type Subgoal = Int
  val conclusion: Sequent

  val subgoals: immutable.IndexedSeq[Sequent]

  def isProved: Boolean = subgoals.isEmpty

  def proved: Sequent

  def apply(rule: Rule, subgoal: Subgoal): ProvableSig

  def apply(subderivation: ProvableSig, subgoal: Subgoal): ProvableSig

  def apply(subst: USubst): ProvableSig

  def apply(newConsequence: Sequent, rule: Rule): ProvableSig

  def apply(prolongation: ProvableSig): ProvableSig

  def sub(subgoal: Subgoal): ProvableSig

  def prettyString: String
}

/**
  * PTProvable has the same signature as Provable, but constructs proof terms alongside Provables.
  * @author Nathan Fulton
  */
case class PTProvable(provable: Provable, pt: ProofTerm) extends ProvableSig {
  override val conclusion: Sequent = provable.conclusion
  override val subgoals: IndexedSeq[Sequent] = provable.subgoals

  override def proved: Sequent = provable.proved //@todo should we also check whether pt proof-checks?

  override def apply(rule: Rule, subgoal: Subgoal): ProvableSig =
    PTProvable(provable(rule, subgoal), ???)

  override def apply(subderivation: ProvableSig, subgoal: Subgoal): ProvableSig = subderivation match {
    case subprovable:Provable => PTProvable(provable(subprovable, subgoal), ???) //@todo throw exception?
    case PTProvable(subProvable, subPT) => PTProvable(provable(subProvable, subgoal), subPT)
  }

  override def apply(subst: USubst): ProvableSig =
    PTProvable(provable(subst), ???)

  override def apply(newConsequence: Sequent, rule: Rule): ProvableSig =
    PTProvable(provable(newConsequence, rule), ???)

  override def apply(prolongation: ProvableSig): ProvableSig = prolongation match {
    case subProvable: Provable => ???
    case PTProvable(subProvable, subPT) => PTProvable(provable(subProvable), subPT)
  }

  override def sub(subgoal: Subgoal): ProvableSig =
    PTProvable(provable.sub(subgoal), ???)

  override def toString: String = s"PTProvable(${provable.toString}, ${pt.toString})"

  override def prettyString: String = s"PTProvable(${provable.prettyString}, ${pt.prettyString})"
}
