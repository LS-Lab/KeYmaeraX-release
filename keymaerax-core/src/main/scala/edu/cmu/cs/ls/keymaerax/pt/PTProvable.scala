/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.pt

import edu.cmu.cs.ls.keymaerax.core._

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

  val axiom: immutable.Map[String, Formula] = Provable.axiom

  val axioms: immutable.Map[String, ProvableSig]

  val rules: immutable.Map[String, ProvableSig]

  def startProof(goal : Sequent): ProvableSig

  def startProof(goal : Formula): ProvableSig

  def proveArithmetic(t: QETool, f: Formula): Lemma

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
    PTProvable(provable(rule, subgoal), RuleApplication(pt, rule.name, subgoal))

  override def apply(subderivation: ProvableSig, subgoal: Subgoal): ProvableSig = subderivation match {
    case subprovable:Provable => ???
    case PTProvable(subProvable, subPT) => PTProvable(provable(subProvable, subgoal), subPT)
  }

  override def apply(subst: USubst): ProvableSig =
    PTProvable(provable(subst), UsubstProvableTerm(pt, subst))

  override def apply(newConsequence: Sequent, rule: Rule): ProvableSig =
    PTProvable(provable(newConsequence, rule), ForwardNewConsequenceTerm(pt, newConsequence, rule))

  override def apply(prolongation: ProvableSig): ProvableSig = prolongation match {
    case subProvable: Provable => ???
    case prolongationProof: PTProvable => PTProvable(prolongationProof.provable(prolongation), ProlongationTerm(pt, prolongationProof))
  }

  override def sub(subgoal: Subgoal): ProvableSig =
    PTProvable(provable.sub(subgoal), NoProof())

  val axioms: immutable.Map[String, ProvableSig] = Provable.axioms.map(x => (x._1, PTProvable(x._2.asInstanceOf[Provable], AxiomTerm(x._1))))

  val rules: immutable.Map[String, ProvableSig] = Provable.rules.map(x => (x._1, PTProvable(x._2.asInstanceOf[Provable], RuleTerm(x._1))))

  def startProof(goal : Sequent): ProvableSig = PTProvable(Provable.startProof(goal), NoProof())

  def startProof(goal : Formula): ProvableSig = PTProvable(Provable.startProof(goal), NoProof())

  def proveArithmetic(t: QETool, f: Formula): Lemma = ??? //@todo after changing everything to ProvableSig's, then create a lemma with an PTProvable.

  override def toString: String = s"PTProvable(${provable.toString}, ${pt.toString})"

  override def prettyString: String = s"PTProvable(${provable.prettyString}, ${pt.prettyString})"
}
