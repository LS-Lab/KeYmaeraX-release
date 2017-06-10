/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.pt

import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.immutable
import scala.collection.immutable.IndexedSeq

/**
  * A common signature for [[edu.cmu.cs.ls.keymaerax.pt.ProvableSig]]'s and [[PTProvable]]'s for use in the [[btactics]] package.
  * This allows for tactics to construct proof terms or not.
  *
  * @author Nathan Fulton
  */
trait ProvableSig {
  val underlyingProvable : Provable = this match {
    case PTProvable(child, pt) => child.underlyingProvable
    case NoProofTermProvable(provable) => provable
  }

  /* The number of steps performed to create this provable. */
  def steps: Int = 0

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

  val axioms: Map[String, ProvableSig]

  val rules: immutable.Map[String, ProvableSig]

  def startProof(goal : Sequent): ProvableSig

  def startProof(goal : Formula): ProvableSig

  def proveArithmetic(t: QETool, f: Formula): Lemma

  def prettyString: String
}
object ProvableSig {
  var PROOF_TERMS_ENABLED = false

  val axiom: immutable.Map[String, Formula] = Provable.axiom

  val axioms: immutable.Map[String, ProvableSig] =
    if(PROOF_TERMS_ENABLED) PTProvable.axioms else NoProofTermProvable.axioms

  val rules: immutable.Map[String, ProvableSig] =
    if(PROOF_TERMS_ENABLED) PTProvable.rules else NoProofTermProvable.rules

  def startProof(goal : Sequent): ProvableSig =
    if(PROOF_TERMS_ENABLED) PTProvable.startProof(goal) else NoProofTermProvable.startProof(goal)

  def startProof(goal : Formula): ProvableSig =
    if(PROOF_TERMS_ENABLED) PTProvable.startProof(goal) else NoProofTermProvable.startProof(goal)

  def proveArithmetic(t: QETool, f: Formula): Lemma =
    if(PROOF_TERMS_ENABLED) PTProvable.proveArithmetic(t,f) else Provable.proveArithmetic(t,f)
}

case class NoProofTermProvable(provable: Provable) extends ProvableSig {
  override val conclusion: Sequent = provable.conclusion
  override val subgoals: IndexedSeq[Sequent] = provable.subgoals

  override def proved: Sequent = provable.proved

  override val axioms: Map[String, ProvableSig] = NoProofTermProvable.axioms
  override val rules: Map[String, ProvableSig] = NoProofTermProvable.rules

  override def apply(rule: Rule, subgoal: Subgoal): ProvableSig = NoProofTermProvable(provable(rule,subgoal), steps+1)

  override def apply(subderivation: ProvableSig, subgoal: Subgoal): ProvableSig =
    NoProofTermProvable(provable(subderivation.underlyingProvable, subgoal), steps+subderivation.steps)

  override def apply(subst: USubst): ProvableSig = NoProofTermProvable(provable(subst), steps+1)

  override def apply(newConsequence: Sequent, rule: Rule): ProvableSig = NoProofTermProvable(provable(newConsequence, rule), steps+1)

  override def apply(prolongation: ProvableSig): ProvableSig = NoProofTermProvable(provable(prolongation.underlyingProvable), steps+prolongation.steps)

  override def sub(subgoal: Subgoal): ProvableSig = NoProofTermProvable(provable.sub(subgoal), steps)

  override def startProof(goal: Sequent): ProvableSig = NoProofTermProvable(Provable.startProof(goal), 0)

  override def startProof(goal: Formula): ProvableSig = NoProofTermProvable(Provable.startProof(goal), 0)

  override def proveArithmetic(t: QETool, f: Formula): Lemma = Provable.proveArithmetic(t,f)

  override def prettyString: String = s"NoProofTermProvable(${provable.prettyString})"
}
object NoProofTermProvable {
  val axioms: Map[String, ProvableSig] = Provable.axioms.map(kvp => (kvp._1, NoProofTermProvable(kvp._2, 0)))
  val rules: Map[String, ProvableSig] = Provable.rules.map(kvp => (kvp._1, NoProofTermProvable(kvp._2, 0)))

  def apply(provable: Provable, initSteps: Int): NoProofTermProvable = new NoProofTermProvable(provable) { override def steps: Int = initSteps }

  def startProof(goal: Sequent): ProvableSig = NoProofTermProvable(Provable.startProof(goal), 0)

  def startProof(goal: Formula): ProvableSig = NoProofTermProvable(Provable.startProof(goal), 0)

  def proveArithmetic(t: QETool, f: Formula): Lemma = Provable.proveArithmetic(t,f)
}

/**
  * PTProvable has the same signature as Provable, but constructs proof terms alongside Provables.
  * @author Nathan Fulton
  */
case class PTProvable(provable: ProvableSig, pt: ProofTerm) extends ProvableSig {
  override val conclusion: Sequent = provable.conclusion
  override val subgoals: IndexedSeq[Sequent] = provable.subgoals

  override def proved: Sequent = provable.proved //@todo should we also check whether pt proof-checks?

  override def apply(rule: Rule, subgoal: Subgoal): ProvableSig =
    PTProvable(provable(rule, subgoal), RuleApplication(pt, rule.name, subgoal))

  override def apply(subderivation: ProvableSig, subgoal: Subgoal): ProvableSig = subderivation match {
    case subprovable: ProvableSig => ???
    case PTProvable(subProvable, subPT) => PTProvable(provable(subProvable, subgoal), subPT)
  }

  override def apply(subst: USubst): ProvableSig =
    PTProvable(provable(subst), UsubstProvableTerm(pt, subst))

  override def apply(newConsequence: Sequent, rule: Rule): ProvableSig =
    PTProvable(provable(newConsequence, rule), ForwardNewConsequenceTerm(pt, newConsequence, rule))

  override def apply(prolongation: ProvableSig): ProvableSig = prolongation match {
    case subProvable: ProvableSig => ???
    case prolongationProof: PTProvable => PTProvable(prolongationProof.provable(prolongation), ProlongationTerm(pt, prolongationProof))
  }

  override def sub(subgoal: Subgoal): ProvableSig =
    PTProvable(provable.sub(subgoal), NoProof())

  val axioms: immutable.Map[String, ProvableSig] = PTProvable.axioms

  val rules: immutable.Map[String, ProvableSig] = PTProvable.rules

  def startProof(goal : Sequent): ProvableSig = PTProvable.startProof(goal)

  def startProof(goal : Formula): ProvableSig = PTProvable.startProof(goal)

  def proveArithmetic(t: QETool, f: Formula): Lemma = PTProvable.proveArithmetic(t,f)

  override def toString: String = s"PTProvable(${provable.toString}, ${pt.toString})"

  override def prettyString: String = s"PTProvable(${provable.prettyString}, ${pt.prettyString})"
}

object PTProvable {
  val axioms: immutable.Map[String, ProvableSig] = Provable.axioms.map(x => (x._1, PTProvable(x._2.asInstanceOf[ProvableSig], AxiomTerm(x._1))))

  val rules: immutable.Map[String, ProvableSig] = Provable.rules.map(x => (x._1, PTProvable(x._2.asInstanceOf[ProvableSig], RuleTerm(x._1))))

  def startProof(goal : Sequent): ProvableSig = PTProvable(NoProofTermProvable.startProof(goal), NoProof())

  def startProof(goal : Formula): ProvableSig = PTProvable(NoProofTermProvable.startProof(goal), NoProof())

  def proveArithmetic(t: QETool, f: Formula): Lemma = ??? //@todo after changing everything to ProvableSig's, then create a lemma with an PTProvable.
}
