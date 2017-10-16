/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.pt

import edu.cmu.cs.ls.keymaerax.btactics.{DerivationInfo, ProvableInfo}
import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.immutable
import scala.collection.immutable.IndexedSeq

/**
  * A common signature for [[edu.cmu.cs.ls.keymaerax.pt.ProvableSig]]'s and [[PTProvable]]'s for use in the [[btactics]] package.
  * This allows for tactics to construct proof terms or not.
  *
  * @author Nathan Fulton
  * @author Brandon Bohrer
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
  var PROOF_TERMS_ENABLED = true

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

/**
 * A direct [[Provable]] straight from the core that does not keep track of its proof term.
 */
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

  override def apply(prolongation: ProvableSig): ProvableSig =
    NoProofTermProvable(provable(prolongation.underlyingProvable), steps+prolongation.steps)

  override def sub(subgoal: Subgoal): ProvableSig = NoProofTermProvable(provable.sub(subgoal), steps)

  override def startProof(goal: Sequent): ProvableSig = NoProofTermProvable(Provable.startProof(goal), 0)

  override def startProof(goal: Formula): ProvableSig = NoProofTermProvable(Provable.startProof(goal), 0)

  override def proveArithmetic(t: QETool, f: Formula): Lemma = Provable.proveArithmetic(t,f)

  override def prettyString: String = provable.prettyString
  //s"NoProofTermProvable(${provable.prettyString})"
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

  override def proved: Sequent = provable.proved

  override def apply(rule: Rule, subgoal: Subgoal): ProvableSig = {
    //@todo do a total pattern match on all rules in the core and produce individualized proof terms for each of them.
    //This is necessary because we need positions where the rule should be applied within the *sequent* in addition to subgoal,
    //which is the position within the *provable*. Alternatively a subtype heirarchy for Rule would do the trick...
    val sequentPositions = rule match {
        // @TODO: double-check index funtimes
      case Close(ante,succ) => -(ante.getIndex + 1) :: (succ.getIndex + 1) :: Nil
      case CoHide2(ante, succ)  => -(ante.getIndex + 1) :: (succ.getIndex + 1) :: Nil
      case CutRight(fml, succ) => succ.getIndex + 1 :: Nil
      case ImplyRight(succ) => succ.getIndex + 1 :: Nil
      case AndRight(succ) => succ.getIndex + 1 :: Nil
      case CoHideRight(succ) => succ.getIndex + 1 :: Nil
      case CommuteEquivRight(succ) => succ.getIndex + 1 :: Nil
      case EquivifyRight(succ) => succ.getIndex + 1 :: Nil
      case EquivRight(succ) => succ.getIndex + 1 :: Nil
      case NotRight(succ) => succ.getIndex + 1 :: Nil
      case CloseTrue(succ) => succ.getIndex + 1 :: Nil
      case HideRight(succ) => succ.getIndex + 1 :: Nil
      case OrRight(succ) => succ.getIndex + 1 :: Nil

      case OrLeft(ante) => -(ante.getIndex + 1) :: Nil
      case AndLeft(ante) => -(ante.getIndex + 1) :: Nil
      case HideLeft(ante) => -(ante.getIndex + 1) :: Nil
      case CutLeft(fml,ante) => -(ante.getIndex + 1) :: Nil
      case ImplyLeft(ante) => -(ante.getIndex + 1) :: Nil
      case NotLeft(ante) => -(ante.getIndex + 1) :: Nil
      case EquivLeft(ante) => -(ante.getIndex + 1) :: Nil
      case CloseFalse(ante) => -(ante.getIndex + 1) :: Nil

      case BoundRenaming(what, repl, ante:AntePos) => -(ante.getIndex + 1) :: Nil
      case BoundRenaming(what, repl, succ:SuccPos) => -(succ.getIndex + 1) :: Nil
      case Skolemize(ante:AntePos) => -(ante.getIndex + 1) :: Nil
      case Skolemize(succ:SuccPos) => -(succ.getIndex + 1) :: Nil

      case UniformRenaming(what, repl) => Nil
      case Cut(fml) => Nil

      case _ =>
        throw new Exception(s"PTProvable.apply(Rule,provable pos) is not completely implemented. Missing case: ${rule.name}") //See @todo above add cases as necessary...
    }
    PTProvable(provable(rule, subgoal), RuleApplication(pt, rule.name, subgoal, sequentPositions))
  }


  override def apply(subderivation: ProvableSig, subgoal: Subgoal): ProvableSig = subderivation match {
    case PTProvable(subProvable, subPT) => PTProvable(provable(subProvable, subgoal), subPT)
    case subprovable: ProvableSig => {
      //Find an axiom or rule with the same name.
      // @TODO: Add derived axioms
      val coreAxiom = PTProvable.axioms.find(p => p._2.underlyingProvable == subprovable.underlyingProvable)
      val infos = ProvableInfo.allInfo
      val derivedAxiom = infos.find(info => info.provable.underlyingProvable == subprovable.underlyingProvable)
      val rule = PTProvable.rules.find(p => p._2.underlyingProvable == subprovable.underlyingProvable)

      //If such an axiom exists, create evidence using the axiom's associated proof certificate.
      if(coreAxiom.isDefined) {
        val PTProvable(subProvable, subPT) = PTProvable.axioms(coreAxiom.get._1)
        PTProvable(provable(subProvable, subgoal), subPT)
      } else if (derivedAxiom.isDefined) {
        val term = AxiomTerm(derivedAxiom.get.codeName)
        val axiomPT = PTProvable(NoProofTermProvable(derivedAxiom.get.provable.underlyingProvable), term)
        PTProvable(provable(subprovable, subgoal), term)
      }
      //And ditto for rules.
      else if(rule.isDefined) {
        val PTProvable(subProvable, subPT) = PTProvable.rules(rule.get._1)
        PTProvable(provable(subProvable, subgoal), subPT)
      }
      else {
        //For more complicated uses of useAt, by, etc. it's unclear what to do (and indeed the general architecture is problematic -- same reason that extraction works by the miracle of hard work aone).
        throw new Exception(s"Cannot construct a proof term for ${subderivation} because it has no associated proof term.")
      }
    }
  }

  override def apply(subst: USubst): ProvableSig =
    PTProvable(provable(subst), UsubstProvableTerm(pt, subst))

  override def apply(newConsequence: Sequent, rule: Rule): ProvableSig =
    PTProvable(provable(newConsequence, rule), ForwardNewConsequenceTerm(pt, newConsequence, rule))

  override def apply(prolongation: ProvableSig): ProvableSig = prolongation match {
    case prolongationProof: PTProvable =>
      PTProvable(provable(prolongationProof), ProlongationTerm(pt, prolongationProof))
    case subProvable: ProvableSig =>
      /* @TODO: Arguable this should just not be allowed and represents a bug elsewhere */
      PTProvable(NoProofTermProvable(provable.underlyingProvable(subProvable.underlyingProvable)), ProlongationTerm(pt, PTProvable(subProvable, NoProof())))
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
  val axioms: immutable.Map[String, ProvableSig] = Provable.axioms.map(x => (x._1, PTProvable(NoProofTermProvable.axioms.apply(x._1), AxiomTerm(x._1))))

  val rules: immutable.Map[String, ProvableSig] = Provable.rules.map(x => (x._1, PTProvable(NoProofTermProvable.rules.apply(x._1), RuleTerm(x._1))))

  def startProof(goal : Sequent): ProvableSig = PTProvable(NoProofTermProvable.startProof(goal), NoProof())

  def startProof(goal : Formula): ProvableSig = PTProvable(NoProofTermProvable.startProof(goal), NoProof())

  def proveArithmetic(t: QETool, f: Formula): Lemma = {
    //@todo after changing everything to ProvableSig's, then create a lemma with an PTProvable.
    //@TODO Does this work at all
    //???
    val lem = NoProofTermProvable.proveArithmetic(t,f)
    Lemma(PTProvable(lem.fact, FOLRConstant(f)), lem.evidence, lem.name)
  }

}

