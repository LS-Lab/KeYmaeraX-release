/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.pt

import edu.cmu.cs.ls.keymaerax.{Configuration, Logging}
import edu.cmu.cs.ls.keymaerax.btactics.macros._
import DerivationInfoAugmentors._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.lemma.Lemma

import scala.collection.immutable
import scala.collection.immutable.IndexedSeq

/**
  * A common signature for [[edu.cmu.cs.ls.keymaerax.pt.ProvableSig]]'s and [[TermProvable]]'s for use in the [[btactics]] package.
  * This allows for tactics to construct proof terms or not depending on which implementation they use.
  *
  * This file mimics [[edu.cmu.cs.ls.keymaerax.core.Provable]] outside the core and forwards all operations to the core.
  *
  * @author Andre Platzer
  * @author Nathan Fulton
  * @author Brandon Bohrer
  * @author Andre Platzer
  * @see [[Provable]]
  */
trait ProvableSig {
  /** The core's [[Provable]] that this object really represents. */
  val underlyingProvable : Provable = this match {
    case TermProvable(child, _) => child.underlyingProvable
    case ElidingProvable(provable) => provable
  }

  /** Returns a copy of this provable with the underlying provable replaced by `underlying`. */
  def reapply(underlying: Provable): ProvableSig = this match {
    case t: TermProvable => t.copy(provable = t.provable.reapply(underlying))
    case e: ElidingProvable => e.copy(provable = underlying)
  }

  /* The number of steps performed to create this provable. */
  def steps: Int = 0

  /**
    * Position types for the subgoals of a Provable.
    */
  type Subgoal = Int

  /** the conclusion `G |- D` that follows if all subgoals are valid. */
  val conclusion: Sequent

  /** the premises `Gi |- Di` that, if they are all valid, imply the conclusion. */
  val subgoals: immutable.IndexedSeq[Sequent]

  /**
    * Checks whether this Provable proves its conclusion.
    *
    * @return true if conclusion is proved by this Provable,
    *         false if subgoals are missing that need to be proved first.
    * @see [[Provable.isProved]]
    */
  final def isProved: Boolean = underlyingProvable.isProved

  /**
    * What conclusion this Provable proves if isProved.
    *
    * @requires(isProved)
    */
  def proved: Sequent

  /**
    * Apply Rule: Apply given proof rule to the indicated subgoal of this Provable, returning the resulting Provable
    * {{{
    *    G1 |- D1 ... Gi |- Di ... Gn |- Dn              G1 |- D1 ... Gr1 |- Dr1 ... Gn |- Dn Gr2 |- Dr2 ... Grk | Drk
    *   ------------------------------------     =>     ---------------------------------------------------------------
    *                  G |- D                                         G |- D
    * }}}
    * using the rule instance
    * {{{
    *   Gr1 |- Dr1  Gr2 |- Dr2 ... Grk |- Drk
    *   ------------------------------------ (rule)
    *                Gi |- Di
    * }}}
    *
    * @param rule the proof rule to apply to the indicated subgoal of this Provable derivation.
    * @param subgoal which of our subgoals to apply the given proof rule to.
    * @return A Provable derivation that proves the premise subgoal by using the given proof rule.
    * Will return a Provable with the same conclusion but an updated set of premises.
    * @requires(0 <= subgoal && subgoal < subgoals.length)
    */
  def apply(rule: Rule, subgoal: Subgoal): ProvableSig

  /**
    * Substitute subderivation as a proof of subgoal.
    * Merge: Replace premise subgoal by the given subderivation.
    * Use the given provable derivation in place of the indicated subgoal of this Provable, returning the resulting concatenated Provable.
    *
    * In particular, if subderivation.isProved, then the given subgoal will disappear,
    * otherwise it will be replaced by the subgoals of subderivation
    * (with the first subgoal of subderivation in place of subgoal and all other subgoals at the end).
    *
    * This function implements the substitution principle for hypotheses.
    * {{{
    *    G1 |- D1 ... Gi |- Di ... Gn |- Dn              G1 |- D1 ... Gr1 |- Dr1 ... Gn |- Dn Gr2 |- Dr2 ... Grk | Drk
    *   ------------------------------------     =>     ---------------------------------------------------------------
    *                  G |- D                                         G |- D
    * }}}
    * using the given subderivation
    * {{{
    *   Gr1 |- Dr1  Gr2 |- Dr2 ... Grk |- Drk
    *   ------------------------------------ (subderivation)
    *                Gi |- Di
    * }}}
    *
    * @param subderivation the Provable derivation that proves premise subgoal.
    * @param subgoal the index of our subgoal that the given subderivation concludes.
    * @return A Provable derivation that joins our derivation and subderivation to a joint derivation of our conclusion using subderivation to show our subgoal.
    * Will return a Provable with the same conclusion but an updated set of premises.
    * @requires(0 <= subgoal && subgoal < subgoals.length)
    * @requires(subderivation.conclusion == subgoals(subgoal))
    */
  def apply(subderivation: ProvableSig, subgoal: Subgoal): ProvableSig

  /** Apply forward tactic `fw` at `subgoal`. */
  def apply(fw: ProvableSig=>ProvableSig, subgoal: Subgoal): ProvableSig = apply(fw(sub(subgoal)), subgoal)

  /**
    * Apply a uniform substitution to a (locally sound!) Provable.
    * Substitutes both subgoals and conclusion with the same uniform substitution `subst`.
    * {{{
    *    G1 |- D1 ... Gn |- Dn              s(G1) |- s(D1) ... s(Gn) |- s(Dn)
    *   -----------------------     =>     -----------------------------------   (USR)
    *            G |- D                                s(G) |- s(D)
    * }}}
    *
    * @param subst The uniform substitution (of no free variables) to be used on the premises and conclusion of this Provable.
    * @return The Provable resulting from applying `subst` to our subgoals and conclusion.
    * @author Andre Platzer
    * @see Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017. Theorem 26+27."
    */
  def apply(subst: USubst): ProvableSig

  def apply(ren: URename): ProvableSig

  // forward proofs (convenience)

  /**
    * Apply Rule Forward: Apply given proof rule forward in Hilbert style to prolong this Provable to a Provable for concludes.
    * This Provable with conclusion `G |- D` transforms as follows
    * {{{
    *     G1 |- D1 ... Gn |- Dn                  G1 |- D1 ... Gn |- Dn
    *   -------------------------       =>     -------------------------
    *            G |- D                              newConsequence
    * }}}
    * provided
    * {{{
    *            G |- D
    *   ------------------------- rule
    *         newConsequence
    * }}}
    *
    * @param newConsequence the new conclusion that the rule shows to follow from this.conclusion
    * @param rule the proof rule to apply to concludes to reduce it to this.conclusion.
    * @return A Provable derivation that proves concludes from the same subgoals by using the given proof rule.
    * Will return a Provable with the same subgoals but an updated conclusion.
    */
  def apply(newConsequence: Sequent, rule: Rule): ProvableSig

  /**
    * Substitute Subderivation Forward: Prolong this Provable with the given prolongation.
    * This Provable with conclusion `G |- D` transforms as follows
    * {{{
    *     G1 |- D1 ... Gn |- Dn                  G1 |- D1 ... Gn |- Dn
    *   -------------------------       =>     -------------------------
    *            G |- D                                 G0 |- D0
    * }}}
    * provided
    * {{{
    *            G |- D
    *   ------------------------- prolongation
    *           G0 |- D0
    * }}}
    *
    * @param prolongation the subderivation used to prolong this Provable.
    *                       Where subderivation has a  subgoal equaling our conclusion.
    * @return A Provable derivation that proves prolongation's conclusion from our subgoals.
    */
  def apply(prolongation: ProvableSig): ProvableSig

  /**
    * Sub-Provable: Get a sub-Provable corresponding to a Provable with the given subgoal as conclusion.
    * Provables resulting from the returned subgoal can be merged into this Provable to prove said subgoal.
    *
    * @param subgoal the index of our subgoal for which to return a new open Provable.
    * @return an initial unfinished open Provable for the subgoal `i`:
    * {{{
    *    Gi |- Di
    *   ----------
    *    Gi |- Di
    * }}}
    * which is suitable for being merged back into this Provable for subgoal `i` subsequently.
    */
  def sub(subgoal: Subgoal): ProvableSig

  // included from Provable object here already for departure point with or without proof terms

  /** immutable list of sound axioms, i.e., valid formulas of differential dynamic logic. (convenience method) */
  val axiom: immutable.Map[String, Formula] = Provable.axiom

  /** immutable list of Provables of sound axioms, i.e., valid formulas of differential dynamic logic.
    * {{{
    *       *
    *   ---------- (axiom)
    *    |- axiom
    * }}}
    *
    * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic. In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. arXiv 1503.01981, 2015."
    */
  val axioms: Map[String, ProvableSig]

  /** immutable list of Provables of locally sound axiomatic proof rules.
    * {{{
    *    Gi |- Di
    *   ---------- (axiomatic rule)
    *     G |- D
    * }}}
    *
    * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic. In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. arXiv 1503.01981, 2015."
    * @see [[Provable.apply(USubst)]]
    */
  val rules: immutable.Map[String, ProvableSig]

  /**
    * Begin a new proof for the desired conclusion goal
    * {{{
    *    goal
    *   ------
    *    goal
    * }}}
    *
    * @param goal the desired conclusion.
    * @return a Provable whose subgoals need to be all proved in order to prove goal.
    */
  def startProof(goal : Sequent): ProvableSig

  /**
    * Begin a new proof for the desired conclusion formula from no antecedent.
    * {{{
    *    |- goal
    *   ---------
    *    |- goal
    * }}}
    *
    * @param goal the desired conclusion formula for the succedent.
    * @return a Provable whose subgoals need to be all proved in order to prove goal.
    */
  def startProof(goal : Formula): ProvableSig

  /**
    * Proves a formula f in real arithmetic using an external tool for quantifier elimination.
    *
    * @param t The quantifier-elimination tool.
    * @param f The formula.
    * @return a Lemma with a quantifier-free formula equivalent to f and evidence as provided by the tool.
    */
  def proveArithmeticLemma(t: QETool, f: Formula): Lemma

  def proveArithmetic(t: QETool, f: Formula): ProvableSig


  def prettyString: String
}

/**
  * @see [[Provable]]
  */
object ProvableSig {
  /** Whether to use proof terms instead of eliding them */
  var PROOF_TERMS_ENABLED: Boolean = Configuration(Configuration.Keys.PROOF_TERM) == "true"

  /** immutable list of sound axioms, i.e., valid formulas of differential dynamic logic. (convenience method) */
  val axiom: immutable.Map[String, Formula] = Provable.axiom

  // lazy so that startup-time change in PROOF_TERMS_ENABLED is taken
  /** immutable list of Provables of sound axioms, i.e., valid formulas of differential dynamic logic.
    * {{{
    *       *
    *   ---------- (axiom)
    *    |- axiom
    * }}}
    *
    * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic. In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. arXiv 1503.01981, 2015."
    */
  def axioms: immutable.Map[String, ProvableSig] = {
    if (PROOF_TERMS_ENABLED) TermProvable.axioms else ElidingProvable.axioms
  }

  /** immutable list of Provables of locally sound axiomatic proof rules.
    * {{{
    *    Gi |- Di
    *   ---------- (axiomatic rule)
    *     G |- D
    * }}}
    *
    * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic. In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. arXiv 1503.01981, 2015."
    * @see [[Provable.apply(USubst)]]
    */
  def rules: immutable.Map[String, ProvableSig] = {
    if (PROOF_TERMS_ENABLED) TermProvable.rules else ElidingProvable.rules
  }

  /**
    * Begin a new proof for the desired conclusion goal
    * {{{
    *    goal
    *   ------
    *    goal
    * }}}
    *
    * @param goal the desired conclusion.
    * @return a Provable whose subgoals need to be all proved in order to prove goal.
    */
  def startProof(goal : Sequent): ProvableSig =
    if(PROOF_TERMS_ENABLED) TermProvable.startProof(goal) else ElidingProvable.startProof(goal)

  /**
    * Begin a new proof for the desired conclusion formula from no antecedent.
    * {{{
    *    |- goal
    *   ---------
    *    |- goal
    * }}}
    *
    * @param goal the desired conclusion formula for the succedent.
    * @return a Provable whose subgoals need to be all proved in order to prove goal.
    */
  def startProof(goal : Formula): ProvableSig =
    if(PROOF_TERMS_ENABLED) TermProvable.startProof(goal) else ElidingProvable.startProof(goal)

  def proveArithmetic(t: QETool, f: Formula): ProvableSig =
    if(PROOF_TERMS_ENABLED) TermProvable.proveArithmetic(t,f) else ElidingProvable.proveArithmetic(t,f)

  /**
    * Proves a formula f in real arithmetic using an external tool for quantifier elimination.
    *
    * @param t The quantifier-elimination tool.
    * @param f The formula.
    * @return a Lemma with a quantifier-free formula equivalent to f and evidence as provided by the tool.
    */
  def proveArithmeticLemma(t: QETool, f: Formula): Lemma =
    if(PROOF_TERMS_ENABLED) TermProvable.proveArithmeticLemma(t,f) else ElidingProvable.proveArithmeticLemma(t,f)

}

/**
  * A direct [[Provable]] straight from the core that does not keep track of its proof term.
  * Directly forwards all function calls to [[provable]].
  */
case class ElidingProvable(provable: Provable) extends ProvableSig {
  override val conclusion: Sequent = provable.conclusion
  override val subgoals: IndexedSeq[Sequent] = provable.subgoals

  override def proved: Sequent = provable.proved

  override val axioms: Map[String, ProvableSig] = ElidingProvable.axioms
  override val rules: Map[String, ProvableSig] = ElidingProvable.rules

  override def apply(rule: Rule, subgoal: Subgoal): ProvableSig = ElidingProvable(provable(rule,subgoal), steps+1)

  override def apply(subderivation: ProvableSig, subgoal: Subgoal): ProvableSig =
    ElidingProvable(provable(subderivation.underlyingProvable, subgoal), steps+subderivation.steps)

  override def apply(subst: USubst): ProvableSig =
    ElidingProvable(provable(subst), steps+1)

  override def apply(ren: URename): ProvableSig =
    ElidingProvable(provable(ren), steps+1)

  override def apply(newConsequence: Sequent, rule: Rule): ProvableSig = ElidingProvable(provable(newConsequence, rule), steps+1)

  override def apply(prolongation: ProvableSig): ProvableSig =
    ElidingProvable(provable(prolongation.underlyingProvable), steps+prolongation.steps)

  override def sub(subgoal: Subgoal): ProvableSig = ElidingProvable(provable.sub(subgoal), steps)

  override def startProof(goal: Sequent): ProvableSig = ElidingProvable(Provable.startProof(goal), 0)

  override def startProof(goal: Formula): ProvableSig = ElidingProvable(Provable.startProof(goal), 0)

  override def proveArithmetic(t: QETool, f: Formula): ProvableSig = ElidingProvable.proveArithmetic(t,f)

  override def proveArithmeticLemma(t: QETool, f: Formula): Lemma = ElidingProvable.proveArithmeticLemma(t,f)

  override def prettyString: String = s"ElidingProvable(${provable.prettyString})"
}

object ElidingProvable {
  val axioms: Map[String, ProvableSig] = Provable.axioms.map(kvp => (kvp._1, ElidingProvable(kvp._2, 0)))
  val rules: Map[String, ProvableSig] = Provable.rules.map(kvp => (kvp._1, ElidingProvable(kvp._2, 0)))

  def apply(provable: Provable, initSteps: Int): ElidingProvable = new ElidingProvable(provable) { override def steps: Int = initSteps }

  def startProof(goal: Sequent): ProvableSig = ElidingProvable(Provable.startProof(goal), 0)

  def startProof(goal: Formula): ProvableSig = ElidingProvable(Provable.startProof(goal), 0)

  def proveArithmetic(tool: QETool, f: Formula): ProvableSig = ElidingProvable(Provable.proveArithmetic(tool,f))

  def proveArithmeticLemma(tool: QETool, f: Formula): Lemma = {
    val fact = proveArithmetic(tool, f)
    Lemma(fact, Lemma.requiredEvidence(fact, Nil), None)
  }
}

object TermProvable {

  val axioms: immutable.Map[String, ProvableSig] = Provable.axioms.map(x => (x._1, TermProvable(ElidingProvable.axioms.apply(x._1),
    {//println("Provable-axiom:" + x._1);
    AxiomTerm(x._1)}
  )))

  val rules: immutable.Map[String, ProvableSig] = Provable.rules.map(x => (x._1, TermProvable(ElidingProvable.rules.apply(x._1), RuleTerm(x._1))))

  def startProof(goal : Sequent): ProvableSig = {
    val sym = StaticSemantics.signature(goal)
    if(sym.exists({case _:UnitFunctional => true case _ => false})) {
      val 2 = 1 + 1
      ???
    }

    TermProvable(ElidingProvable.startProof(goal), StartProof(goal))
  }

  private def fml2Seq(f:Formula):Sequent = Sequent(IndexedSeq(), IndexedSeq(f))

  def startProof(goal : Formula): ProvableSig = {
    val sym = StaticSemantics.signature(goal)
    if(sym.exists({case _:UnitFunctional => true case _ => false})) {
      //println("Goal needs exemption: " + goal)

    }
    TermProvable(ElidingProvable.startProof(goal), StartProof(fml2Seq(goal)))
  }

  def proveArithmetic(tool: QETool, f: Formula): ProvableSig = ElidingProvable(Provable.proveArithmetic(tool,f))

  def proveArithmeticLemma(t: QETool, f: Formula): Lemma = {
    //@todo after changing everything to ProvableSig's, then create a lemma with an PTProvable.
    //@TODO Does this work at all
    val lem = ElidingProvable.proveArithmeticLemma(t,f)
    Lemma(TermProvable(lem.fact, FOLRConstant(lem.fact.conclusion.succ.head)), lem.evidence, lem.name)
  }

}


/**
  * TermProvable has the same signature as Provable, but constructs proof terms alongside Provables.
  * The ProofTerms remember how the provable was proved.
  * @author Nathan Fulton
  * @author Brandon Bohrer
  */
case class TermProvable(provable: ProvableSig, pt: ProofTerm) extends ProvableSig with Logging {
  override val conclusion: Sequent = provable.conclusion
  override val subgoals: IndexedSeq[Sequent] = provable.subgoals

  override def proved: Sequent = provable.proved

  override def apply(rule: Rule, subgoal: Subgoal): ProvableSig = {
    //@todo do a total pattern match on all rules in the core and produce individualized proof terms for each of them.
    //This is necessary because we need positions where the rule should be applied within the *sequent* in addition to subgoal,
    //which is the position within the *provable*. Alternatively a subtype heirarchy for Rule would do the trick...
    val (sequentPositions,expArgs) = rule match {
      case Close(ante,succ) => (ante :: succ :: Nil, Nil)
      case CoHide2(ante, succ)  => (ante :: succ :: Nil, Nil)
      case CutRight(fml, succ) => (succ :: Nil, fml:: Nil)
      case ImplyRight(succ) => (succ :: Nil, Nil)
      case AndRight(succ) => (succ :: Nil, Nil)
      case CoHideRight(succ) => (succ :: Nil, Nil)
      case CommuteEquivRight(succ) => (succ :: Nil, Nil)
      case EquivifyRight(succ) => (succ :: Nil, Nil)
      case EquivRight(succ) => (succ :: Nil, Nil)
      case NotRight(succ) => (succ :: Nil, Nil)
      case CloseTrue(succ) => (succ :: Nil, Nil)
      case HideRight(succ) => (succ :: Nil, Nil)
      case OrRight(succ) => (succ :: Nil, Nil)

      case OrLeft(ante) => (ante :: Nil, Nil)
      case AndLeft(ante) => (ante :: Nil, Nil)
      case HideLeft(ante) => (ante :: Nil, Nil)
      case CutLeft(fml,ante) => (ante :: Nil, fml :: Nil)
      case ImplyLeft(ante) => (ante :: Nil, Nil)
      case NotLeft(ante) => (ante :: Nil, Nil)
      case EquivLeft(ante) => (ante :: Nil, Nil)
      case CloseFalse(ante) => (ante :: Nil, Nil)

      case BoundRenaming(what, repl, seq:SeqPos) => (seq :: Nil, what :: repl :: Nil)
      case Skolemize(seq:SeqPos) => (seq :: Nil, Nil)

      case UniformRenaming(what, repl) => (Nil, what :: repl :: Nil)
      case Cut(fml) => (Nil, fml :: Nil)

      case _ =>
        throw new Exception(s"TermProvable.apply(Rule,provable pos) is not completely implemented. Missing case: ${rule.name}") //See @todo above add cases as necessary...
    }
    TermProvable(provable(rule, subgoal), RuleApplication(pt, rule.name, subgoal, sequentPositions,expArgs))
  }


  // @TODO: This makes no sense needs new proof term class probably
  override def apply(subderivation: ProvableSig, subgoal: Subgoal): ProvableSig = {
    subderivation match {
      case TermProvable (subProvable, subPT) => {
        val thePt = Sub(pt, subPT, subgoal)
        TermProvable(ElidingProvable(underlyingProvable(subProvable.underlyingProvable,subgoal)), thePt)
      }

      case subprovable: ProvableSig => {
        //Find an axiom or rule with the same name.
        // @TODO: Add derived axioms
        val coreAxiom = TermProvable.axioms.find(p => p._2.underlyingProvable == subprovable.underlyingProvable)
        val axinfos = DerivedAxiomInfo.allInfo
        val derivedAxiom = axinfos.find({case (name, info) => info.provable.underlyingProvable == subprovable.underlyingProvable}).map(_._2)
        val rule = TermProvable.rules.find(p => p._2.underlyingProvable == subprovable.underlyingProvable)
        val ruleInfos = DerivedRuleInfo.allInfo
        val derivedRule = ruleInfos.find({case (name, info) => info.provable.underlyingProvable == subprovable.underlyingProvable}).map(_._2)

        //If such an axiom exists, create evidence using the axiom's associated proof certificate.
        if (coreAxiom.isDefined) {
          val TermProvable(subProvable, subPT) = TermProvable.axioms(coreAxiom.get._1)
          val thePt = Sub(pt, subPT, subgoal)
          TermProvable(provable(subProvable, subgoal), thePt)
        } else if (derivedAxiom.isDefined) {
          val term = Sub(pt, AxiomTerm(derivedAxiom.get.codeName), subgoal)
          logger.trace("derivedaxiom codename: " + derivedAxiom.get.codeName)
          val axiomPT = TermProvable(ElidingProvable(derivedAxiom.get.provable.underlyingProvable), term)
          TermProvable(provable(subprovable, subgoal), term)
        }
        //And ditto for rules.
        else if (rule.isDefined) {
          val TermProvable(subProvable, subPT) = TermProvable.rules(rule.get._1)
          val thePt = Sub(pt, subPT, subgoal)
          TermProvable(provable(subProvable, subgoal), thePt)
        } else if (derivedRule.isDefined) {
          val term = Sub(pt, RuleTerm(derivedRule.get.codeName), subgoal)
          val axiomPT = TermProvable(ElidingProvable(derivedRule.get.provable.underlyingProvable), term)
          TermProvable(provable(subprovable, subgoal), term)
        }
        else {
          //For more complicated uses of useAt, by, etc. it's unclear what to do (and indeed the general architecture is problematic -- same reason that extraction works by the miracle of hard work aone).
          throw new DebugMeException()
          //throw new Exception(s"Cannot construct a proof term for ${subderivation} because it has no associated proof term.")
        }
      }
    }
  }

  class DebugMeException extends Exception {}

  override def apply(subst: USubst): ProvableSig = {
    TermProvable(provable(subst), UsubstProvableTerm(pt, subst))
  }

  //@todo implement
  override def apply(ren: URename): ProvableSig = ???

  override def apply(newConsequence: Sequent, rule: Rule): ProvableSig =
    TermProvable(provable(newConsequence, rule), ForwardNewConsequenceTerm(pt, newConsequence, rule))

  override def apply(prolongation: ProvableSig): ProvableSig = prolongation match {
    case prolongationProof: TermProvable =>
      TermProvable(provable(prolongationProof), ProlongationTerm(pt, prolongationProof.pt))
    case subProvable: ProvableSig =>
      /* @TODO: Arguable this should just not be allowed and represents a bug elsewhere */
      TermProvable(ElidingProvable(provable.underlyingProvable(subProvable.underlyingProvable)), ProlongationTerm(pt, NoProof()))
  }

  override def sub(subgoal: Subgoal): ProvableSig =
    TermProvable(provable.sub(subgoal), NoProof())

  lazy val axioms: immutable.Map[String, ProvableSig] = TermProvable.axioms

  lazy val rules: immutable.Map[String, ProvableSig] = TermProvable.rules

  def startProof(goal : Sequent): ProvableSig = {
    val sym = StaticSemantics.signature(goal)
    if(sym.exists({case _:UnitFunctional => true case _ => false})) {
      val 2 = 1 + 1
      ???
    }
    TermProvable.startProof(goal)
  }

  def startProof(goal : Formula): ProvableSig = {
    val sym = StaticSemantics.signature(goal)
    if (sym.exists({ case _: UnitFunctional => true case _ => false })) {
      val 2 = 1 + 1
      ???
    }
    TermProvable.startProof(goal)
  }

  def proveArithmetic(t: QETool, f: Formula): ProvableSig =
    TermProvable.proveArithmetic(t,f)

  def proveArithmeticLemma(t: QETool, f: Formula): Lemma =
    TermProvable.proveArithmeticLemma(t,f)


  override def toString: String = s"TermProvable(${provable.toString}, ${pt.toString})"

  override def prettyString: String = s"TermProvable(${provable.prettyString}, ${pt.prettyString})"
}

