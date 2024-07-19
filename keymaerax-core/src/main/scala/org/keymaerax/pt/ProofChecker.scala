/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.pt

import org.keymaerax.btactics.TactixLibrary._
import org.keymaerax.btactics.macros.DerivationInfoAugmentors._
import org.keymaerax.btactics.macros._
import org.keymaerax.core._

import scala.collection.immutable

class ProofCheckException(message: String) extends Exception(message)

/**
 * ProofChecker maps a proof term to the Provable it proves.
 * {{{
 *   ProofChecker : ProofTerm * Formula => Provable
 * }}}
 * with a successful answer if the proof indeed checked successfully. Not soundness-critical, because the proof checker
 * compiles the proof term into subsequent proof rule and axiom applications in the [[org.keymaerax.core prover core]].
 * Created by nfulton on 10/15/15.
 *
 * @author
 *   Nathan Fulton
 * @author
 *   Brandon Bohrer
 * @see
 *   [[ProofTerm]]
 * @see
 *   [[ProvableSig]]
 * @todo
 *   Currently not operational: fixme
 */
object ProofChecker {

  private def goalSequent(phi: Formula) = Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(phi))
  private def proofNode(phi: Formula) = ProvableSig.startPlainProof(goalSequent(phi))
  private def proofNode(phi: Sequent) = ProvableSig.startPlainProof(phi)

  /**
   * Converts proof term e for goal phi into a Provable iff e indeed justifies phi.
   *
   * @todo
   *   could remove phi except no more contract then
   */
  def apply(e: ProofTerm, phi: Option[Formula] = None): ProvableSig = {
    val result: ProvableSig = e match {
      case FOLRConstant(f) => proveBy(proofNode(f), QE & done)
      case AxiomTerm(axiomName) =>
        try {
          val info = ProvableInfo.ofStoredName(axiomName)
          val axiomFml = info.provable.conclusion
          val node = proofNode(axiomFml)
          // @TODO: Why?
          // Just do an empty uniform substitution...
          //
          ??? // @todo proveBy(node, US(USubst(scala.collection.immutable.Seq()), info.canonicalName))
        } catch {
          // If derived axioms didn't do it, try core axioms too
          case _: Exception =>
            val axiomFml = AxiomInfo(axiomName).provable.conclusion
            val node = proofNode(axiomFml)
            ??? // @todo proveBy(node, US(USubst(scala.collection.immutable.Seq()), axiomName))
        }
      case RuleApplication(child, rule, subgoal) => apply(child)(rule, subgoal)
      case RuleTerm(name) =>
        if (ProvableSig.rules.contains(name)) ProvableSig.rules(name)
        else ProvableInfo.ofStoredName(name).asInstanceOf[DerivedRuleInfo].provable
      case ForwardNewConsequenceTerm(child, con, rule) => apply(child)(con, rule)
      case ProlongationTerm(child, pro) => apply(child)(apply(pro))
      case Sub(child, sub, i) => apply(child)(apply(sub), i)
      case StartProof(goal) => ProvableSig.startPlainProof(goal)
      case UsubstProvableTerm(child, sub) => apply(child)(sub)
      case URenameTerm(child, ren) => apply(child)(ren)
      case NoProof => throw new ProofCheckException(s"Tried to check proof of $phi but it has NoProof")
    }

    result
  } ensures
    (
      r => phi.isEmpty || r.conclusion == goalSequent(phi.get),
      "Resulting Provable proves given formula if defined for " + phi + " : " + e,
    )
}