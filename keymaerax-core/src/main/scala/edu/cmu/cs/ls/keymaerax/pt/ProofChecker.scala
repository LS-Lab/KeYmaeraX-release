package edu.cmu.cs.ls.keymaerax.pt

import edu.cmu.cs.ls.keymaerax.btactics.DerivedRuleInfo
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._

import scala.collection.immutable

/**
 * ProofChecker maps a proof term to the Provable it proves.
 * {{{
 *   ProofChecker : ProofTerm * Formula => Provable
 * }}}
 * with a successful answer if the proof indeed checked successfully.
 * Not soundness-critical, because the proof checker compiles the proof term into
 * subsequent proof rule and axiom applications in the [[edu.cmu.cs.ls.keymaerax.core prover core]].
 * Created by nfulton on 10/15/15.
  *
  * @author Nathan Fulton
 * @see [[ProofTerm]]
 * @see [[ProvableSig]]
 */
object ProofChecker {
  private val tool = new edu.cmu.cs.ls.keymaerax.tools.Mathematica()

  private def goalSequent(phi : Formula) = Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(phi))
  private def proofNode(phi : Formula) = ProvableSig.startProof(goalSequent(phi))

  /**
   * Converts proof term e for goal phi into a Provable iff e indeed justifies phi.
    *
    * @todo could remove phi except no more contract then
   */
  def apply(e: ProofTerm, phi: Formula) : Option[ProvableSig] = {
    val result : Option[ProvableSig] =
      e match {
        case FOLRConstant(f) => {
          val node = proofNode(phi)
          Some(proveBy(node, QE & done))
        }

        case AxiomTerm(axiomName) => {
          val node = proofNode(phi)
          Some(proveBy(node, useAt(axiomName)(1)))
        }

        case UsubstTerm(proofOfPremise, premise, substitution) => {
          val phiPrimeCert = ProofChecker(proofOfPremise, premise)
          if (phiPrimeCert.isDefined && phiPrimeCert.get.isProved) {
            val goalS = goalSequent(phi)
            Some(proveBy(phi, US(phiPrimeCert.get)))
          }
          else None
        }

        case RenamingTerm(e, phiPrime, what, repl) => {
          val phiPrimeCert = ProofChecker(e, phiPrime)
          if (phiPrimeCert.isDefined && phiPrimeCert.get.isProved) {
            val goalS = goalSequent(phi)
            Some(UniformRenaming.UniformRenamingForward(ProvableSig.startProof(goalS), what, repl))
          }
          else None
        }

        case _ => ???
      }

    result
  } ensuring(r => r.isEmpty || r.get.conclusion == goalSequent(phi), "Resulting Provable proves given formula if defined for " + phi + " : " + e)
}
