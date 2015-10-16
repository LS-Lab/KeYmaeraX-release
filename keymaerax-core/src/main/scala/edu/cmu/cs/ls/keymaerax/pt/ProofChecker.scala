package edu.cmu.cs.ls.keymaerax.pt

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics._

import scala.collection.immutable

/**
 * Created by nfulton on 10/15/15.
 */
object ProofChecker {
  private val tool = new edu.cmu.cs.ls.keymaerax.tools.Mathematica()

  private def goalSequent(phi : Formula) = Sequent(Nil, immutable.IndexedSeq(), immutable.IndexedSeq(phi))
  private def proofNode(phi : Formula) = new RootNode(goalSequent(phi))

  /**
   * Returns true iff goal is a theorem of dL
   */
  def apply(e: ProofTerm, phi: Formula) : Option[Provable] = {
    e match {
      case folrConstant(f) => {
        val node = proofNode(phi)
        ArithmeticTacticsImpl.quantifierEliminationT("Mathematica").apply(tool, node)
        Some(node.provableWitness)
      }

      case AndTerm(e, d) => phi match {
        case And(varphi, psi) => {
          val varphiCert = ProofChecker(e, varphi)
          val psiCert = ProofChecker(d, psi)
          (varphiCert, psiCert) match {
            case (Some(varphiCert), Some(psiCert)) => {
              //This is the ^R schematic proof rule referred to in the proof.
              val andR = edu.cmu.cs.ls.keymaerax.core.AndRight(SuccPos(0))
              Some(
                Provable.startProof(goalSequent(phi))
                  (andR, 0)
                  (varphiCert, 0)
                  (psiCert, 0)
              )
            }
            case _ => None
          }
        }
        case _ => None
      }

      case ApplicationTerm(e, psi, d) => {
        val implCert = ProofChecker(e, Imply(psi, phi))
        val psiCert = ProofChecker(d, psi)

        if(implCert.isDefined && implCert.get.isProved && psiCert.isDefined && psiCert.get.isProved)
          //@todo Eisegesis. Adopt implementation or adopt proof so that they are the same.
          Some(
            Provable.startProof(goalSequent(phi))
              (Cut(Imply(psi, phi)), 0)
              (HideRight(SuccPos(0)), 1)(implCert.get, 1) // hide phi and prove psi -> phi using proof produced by IH
              (Cut(psi), 0)
              (HideLeft(AntePos(0)), 1)(HideRight(SuccPos(0)), 1)(psiCert.get, 1) // have phi -> psi |- phi, psi. Hides antecendent and phi, and proves psi by IH.
              (ImplyLeft(AntePos(0)), 0)
              (Close(AntePos(0), SuccPos(1)), 0)
              (Close(AntePos(1), SuccPos(0)), 0)
          )
        else None
      }

      case LeftEquivalence(e, psi, d) => {
        val equivCert = ProofChecker(e, Equiv(psi, phi))
        val psiCert   = ProofChecker(d, psi)

        if(equivCert.isDefined && equivCert.get.isProved && psiCert.isDefined && psiCert.get.isProved) {
          /* Game plan:
           *     - Transform to the goal psi<->phi, phi |- psi (readyForRewrite)
           *     - Rewrite to phi |- phi using equality rewriting tactics and then close the proof
           *     - Extract provable (rewritingWitness)
           *     - apply tactic provable to the remaining goal on the provable with the desired conclusion (readyForRewrite)
           */
          //@todo Eisegesis. Adopt implementation or adopt proof so that they are the same.
          val readyForRewrite = (
            Provable.startProof(goalSequent(phi))
            (Cut(Equiv(psi, phi)), 0)
            (HideRight(SuccPos(0)), 1)(equivCert.get, 1) // hide phi and prove psi <-> phi using proof produced by IH
            (Cut(psi), 0)
            (HideLeft(AntePos(0)), 1)(HideRight(SuccPos(0)), 1)(psiCert.get, 1) // have phi <-> psi |- phi, psi. Hides antecendent and phi, and proves psi by IH.
            (CommuteEquivLeft(AntePos(0)), 0)
          )

          //@todo is there a better way of combining scheduled tactics with direct manipulation proofs?
          //@todo and/or is there a better way of doing equivalence rewriting with direct manipulation proofs?
          val rewritingWitness = {
            val node = new RootNode(readyForRewrite.subgoals.last)
            val tactic =
              EqualityRewritingImpl.equivRewriting(AntePos(0), SuccPos(0)) ~
              TacticLibrary.AxiomCloseT(AntePos(0), SuccPos(0))
            tactic.apply(tool, node)
            node.provableWitness
          } ensuring(r => r.isProved)

          Some(readyForRewrite(rewritingWitness, 0))
        }
        else None
      }

      case RightEquivalence(e, psi, d) => {
        val equivCert = ProofChecker(e, Equiv(psi, phi))
        val psiCert   = ProofChecker(d, psi)

        if(equivCert.isDefined && equivCert.get.isProved && psiCert.isDefined && psiCert.get.isProved) {
          /* Game plan:
           *     - Transform to the goal psi<->phi, phi |- psi (readyForRewrite)
           *     - Rewrite to phi |- phi using equality rewriting tactics and then close the proof
           *     - Extract provable (rewritingWitness)
           *     - apply tactic provable to the remaining goal on the provable with the desired conclusion (readyForRewrite)
           */
          //@todo Eisegesis. Adopt implementation or adopt proof so that they are the same.
          val readyForRewrite = (
            Provable.startProof(goalSequent(phi))
            (Cut(Equiv(psi, phi)), 0)
            (HideRight(SuccPos(0)), 1)(equivCert.get, 1) // hide phi and prove psi <-> phi using proof produced by IH
            (Cut(psi), 0)
            (HideLeft(AntePos(0)), 1)(HideRight(SuccPos(0)), 1)(psiCert.get, 1) // have phi <-> psi |- phi, psi. Hides antecendent and phi, and proves psi by IH.
            (CommuteEquivLeft(AntePos(0)), 0)
          )

          //@todo is there a better way of combining scheduled tactics with direct manipulation proofs?
          //@todo and/or is there a better way of doing equivalence rewriting with direct manipulation proofs?
          val rewritingWitness = {
            val node = new RootNode(readyForRewrite.subgoals.last)
            val tactic =
              EqualityRewritingImpl.equivRewriting(AntePos(0), SuccPos(0)) ~
              TacticLibrary.AxiomCloseT(AntePos(0), SuccPos(0))
            tactic.apply(tool, node)
            node.provableWitness
          } ensuring(r => r.isProved)

          Some(readyForRewrite(rewritingWitness, 0))
        }
        else None
      }
    }
  }
}
