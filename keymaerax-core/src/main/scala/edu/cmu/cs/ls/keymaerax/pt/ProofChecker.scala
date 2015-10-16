package edu.cmu.cs.ls.keymaerax.pt

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.{RootNode, ProofNode, ArithmeticTacticsImpl, TacticLibrary}

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
          val psiCert    = ProofChecker(d, psi)
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
    }
  }

}
