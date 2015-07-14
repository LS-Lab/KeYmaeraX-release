/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package testHelper

import edu.cmu.cs.ls.keymaerax.core.{UnknownOperatorException, Sequent}
import edu.cmu.cs.ls.keymaerax.tactics.ProofNode
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.Tactic
import testHelper.ProvabilityTestHelper

import scala.collection.immutable.List

/**
 * Created by ran on 01/27/15.
 * @author Ran Ji
 */
object ProofFactory {

  val helper = new ProvabilityTestHelper((x) => println(x))

  /**
   * Get the proof nodes of all open goals in a proof tree
   * @param tactic
   * @param rootNode
   * @return
   */
  def getProofGoals(tactic : Tactic, rootNode : Any): Any = rootNode match {
    case rootNode : ProofNode =>  getProofGoalsOne(tactic, rootNode)
    case rootNode : List[ProofNode] => getProofGoalsMany(tactic, rootNode)
    case _ =>
  }

  private def getProofGoalsOne(tactic : Tactic, rootNode : ProofNode) = {
    val goalList = helper.runTactic(tactic, rootNode).openGoals()
    goalList.length match {
      case 0 =>
      case 1 => goalList.head
      case _ => goalList
    }
  }

  private def getProofGoalsMany(tactic : Tactic, rootNodes : List[ProofNode]) = {
    rootNodes.length match {
      case 0 =>
      case 1 => getProofGoalsOne(tactic, rootNodes.head)
      case _ =>
        var nodeList: List[ProofNode] = Nil
        for (j <- 0 to rootNodes.length - 1) {
          val goalList = helper.runTactic(tactic, rootNodes.apply(j)).openGoals()
          goalList.length match {
            case 0 => nodeList
            case 1 => goalList.head :: nodeList
            case _ =>
              for (i <- 0 to goalList.length - 1)
                nodeList = goalList.apply(i) :: nodeList
          }
        }
        nodeList
    }
  }

  def getProofSequentFromGoals(proofNode: Any): Any = proofNode match {
    case proofNode : ProofNode => proofNode.sequent
    case proofNode : List[ProofNode] =>
      proofNode.length match {
        case 0 =>
        case 1 => proofNode.head.sequent
        case _ =>
          var seqList: List[Sequent] = Nil
          for(i <- 0 to proofNode.length-1) {
            seqList = proofNode.apply(i).sequent :: seqList
          }
          seqList
      }
    case _ =>
   }

  /**
   * Get the sequents of all open goals in a proof tree
   * @param tactic
   * @param rootNode
   * @return
   */
  def getProofSequent(tactic : Tactic, rootNode : Any) = getProofSequentFromGoals(getProofGoals(tactic, rootNode))

}
