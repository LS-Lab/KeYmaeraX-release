package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.bellerophon._
import TacticExtractionErrors._
import edu.cmu.cs.ls.keymaerax.parser.ParseException

class ExtractTacticFromTrace(db: DBAbstraction) {
  // Additional wrappers
  def apply(proofId: Int): BelleExpr = apply(db.getExecutionTrace(proofId))
  def apply(trace : ExecutionTrace) : BelleExpr  = apply(ProofTree.ofTrace(trace))()

  /**
    * @note this could be tailrec.
    * @param tree A proof tree
    * @return A structured Bellerophon tactic that constructs the proof tree.
    */
  def apply(tree : ProofTree)(node: TreeNode = tree.root) : BelleExpr = {
    assert(tree.root.startStep.isEmpty, "Root should not have a startStep")
    val descendants = node.allDescendants
    if(descendants == 0) tacticAt(node)
    else if(descendants == 1) tacticAt(node) & apply(tree)(descendants.head)
    else tacticAt(node) & BranchTactic(descendants.map(apply(tree)))
  }

  private def tacticAt(node: TreeNode) : BelleExpr = node.endStep match {
    case Some(step) => try {
      db.getExecutable(step.executableId).belleExpr match {
        case Some(exprString) => BTacticParser(exprString) match {
          case Some(expr) => expr
          case None => throw new BParserException(s"Could not parse Bellerophon expression ${exprString}")
        }
        case None => throw TacticExtractionError("Tactic extraction does not currently support non-Bellerophon tactic extraction")
      }
    } catch {
      case e : BParserException => throw TacticExtractionError(e.getMessage, e)
      case e : ReflectiveExpressionBuilderExn => throw TacticExtractionError(s"Could not parse Bellerophon tactic becuase a base-tactic was missing", e)
      case t : Throwable => throw TacticExtractionError(s"Could not retrieve executable ${step.executableId} from the database", t)
    }
    case None => ??? //@todo determine if this is an error or if we end up here when there are open (closed?) leaves.
  }
}

object TacticExtractionErrors {
  class TacticExtractionError(message: String, cause: Option[Throwable]) extends Exception(message + {cause match {case Some(e) => "Caused by: " + e.printStackTrace(); case None => ""}})
  object TacticExtractionError {
    def apply(message: String, cause: Exception) = new TacticExtractionError(message, Some(cause))
    def apply(message: String, cause: Throwable) = new TacticExtractionError(message, Some(cause))
    def apply(message: String) = new TacticExtractionError(message, None)
  }
}

