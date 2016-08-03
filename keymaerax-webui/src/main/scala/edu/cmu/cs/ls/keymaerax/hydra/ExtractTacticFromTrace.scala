package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.bellerophon._
import TacticExtractionErrors._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms
import edu.cmu.cs.ls.keymaerax.parser.ParseException

class ExtractTacticFromTrace(db: DBAbstraction) {
  // Additional wrappers
  def apply(proofId: Int): BelleExpr = apply(db.getExecutionTrace(proofId))
  def apply(trace : ExecutionTrace) : BelleExpr  = {
    val tree = ProofTree.ofTrace(trace)
    apply(tree)(tree.root)
  }

  //@todo deprecate this approach and prefer [[apply(tree)(node).prettyString]]
  def extractTextWithoutParsing(proofId: Int): String = {
    val tree = ProofTree.ofTrace(db.getExecutionTrace(proofId))
    extractTextWithoutParsing(tree)(tree.root)
  }
  //@todo deprecate this approach and prefer [[apply(tree)(node).prettyString]]
  def extractTextWithoutParsing(tree : ProofTree)(node: TreeNode) : String = {
    val thisTactic = node.endStep match {
      case Some(step) => db.getExecutable(step.executableId).belleExpr
      case None =>  "nil" //why is this correct behavior? //@todo this should be a "partial"/"emit" if the goal is closed and nothing otherwise.
    }

    val children = node.children
    assert(!children.contains(node), "A node should not be its own child.") //but apparently this happens.

    if(children.length == 0) thisTactic
    else if(children.length == 1) thisTactic + " & " + extractTextWithoutParsing(tree)(children.head)
    else thisTactic + " <(\n  " + children.map(child => extractTextWithoutParsing(tree)(child)).mkString(",\n  ") + "\n)" //@note This doesn't work properly -- it generates the subgoals in the wrong order.
  }

  /**
    * @note this could be tailrec.
    * @param tree A proof tree
    * @return A structured Bellerophon tactic that constructs the proof tree.
    */
  def apply(tree : ProofTree)(node: TreeNode) : BelleExpr = {
    assert(tree.root.startStep.isEmpty, "Root should not have a startStep")
    val children = node.children
//      .filter(_ != node) //@todo remove this line... seems like a bug in ProofTree.
    assert(!children.contains(node), "A node should not be its own child.") //but apparently this happens.

    val thisTactic = tacticAt(node)

    if(children.length == 0) thisTactic
    else if(children.length == 1) thisTactic & apply(tree)(children.head)
    else thisTactic & BranchTactic(children.map(child => apply(tree)(child))) //@note This doesn't work properly -- it generates the subgoals in the wrong order.
  }

  private def tacticAt(node: TreeNode) : BelleExpr = node.endStep match {
    case Some(step) => try {
      val exprString = db.getExecutable(step.executableId).belleExpr
      BTacticParser(exprString) match {
          case Some(expr) => expr
          case None => throw new BParserException(s"Could not parse Bellerophon expression ${exprString}")
      }
    } catch {
      case e : BParserException => throw TacticExtractionError(e.getMessage, e)
      case e : ReflectiveExpressionBuilderExn => throw TacticExtractionError(s"Could not parse Bellerophon tactic because a base-tactic was missing", e)
      case t : Throwable => throw TacticExtractionError(s"Could not retrieve executable ${step.executableId} from the database", t)
    }
    case None => Idioms.nil //@todo this should be a "partial"/"emit" if the goal is closed and nothing otherwise. More generally, why is this (or similar) correct behavior?
  }
}

object TacticExtractionErrors {
  class TacticExtractionError(message: String, cause: Option[Throwable]) extends Exception(message + {cause match {case Some(e) => ". Caused by: " + e.getMessage; case None => ""}})
  object TacticExtractionError {
    def apply(message: String, cause: Exception) = new TacticExtractionError(message, Some(cause))
    def apply(message: String, cause: Throwable) = new TacticExtractionError(message, Some(cause))
    def apply(message: String) = new TacticExtractionError(message, None)
  }
}

