package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.bellerophon._
import TacticExtractionErrors._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BelleParser, BellePrettyPrinter}
import edu.cmu.cs.ls.keymaerax.btactics.{ConfigurableGenerator, Generator, Idioms}
import edu.cmu.cs.ls.keymaerax.core.Formula
import edu.cmu.cs.ls.keymaerax.parser.ParseException

class ExtractTacticFromTrace(db: DBAbstraction) {
  // Additional wrappers
  def apply(trace: ExecutionTrace): BelleExpr  = {
    val tree = ProofTree.ofTrace(trace)
    assert(tree.root.startStep.isEmpty, "Root should not have a startStep")
    val modelId = db.getProofInfo(trace.proofId).modelId
    apply(modelId)(tree.root)
  }

  def getTacticString(trace: ExecutionTrace): String = {
    val tree = ProofTree.ofTrace(trace)
    assert(tree.root.startStep.isEmpty, "Root should not have a startStep")
    val modelId = db.getProofInfo(trace.proofId).modelId
    getTacticString(modelId, "  ")(tree.root)
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
      case None =>  BellePrettyPrinter(Idioms.nil)
    }

    val children = node.children
    assert(!children.contains(node), "A node should not be its own child.") //but apparently this happens.

    if(children.length == 0) thisTactic
    else if(children.length == 1) thisTactic + " & " + extractTextWithoutParsing(tree)(children.head)
    else thisTactic + " <(\n  " + children.map(child => extractTextWithoutParsing(tree)(child)).mkString(",\n  ") + "\n)" //@note This doesn't work properly -- it generates the subgoals in the wrong order.
  }

  /**
    * @note this could be tailrec.
    * @return A structured Bellerophon tactic that constructs the proof tree.
    */
  def apply(modelId: Int)(node: TreeNode): BelleExpr = {
    val children = node.children
    assert(!children.contains(node), "A node should not be its own child.") //but apparently this happens.
    val gen = new ConfigurableGenerator(db.getInvariants(modelId))
    val thisTactic = tacticAt(gen, node)

    if (children.isEmpty || children.forall(_.endStep.isEmpty)) thisTactic
    else if (children.length == 1) thisTactic & apply(modelId)(children.head)
    else thisTactic & BranchTactic(children.map(child => apply(modelId)(child))) //@note This doesn't work properly -- it generates the subgoals in the wrong order.
  }

  def getTacticString(modelId: Int, indent: String)(node: TreeNode): String = {
    val children = node.children
    assert(!children.contains(node), "A node should not be its own child.") //but apparently this happens.
    val thisTactic = tacticStringAt(node)

    //@todo does pretty-printing
    if (children.isEmpty) thisTactic
    else if (children.length == 1) thisTactic + " & " + getTacticString(modelId, indent)(children.head)
    else thisTactic + " & <(\n" + children.map(child => indent + getTacticString(modelId, indent + "  ")(child)).mkString(",\n") + "\n" + indent + ")" //@note This doesn't work properly -- it generates the subgoals in the wrong order.
  }

  private def tacticAt(gen:Generator.Generator[Formula], node: TreeNode): BelleExpr = BelleParser.parseWithInvGen(tacticStringAt(node), Some(gen))

  private def tacticStringAt(node: TreeNode): String = node.endStep match {
    case Some(step) => try {
      db.getExecutable(step.executableId).belleExpr
    } catch {
      case e : ParseException => throw TacticExtractionError(e.getMessage, e)
      case e : ReflectiveExpressionBuilderExn => throw TacticExtractionError(s"Could not parse Bellerophon tactic because a base-tactic was missing (${e.getMessage}):" + db.getExecutable(step.executableId).belleExpr, e)
      case t : Throwable =>
        t.printStackTrace() //Super useful for debugging since TacticExtractionError seems to swallow its cause, or at least it doesn't always get printed out...
        throw TacticExtractionError(s"Could not retrieve executable ${step.executableId} from the database because $t", t)
    }
    case None => BellePrettyPrinter(Idioms.nil)
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

