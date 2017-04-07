package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BRANCH_COMBINATOR, BelleParser, SEQ_COMBINATOR}
import edu.cmu.cs.ls.keymaerax.btactics.{ConfigurableGenerator, Generator, Idioms}
import edu.cmu.cs.ls.keymaerax.core.Formula

class ExtractTacticFromTrace(db: DBAbstraction) {
  // Additional wrappers
  def apply(tree: ProofTree): BelleExpr  = {
    apply(tree.info.modelId)(tree.root)
  }

  def getTacticString(tree: ProofTree): String = {
    getTacticString("  ")(tree.root)
  }

  /**
    * @note this could be tailrec.
    * @return A structured Bellerophon tactic that constructs the proof tree.
    */
  def apply(modelId: Option[Int])(node: ProofTreeNode): BelleExpr = {
    assert(!node.children.contains(node), "A node should not be its own child.") //but apparently this happens.
    val gen = None /* new ConfigurableGenerator(
      modelId match {
        case Some(mid) => db.getInvariants(mid)
        case None => Map()
      })*/
    val subgoals = node.children.map(apply(modelId)(_))
    val thisTactic = tacticAt(gen, node)

    if (subgoals.isEmpty || (subgoals.length == 1 && subgoals.head == Idioms.nil)) thisTactic
    else if (subgoals.length == 1) thisTactic & subgoals.head
    else thisTactic & BranchTactic(subgoals)
  }

  def getTacticString(indent: String)(node: ProofTreeNode): String = {
    assert(!node.children.contains(node), "A node should not be its own child.") //but apparently this happens.
    val thisTactic = tacticStringAt(node)
    val subgoals = node.children.map(getTacticString(indent + "  ")(_))

    //@todo does pretty-printing
    if (subgoals.isEmpty) thisTactic
    else if (subgoals.size == 1) sequentialTactic(thisTactic, subgoals.head)
    else sequentialTactic(thisTactic, BRANCH_COMBINATOR.img + "(\n" + subgoals.mkString(",\n") + "\n" + indent + ")")
  }

  private def tacticAt(gen: Option[Generator.Generator[Formula]], node: ProofTreeNode): BelleExpr = BelleParser.parseWithInvGen(tacticStringAt(node), gen)

  private def sequentialTactic(ts1: String, ts2: String): String = (ts1.trim(), ts2.trim()) match {
    case ("nil", _) => ts2
    case (_, "nil") => ts1
    case _ => ts1 + " " + SEQ_COMBINATOR.img + " " + ts2
  }

  //@note all children share the same maker
  private def tacticStringAt(node: ProofTreeNode): String = node.children.headOption match {
    case None => "nil"
    case Some(c) => c.maker match {
      case None => "nil"
      case Some(m) => m
    }
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

