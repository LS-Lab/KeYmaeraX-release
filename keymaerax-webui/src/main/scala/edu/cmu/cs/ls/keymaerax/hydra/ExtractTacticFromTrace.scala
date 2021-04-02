package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BRANCH_COMBINATOR, BelleParser, BellePrettyPrinter, SEQ_COMBINATOR}
import edu.cmu.cs.ls.keymaerax.hydra.TacticExtractionErrors.TacticExtractionError
import edu.cmu.cs.ls.keymaerax.infrastruct.{AntePosition, Position, SuccPosition}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._

trait TraceToTacticConverter {
  def getTacticString(tree: ProofTree): String = getTacticString(tree.root, "  ")
  def getTacticString(node: ProofTreeNode, indent: String): String
}

class VerboseTraceToTacticConverter extends TraceToTacticConverter {
  def getTacticString(node: ProofTreeNode, indent: String): String = {
    assert(!node.children.contains(node), "A node should not be its own child.")
    val thisTactic = tacticStringAt(node)
    val subgoals = node.children.map(getTacticString(_, indent + (if (node.children.size <= 1) "" else "  ")))

    //@todo does pretty-printing
    if (subgoals.isEmpty) thisTactic
    else if (subgoals.size == 1) sequentialTactic(thisTactic, subgoals.head)
    else sequentialTactic(thisTactic, BRANCH_COMBINATOR.img + "(\n" + indent + subgoals.mkString(",\n" + indent) + "\n" + indent + ")")
  }

  private def sequentialTactic(ts1: String, ts2: String): String = (ts1.trim(), ts2.trim()) match {
    case ("nil", _) | ("skip", _)=> ts2
    case (_, "nil") | (_, "skip") => ts1
    case ("" | "()", "" | "()") => ""
    case (_, "" | "()") => ts1
    case ("" | "()", _) => ts2
    case _ => ts1 + SEQ_COMBINATOR.img + "\n" + ts2
  }

  /** Returns a copy of `pos` with index 0. */
  private def firstInSuccOrAnte(pos: Position): Position =
    if (pos.isAnte) AntePosition.base0(0, pos.inExpr) else SuccPosition.base0(0, pos.inExpr)

  /** Converts fixed position locators into search locators. */
  private def convertLocator(loc: PositionLocator, node: ProofTreeNode): PositionLocator = loc match {
    case Fixed(pos, None, _) => node.localProvable.subgoals.head.sub(pos.top) match {
      case Some(e) => Find(0, Some(e), firstInSuccOrAnte(pos), exact=true)
      case None => throw TacticExtractionError("Recorded position " + pos.prettyString + " does not exist in " +
        node.localProvable.subgoals.head.prettyString)
    }
    case Fixed(pos, Some(f), exact) => Find(0, Some(f), firstInSuccOrAnte(pos), exact)
    case _ => loc
  }

  //@note all children share the same maker
  private def tacticStringAt(node: ProofTreeNode): String = node.children.headOption match {
    case None => "nil"
    case Some(c) => c.maker match {
      case None => "nil"
      case Some(m) =>
        if (BelleExpr.isInternal(m)) "???" //@note internal tactics are not serializable (and should not be in the trace)
        else BelleParser(m) match {
          case t@AppliedPositionTactic(_, l) => BellePrettyPrinter(t.copy(locator = convertLocator(l, node)))
          case t: AppliedDependentPositionTactic =>
            BellePrettyPrinter(new AppliedDependentPositionTactic(t.pt, convertLocator(t.locator, node)))
          case t: AppliedDependentPositionTacticWithAppliedInput =>
            BellePrettyPrinter(new AppliedDependentPositionTacticWithAppliedInput(t.pt, convertLocator(t.locator, node)))
          case _ => m
        }
    }
  }
}

/** A legacy trace to tactic converter whose tactics are not verbose but unfortunately not robust either. */
@deprecated(since="4.9.4")
class LegacyTraceToTacticConverter extends TraceToTacticConverter {

  def getTacticString(node: ProofTreeNode, indent: String): String = {
    assert(!node.children.contains(node), "A node should not be its own child.")
    val thisTactic = tacticStringAt(node)
    val subgoals = node.children.map(getTacticString(_, indent + (if (node.children.size <= 1) "" else "  ")))

    //@todo does pretty-printing
    if (subgoals.isEmpty) thisTactic
    else if (subgoals.size == 1) sequentialTactic(thisTactic, subgoals.head)
    else sequentialTactic(thisTactic, BRANCH_COMBINATOR.img + "(\n" + indent + subgoals.mkString(",\n" + indent) + "\n" + indent + ")")
  }
  
  private def sequentialTactic(ts1: String, ts2: String): String = (ts1.trim(), ts2.trim()) match {
    case ("nil", _) | ("skip", _)=> ts2
    case (_, "nil") | (_, "skip") => ts1
    case ("" | "()", "" | "()") => ""
    case (_, "" | "()") => ts1
    case ("" | "()", _) => ts2
    case _ => ts1 + " " + SEQ_COMBINATOR.img + " " + ts2
  }

  //@note all children share the same maker
  private def tacticStringAt(node: ProofTreeNode): String = node.children.headOption match {
    case None => "nil"
    case Some(c) => c.maker match {
      case None => "nil"
      case Some(m) =>
        if (BelleExpr.isInternal(m)) "???" //@note internal tactics are not serializable (and should not be in the trace)
        else m
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

