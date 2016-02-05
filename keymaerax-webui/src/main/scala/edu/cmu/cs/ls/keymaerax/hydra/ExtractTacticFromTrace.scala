package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.bellerophon.{BranchTactic, BTacticParser, BelleExpr}

class ExtractTacticFromTrace(db: DBAbstraction) {
  def apply(proofId: Int): BelleExpr = apply(db.getExecutionTrace(proofId))

  def apply(et: ExecutionTrace) : BelleExpr = apply(et.steps.head, pruneDeadAlternatives(et), None)

  private def apply(hd: ExecutionStep, et : ExecutionTrace, prevExpr: Option[BelleExpr]): BelleExpr = {
    val(currentExpr, nextTrace) = toExpr(hd, et)

    val nextExpr = prevExpr match {
      case Some(prev) => prev & currentExpr
      case None       => currentExpr
    }

    if(nextTrace.steps.length == 0) nextExpr
    else apply(nextTrace.steps.head, nextTrace, Some(nextExpr))
  }

  /** Computes the expression for es and returns the resulting tactic together with the portion of the trace that wasn't consumed to construct the resulting tactic. */
  private def toExpr(es : ExecutionStep, trace : ExecutionTrace): (BelleExpr, ExecutionTrace) = {
    assert(trace.steps.contains(es), "trace could contain the step that is being converted.")
    if(isBranchingStep(es)) {
      val (branches, newTrace) = extractOrderedBranches(es, trace)
      val branchTactics = branches.map(branch => apply(branch))
      val expr = tacticAtStep(es) & BranchTactic(branchTactics)
      (expr, newTrace)
    }
    else (tacticAtStep(es), dropFromTrace(trace, 1))
  }

  /** Divides the trace into branchCount(hd)+1 parts -- the traces in each branch, and the trace that comes after the branching. */
  private def extractOrderedBranches(hd: ExecutionStep, trace: ExecutionTrace) : (List[ExecutionTrace], ExecutionTrace) = {
    val n = branchCount(hd)
    val subgoals = hd.output.get.subgoals
    assert(subgoals.length == n)

    ???
  }

  //@todo need to ask Brandon how alternatives work. For now assume no backtracking.
  private def pruneDeadAlternatives(et: ExecutionTrace): ExecutionTrace = {
    assert(et.alternativeOrder == 0 && et.steps.forall(_.alternativeOrder == 0), "Extraction does not yet support tactic extraction for proofs with alternatives (i.e., backtracking)")
    et
  }

  /** Returns the tactic that is associated with this step.
    * @note This extraction is purely local and therefore insufficient for treatment of branching tactics.
    *       See [[ExtractTacticFromTrace.toExpr]] which does global tactic extraction. */
  private def tacticAtStep(es: ExecutionStep) : BelleExpr = {
    val exprPrettyString = db.getExecutable(es.executableId).belleExpr
    exprPrettyString match {
      case Some(expr) => BTacticParser(expr).getOrElse(throw TacticExtractionError(s"Could not extract a tactic because the execution trace contains a step whose tactic does not parse: ${exprPrettyString}"))
      case None => throw TacticExtractionError("Tactic extraction failed because it assumes every executable is just a BelleExpr.")
    }
  }

  private def branchCount(es: ExecutionStep): Int = es.output match {
    case Some(output) => (output.subgoals.length - es.input.subgoals.length) + 1
    case None => 0 + 1
  }

  private def isBranchingStep(es : ExecutionStep) = branchCount(es) > 1


  /** Ftopd n steps from the front of et and returns the result. */
  private def dropFromTrace(et : ExecutionTrace, n: Int) =
    new ExecutionTrace(et.proofId, et.executionId, et.conclusion, et.steps.drop(n))

  case class TacticExtractionError(msg: String) extends Exception(msg)
}

