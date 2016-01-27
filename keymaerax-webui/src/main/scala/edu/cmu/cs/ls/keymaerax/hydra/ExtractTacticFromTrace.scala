package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.bellerophon.{BTacticParser, BranchTactic, SeqTactic, BelleExpr}

import scala.annotation.tailrec

/**
  * Extracts a tactic from a sequence of execution steps.
  * @author Nathan Fulton
  */
class ExtractTacticFromTrace(db: DBAbstraction) {
  def apply(proofId: Int) = {???}

  /** A perfect proof is a tactic that contains no back-tracking. */
  private def removePrunedAlternatives(steps: List[ExecutionStepPOJO]) = steps //@todo implement.


  private def expressionFor(steps: List[ExecutionStepPOJO]) : BelleExpr = expressionFor(None, steps)

  /** Computes a [[BelleExpr]] corresponding to steps.
    * @note slightly convoluted so that it's tailrec. */
  @tailrec
  private def expressionFor(prevExpr: Option[BelleExpr], steps: List[ExecutionStepPOJO]) : BelleExpr = {
    if(headIsBranchingTactic(steps)) {
      val (branchExpr, branchTail) = expressionForBranchingStep(steps)
      val recExpr = prevExpr match {
        case Some(prev) => prev & branchExpr
        case None       => branchExpr
      }
      expressionFor(Some(recExpr), branchTail)
    }
    else {
      val nextExpr = expressionFor(steps.head)
      val recExpr = prevExpr match {
        case Some(prev) => prev & nextExpr
        case None       => nextExpr
      }
      expressionFor(Some(recExpr), steps.tail)
    }
  }

  /** Extracts a [[BelleExpr]] for a single step. */
  private def expressionFor(step: ExecutionStepPOJO) : BelleExpr = {
    //If steps.head isn't a branching tactic, then peel it off the list and retrieve the belle expr corresponding to its executable.
    val exprStr = db.getExecutable(step.executableId).belleExpr match {
      case Some(s) => s
      case None    => ??? //@todo currently the UI is using belle exprs for everything anyways.
    }
    BTacticParser(exprStr).get //@todo enforce this contract when we insert into the database, rather than crying later on that we can't actually reproduce the proof.
  }

  /** Returns true if this tactic has any child tactics. */
  def headIsBranchingTactic(steps: List[ExecutionStepPOJO]) = {
    assert(steps.length >= 1)
    val head = steps(0)
    assert(head.stepId.isDefined)
    steps.contains((step : ExecutionStepPOJO) => head.stepId == step.previousStep)
  }

  /**
    * Returns a pair p:
    *     p._1 is (steps.head < (e1, ..., en)) where e1 ... en are tactics for the child steps of steps.head
    *     p._2 is all of the steps that weren't either head or involved in any of e1 ... en
    */
  private def expressionForBranchingStep(steps: List[ExecutionStepPOJO]) : (BelleExpr, List[ExecutionStepPOJO]) = {
    assert(steps.head.stepId.isDefined)

    val parent = steps.head

    val orderedBranches : List[List[ExecutionStepPOJO]] = {
      val branchHeads = steps.filter(childCandidate => childCandidate.parentStep.isDefined && childCandidate.parentStep == parent.stepId)
      assert(branchHeads.length != 0, "expressionForBranchingStep should be called only when steps.head has a child.")

      val prunedBranchHeads = branchHeads //@todo prune out branches that are old alternatives.

      assert(branchHeads.forall(_.branchOrder.isDefined), "Do not currently support labeled branches.") //@todo support labeled branches.
      val orderedAndPrunedBranchHeads = prunedBranchHeads.sortBy(branchHead => branchHead.branchOrder.get)

      orderedAndPrunedBranchHeads.map(branchOf(steps.tail))
    }

    val orderedBranchTactics = orderedBranches.map(expressionFor)
    val theTactic = expressionFor(parent) & BranchTactic(orderedBranchTactics.toSeq)

    val allBranchSteps = orderedBranches.flatten
    val remainingSteps = steps.tail.filter(!allBranchSteps.contains(_))

    (theTactic, remainingSteps)
  }

  /** Returns a list of all tactics that are transitive children or transitive successors of brancHead. */
  def branchOf(steps: List[ExecutionStepPOJO])(branchHead: ExecutionStepPOJO) : List[ExecutionStepPOJO] = {
    assert(branchHead.stepId.isDefined)
    ???
  }

  def transitiveSuccessors(id: Int, steps: List[ExecutionStepPOJO]) : List[ExecutionStepPOJO] = {
    val next = steps.find(step => step.previousStep.isDefined && step.previousStep.get == id)
    next match {
      case Some(next) => next +: transitiveSuccessors(next.previousStep.get, steps) //@todo assuming that there aren't any cycles in previousStep relationships... enforce on insert?
      case None       => ???
    }
  }

}
