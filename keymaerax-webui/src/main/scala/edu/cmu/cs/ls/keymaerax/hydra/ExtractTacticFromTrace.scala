package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.bellerophon.{BTacticParser, BranchTactic, SeqTactic, BelleExpr}
import edu.cmu.cs.ls.keymaerax.btactics.Idioms.nil

import scala.annotation.tailrec

/**
  * Extracts a tactic from a sequence of execution steps. Very inefficient.
  * @author Nathan Fulton
  */
class ExtractTacticFromTrace(db: DBAbstraction) {
  def apply(executionId: Int) = {
    val steps = db.getExecutionSteps(executionId)
    println(steps.length)
    assert(steps.length > 0, "All proofs should have at least one step.")
    extract(steps)
  }


  private def extract(steps: List[ExecutionStepPOJO]) : BelleExpr = extract(None, firstStep(steps), steps)

  /** Computes a [[BelleExpr]] corresponding to steps.
    * @note slightly convoluted so that it's tailrec. */
  @tailrec
  private def extract(prevExpr: Option[BelleExpr], currentStep : ExecutionStepPOJO, allSteps: List[ExecutionStepPOJO]) : BelleExpr = {
    println("Extracting step " + currentStep)
    if(isBranchingTactic(currentStep, allSteps)) {
      println("Found branching tactic: " + currentStep)
      val (branchExpr, next) = (expressionForBranchingStep(currentStep, allSteps), nextStep(currentStep, allSteps))

      if(next.isEmpty) branchExpr
      else {
        val recExpr = prevExpr match {
          case Some(prev) => prev & branchExpr
          case None => branchExpr
        }
        extract(Some(recExpr), next.get, allSteps)
      }
    }
    else { //this is not a branching tactic.
      //@note if we get the list of execution steps in a given order, then we can pretty efficiently traverse that list.
      //But I'm assuming we don't get the list of execution steps in any particular order, and that we haven't pre-sorted them, so we have to call the expensive transitive function.
      val linear = orderedNonBranchingTransitiveSuccessors(currentStep.stepId.get, allSteps)
      val linearSequenceFromCurrent = {
        if(linear.length == 0) exprAtStep(currentStep)
        else if(linear.length == 1) exprAtStep(currentStep) & exprAtStep(linear.head)
        else {
          //Drop the right-most to prevent stuttering. It'll be added back in the recursive call.
          linear.dropRight(1).map(exprAtStep).foldLeft(exprAtStep(currentStep))((seq, next) => seq & next)
        }
      }
      val recExpr = prevExpr match {
        case Some(prev) => prev & linearSequenceFromCurrent
        case None => linearSequenceFromCurrent
      }
      if(linear.length != 0) extract(Some(recExpr), linear.last, allSteps)
      else recExpr
    }
  }

  /** Returns the unqiue first step in the proof, or fails an assertion. */
  private def firstStep(steps: List[ExecutionStepPOJO]) = {
    val candidates = steps.filter(step => step.previousStep.isEmpty && step.parentStep.isEmpty)
    assert(candidates.length == 1, "Every proof needs a first step -- i.e. a step with no previous step and no parent step.")
    candidates.head
  }


  /** Returns the step in the proof that comes after currentStep. */
  private def nextStep(currentStep : ExecutionStepPOJO, steps : List[ExecutionStepPOJO]) : Option[ExecutionStepPOJO] = {
    if(steps.length == 0) None
    else {
      assert(currentStep.stepId.isDefined)

      val stepId = steps.head.stepId.get
      val nextSteps = steps.filter(step => step.previousStep match {
        case Some(previousStepId) => stepId == previousStepId
        case None => false
      })

      if(nextSteps.length == 0) None
      else {
        val pruned = pruneAlternatives(nextSteps)
        assert(pruned.length <= 1)
        pruned.headOption match {
          case Some(theHead) => Some(theHead)
          case None => ??? //Really, there should have been something.
        }
      }
    }
  }

  /** Extracts a [[BelleExpr]] for a single step. */
  private def exprAtStep(step: ExecutionStepPOJO) : BelleExpr = {
    //If steps.head isn't a branching tactic, then peel it off the list and retrieve the belle expr corresponding to its executable.
    val exprStr = db.getExecutable(step.executableId).belleExpr match {
      case Some(s) => s
      case None    => throw new Exception("Incorrectly assumed the UI is using BelleExprs for everything.")
    }
    //@todo enforce a contract that all expressions entered into the database actually parse.
    println("About to try parsing " + exprStr)
    BTacticParser(exprStr).get
  }

  private def headIsBranchingTactic(steps: List[ExecutionStepPOJO]) = {
    assert(steps.length >= 1)
    val head = steps(0)
    isBranchingTactic(head, steps.tail)
  }

  /** Returns true if branchHead has any child steps. */
  private def isBranchingTactic(branchHead: ExecutionStepPOJO, steps: List[ExecutionStepPOJO]) = {
    assert(branchHead.stepId.isDefined)
    steps.contains((step : ExecutionStepPOJO) => branchHead.stepId == step.parentStep)
  }

  /** Filters out all obsolete branch alternatives. */
  private def pruneAlternatives(steps: List[ExecutionStepPOJO]) : List[ExecutionStepPOJO] = {
    //@note written this way so that the order isn't modified...
    //Break the list of steps into groupings based upon their previous step.
    val oldAlternatives =
      steps.groupBy(_.previousStep)
        .map(grouping => {
          val newest = newestAlternative(grouping._2.head, grouping._2)
          grouping._2.filter(step => step != newest)
        }).flatten.toList
    steps.filter(step => !oldAlternatives.contains(step))
  }

  private def newestAlternative(anAlternative: ExecutionStepPOJO, steps: List[ExecutionStepPOJO]) = {
    steps.foldLeft(anAlternative)((smallestAlternative, step) => {
      if(step.alternativeOrder < smallestAlternative.alternativeOrder) step else smallestAlternative
    })
  }

  private def expressionForBranchingStep(parent: ExecutionStepPOJO, stepsMaybeContainingHead: List[ExecutionStepPOJO]) : BelleExpr = {
    assert(parent.stepId.isDefined)

    val steps = stepsMaybeContainingHead.filter(x => x != parent)

    val branchTactics : Seq[BelleExpr] = {
      val branchHeads = steps.filter(childCandidate => childCandidate.parentStep.isDefined && childCandidate.parentStep == parent.stepId)
      assert(branchHeads.length != 0, "expressionForBranchingStep should be called only when steps.head has a child.")

      val prunedBranchHeads = pruneAlternatives(branchHeads) //@todo prune out branches that are old alternatives.

      assert(branchHeads.forall(_.branchOrder.isDefined), "Do not currently support labeled branches.") //@todo support labeled branches.
      prunedBranchHeads
        .sortBy(branchHead => branchHead.branchOrder.get)
        .map(branchHead => extract(None, branchHead, steps))
    }

    exprAtStep(parent) & BranchTactic(branchTactics.toSeq)
  }

  def orderedNonBranchingTransitiveSuccessors(id: Int, steps: List[ExecutionStepPOJO]) : Seq[ExecutionStepPOJO] = {
    val next = steps.find(step => step.previousStep.isDefined && step.previousStep.get == id && !isBranchingTactic(step, steps))
    next match {
      case Some(next) => next +: orderedNonBranchingTransitiveSuccessors(next.stepId.get, steps) //@todo assuming that there aren't any cycles in previousStep relationships... enforce on insert?
      case None       => List()
    }
  }

}
