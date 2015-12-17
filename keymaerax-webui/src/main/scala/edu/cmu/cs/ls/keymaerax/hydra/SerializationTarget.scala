package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.core.Provable

case class ExecutionTrace(steps : scala.collection.mutable.Seq[ExecutioneStep]) {
  assert(steps.nonEmpty)

  /** Checks that inputs and outputs match */
  def isAxiomaticProof =
    steps.foldLeft[Option[ExecutioneStep]](Some(steps.head))((current: Option[ExecutioneStep], next: ExecutioneStep) => {
      current match {
        case None => None
        case Some(currStep) => if(currStep.result == next.input) Some(next) else None
      }
    }).nonEmpty
}

case class ExecutioneStep(input: Provable, step: ExecutionStepResult) {
  def result = step.result(input)
}

sealed trait ExecutionStepResult {
  def result(input: Provable): Provable
}
trait AtomicProvableStepResult extends ExecutionStepResult
/** @note output is just result, but doesn't have the correct type.
  */
case class Direct(output: Provable) extends AtomicProvableStepResult{
  override def result(p: Provable) = output
}
case class SubDerivation(at: Int, sub: Provable) extends AtomicProvableStepResult {
  override def result(input: Provable) = input(sub, at)
}
case class Alternative(alts: scala.collection.mutable.Stack[AtomicProvableStepResult]) extends ExecutionStepResult {
  assert(alts.nonEmpty, "Alternative provable steps should have at least one alternative")
  override def result(input: Provable) = alts.pop().result(input)

  def addAlternative(newResult: AtomicProvableStepResult) = alts.push(newResult)
}