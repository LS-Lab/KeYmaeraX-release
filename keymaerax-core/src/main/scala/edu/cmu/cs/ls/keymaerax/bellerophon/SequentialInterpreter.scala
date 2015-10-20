package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core.Provable

import scala.annotation.tailrec

/**
 * An implementation of the evaluation semantics given in the Bellerophon paper.
 * @note Written so that it is easy to step through.
 * @author Nathan Fulton
 */
class SequentialInterpreter extends Interpreter {
  override def apply(expr: BelleExpr, inputValues: Seq[BelleValue]) : Seq[BelleValue] = expr match {
    case SeqTactic(left, right) => {
      val leftResult  = apply(left, inputValues)
      apply(right, leftResult)
    }
    case EitherTactic(left, right) => {
      try {
        Seq(LeftResult(apply(left, inputValues)))
      }
      catch {
        case leftError : BelleError => {
          try {
            Seq(RightResult(apply(right, inputValues)))
          }
          catch {
            case rightError : BelleError => {
              throw new CompoundException(leftError, rightError)
            }
          }
        }
      }
    }
    case ParallelTactic(left, right) => {
      apply(EitherTactic(left, right), inputValues)
    }
    case ExactIterTactic(child, count) => {
      if(count < 0) throw new Exception("Expected non-negative count")
      if(count == 0) inputValues
      else tailrecNTimes(child, inputValues, count)
    }
    case SaturateTactic(child, annotation) =>
      tailrecSaturate(child, toBelleProvables(inputValues), annotation)
    case BranchTactic(children) =>
      if(inputValues.length == children.length)
        (children zip inputValues) flatMap (ci => apply(ci._1, Seq(ci._2)))
      else
        throw BelleError(s"Length mismatch on branching tactic: have ${inputValues.length} values but ${children.length} tactics")
    case OptionalTactic(child) => {
      try {
        apply(child, inputValues)
      }
      catch {
        case e: BelleError => inputValues
      }
    }

  }

  private def toBelleProvables(values : Seq[BelleValue]) = values.map(_ match {
    case x : BelleProvable => x
    case _                 => throw BelleError("Need only Provables")
  })

  @tailrec
  private final def tailrecSaturate(child: BelleExpr,
                                    values: Seq[BelleProvable],
                                    annotation: BelleType): Seq[BelleValue] =
  {
    if(TypeChecker.findSubst(annotation, values.map(_.p)).isDefined)
      values
    else
      tailrecSaturate(child, toBelleProvables(apply(child, values)), annotation)
  }


  @tailrec
  private final def tailrecNTimes(e : BelleExpr, v: Seq[BelleValue], n: Int) : Seq[BelleValue] = {
    if(n < 0) throw BelleError(s"Should not try to iterate less than 0 times, but tried to iterate $n times")
    if(n == 0) v
    else tailrecNTimes(e, apply(e, v), n - 1)
  }
}
