package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core.Provable

import scala.annotation.tailrec

/**
 * An implementation of the evaluation semantics given in the Bellerophon paper.
 * @note Written so that it is easy to step through with a debugger.
 * @author Nathan Fulton
 */
class SequentialInterpreter extends Interpreter {
  override def apply(expr: BelleExpr, vs: Seq[BelleValue]) : Seq[BelleValue] = expr match {
    case SeqTactic(left, right) => {
      val leftResult  = apply(left, vs)
      apply(right, leftResult)
    }
    case EitherTactic(left, right) => {
      try {
        Seq(LeftResult(apply(left, vs)))
      }
      catch {
        case leftError : BelleError => {
          try {
            Seq(RightResult(apply(right, vs)))
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
      // one possible implementation consistent with parallel
      apply(EitherTactic(left, right), vs)
    }
    case ExactIterTactic(child, count) => {
      if(count < 0) throw new Exception("Expected non-negative count")
      if(count == 0) vs
      else tailrecNTimes(child, vs, count)
    }
    case SaturateTactic(child, annotation) =>
      tailrecSaturate(child, toBelleProvables(vs), annotation)
    case BranchTactic(children) =>
      if(vs.length == children.length)
        (children zip vs) flatMap (ci => apply(ci._1, Seq(ci._2)))
      else
        throw BelleError(s"Length mismatch on branching tactic: have ${vs.length} values but ${children.length} tactics")
    case OptionalTactic(child) => {
      try {
        apply(child, vs)
      }
      catch {
        case e: BelleError => vs
      }
    }
    case USubstPatternTactic(options) => {
      val vsAsProvables : Seq[Provable] = toBelleProvables(vs).map(_.p)
      val firstUsubstMatch = options.find(pi => TypeChecker.findSubst(pi._1, vsAsProvables).isDefined)
      firstUsubstMatch match {
        case Some(pair) => apply(pair._2, vs)
        case None => throw BelleError("USubst case distinction failed.")
      }
    }
    case ParametricTactic(t, body) =>
      throw BelleError("Tried to apply a type-abstracted expression to a value.")
    case ParaAppTactic(fn, arg) => ???

    case ProductProjection(le, re) => uniquev(vs) match {
      case LeftResult(l)  => apply(le, l)
      case RightResult(r) => apply(re, r)
    }
  }

  private def uniquev(values : Seq[BelleValue]) =
    if(values.length != 1) throw BelleError(s"Expected 1 (one) value but found ${values.length}")
    else values.head

  private def toBelleProvables(values : Seq[BelleValue]) = values.map(_ match {
    case x : BelleProvable => x
    case _                 => throw BelleError("Need only Provables")
  })

  @tailrec
  private final def tailrecSaturate(child: BelleExpr,
                                    values: Seq[BelleProvable],
                                    annotation: BelleType): Seq[BelleValue] =
  {
    val oneStep = toBelleProvables(apply(child, values))
    if(oneStep == values) {
      if(TypeChecker.findSubst(annotation, values.map(_.p)).isDefined) values
      else throw BelleError("Result should have matched result type annotation after reaching fixed point.")
    }
    else tailrecSaturate(child, oneStep, annotation)
  }


  @tailrec
  private final def tailrecNTimes(e : BelleExpr, v: Seq[BelleValue], n: Int) : Seq[BelleValue] = {
    if(n < 0) throw BelleError(s"Should not try to iterate less than 0 times, but tried to iterate $n times")
    if(n == 0) v
    else tailrecNTimes(e, apply(e, v), n - 1)
  }
}
