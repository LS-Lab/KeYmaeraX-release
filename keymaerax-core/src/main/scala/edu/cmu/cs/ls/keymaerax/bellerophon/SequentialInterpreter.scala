//package edu.cmu.cs.ls.keymaerax.bellerophon
//
//import edu.cmu.cs.ls.keymaerax.core.Provable
//
//import scala.annotation.tailrec
//
///**
// * An implementation of the evaluation semantics given in the Bellerophon paper.
// * @note Written so that it is easy to step through with a debugger.
// * @author Nathan Fulton
// */
//class SequentialInterpreter extends Interpreter {
//  override def apply(expr: BelleExpr, value: BelleValue) : BelleValue = expr match {
//    case SeqTactic(left, right) => {
//      val leftResult  = apply(left, value)
//      apply(right, leftResult)
//    }
//    case EitherTactic(left, right) => {
//      try {
//        LeftResult(apply(left, value))
//      }
//      catch {
//        case leftError : BelleError => {
//          try {
//            RightResult(apply(right, value))
//          }
//          catch {
//            case rightError : BelleError => {
//              throw new CompoundException(leftError, rightError)
//            }
//          }
//        }
//      }
//    }
//    case ExactIterTactic(child, count) => {
//      if(count < 0) throw new Exception("Expected non-negative count")
//      if(count == 0) value
//      else tailrecNTimes(child, value, count)
//    }
//    case SaturateTactic(child, annotation) => tailrecSaturate(child, asBelleProvable(value), annotation)
//    case BranchTactic(children) => {
//      val belleProvable = asBelleProvable(value)
//      val subgoals = belleProvable.p.subgoals.map(Provable.startProof)
//
//      if(subgoals.length != children.length)
//        throw BelleError("Provable list and child list length mismatch")
//
//      val results = (children zip subgoals) map (pi => apply(pi._1, BelleProvable(pi._2)))
//      ???
//    }
////      if(vs.length == children.length)
////        (children zip vs) flatMap (ci => apply(ci._1, Seq(ci._2)))
////      else
////        throw BelleError(s"Length mismatch on branching tactic: have ${vs.length} values but ${children.length} tactics")
//    case OptionalTactic(child) => {
//      try {
//        apply(child, value)
//      }
//      catch {
//        case e: BelleError => value
//      }
//    }
////    case USubstPatternTactic(options) => {
////      val vsAsProvables : Seq[Provable] = toBelleProvables(vs).map(_.p)
////      val firstUsubstMatch = options.find(pi => TypeChecker.findSubst(pi._1, vsAsProvables).isDefined)
////      firstUsubstMatch match {
////        case Some(pair) => apply(pair._2, vs)
////        case None => throw BelleError("USubst case distinction failed.")
////      }
////    }
////    case ParametricTactic(t, body) =>
////      throw BelleError("Tried to apply a type-abstracted expression to a value.")
////    case ParaAppTactic(fn, arg) => ???
//
//    case SumProjection(le, re) => value match {
//      case LeftResult(l)  => apply(le, l)
//      case RightResult(r) => apply(re, r)
//      case _ => throw BelleError(s"Expected LeftResult or RightResult but found a ${value.getClass.getName}")
//    }
//  }
//
//  private def toBelleProvables(values : Seq[BelleValue]) = values.map(_ match {
//    case x : BelleProvable => x
//    case _                 => throw BelleError("Need only Provables")
//  })
//
//  @tailrec
//  private final def tailrecSaturate(child: BelleExpr,
//                                    value: BelleProvable,
//                                    annotation: BelleType): BelleProvable =
//  {
//    val oneStep = apply(child, value)
//    if(value == oneStep) {
//      if(TypeChecker.findSubst(annotation, value.p).isDefined) value
//      else throw BelleError("Result should have matched result type annotation after reaching fixed point.")
//    }
//    else oneStep match {
//      case p : BelleProvable => tailrecSaturate(child, p, annotation)
//      case _ => throw BelleError(s"Result should have been a BelleProvable but found a ${oneStep.getClass.getName}")
//    }
//  }
//
//
//  @tailrec
//  private final def tailrecNTimes(e : BelleExpr, value: BelleValue, n: Int) : BelleValue = {
//    if(n < 0) throw BelleError(s"Should not try to iterate less than 0 times, but tried to iterate $n times")
//    if(n == 0) value
//    else tailrecNTimes(e, apply(e, value), n - 1)
//  }
//
//  private def asBelleProvable(v : BelleValue) = v match {
//    case bp : BelleProvable => bp
//    case _ => throw BelleError(s"Expected a BelleProvable but found ${v.getClass.getName}")
//  }
//}
