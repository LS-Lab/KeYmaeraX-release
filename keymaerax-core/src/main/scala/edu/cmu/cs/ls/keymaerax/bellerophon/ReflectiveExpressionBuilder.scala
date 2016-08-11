package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.btactics.{DerivationInfo, Generator}
import edu.cmu.cs.ls.keymaerax.core.{Expression, Formula, Term, Variable}

/**
  * Constructs a [[edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr]] from a tactic name
  * @author Nathan Fulton
  * @author Brandon Bohrer
  */
object ReflectiveExpressionBuilder {
  def build(info: DerivationInfo, args: List[Either[Seq[Expression], PositionLocator]], generator: Option[Generator[Formula]]): BelleExpr = {
    val posArgs = args.filter(_.isRight).map(_.right.getOrElse(throw new ReflectiveExpressionBuilderExn("Filtered down to only right-inhabited elements... this exn should never be thrown.")))
    val withGenerator =
      if (info.needsGenerator) {
        generator match {
          case Some(theGenerator) => info.belleExpr.asInstanceOf[Generator[Formula] => Any](theGenerator)
          case None => throw new ReflectiveExpressionBuilderExn(s"Need a generator for tactic ${info.codeName} but none was provided.")
        }
      } else {
        info.belleExpr
      }
    val expressionArgs = args.filter(_.isLeft).map(_.left.getOrElse(throw new ReflectiveExpressionBuilderExn("Filtered down to only left-inhabited elements... this exn should never be thrown.")))
    val applied: Any = expressionArgs.foldLeft(withGenerator) {
      case (expr: (Formula => Any), (fml: Formula) :: Nil) =>
        expr(fml)
      case (expr: (Variable => Any), (y: Variable) :: Nil) =>
        expr(y)
      case (expr: (Term => Any), (term: Term) :: Nil) =>
        expr(term)
      case (expr: (Seq[Expression] => Any), fmls: Seq[Expression]) =>
        expr(fmls)
      case (expr, fml) =>
        throw new Exception("Expected type Formula => Any , got " + expr.getClass.getSimpleName)
    }

    (applied, posArgs, info.numPositionArgs) match {
      // If the tactic accepts arguments but wasn't given any, return the unapplied tactic under the assumption that
      // someone is going to plug in the arguments later
      case (expr:BelleExpr, Nil, _) => expr
      case (expr:BelleExpr with PositionalTactic , arg::Nil, 1) => AppliedPositionTactic(expr, arg)
      case (expr:DependentTwoPositionTactic, Fixed(arg1: Position, _, _) :: Fixed(arg2: Position, _, _) :: Nil, 2) =>
        AppliedDependentTwoPositionTactic(expr, arg1, arg2)
      case (expr:DependentPositionWithAppliedInputTactic, loc::Nil, 1) => new AppliedDependentPositionTacticWithAppliedInput(expr, loc)
      case (expr:DependentPositionTactic, arg::Nil, 1) => new AppliedDependentPositionTactic(expr, arg)
      case (expr:BuiltInTwoPositionTactic, Fixed(arg1: Position, _, _)::Fixed(arg2: Position, _, _)::Nil, 2) =>
        AppliedBuiltinTwoPositionTactic(expr, arg1, arg2)
      case (expr: (Position => DependentPositionTactic), Fixed(arg1: Position, _, _)::arg2::Nil, 2) =>
        new AppliedDependentPositionTactic(expr(arg1), arg2)
      case (expr: ((Position, Position) => BelleExpr), Fixed(arg1: Position, _, _)::Fixed(arg2: Position, _, _)::Nil, 2) => expr(arg1, arg2)
      case (expr, pArgs, num) =>
        if (pArgs.length > num) {
          throw new ReflectiveExpressionBuilderExn("Expected either " + num + s" or 0 position arguments for ${expr.getClass} (${expr}), got " + pArgs.length)
        } else {
          throw new ReflectiveExpressionBuilderExn("Tactics with " + num + " arguments cannot have type " + expr.getClass.getSimpleName)
        }
    }
  }

  def apply(name: String, arguments: List[Either[Seq[Expression], PositionLocator]] = Nil, generator: Option[Generator[Formula]]) : BelleExpr = {
    if(!DerivationInfo.hasCodeName(name)) {
      throw new ReflectiveExpressionBuilderExn(s"Identifier '$name' is not recognized as a tactic identifier.")
    }
    else {
      try {
        build(DerivationInfo.ofCodeName(name), arguments, generator)
      }
      catch {
        case e: java.util.NoSuchElementException =>
          println("Error: " + e)
          throw new Exception(s"Encountered errror when trying to find info for identifier ${name}, even though ${name} is a code-name for a tactic.")
      }
    }
  }
}


class ReflectiveExpressionBuilderExn(msg: String) extends Exception(msg)
