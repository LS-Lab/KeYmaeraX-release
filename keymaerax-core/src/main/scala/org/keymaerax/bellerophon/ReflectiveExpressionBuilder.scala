/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.bellerophon

import org.keymaerax.Logging
import org.keymaerax.btactics.*
import org.keymaerax.btactics.macros.*
import org.keymaerax.core.*
import org.keymaerax.infrastruct.{PosInExpr, Position}
import org.keymaerax.parser.{Declaration, ParseException, UnknownLocation}

import scala.annotation.nowarn

/**
 * Constructs a [[org.keymaerax.bellerophon.BelleExpr]] from a tactic name
 * @author Nathan Fulton
 * @author Brandon Bohrer
 */
object ReflectiveExpressionBuilder extends Logging {
  private def generatorArg(generator: Option[InvariantGenerator]): InvariantGenerator = generator.getOrElse {
    logger.debug(s"Need a generator but none was provided; switching to default.")
    TactixLibrary.invGenerator
  }

  private def castArg(info: ArgInfo, arg: Seq[Any]): Any = {
    (info, arg) match {
      // The previous code did not implement casting of GeneratorArgs,
      // but I don't see a good reason why not, so it is allowed here.
      // If something breaks because of this, it should be safe to remove.
      case (_: GeneratorArg, Seq(value: InvariantGenerator)) => value

      case (_: FormulaArg, Seq(value: Formula)) => value
      case (_: StringArg, Seq(value: String)) => value
      case (_: NumberArg, Seq(value: Number)) => value
      case (_: VariableArg, Seq(value: Variable)) => value
      case (_: TermArg, Seq(value: Term)) => value
      case (_: SubstitutionArg, Seq(value: SubstitutionPair)) => value
      case (_: ExpressionArg, Seq(value: Expression)) => value
      case (_: PosInExprArg, Seq(value: PosInExpr)) => value

      case (OptionArg(_: GeneratorArg), Seq(value: GeneratorArg)) => Some(value)
      case (OptionArg(_: FormulaArg), Seq(value: Formula)) => Some(value)
      case (OptionArg(_: StringArg), Seq(value: String)) => Some(value)
      case (OptionArg(_: NumberArg), Seq(value: Number)) => Some(value)
      case (OptionArg(_: VariableArg), Seq(value: Variable)) => Some(value)
      case (OptionArg(_: TermArg), Seq(value: Term)) => Some(value)
      case (OptionArg(_: SubstitutionArg), Seq(value: SubstitutionPair)) => Some(value)
      case (OptionArg(_: ExpressionArg), Seq(value: Expression)) => Some(value)
      case (OptionArg(_: PosInExprArg), Seq(value: PosInExpr)) => Some(value)

      // This blindly trusts the contents of the list because the previous code also did.
      // Thanks to type erasure, we'd have to check each argument's type individually,
      // which would worsen performance (though I don't know how much).
      case (ListArg(_: GeneratorArg), arg) => arg
      case (ListArg(_: FormulaArg), arg) => arg
      case (ListArg(_: StringArg), arg) => arg
      case (ListArg(_: NumberArg), arg) => arg
      case (ListArg(_: VariableArg), arg) => arg
      case (ListArg(_: TermArg), arg) => arg
      case (ListArg(_: SubstitutionArg), arg) => arg
      case (ListArg(_: ExpressionArg), arg) => arg
      case (ListArg(_: PosInExprArg), arg) => arg

      case _ => throw ParseException(s"Failed to convert arguments to $info", UnknownLocation)
    }
  }

  private def placeholderArg(info: ArgInfo): Any = {
    info match {
      case _: OptionArg => None
      case _: ListArg => Nil
      case _ => throw ParseException(s"Failed to create placeholder argument for $info", UnknownLocation)
    }
  }

  private def prepareArgs(
      inputs: List[ArgInfo],
      args: List[Seq[Any]],
      generator: Option[InvariantGenerator],
  ): List[Any] = (inputs, args) match {
    case ((_: GeneratorArg) :: inputs, args) => generatorArg(generator) :: prepareArgs(inputs, args, generator)
    case (input :: inputs, arg :: args) => castArg(input, arg) :: prepareArgs(inputs, args, generator)
    case (input :: inputs, Nil) => placeholderArg(input) :: prepareArgs(inputs, args, generator)
    case (Nil, Nil) => Nil
    case (Nil, _) => throw ParseException("Too many arguments supplied", UnknownLocation)
  }

  def applyNonpositionalArgs(info: TacticInfo, args: List[Seq[Any]], generator: Option[InvariantGenerator]): BelleExpr =
    info.constructor.construct(prepareArgs(info.inputs, args, generator)).asInstanceOf[BelleExpr]

  @nowarn("cat=deprecation&origin=org.keymaerax.bellerophon.DependentTwoPositionTactic")
  @nowarn("cat=deprecation&origin=org.keymaerax.bellerophon.AppliedDependentTwoPositionTactic")
  def applyPositionalArgs(info: DerivationInfo, expr: BelleExpr, args: List[PositionLocator]): BelleExpr = {
    (expr, args, info.numPositionArgs) match {
      // If the tactic accepts arguments but wasn't given any, return the unapplied tactic under the assumption that
      // someone is going to plug in the arguments later
      case (expr: BelleExpr, Nil, _) => expr
      case (expr: (BelleExpr & PositionalTactic), arg :: Nil, 1) => AppliedPositionTactic(expr, arg)
      case (expr: DependentTwoPositionTactic, Fixed(arg1: Position, _, _) :: Fixed(arg2: Position, _, _) :: Nil, 2) =>
        AppliedDependentTwoPositionTactic(expr, arg1, arg2)
      case (expr: DependentPositionWithAppliedInputTactic, loc :: Nil, 1) =>
        new AppliedDependentPositionTacticWithAppliedInput(expr, loc)
      case (expr: DependentPositionTactic, arg :: Nil, 1) => new AppliedDependentPositionTactic(expr, arg)
      case (expr: BuiltInTwoPositionTactic, Fixed(arg1: Position, _, _) :: Fixed(arg2: Position, _, _) :: Nil, 2) =>
        AppliedBuiltinTwoPositionTactic(expr, arg1, arg2)
      case (expr: Function1[_, _], Fixed(arg1: Position, _, _) :: arg2 :: Nil, 2) =>
        new AppliedDependentPositionTactic(expr.asInstanceOf[(Position => DependentPositionTactic)](arg1), arg2)
      case (expr: Function2[_, _, _], Fixed(arg1: Position, _, _) :: Fixed(arg2: Position, _, _) :: Nil, 2) => expr
          .asInstanceOf[((Position, Position) => BelleExpr)](arg1, arg2)
      case (expr, pArgs, num) =>
        if (pArgs.length > num) {
          throw ParseException(
            "Expected either " + num + s" or 0 position arguments for ${expr.getClass} ($expr), got " + pArgs.length,
            UnknownLocation,
          )
        } else {
          throw ParseException(
            "Tactic " + info.codeName + "\n  arguments\ndoes not match type " + expr.getClass.getSimpleName,
            UnknownLocation,
          )
        }
    }
  }

  /**
   * Create the BelleExpr tactic expression `name(arguments)`.
   * @param name The codeName of the Bellerophon tactic to create according to [[TacticInfo.codeName]].
   * @param arguments the list of arguments passed to the tactic, either expressions or positions.
   * @param generator invariant generators passed to the tactic, if any.
   * @param defs
   * @return `name(arguments)` as a BelleExpr.
   */
  def apply(
      name: String,
      arguments: List[Either[Seq[Any], PositionLocator]] = Nil,
      generator: Option[InvariantGenerator],
      defs: Declaration,
  ): BelleExpr = {
    val info = DerivationInfo
      .byCodeName
      .getOrElse(name, throw ParseException(s"Identifier '$name' does not exist.", UnknownLocation))

    val positional = arguments.flatMap(_.toOption)
    val nonpositional = arguments.flatMap(_.left.toOption)

    val expr = info match {
      case info: TacticInfo => applyNonpositionalArgs(info, nonpositional, generator)
      case info: ProvableInfo => UnifyUSCalculus.useAt(info)
      case _ => throw ParseException(s"Identifier '$name' is neither a tactic nor a provable.", UnknownLocation)
    }

    applyPositionalArgs(info, expr, positional)
  }
}
