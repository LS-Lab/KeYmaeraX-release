/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.bellerophon

import org.keymaerax.Logging
import org.keymaerax.btactics.*
import org.keymaerax.btactics.macros.*
import org.keymaerax.btactics.macros.DerivationInfoAugmentors.*
import org.keymaerax.core.*
import org.keymaerax.infrastruct.{PosInExpr, Position}
import org.keymaerax.parser.{Declaration, ParseException, UnknownLocation}

import scala.annotation.{nowarn, tailrec}
import scala.reflect.runtime.universe.{typeTag, Type}

/**
 * Constructs a [[org.keymaerax.bellerophon.BelleExpr]] from a tactic name
 * @author
 *   Nathan Fulton
 * @author
 *   Brandon Bohrer
 */
object ReflectiveExpressionBuilder extends Logging {

  /** A sort of inverse of the `typeName` function in the [[Tactic]] macro. */
  private def argTypeToArgInfo(t: Type): ArgInfo = {
    if (t <:< typeTag[org.keymaerax.btactics.InvariantGenerator].tpe) GeneratorArg("_")
    else if (t <:< typeTag[org.keymaerax.core.Formula].tpe) FormulaArg("_")
    else if (t <:< typeTag[String].tpe) StringArg("_")
    else if (t <:< typeTag[org.keymaerax.core.Number].tpe) NumberArg("_")
    else if (t <:< typeTag[org.keymaerax.core.Variable].tpe) VariableArg("_")
    else if (t <:< typeTag[org.keymaerax.core.Term].tpe) TermArg("_")
    else if (t <:< typeTag[org.keymaerax.core.SubstitutionPair].tpe) SubstitutionArg("_")
    else if (t <:< typeTag[org.keymaerax.core.Expression].tpe) ExpressionArg("_")
    else if (t <:< typeTag[org.keymaerax.infrastruct.PosInExpr].tpe) PosInExprArg("_")
    else if (t <:< typeTag[Option[?]].tpe) {
      val Seq(arg) = t.dealias.typeArgs
      OptionArg(argTypeToArgInfo(arg))
    } else if (t <:< typeTag[List[?]].tpe) {
      val Seq(arg) = t.dealias.typeArgs
      ListArg(argTypeToArgInfo(arg))
    } else throw ParseException(s"Unexpected argument type $t", UnknownLocation)
  }

  private def castArg(info: ArgInfo, arg: Seq[Any]): Any = {
    (info, arg) match {
      case (_: GeneratorArg, Seq(value: GeneratorArg)) => value
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

  private def applyGenerator(expr: Any, generator: Option[InvariantGenerator]): Any = {
    val theGenerator = generator.getOrElse {
      logger.debug(s"Need a generator but none was provided; switching to default.")
      TactixLibrary.invGenerator
    }
    expr.asInstanceOf[InvariantGenerator => Any](theGenerator)
  }

  @tailrec
  private def applyArgs(expr: Any, args: List[Seq[Any]]): Any = {
    val (arg, rest) = args match {
      case Nil => return expr
      case arg :: rest => (arg, rest)
    }

    val exprTyped = expr match {
      case e: TypedFunc[_, _] => e
      case _ => throw ParseException("Expected a TypedFunc", UnknownLocation)
    }

    val preparedArg = castArg(argTypeToArgInfo(exprTyped.argType.tpe), arg)
    val appliedExpr = exprTyped.asInstanceOf[TypedFunc[Any, ?]](preparedArg)
    applyArgs(appliedExpr, rest)
  }

  @tailrec
  private def fillArgs(expr: Any): Any = {
    val exprTyped = expr match {
      case e: TypedFunc[_, _] => e
      case _ => return expr
    }

    val info = argTypeToArgInfo(exprTyped.argType.tpe)
    if (!info.isInstanceOf[OptionArg] && !info.isInstanceOf[ListArg]) return expr

    val preparedArg = placeholderArg(info)
    val appliedExpr = exprTyped.asInstanceOf[TypedFunc[Any, ?]](preparedArg)
    fillArgs(appliedExpr)
  }

  @nowarn("cat=deprecation&origin=org.keymaerax.bellerophon.DependentTwoPositionTactic")
  @nowarn("cat=deprecation&origin=org.keymaerax.bellerophon.AppliedDependentTwoPositionTactic")
  def build(
      info: DerivationInfo,
      args: List[Either[Seq[Any], PositionLocator]],
      generator: Option[InvariantGenerator],
      defs: Declaration,
  ): BelleExpr = {
    val posArgs = args.flatMap(_.toOption)
    val expressionArgs = args.flatMap(_.left.toOption)

    var expr = info.belleExpr
    if (info.needsGenerator) expr = applyGenerator(expr, generator)
    expr = applyArgs(expr, expressionArgs)
    expr = fillArgs(expr)

    (expr, posArgs, info.numPositionArgs) match {
      // If the tactic accepts arguments but wasn't given any, return the unapplied tactic under the assumption that
      // someone is going to plug in the arguments later
      case (expr: BelleExpr, Nil, _) => expr
      case (expr: BelleExpr with PositionalTactic, arg :: Nil, 1) => AppliedPositionTactic(expr, arg)
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
            "Tactic " + info.codeName + " called with\n  " + expressionArgs.mkString(";") +
              "\n  arguments\ndoes not match type " + expr.getClass.getSimpleName,
            UnknownLocation,
          )
        }
    }
  }

  /**
   * Create the BelleExpr tactic expression `name(arguments)`.
   * @param name
   *   The codeName of the Bellerophon tactic to create according to [[TacticInfo.codeName]].
   * @param arguments
   *   the list of arguments passed to the tactic, either expressions or positions.
   * @param generator
   *   invariant generators passed to the tactic, if any.
   * @param defs
   * @return
   *   `name(arguments)` as a BelleExpr.
   */
  def apply(
      name: String,
      arguments: List[Either[Seq[Any], PositionLocator]] = Nil,
      generator: Option[InvariantGenerator],
      defs: Declaration,
  ): BelleExpr = {
    if (!DerivationInfo.hasCodeName(name)) {
      throw ParseException(s"Identifier '$name' is not recognized as a tactic identifier.", UnknownLocation)
    } else {
      try { build(DerivationInfo.ofCodeName(name), arguments, generator, defs) }
      catch { case e: java.util.NoSuchElementException => throw ParseException(s"Error when building tactic $name", e) }
    }
  }
}
