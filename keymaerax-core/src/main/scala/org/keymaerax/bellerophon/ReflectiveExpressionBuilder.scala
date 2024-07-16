/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.bellerophon

import org.keymaerax.Logging
import org.keymaerax.btactics.InvariantGenerator.GenProduct
import org.keymaerax.btactics._
import org.keymaerax.btactics.macros.DerivationInfoAugmentors._
import org.keymaerax.btactics.macros._
import org.keymaerax.core._
import org.keymaerax.infrastruct.{PosInExpr, Position}
import org.keymaerax.parser.{Declaration, ParseException, UnknownLocation}

import scala.annotation.{nowarn, tailrec}
import scala.reflect.runtime.universe.typeTag

/**
 * Constructs a [[org.keymaerax.bellerophon.BelleExpr]] from a tactic name
 * @author
 *   Nathan Fulton
 * @author
 *   Brandon Bohrer
 */
object ReflectiveExpressionBuilder extends Logging {
  @nowarn("cat=deprecation&origin=org.keymaerax.bellerophon.DependentTwoPositionTactic")
  @nowarn("cat=deprecation&origin=org.keymaerax.bellerophon.AppliedDependentTwoPositionTactic")
  def build(
      info: DerivationInfo,
      args: List[Either[Seq[Any], PositionLocator]],
      generator: Option[Generator[GenProduct]],
      defs: Declaration,
  ): BelleExpr = {
    val posArgs = args.flatMap(_.toOption)
    val withGenerator =
      if (info.needsGenerator) {
        generator match {
          case Some(theGenerator) => info.belleExpr.asInstanceOf[Generator[GenProduct] => Any](theGenerator)
          case None =>
            logger.debug(s"Need a generator for tactic ${info.codeName} but none was provided; switching to default.")
            info.belleExpr.asInstanceOf[Generator[GenProduct] => Any](TactixLibrary.invGenerator)
        }
      } else { info.belleExpr }
    val expressionArgs = args
      .filter(_.isLeft)
      .map(
        _.left
          .getOrElse(
            throw ParseException(
              "Filtered down to only left-inhabited elements... this exn should never be thrown.",
              UnknownLocation,
            )
          )
      )

    val applied: Any = expressionArgs.foldLeft(withGenerator) {
      case (expr: TypedFunc[_, _], (s: String) :: Nil) if expr.argType.tpe <:< typeTag[String].tpe =>
        expr.asInstanceOf[TypedFunc[String, _]](s)
      case (expr: TypedFunc[_, _], (pie: PosInExpr) :: Nil) if expr.argType.tpe <:< typeTag[PosInExpr].tpe =>
        expr.asInstanceOf[TypedFunc[PosInExpr, _]](pie)
      case (expr: TypedFunc[_, _], (fml: Formula) :: Nil) if expr.argType.tpe <:< typeTag[Formula].tpe =>
        expr.asInstanceOf[TypedFunc[Formula, _]](fml)
      case (expr: TypedFunc[_, _], (y: Variable) :: Nil) if expr.argType.tpe <:< typeTag[Variable].tpe =>
        expr.asInstanceOf[TypedFunc[Variable, _]](y)
      case (expr: TypedFunc[_, _], (term: Term) :: Nil) if expr.argType.tpe <:< typeTag[Term].tpe =>
        expr.asInstanceOf[TypedFunc[Term, _]](term)
      case (expr: TypedFunc[_, _], (ex: Expression) :: Nil) if expr.argType.tpe <:< typeTag[Expression].tpe =>
        expr.asInstanceOf[TypedFunc[Expression, _]](ex)
      case (expr: TypedFunc[_, _], (ex: SubstitutionPair) :: Nil)
          if expr.argType.tpe <:< typeTag[SubstitutionPair].tpe => expr.asInstanceOf[TypedFunc[SubstitutionPair, _]](ex)
      case (expr: TypedFunc[_, _], (fml: Formula) :: Nil) if expr.argType.tpe <:< typeTag[Option[Formula]].tpe =>
        expr.asInstanceOf[TypedFunc[Option[Formula], _]](Some(fml))
      case (expr: TypedFunc[_, _], (y: Variable) :: Nil) if expr.argType.tpe <:< typeTag[Option[Variable]].tpe =>
        expr.asInstanceOf[TypedFunc[Option[Variable], _]](Some(y))
      case (expr: TypedFunc[_, _], (term: Term) :: Nil) if expr.argType.tpe <:< typeTag[Option[Term]].tpe =>
        expr.asInstanceOf[TypedFunc[Option[Term], _]](Some(term))
      case (expr: TypedFunc[_, _], (ex: Expression) :: Nil) if expr.argType.tpe <:< typeTag[Option[Expression]].tpe =>
        expr.asInstanceOf[TypedFunc[Option[Expression], _]](Some(ex))
      case (expr: TypedFunc[_, _], (s: String) :: Nil) if expr.argType.tpe <:< typeTag[Option[String]].tpe =>
        expr.asInstanceOf[TypedFunc[Option[String], _]](Some(s))
      case (expr: TypedFunc[_, _], (pie: PosInExpr) :: Nil) if expr.argType.tpe <:< typeTag[Option[PosInExpr]].tpe =>
        expr.asInstanceOf[TypedFunc[Option[PosInExpr], _]](Some(pie))
      case (expr: TypedFunc[_, _], fmls: Seq[_]) if expr.argType.tpe <:< typeTag[Seq[Expression]].tpe =>
        expr.asInstanceOf[TypedFunc[Seq[Expression], _]](fmls.asInstanceOf[Seq[Expression]])
      case (expr: TypedFunc[_, _], fml: Expression) if expr.argType.tpe <:< typeTag[Seq[Expression]].tpe =>
        expr.asInstanceOf[TypedFunc[Seq[Expression], _]](Seq(fml))
      case (expr: TypedFunc[_, _], ex: Seq[_]) if expr.argType.tpe <:< typeTag[Seq[SubstitutionPair]].tpe =>
        expr.asInstanceOf[TypedFunc[Seq[SubstitutionPair], _]](ex.asInstanceOf[Seq[SubstitutionPair]])
      case (expr: TypedFunc[_, _], (ex: SubstitutionPair) :: Nil)
          if expr.argType.tpe <:< typeTag[Seq[SubstitutionPair]].tpe =>
        expr.asInstanceOf[TypedFunc[Seq[SubstitutionPair], _]](Seq(ex))
      case (expr: TypedFunc[_, _], _) => throw ParseException(
          s"Expected argument of type ${expr.argType}, but got " + expr.getClass.getSimpleName,
          UnknownLocation,
        )
      case _ => throw ParseException("Expected a TypedFunc (cannot match due to type erasure)", UnknownLocation)
    }

    @tailrec
    def fillOptions(expr: Any): Any = expr match {
      case e: TypedFunc[_, _] if e.argType.tpe <:< typeTag[Option[Formula]].tpe =>
        fillOptions(e.asInstanceOf[TypedFunc[Option[Formula], _]](None))
      case e: TypedFunc[_, _] if e.argType.tpe <:< typeTag[Option[Term]].tpe =>
        fillOptions(e.asInstanceOf[TypedFunc[Option[Term], _]](None))
      case e: TypedFunc[_, _] if e.argType.tpe <:< typeTag[Option[Variable]].tpe =>
        fillOptions(e.asInstanceOf[TypedFunc[Option[Variable], _]](None))
      case e: TypedFunc[_, _] if e.argType.tpe <:< typeTag[Option[String]].tpe =>
        fillOptions(e.asInstanceOf[TypedFunc[Option[String], _]](None))
      case e: TypedFunc[_, _] if e.argType.tpe <:< typeTag[Option[PosInExpr]].tpe =>
        fillOptions(e.asInstanceOf[TypedFunc[Option[PosInExpr], _]](None))
      case e: TypedFunc[_, _] if e.argType.tpe <:< typeTag[List[Formula]].tpe =>
        fillOptions(e.asInstanceOf[TypedFunc[List[Formula], _]](List.empty))
      case e: TypedFunc[_, _] if e.argType.tpe <:< typeTag[List[Term]].tpe =>
        fillOptions(e.asInstanceOf[TypedFunc[List[Term], _]](List.empty))
      case e: TypedFunc[_, _] if e.argType.tpe <:< typeTag[List[Variable]].tpe =>
        fillOptions(e.asInstanceOf[TypedFunc[List[Variable], _]](List.empty))
      case e: TypedFunc[_, _] if e.argType.tpe <:< typeTag[List[String]].tpe =>
        fillOptions(e.asInstanceOf[TypedFunc[List[String], _]](List.empty))
      case e => e
    }

    (fillOptions(applied), posArgs, info.numPositionArgs) match {
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
      generator: Option[Generator[GenProduct]],
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
