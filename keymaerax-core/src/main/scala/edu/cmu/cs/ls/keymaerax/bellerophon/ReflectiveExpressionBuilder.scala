/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.Logging
import edu.cmu.cs.ls.keymaerax.btactics.macros._
import edu.cmu.cs.ls.keymaerax.btactics.InvariantGenerator.GenProduct
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{PosInExpr, Position}
import edu.cmu.cs.ls.keymaerax.parser.{Declaration, ParseException, UnknownLocation}

import scala.annotation.tailrec
import scala.reflect.runtime.universe.typeTag
import DerivationInfoAugmentors._

/**
  * Constructs a [[edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr]] from a tactic name
  * @author Nathan Fulton
  * @author Brandon Bohrer
  */
object ReflectiveExpressionBuilder extends Logging {
  def build(info: DerivationInfo, args: List[Either[Seq[Any], PositionLocator]],
            generator: Option[Generator.Generator[GenProduct]], defs: Declaration): BelleExpr = {
    val posArgs = args.flatMap(_.toOption)
    val withGenerator =
      if (info.needsGenerator) {
        generator match {
          case Some(theGenerator) => info.belleExpr.asInstanceOf[Generator.Generator[GenProduct] => Any](theGenerator)
          case None =>
            logger.debug(s"Need a generator for tactic ${info.codeName} but none was provided; switching to default.")
            info.belleExpr.asInstanceOf[Generator.Generator[GenProduct] => Any](TactixLibrary.invGenerator)
        }
      } else {
        info.belleExpr
      }
    val expressionArgs = args.filter(_.isLeft).
      map(_.left.getOrElse(throw ParseException("Filtered down to only left-inhabited elements... this exn should never be thrown.", UnknownLocation)))

    val applied: Any = expressionArgs.foldLeft(withGenerator) {
      //@note matching on generics only to make IntelliJ happy, "if type <:< other" is the relevant check
      case (expr: TypedFunc[String, _], (s: String) :: Nil) if expr.argType.tpe <:< typeTag[String].tpe => expr(s)
      case (expr: TypedFunc[PosInExpr, _], (pie: PosInExpr) :: Nil) if expr.argType.tpe <:< typeTag[PosInExpr].tpe => expr(pie)
      case (expr: TypedFunc[Formula, _], (fml: Formula) :: Nil) if expr.argType.tpe <:< typeTag[Formula].tpe => expr(fml)
      case (expr: TypedFunc[Variable, _], (y: Variable) :: Nil) if expr.argType.tpe <:< typeTag[Variable].tpe => expr(y)
      case (expr: TypedFunc[Term, _], (term: Term) :: Nil) if expr.argType.tpe <:< typeTag[Term].tpe => expr(term)
      case (expr: TypedFunc[Expression, _], (ex: Expression) :: Nil) if expr.argType.tpe <:< typeTag[Expression].tpe => expr(ex)
      case (expr: TypedFunc[SubstitutionPair, _], (ex: SubstitutionPair) :: Nil) if expr.argType.tpe <:< typeTag[SubstitutionPair].tpe => expr(ex)
      case (expr: TypedFunc[Option[Formula], _], (fml: Formula) :: Nil) if expr.argType.tpe <:< typeTag[Option[Formula]].tpe  => expr(Some(fml))
      case (expr: TypedFunc[Option[Variable], _], (y: Variable) :: Nil) if expr.argType.tpe <:< typeTag[Option[Variable]].tpe => expr(Some(y))
      case (expr: TypedFunc[Option[Term], _], (term: Term) :: Nil) if expr.argType.tpe <:< typeTag[Option[Term]].tpe => expr(Some(term))
      case (expr: TypedFunc[Option[Expression], _], (ex: Expression) :: Nil) if expr.argType.tpe <:< typeTag[Option[Expression]].tpe => expr(Some(ex))
      case (expr: TypedFunc[Option[String], _], (s: String) :: Nil) if expr.argType.tpe <:< typeTag[Option[String]].tpe => expr(Some(s))
      case (expr: TypedFunc[Option[PosInExpr], _], (pie: PosInExpr) :: Nil) if expr.argType.tpe <:< typeTag[Option[PosInExpr]].tpe => expr(Some(pie))
      case (expr: TypedFunc[Seq[Expression], _], fmls: Seq[Expression]) if expr.argType.tpe <:< typeTag[Seq[Expression]].tpe => expr(fmls)
      case (expr: TypedFunc[Seq[Expression], _], fml: Expression) if expr.argType.tpe <:< typeTag[Seq[Expression]].tpe => expr(Seq(fml))
      case (expr: TypedFunc[Seq[SubstitutionPair], _], ex: Seq[SubstitutionPair]) if expr.argType.tpe <:< typeTag[Seq[SubstitutionPair]].tpe => expr(ex)
      case (expr: TypedFunc[Seq[SubstitutionPair], _], (ex: SubstitutionPair) :: Nil) if expr.argType.tpe <:< typeTag[Seq[SubstitutionPair]].tpe => expr(Seq(ex))
      case (expr: TypedFunc[_, _], _) => throw ParseException(s"Expected argument of type ${expr.argType}, but got " + expr.getClass.getSimpleName, UnknownLocation)
      case _ => throw ParseException("Expected a TypedFunc (cannot match due to type erasure)", UnknownLocation)
    }

    @tailrec
    def fillOptions(expr: Any): Any = expr match {
      case e: TypedFunc[Option[Formula], _]  if e.argType.tpe <:< typeTag[Option[Formula]].tpe  => fillOptions(e(None))
      case e: TypedFunc[Option[Term], _]     if e.argType.tpe <:< typeTag[Option[Term]].tpe     => fillOptions(e(None))
      case e: TypedFunc[Option[Variable], _] if e.argType.tpe <:< typeTag[Option[Variable]].tpe => fillOptions(e(None))
      case e: TypedFunc[Option[String], _]   if e.argType.tpe <:< typeTag[Option[String]].tpe   => fillOptions(e(None))
      case e: TypedFunc[Option[PosInExpr], _] if e.argType.tpe <:< typeTag[Option[PosInExpr]].tpe => fillOptions(e(None))
      case e: TypedFunc[List[Formula], _]    if e.argType.tpe <:< typeTag[List[Formula]].tpe => fillOptions(e(List.empty))
      case e: TypedFunc[List[Term], _]       if e.argType.tpe <:< typeTag[List[Term]].tpe => fillOptions(e(List.empty))
      case e: TypedFunc[List[Variable], _]   if e.argType.tpe <:< typeTag[List[Variable]].tpe => fillOptions(e(List.empty))
      case e: TypedFunc[List[String], _]     if e.argType.tpe <:< typeTag[List[String]].tpe => fillOptions(e(List.empty))
      case e => e
    }

    (fillOptions(applied), posArgs, info.numPositionArgs) match {
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
          throw ParseException("Expected either " + num + s" or 0 position arguments for ${expr.getClass} ($expr), got " + pArgs.length, UnknownLocation)
        } else {
          throw ParseException("Tactic " + info.codeName + " called with\n  " + expressionArgs.mkString(";") + "\n  arguments\ndoes not match type " + expr.getClass.getSimpleName, UnknownLocation)
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
  def apply(name: String, arguments: List[Either[Seq[Any], PositionLocator]] = Nil,
            generator: Option[Generator.Generator[GenProduct]], defs: Declaration) : BelleExpr = {
    if (!DerivationInfo.hasCodeName(name)) {
      throw ParseException(s"Identifier '$name' is not recognized as a tactic identifier.", UnknownLocation)
    } else {
      try {
        build(DerivationInfo.ofCodeName(name), arguments, generator, defs)
      } catch {
        case e: java.util.NoSuchElementException =>
          throw ParseException(s"Error when building tactic $name", e)
      }
    }
  }
}
