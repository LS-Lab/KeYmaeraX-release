package edu.cmu.cs.ls.keymaerax.btacticinterface

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.{Generator, DerivationInfo}
import edu.cmu.cs.ls.keymaerax.core.{SeqPos, Formula}

/**
  * Constructs a [[edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr]] from a tactic name
  * @author Nathan Fulton
  * @author Brandon Bohrer
  */
object ReflectiveExpressionBuilder {
  def build(info: DerivationInfo, args: List[Either[Formula, SeqPos]], generator: Option[Generator[Formula]]): BelleExpr = {
    val posArgs = args.filter{case arg => arg.isRight}.map{case arg => arg.right.get}
    val withGenerator =
      if (info.needsGenerator) {
        info.belleExpr.asInstanceOf[Generator[Formula] => Any](generator.get)
      } else {
        info.belleExpr
      }
    val formulaArgs = args.filter{case arg => arg.isLeft}.map{case arg => arg.left.get}
    val applied:Any = formulaArgs.foldLeft(withGenerator) {
      case ((expr:(Formula => Any)), fml) => expr(fml)
      case (expr:(Any), fml) =>
        throw new Exception("Expected type Formula => Any , got " + expr.getClass.getSimpleName)
    }

    (applied, posArgs, info.numPositionArgs) match {
      // If the tactic accepts arguments but wasn't given any, return the unapplied tactic under the assumption that
      // someone is going to plug in the arguments later
      case (expr:BelleExpr, Nil, _) => expr
      case (expr:BelleExpr with PositionalTactic , arg::Nil, 1) =>
        AppliedPositionTactic(expr, Fixed(arg))
      case (expr:BuiltInTwoPositionTactic, arg1::arg2::Nil, 2) =>
        AppliedTwoPositionTactic(expr, arg1, arg2)
      case (expr, posArgs, num) =>
        if (posArgs.length > num) {
          throw new Exception("Expected either " + num + " or 0 position arguments, got " + posArgs.length)
        } else {
          throw new Exception("Tactics with " + num + " arguments cannot have type " + expr.getClass.getSimpleName)
        }
    }
  }

  def apply(name: String, arguments: List[Either[Formula, SeqPos]] = Nil, generator: Option[Generator[Formula]]) : BelleExpr =
    try {
      build(DerivationInfo.ofCodeName(name), arguments, generator)
    }
    catch {
      case e:java.util.NoSuchElementException =>
        println("Error" + e)
        throw new Exception(s"$name is not recognized as a tactic identifier.")
    }
}

