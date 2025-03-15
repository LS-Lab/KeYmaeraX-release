/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon.{BelleExpr, NamedBelleExpr}
import org.keymaerax.btactics.macros.*
import org.keymaerax.core.*
import org.keymaerax.infrastruct.PosInExpr
import org.keymaerax.tags.CheckinTest
import org.scalatest.matchers.should.Matchers

/** Tests code names of tactics for consistency with their [[TacticInfo]]. */
@CheckinTest
class CodeNameChecker extends TacticTestBase with Matchers {
  private def buildTacticWithBogusData(info: TacticInfo): BelleExpr = {
    val args = info
      .constructor
      .args
      .map {
        case _: GeneratorArg => TactixLibrary.invGenerator
        case _: FormulaArg => True
        case _: StringArg => "hi"
        case _: NumberArg => Number(42)
        case _: VariableArg => Variable("dummy")
        case _: TermArg => Number(42)
        case _: SubstitutionArg => SubstitutionPair(Variable("dummy"), Variable("dummy"))
        case _: ExpressionArg => Variable("dummy")
        case _: PosInExprArg => PosInExpr(List(1, 1))
        case _: OptionArg => None
        case _: ListArg => Nil
      }
    info.constructor.construct(args).asInstanceOf[BelleExpr]
  }

  "Tactic codeNames" should "match their DerivationInfo" in withMathematica { _ =>
    val allTacticInfo = DerivationInfo
      .allInfo
      .flatMap { case (name, info) =>
        info match {
          case info: TacticInfo => Some((name, info))
          case _ => None
        }
      }

    for ((name, info) <- allTacticInfo) {
      name shouldBe info.codeName

      buildTacticWithBogusData(info) match {
        case expr: NamedBelleExpr => expr.name shouldBe info.codeName
        case _ => // No name is fine too, only inconsistent names are bad
      }
    }
  }
}
