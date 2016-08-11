/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.SummaryTest
import org.scalatest.{Matchers, FlatSpec}

import scala.collection.immutable.Set

/**
 * Tests free variables
 *
 * @author Andre Platzer
 */
@SummaryTest
class CodeNameChecker extends FlatSpec with Matchers {
  "Tactic codeNames versus AxiomInfo codeNames" should "agree" in {
    val all = DerivationInfo.allInfo
    for (info <- all) {
      instantiateSomeBelle(info) match {
          //@todo make compile by reflection or generalizing type hierarchy for some BelleExpr
        case Some(b) => //@todo info.codeName.toLowerCase shouldBe (b.name.toLowerCase())
        case None =>
      }
    }
  }

  /** get some silly BelleExpr from info by feeding it its input */
  private def instantiateSomeBelle(info: DerivationInfo): Option[BelleExpr] = {
    val e = info.inputs.foldLeft(info.belleExpr) ((t,arg) => arg match {
      case _: FormulaArg => t.asInstanceOf[Formula=>Any](True)
      case _: VariableArg => t.asInstanceOf[Variable=>Any](Variable("dummy"))
      case _: TermArg => t.asInstanceOf[Term=>Any](Number(42))
    })
    e match {
      case t: BelleExpr => Some(t)
      case _ => println("WARNING: input and function seem incompatible for DerivationInfo: " + info); None
    }
  }
}
