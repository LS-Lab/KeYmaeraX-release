/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.bellerophon.NamedBelleExpr
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.{IgnoreInBuildTest, SummaryTest}
import org.scalatest.{FlatSpec, Matchers}

import scala.collection.immutable.Set

/**
 * Tests code names of tactics and AxiomInfo for compatibility for TacticExtraction.
 *
 * @author Andre Platzer
 */
@SummaryTest
@IgnoreInBuildTest
class CodeNameChecker extends FlatSpec with Matchers {
  "Tactic codeNames versus AxiomInfo codeNames" should "agree" in {
    val all = DerivationInfo.allInfo
    for (info <- all) {
      println("Checking " + info.codeName)
      instantiateSomeBelle(info) match {
          // made compile by reflection or generalizing type hierarchy for some BelleExpr
        case Some(b: NamedBelleExpr) =>
          if (info.codeName.toLowerCase != b.name.toLowerCase())
            println("TEST: codeName should be changed to a consistent name: " + info.codeName + " alias " + info.canonicalName + " gives " + b.name)
        case None =>
      }
    }
  }

  /** get some silly BelleExpr from info by feeding it its input in a type-compliant way. */
  private def instantiateSomeBelle(info: DerivationInfo): Option[BelleExpr] = {
    val e = info.inputs.foldLeft(info.belleExpr) ((t,arg) => arg match {
      case _: FormulaArg => t.asInstanceOf[Formula=>Any](True)
      case _: VariableArg => t.asInstanceOf[Variable=>Any](Variable("dummy"))
      case _: TermArg => t.asInstanceOf[Term=>Any](Number(42))
    })
    e match {
      case t: BelleExpr => Some(t)
      case _ => println("WARNING: input() and belleExpr() function seem incompatible for DerivationInfo: " + info); None
    }
  }
}
