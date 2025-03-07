/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon.{BelleExpr, NamedBelleExpr}
import org.keymaerax.btactics.macros.*
import org.keymaerax.btactics.macros.DerivationInfoAugmentors.*
import org.keymaerax.core.*
import org.keymaerax.infrastruct.PosInExpr
import org.keymaerax.lemma.Lemma
import org.keymaerax.tags.IgnoreInBuildTest
import org.scalatest.matchers.should.Matchers

import scala.reflect.runtime.universe as ru

/**
 * Tests code names of tactics and AxiomInfo for compatibility for TacticExtraction.
 *
 * @author
 *   Andre Platzer
 */
@IgnoreInBuildTest
class CodeNameChecker extends TacticTestBase with Matchers {
  // @todo also reflect through all DerivedAxioms to check they've been added to AxiomInfo
  "Tactic codeNames versus AxiomInfo codeNames" should "agree" in withMathematica { _ =>
    val all = DerivationInfo.allInfo
    for ((name, info) <- all) {
      // println("Checking " + info.codeName)
      instantiateSomeBelle(info) match {
        // made compile by reflection or generalizing type hierarchy for some BelleExpr
        case Some(b: NamedBelleExpr) => if (info.codeName != b.name) println(
            "TEST(WARNING): codeName should be changed to a consistent name: " + info.codeName + " alias " +
              info.canonicalName + " gives " + b.name
          )
        case Some(b: BelleExpr) => println(
            "TEST: belleExpr does not have a codeName: " + info.codeName + " alias " + info.canonicalName + " gives " +
              b
          )
        case None =>
          println("TEST(INFO): cannot instantiate belleExpr " + info.codeName + " alias " + info.canonicalName)
      }
    }
  }

  "Derived axioms" should "all be specified in AxiomInfo" in withMathematica { _ =>
    val lemmas = Ax.getClass.getDeclaredFields.filter(f => classOf[Lemma].isAssignableFrom(f.getType))
    val fns = lemmas.map(_.getName)

    val mirror = ru.runtimeMirror(getClass.getClassLoader)
    // access the singleton object
    val moduleMirror = mirror.reflectModule(ru.typeOf[Ax.type].termSymbol.asModule)
    val im = mirror.reflect(moduleMirror.instance)

    // @note lazy vals have a "hidden" getter method that does the initialization
    val fields = fns.map(fn => fn -> ru.typeOf[Ax.type].member(ru.TermName(fn)).asMethod.getter.asMethod)
    val fieldMirrors = fields.map(f => im.reflectMethod(f._2))

    Range(0, fieldMirrors.length - 1).foreach(idx => {
      try {
        val axiom = fieldMirrors(idx)().asInstanceOf[Lemma]
        // println("Checking " + axiom.name)
        try {
          ProvableInfo.ofStoredName(
            axiom.name.getOrElse(fail("Derived axiom without name defined in " + fieldMirrors(idx).symbol.name))
          )
        } catch {
          case _: Throwable => println(
              "TEST(WARNING): codeName of axiom " + axiom.name +
                " not found in DerivationInfo, should be added/changed to a consistent name"
            )
        }

      } catch {
        case _: Throwable => println("TEST(INFO): cannot instantiate derived axiom " + fieldMirrors(idx).symbol.name)
      }
    })
  }

  /** get some silly BelleExpr from info by feeding it its input in a type-compliant way. */
  private def instantiateSomeBelle(info: DerivationInfo): Option[BelleExpr] =
    try {
      val e = info
        .inputs
        .foldLeft(info.belleExpr) { (e, i) =>
          val arg: Any = i match {
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
          e.asInstanceOf[Any => ?](arg)
        }
      e match {
        case t: BelleExpr => Some(t)
        case _ =>
          println("WARNING: input() and belleExpr() function seem incompatible for DerivationInfo: " + info); None
      }
    } catch { case _: NotImplementedError => None }
}
